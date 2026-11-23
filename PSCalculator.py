# -*- coding: utf-8 -*-
"""體力分配計算機 —— Tkinter GUI 主程式。

主要結構：
  * 頂端選單列「設定」（帳號新增刪除／重置與回復／任務清單／獎勵道具／匯入匯出）、「說明」
  * 頂部固定「帳號切換」，開程式自動載入上次使用的帳號
  * 六個分頁：目前狀態 / 活動設定 / 排程設定 /
    任務進度 / 計算結果 / 每日紀錄
  * 活動與任務所有帳號共用；積分、加成、體力上限、任務進度各帳號獨立
"""

from __future__ import annotations

import contextlib
import copy
import ctypes
import json
import os
import re
import threading
import time
import traceback
from datetime import date, datetime, timedelta
from pathlib import Path

import tkinter as tk
from tkinter import filedialog, messagebox, ttk
from tkinter import font as tkfont

import scheduler
import storage
from version import __version__

# 「說明 → 使用說明…」打開的操作手冊（網頁版，用預設瀏覽器開），跟程式放在同一個資料夾
# （不是 storage.APP_DIR：資料目錄可以用環境變數搬走，手冊不會跟著搬）
MANUAL_HTML = Path(__file__).resolve().parent / "PSCalculator_操作手冊.html"

# 「說明 → 關於…」顯示的專案網址，點了用預設瀏覽器打開
PROJECT_URL = "https://github.com/yayumicode/PSCalculator"

DAY_FROM_START = "從第一天"
DAY_FROM_END = "從最後一天"

# 每日紀錄的分筆時刻欄位鍵。跟關卡鍵放在同一個 dict 裡，所以取個不可能撞名的
# （關卡鍵長 "<event_id>/<level_id>"，不會有底線開頭的）。
TIME_KEY = "_at"

# 主視窗最小能縮到多小。「實際打法」對話框也用同一個寬度，
# 視窗縮到最小時兩個並排／疊在一起才對得齊。
MIN_WIDTH, MIN_HEIGHT = 613, 640

# 限時體力是用道具發的，面額只有這三種。使用者手上看到的是「幾個 100、幾個 30、
# 幾個 10」，不是總點數，所以輸入用數量、由程式換算。之後遊戲改面額只要改這裡。
STAMINA_ITEMS = (100, 30, 10)
ITEM_KEYS = tuple(f"qty_{denom}" for denom in STAMINA_ITEMS)


def items_total(record) -> int:
    """三種道具的數量換算成總點數（存檔的 amount，排程吃的是它）。"""
    return sum(denom * int(record.get(key) or 0)
               for denom, key in zip(STAMINA_ITEMS, ITEM_KEYS))


def split_amount(amount) -> dict:
    """總點數拆回三種道具的數量（大面額優先）。

    舊資料只存了總點數，畫面要顯示數量就得拆回來。面額是 100/30/10，
    10 的倍數一定拆得盡；遊戲發的體力都是 10 的倍數，拆不盡的零頭不保留。
    """
    left = max(0, int(amount or 0))
    out = {}
    for denom, key in zip(STAMINA_ITEMS, ITEM_KEYS):
        out[key], left = divmod(left, denom)
    return out


def item_specs(label_prefix: str) -> list[dict]:
    """三個數量欄的 specs。面額就 100/30/10 三種。"""
    return [{"key": key, "label": f"{label_prefix}{denom} 點道具",
             "type": "int", "minimum": 0, "default": 0}
            for denom, key in zip(STAMINA_ITEMS, ITEM_KEYS)]


def item_total_text(values) -> str:
    """對話框底下的即時合計。輸入還沒填完整時不要爆掉，顯示破折號就好。"""
    try:
        return f"合計 {items_total(values)} 點"
    except (TypeError, ValueError):
        return "合計 —"


def items_from_record(record) -> dict:
    """編輯用的扁平欄位 → 存檔用的 {面額: 數量}。"""
    return {str(denom): int(record.get(key) or 0)
            for denom, key in zip(STAMINA_ITEMS, ITEM_KEYS)}


def record_from_items(items, amount) -> dict:
    """存檔用的 {面額: 數量} → 編輯用的扁平欄位。

    沒有 items（舊資料）就從總點數拆回來；有 items 但跟總點數對不上
    （手改過 JSON）也以總點數為準——scheduler 吃的是總點數，畫面要跟它一致。
    """
    if not items:
        return split_amount(amount)
    out = {key: int(items.get(str(denom)) or 0)
           for denom, key in zip(STAMINA_ITEMS, ITEM_KEYS)}
    if items_total(out) != int(amount or 0):
        return split_amount(amount)
    return out


def item_summary(record) -> str:
    """清單上顯示的數量：5／6／9。"""
    return "／".join(str(int(record.get(key) or 0)) for key in ITEM_KEYS)


# 基礎積分的常見表在 storage.BASE_POINT_TABLES（依「消耗體力」對應基礎積分）。
# 關卡類型：一個三選一的下拉，底下對應 scoring / counts_clears 兩個布林。
# 「只算次數」是活動BOSS關那種——沒有積分，但要算進「總量最低關卡數」。
LEVEL_KINDS = [
    ("scoring", "計分", True, True),
    ("count_only", "只算次數", False, True),
    ("none", "都不算", False, False),
]
LEVEL_KIND_CHOICES = [(key, label) for key, label, _s, _c in LEVEL_KINDS]
LEVEL_KIND_FLAGS = {key: (sc, co) for key, _l, sc, co in LEVEL_KINDS}
LEVEL_KIND_LABELS = dict(LEVEL_KIND_CHOICES)


def level_kind_of(record) -> str:
    """關卡記錄 → 類型代號。

    編輯中的記錄帶著對話框選的 `kind`，以它為準；直接從 shared_config 讀出來的
    關卡沒有這個鍵，就照 scoring／counts_clears 推（舊資料只有 scoring）。
    """
    kind = record.get("kind")
    if kind in LEVEL_KIND_FLAGS:
        return kind
    if record.get("scoring"):
        return "scoring"
    counts = record.get("counts_clears", record.get("scoring", True))
    return "count_only" if counts else "none"


def level_is_scoring(record) -> bool:
    return level_kind_of(record) == "scoring"


def open_day_text(offset) -> str:
    """關卡的開放日（相對起始日的天數）：None＝全期，0＝第 1 天（起始日）起。"""
    return "全期" if offset is None else f"第 {int(offset) + 1} 天起"


def level_summary(level) -> str:
    """一關的設定講成一句：「10 體、都不算、第 8 天起、必打 3 次、同日」。"""
    parts = [f"{level.get('stamina_cost', 0)} 體",
             LEVEL_KIND_LABELS.get(level_kind_of(level), "")]
    if level.get("available_from") is not None:
        parts.append(open_day_text(level["available_from"]))
    cap = level.get("max_total")
    if cap:
        parts.append(("必打" if level.get("must_finish") else "共") + f" {cap} 次")
        if level.get("same_day") and cap > 1:
            parts.append("同日")
    if level.get("unlock_first"):
        parts.append("先解鎖")
    return "、".join(p for p in parts if p)


# 體力來源的預設值。kind：daily＝期間內每天、weekly＝期間內每週、
# monthly＝期間內每個月的指定幾號、once＝某天一次。
# 面額只有 100/30/10 三種，所有來源都是這三種的組合。
# 第四格是「新增時要帶入的欄位」，除了道具數量之外也可以帶該型態專用的欄位。
STAMINA_SOURCE_PRESETS = [
    ("big_card", "大月卡", "daily", {"qty_100": 1, "qty_30": 0, "qty_10": 0}),
    ("small_card", "小月卡", "daily", {"qty_100": 0, "qty_30": 2, "qty_10": 0}),
    ("daily_task", "每日任務", "daily", {"qty_100": 0, "qty_30": 1, "qty_10": 0}),
    ("weekly_task", "每週任務", "weekly", {"qty_100": 2, "qty_30": 2, "qty_10": 0}),
    ("checkin", "每日簽到", "monthly", {"qty_100": 0, "qty_30": 0, "qty_10": 2,
                                        "month_days": [5, 11, 17, 23]}),
    # 積分兌換：最晚活動結束後 7 天（週四中午）要換；像信箱一樣記已領取／領取日，
    # 沒填領取日就當成最後一天才領（scheduler.gift_claim_day）
    ("gift", "積分兌換", "once", {"qty_100": 0, "qty_30": 0, "qty_10": 0,
                                  "claimed": False, "claimed_date": ""}),
    # 信箱：收到日起放 29 天、整封一次領，哪天領由排程決定（scheduler.MAIL_HOLD_DAYS）
    ("mail", "信箱", "mail", {"qty_100": 0, "qty_30": 0, "qty_10": 0,
                              "claimed": False}),
    ("custom", "自訂", "daily", {"qty_100": 0, "qty_30": 0, "qty_10": 0}),
]
SOURCE_PRESET_LABELS = {key: label
                        for key, label, _kind, _defaults in STAMINA_SOURCE_PRESETS}
SOURCE_KIND_LABELS = {"daily": "每天", "weekly": "每週", "monthly": "每月",
                      "once": "一次", "mail": "一封"}
# 體力來源的「依據哪一檔活動」多一個「不依據活動」——選了就把日期存成絕對日期，
# 不做偏移量換算。月卡是真實世界的 30 天，綁在某一檔活動上的話活動一結束就不再
# 發體力，那不是使用者的意思。
#
# 這個值**一定要是 truthy 的字串**：程式裡到處是
# `record.get("event_id") or self._first_event_id()`，空字串會被默默吃掉、
# 退回第一檔活動，使用者選的「不依據活動」就這麼消失了。
# 它只活在介面裡——存檔寫的是 `event_id: null` ＋ 絕對日期鍵。
NO_EVENT_ID = "__none__"
NO_EVENT_LABEL = "不依據活動（直接填實際日期）"
NO_EVENT_SHORT = "不依據活動"        # 清單那一列的「依據活動」欄
# 月卡預設不依據活動，期間給今天起算這麼多天（含今天）
MONTHLY_CARD_DAYS = 30
MONTHLY_CARD_PRESETS = ("big_card", "small_card")
# 新增時預設「不依據活動」、日期從今天起算的來源：月卡（真實世界的 30 天）與
# 信箱（收到日）。積分兌換另外處理（預設依據還在兌換期限內的那檔活動）
ABSOLUTE_DATE_PRESETS = MONTHLY_CARD_PRESETS + ("mail",)
DEFAULT_MONTH_DAYS = [5, 11, 17, 23]
# 活動任務的體力獎勵：達標後放著自己去領（排程決定哪一週），還是一達標就自動進包包
REWARD_MODE_CHOICES = [("manual", "手動領取"), ("auto", "達標自動領取")]
WEEKDAY_CHOICES = [(i, name) for i, name in enumerate(
    ["週一", "週二", "週三", "週四", "週五", "週六", "週日"])]

# 表本身定義在 storage（第一次執行建立的預設活動也要用到）
BASE_POINT_TABLES = storage.BASE_POINT_TABLES

SPECIAL_TYPES = [
    ("stamina_cap_override", "當日體力使用上限"),
    ("event_cap_override", "當日該活動體力上限"),
    ("ending_cap_override", "當日結束活動體力上限"),
    ("daily_min_override", "當日最低關卡數"),
    ("daily_enemy_min_override", "當日最低敵人數"),
    ("daily_stamina_min_override", "當日最低耗體"),
]
SPECIAL_TYPE_LABELS = dict(SPECIAL_TYPES)
SPECIAL_TYPE_NOTES = {
    "stamina_cap_override": "當天最多只能用這麼多體力（所有活動合計）",
    "event_cap_override": "只限制當天花在「依據活動」那檔關卡上的體力",
    "ending_cap_override": "當天結束的活動（當期／復刻）合計最多花這麼多；"
                           "當天才開始的新活動、常駐與限期關卡不算",
    "daily_min_override": "當天改成最少打這麼多關（蓋過每日下限）",
    "daily_enemy_min_override": "當天改成最少打這麼多敵人（蓋過每日下限）",
    "daily_stamina_min_override": "當天改成最少耗這麼多體力（蓋過每日下限）",
}
# 「每檔活動自動套用的規則」可以套的活動類型（限期關卡不是活動，不列）
DEFAULT_RULE_TYPE_CHOICES = [(k, v) for k, v in storage.EVENT_TYPES if k != "limited"]


def default_rule_types_text(rule) -> str:
    types = rule.get("event_types")
    if types is None:
        types = scheduler.DEFAULT_RULE_EVENT_TYPES
    return "、".join(storage.EVENT_TYPE_LABELS.get(t, t) for t in types) or "（沒選）"


def special_from_json(entry) -> dict:
    """特殊日規則 JSON → 編輯器記錄。"""
    return {"day_offset": entry.get("day_offset", 0), "type": entry.get("type"),
            "value": entry.get("value") or 0}


def special_to_json(record) -> dict:
    return {"day_offset": record["day_offset"], "type": record["type"],
            "value": record["value"]}

# 「指定日期打指定次數」的方式
LEVEL_TARGET_MODES = [("exact", "剛好"), ("min", "至少")]
# 「指定日期打指定次數」哪幾天套用（見 scheduler.level_target_dates）
LEVEL_TARGET_REPEATS = [("once", "單一日期"), ("dates", "多個日期"),
                        ("weekly", "每週星期幾")]


# --------------------------------------------------------------------------
# 輸入解析
# --------------------------------------------------------------------------

class FieldError(Exception):
    pass


def profile_name_taken(name: str, except_id: str | None = None) -> bool:
    """別的帳號是不是已經叫這個名字（去掉前後空白後比較）。"""
    wanted = (name or "").strip()
    return any(pid != except_id and (other or "").strip() == wanted
               for pid, other in storage.list_profiles())


NEW_LIMITED_NAME = "新限期關卡"


def next_limited_name(events) -> str:
    """「新增限期系列」的預設名稱：新限期關卡、新限期關卡2、新限期關卡3……

    連按好幾次時名稱才分得出來。已封存的也算進去，免得跟收起來的那幾檔撞名。
    """
    used = []
    for event in events or []:
        name = (event.get("name") or "").strip()
        if name == NEW_LIMITED_NAME:
            used.append(1)
        elif name.startswith(NEW_LIMITED_NAME) and name[len(NEW_LIMITED_NAME):].isdigit():
            used.append(int(name[len(NEW_LIMITED_NAME):]))
    if not used:
        return NEW_LIMITED_NAME
    return f"{NEW_LIMITED_NAME}{max(used) + 1}"


class _SolveCancelled(Exception):
    """按了「停止計算」：在下一個求解階段開始前收工。"""


def kill_solver_processes() -> int:
    """結束本程式底下正在跑的 CBC（cbc.exe）子程序，回傳結束了幾個。

    PuLP 是開子程序跑 CBC 的，等它跑完可能要幾十秒。直接結束它，PuLP 會丟出
    錯誤、背景執行緒馬上收工。只認自己的子程序，不會動到別的程式。
    Windows 以外的系統什麼都不做（照樣會在下一個階段開始前停下）。
    """
    if os.name != "nt":
        return 0
    from ctypes import wintypes

    class ProcessEntry(ctypes.Structure):
        _fields_ = [("dwSize", wintypes.DWORD), ("cntUsage", wintypes.DWORD),
                    ("th32ProcessID", wintypes.DWORD),
                    ("th32DefaultHeapID", ctypes.c_size_t),
                    ("th32ModuleID", wintypes.DWORD), ("cntThreads", wintypes.DWORD),
                    ("th32ParentProcessID", wintypes.DWORD),
                    ("pcPriClassBase", ctypes.c_long), ("dwFlags", wintypes.DWORD),
                    ("szExeFile", ctypes.c_wchar * 260)]

    killed = 0
    try:
        kernel32 = ctypes.windll.kernel32
        kernel32.CreateToolhelp32Snapshot.restype = ctypes.c_void_p
        kernel32.Process32FirstW.argtypes = [ctypes.c_void_p, ctypes.POINTER(ProcessEntry)]
        kernel32.Process32NextW.argtypes = [ctypes.c_void_p, ctypes.POINTER(ProcessEntry)]
        kernel32.OpenProcess.restype = ctypes.c_void_p
        kernel32.TerminateProcess.argtypes = [ctypes.c_void_p, ctypes.c_uint]
        kernel32.CloseHandle.argtypes = [ctypes.c_void_p]
        snapshot = kernel32.CreateToolhelp32Snapshot(0x2, 0)      # TH32CS_SNAPPROCESS
        if not snapshot or snapshot == ctypes.c_void_p(-1).value:
            return 0
        targets = []
        try:
            entry = ProcessEntry()
            entry.dwSize = ctypes.sizeof(ProcessEntry)
            ok = kernel32.Process32FirstW(snapshot, ctypes.byref(entry))
            while ok:
                if (entry.th32ParentProcessID == os.getpid()
                        and entry.szExeFile.lower() == "cbc.exe"):
                    targets.append(entry.th32ProcessID)
                ok = kernel32.Process32NextW(snapshot, ctypes.byref(entry))
        finally:
            kernel32.CloseHandle(snapshot)
        for pid in targets:
            handle = kernel32.OpenProcess(0x1, False, pid)          # PROCESS_TERMINATE
            if handle:
                if kernel32.TerminateProcess(handle, 1):
                    killed += 1
                kernel32.CloseHandle(handle)
    except (OSError, AttributeError):
        pass
    return killed


# 報告裡實際會出現的字元。挑字型時要拿這一整組去驗，
# 光驗一個「日」不夠——MS Gothic 的「日」是乾淨的 2 倍，
# 但 ×、←、全形空白卻是 1.86 倍，表格照樣會歪。
_REPORT_CHARS = "0Aa日關卡（）×★←、：＝－　 ／~"


def step_value(var: tk.StringVar, delta: int, minimum: int | None = 0) -> None:
    """把輸入框裡的數字加減 delta；空白或非數字都當作 0。"""
    try:
        current = int((var.get() or "0").strip())
    except ValueError:
        current = 0
    value = current + delta
    if minimum is not None:
        value = max(minimum, value)
    var.set(str(value))


def stepper_box(parent, var: tk.StringVar, minimum: int | None = 0):
    """「－ 輸入框 ＋」一組控制項。記錄實際打法時多半只是加減一兩次，

    左右各放一顆按鈕比全選重打快得多；仍然可以直接鍵入。
    """
    frame = ttk.Frame(parent)
    ttk.Button(frame, text="－", width=3,
               command=lambda: step_value(var, -1, minimum)).pack(side="left")
    ttk.Entry(frame, textvariable=var, width=6, justify="center"
              ).pack(side="left", padx=dp(5))
    ttk.Button(frame, text="＋", width=3,
               command=lambda: step_value(var, 1, minimum)).pack(side="left")
    return frame


# --------------------------------------------------------------------------
# 畫面縮放（Ctrl + / Ctrl − / 右下角滑桿）
# --------------------------------------------------------------------------
# Tk 沒辦法像 Excel 把整個畫面等比例放大，做法是把全程式共用的具名字型
# 改大小，版面跟著字重新排。寫死成像素的東西（表格欄寬、列高、折行寬度）
# 要另外跟著比例走：新建的用 px()，已經在畫面上的由 apply_zoom() 調整。
ZOOM_MIN, ZOOM_MAX, ZOOM_STEP = 80, 200, 10
# 不含 TkMenuFont：選單另外用 NuMenuFont（見 menu_font），系統的 TkMenuFont 不去動它
_ZOOM_FONTS = ("TkDefaultFont", "TkTextFont", "TkFixedFont", "TkHeadingFont",
               "TkCaptionFont", "TkSmallCaptionFont", "TkIconFont",
               "TkTooltipFont")
REPORT_FONT = "NuReportFont"
# dpi：螢幕實際 DPI ÷ 96（Windows 顯示比例 150% 就是 1.5），見 enable_dpi_awareness
_zoom = {"percent": 100, "base": {}, "dpi": 1.0}


def enable_dpi_awareness() -> None:
    """跟 Windows 說這個程式會自己照顯示比例畫，要在建立 Tk 之前呼叫。

    不說的話，顯示比例不是 100% 時 Windows 會把整個程式（連同它開的選檔視窗）
    先照 100% 畫好、再整張點陣圖拉大，字就糊了。說了之後 Tk 的字型
    （以點為單位）會自動照實際 DPI 放大，寫死的像素數則要靠 px()／dp() 換算。
    """
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(1)     # 1 = 系統 DPI 感知
    except (AttributeError, OSError):
        try:
            ctypes.windll.user32.SetProcessDPIAware()      # Windows 8 以前
        except (AttributeError, OSError):
            pass


def init_dpi(root) -> None:
    """量出螢幕比例。沒開 DPI 感知時 Tk 量到的永遠是 96，比例就是 1。"""
    try:
        # 量到的會有 96.05 這種誤差，取到小數兩位：100% 時比例要剛好是 1，
        # 版面才跟沒開 DPI 感知時一模一樣
        _zoom["dpi"] = max(1.0, round(root.winfo_fpixels("1i") / 96, 2))
    except tk.TclError:
        _zoom["dpi"] = 1.0


def dp(pixels: float) -> int:
    """顯示比例 100% 時的像素數換算成實際螢幕像素（不跟著程式內的縮放走）。

    用在間距、邊框留白這類不需要隨 Ctrl＋ 放大的地方。
    """
    return round(pixels * _zoom["dpi"])


def px(pixels: float) -> int:
    """100% 時的像素數換算成目前縮放比例（含螢幕顯示比例）下的像素數。"""
    return round(pixels * _zoom["percent"] / 100 * _zoom["dpi"])


def report_font() -> str:
    """報表用的等寬字型（具名字型，會跟著縮放）。第一次用到才挑。"""
    if REPORT_FONT not in tkfont.names():
        picked = pick_report_font()
        font = tkfont.Font(name=REPORT_FONT, font=picked, exists=False)
        # 要留著這個物件：它被回收時 tkinter 會把字型從 Tk 刪掉，縮放就改不到了
        _zoom["report_font"] = font
        # 挑到的若是 TkFixedFont，它的大小已經是縮放過的；基準要拿它 100% 的
        # 大小，不然會再乘一次比例（130% 時報表字變成 1.3×1.3 倍）
        _zoom["base"][REPORT_FONT] = _zoom["base"].get(picked, font.cget("size")) \
            if isinstance(picked, str) else font.cget("size")
        _rescale_named(REPORT_FONT)
    return REPORT_FONT


MENU_FONT = "NuMenuFont"


def menu_font() -> str:
    """下拉選單（選單列展開的項目、右鍵選單）用的字型，會跟著縮放。

    選單列本身不用它：那是 Windows 原生畫的，換字型反而變小。
    """
    if MENU_FONT not in tkfont.names():
        font = tkfont.Font(name=MENU_FONT, font="TkMenuFont", exists=False)
        _zoom["menu_font"] = font
        _zoom["base"][MENU_FONT] = font.cget("size")    # TkMenuFont 不縮放，就是 100%
        _rescale_named(MENU_FONT)
    return MENU_FONT


def _rescale_named(name):
    size = _zoom["base"][name]
    scaled = max(1, round(abs(size) * _zoom["percent"] / 100))
    tkfont.nametofont(name).configure(size=-scaled if size < 0 else scaled)


def _remember_tree_widths(tree, percent=None):
    """記下這張表各欄在 100% 時的寬度，之後縮放都從這個基準算，來回縮放不會越跑越偏。"""
    percent = percent or _zoom["percent"]
    tree._nu_base_widths = {
        column: tree.column(column, "width") * 100 / percent
        for column in tree["columns"]}


def apply_zoom(root, percent) -> int:
    """把整個程式縮放到 percent%（會夾在 ZOOM_MIN~ZOOM_MAX）。回傳實際套用的比例。"""
    percent = max(ZOOM_MIN, min(ZOOM_MAX, int(round(percent))))
    old = _zoom["percent"]
    base = _zoom["base"]
    for name in _ZOOM_FONTS:
        if name not in base:
            try:
                base[name] = tkfont.nametofont(name).cget("size")
            except tk.TclError:
                continue
    _zoom["percent"] = percent
    for name, size in base.items():
        scaled = max(1, round(abs(size) * percent / 100))
        try:
            tkfont.nametofont(name).configure(size=-scaled if size < 0 else scaled)
        except tk.TclError:
            pass

    # 表格列高是固定像素（預設 20），不跟著字型走的話字放大會被切掉
    body = tkfont.nametofont("TkDefaultFont")
    ttk.Style(root).configure("Treeview", rowheight=body.metrics("linespace") + dp(5))

    # 已經在畫面上的表格：欄寬依 100% 的基準重算
    def walk(widget):
        for child in widget.winfo_children():
            if isinstance(child, ttk.Treeview):
                if not hasattr(child, "_nu_base_widths"):
                    _remember_tree_widths(child, old)
                for column, width in child._nu_base_widths.items():
                    try:
                        child.column(column, width=round(width * percent / 100))
                    except tk.TclError:
                        pass
            walk(child)
    if old != percent:
        walk(root)
    sync_ime_font(root.focus_get())
    return percent


# 打中文還在選字時（字底下有虛線那段），字是 Windows 輸入法自己畫的，
# 用的是輸入法預設的小字型，不是輸入框的字型；Tk 8.6 也不會幫忙設。
# 程式放大後兩者差很多，所以輸入框一拿到焦點、或縮放比例改了，
# 就把輸入框的字型告訴輸入法（ImmSetCompositionFontW）。
_IME_CLASSES = ("TEntry", "TCombobox", "TSpinbox", "Entry", "Spinbox", "Text")


class _LOGFONTW(ctypes.Structure):
    _fields_ = [("lfHeight", ctypes.c_long), ("lfWidth", ctypes.c_long),
                ("lfEscapement", ctypes.c_long), ("lfOrientation", ctypes.c_long),
                ("lfWeight", ctypes.c_long), ("lfItalic", ctypes.c_byte),
                ("lfUnderline", ctypes.c_byte), ("lfStrikeOut", ctypes.c_byte),
                ("lfCharSet", ctypes.c_byte), ("lfOutPrecision", ctypes.c_byte),
                ("lfClipPrecision", ctypes.c_byte), ("lfQuality", ctypes.c_byte),
                ("lfPitchAndFamily", ctypes.c_byte), ("lfFaceName", ctypes.c_wchar * 32)]


def _ime_logfont(widget) -> _LOGFONTW | None:
    """輸入框目前的字型換成 Windows 的 LOGFONT（高度用實際像素）。"""
    try:
        named = str(widget.cget("font"))
    except tk.TclError:
        named = ""
    if not named:
        named = str(ttk.Style(widget).lookup(widget.winfo_class(), "font")) or "TkTextFont"
    try:
        actual = tkfont.Font(font=named).actual()
        points = actual["size"]
        pixels = -points if points < 0 else points * widget.winfo_fpixels("1p")
    except tk.TclError:
        return None
    lf = _LOGFONTW()
    lf.lfHeight = -max(1, round(pixels))
    lf.lfWeight = 700 if actual.get("weight") == "bold" else 400
    lf.lfItalic = 1 if actual.get("slant") == "italic" else 0
    lf.lfCharSet = 1                                   # DEFAULT_CHARSET
    lf.lfFaceName = actual["family"][:31]
    return lf


def sync_ime_font(widget) -> None:
    """把輸入法選字中那段字的字型改成跟 widget（輸入框）一樣。"""
    if widget is None or not hasattr(ctypes, "windll"):
        return
    try:
        if widget.winfo_class() not in _IME_CLASSES:
            return
        lf = _ime_logfont(widget)
        if lf is None:
            return
        user32, imm32 = ctypes.windll.user32, ctypes.windll.imm32
        user32.GetFocus.restype = ctypes.c_void_p
        imm32.ImmGetContext.restype = ctypes.c_void_p
        imm32.ImmGetContext.argtypes = [ctypes.c_void_p]
        imm32.ImmSetCompositionFontW.argtypes = [ctypes.c_void_p, ctypes.POINTER(_LOGFONTW)]
        imm32.ImmReleaseContext.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
        hwnd = user32.GetFocus() or widget.winfo_id()
        himc = imm32.ImmGetContext(hwnd)
        if himc:
            imm32.ImmSetCompositionFontW(himc, ctypes.byref(lf))
            imm32.ImmReleaseContext(hwnd, himc)
    except (tk.TclError, AttributeError, OSError, KeyError):
        pass


def install_ime_font_sync(root) -> None:
    """所有輸入框拿到焦點時都同步一次輸入法字型。"""
    for cls in _IME_CLASSES:
        root.bind_class(cls, "<FocusIn>", lambda e: sync_ime_font(e.widget), add="+")


@contextlib.contextmanager
def _frozen_redraw(root):
    """這段期間主視窗不重繪，結束後一次整個畫出來。

    換字型後 Tk 的版面要跑好幾輪 idle 才排完，每輪之間都會畫一次，使用者就會
    看到字先變大、再撐開、欄寬再跳的中間過程（抖動）。用 Windows 的
    WM_SETREDRAW 先擋住重繪，排完再一次畫。不是 Windows、視窗還沒顯示
    （啟動時、測試用的隱藏視窗）或呼叫失敗就不凍結，照常重繪。

    凍結的是 winfo_id()（Tk 的內容視窗），不是 wm_frame() 的外框：凍結外框
    會讓 Tk 把內容視窗設成隱藏，解凍後整片空白。

    擋不乾淨的地方：表格換字型時偶爾會比其他部分早一拍（約 0.1 秒）畫出來。
    """
    hwnd = None
    try:
        if root.winfo_ismapped():
            hwnd = root.winfo_id()
            ctypes.windll.user32.SendMessageW(hwnd, _WM_SETREDRAW, 0, 0)
    except (AttributeError, OSError, ValueError, tk.TclError):
        hwnd = None
    try:
        yield
    finally:
        if hwnd is not None:
            user32 = ctypes.windll.user32
            user32.SendMessageW(hwnd, _WM_SETREDRAW, 1, 0)
            # 不清背景（清了會先閃一片灰），直接要每個元件重畫
            user32.RedrawWindow(hwnd, None, None, _RDW_REDRAW_ALL)
            # 重畫通知進了 Tk 的事件佇列，馬上處理掉並畫完，不要等回到事件迴圈
            # 再一塊一塊畫（那樣又會看到一格一格出現）
            _drain_window_events(root)
            root.update_idletasks()


def _drain_window_events(root) -> int:
    """把佇列裡的視窗事件（大小改變、重畫）處理掉，不碰計時器和檔案事件。

    回傳處理了幾個事件。
    """
    for count in range(500):
        if not root.tk.dooneevent(_TK_WINDOW_EVENTS | _TK_DONT_WAIT):
            return count
    return 500


def _settle_window(window) -> None:
    """排版 → 處理視窗事件，重複到沒有事件為止。

    視窗大小一改，系統送回的 Configure 又讓幾何管理員排一輪 idle 重排、
    ScrollableFrame 也會再排一次（見 _on_canvas_configure），重排完又冒出新的
    Configure。只跑一輪的話剩下的會在對話框現身之後才做，就看得到欄位在動。
    """
    for _ in range(10):
        window.update_idletasks()
        if not _drain_window_events(window):
            break


def _descendants(widget, kind):
    for child in widget.winfo_children():
        if isinstance(child, kind):
            yield child
        yield from _descendants(child, kind)


_WM_SETREDRAW = 0x000B
# RDW_INVALIDATE | RDW_ALLCHILDREN | RDW_UPDATENOW | RDW_FRAME
_RDW_REDRAW_ALL = 0x0001 | 0x0080 | 0x0100 | 0x0400
_TK_DONT_WAIT, _TK_WINDOW_EVENTS = 2, 4


def _refresh_tree_scrollbars(widget):
    """欄寬改了之後 Treeview 不會主動通知橫向捲軸，要等視窗大小變了才更新。

    來回捲一下逼它重報捲動範圍，該出現的捲軸才會馬上出現。
    """
    for child in widget.winfo_children():
        if isinstance(child, ttk.Treeview) and child.cget("xscrollcommand"):
            try:
                first = child.xview()[0]
                child.xview_moveto(1.0)
                child.xview_moveto(first)
            except tk.TclError:
                pass
        _refresh_tree_scrollbars(child)


def pick_report_font(size: int = 10):
    """挑一個實際寬度跟 scheduler.text_width 完全吻合的等寬字型。

    報告是用空白排版的表格，只要有一個字元的寬度跟計算不符，整欄就會歪掉。
    所以逐字驗證，而不是只看比值。
    """
    from tkinter import font as tkfont

    def fits(probe):
        unit = probe.measure("0")
        if not unit:
            return False
        return all(probe.measure(ch) == unit * scheduler.text_width(ch)
                   for ch in _REPORT_CHARS)

    families = set(tkfont.families())
    for family in ("細明體", "MingLiU", "MS Gothic", "NSimSun", "Consolas"):
        if family in families and fits(tkfont.Font(family=family, size=size)):
            return (family, size)
    default = tkfont.Font(font="TkFixedFont")
    if fits(default):
        return "TkFixedFont"
    # 都不合格就退回等寬字型，至少純數字的欄位還會對齊
    return "TkFixedFont"


def format_date_digits(text: str) -> str:
    """把使用者輸入的字元濃縮成數字，再補上 YYYY-MM-DD 的連字號。

    「20260827」和「2026-08-27」都會變成「2026-08-27」，
    所以貼上既有日期或純打數字都通。
    """
    digits = "".join(ch for ch in text if ch.isdigit())[:8]
    parts = [digits[:4], digits[4:6], digits[6:8]]
    return "-".join(part for part in parts if part)


def _pos_after_digits(text: str, count: int) -> int:
    """回傳「第 count 個數字之後」的字元位置，用來還原游標。"""
    if count <= 0:
        return 0
    seen = 0
    for index, ch in enumerate(text):
        if ch.isdigit():
            seen += 1
            if seen == count:
                return index + 1
    return len(text)


def example_date(fmt: str = "%Y%m%d", days: int = 0) -> str:
    """提示文字裡「例如 …」用的日期：今天（再加 days 天），不寫死。

    寫死的日期過一陣子就變成過去的日子，看起來像要填以前的日期。
    8 碼數字長度固定，拿來量提示寬度也不受影響。
    """
    return (date.today() + timedelta(days=days)).strftime(fmt)


def text_width_chars(text: str, font_name: str = "TkDefaultFont") -> int:
    """ttk.Label 的 width 是「平均字元寬」的個數，換算一段文字要幾個。

    字型縮放時兩邊一起變大，算一次就好。中文字約佔兩個平均字元寬。
    """
    font = tkfont.nametofont(font_name)
    return -(-font.measure(text) // max(1, font.measure("0"))) + 1


class DateEntry(ttk.Entry):
    """日期輸入框：只收數字，連字號自動補上，不必自己打。

    旁邊的 hint_label 會顯示星期幾當作確認——這個程式的週次是以
    週一到週日切的，看得到星期幾比較不會設錯。
    """

    @staticmethod
    def empty_hint() -> str:
        """空白時的提示，也是三種提示裡最長的一句（固定提示寬度時拿它來量）。

        例子用今天的日期（見 example_date）；長度固定 8 碼，寬度不會變。
        """
        return f"只要打數字，例如 {example_date()}"

    def __init__(self, master, textvariable, hint_label=None, **kwargs):
        super().__init__(master, textvariable=textvariable, **kwargs)
        self._var = textvariable
        self._hint = hint_label
        self._guard = False
        self._pending = None
        self._var.trace_add("write", self._on_write)
        self._update_hint()

    def _on_write(self, *_args):
        if self._guard:
            return
        # trace 是在「元件還沒把游標移到新位置」時就觸發的，這時讀到的游標
        # 會少算剛打進去的那個字，補上的連字號就會插錯位置——打 20260803
        # 會變成 2026-80-30。排到 idle 再處理，那時元件狀態才是完整的。
        if self._pending is None:
            self._pending = self.after_idle(self._reformat)

    def _reformat(self):
        self._pending = None
        if not self.winfo_exists():
            return
        raw = self._var.get()
        formatted = format_date_digits(raw)
        if formatted != raw:
            try:
                digits_before = sum(1 for ch in raw[:self.index("insert")]
                                    if ch.isdigit())
            except tk.TclError:        # 還沒 realize 的元件量不到游標
                digits_before = len(formatted)
            self._guard = True
            self._var.set(formatted)
            self._guard = False
            self.icursor(_pos_after_digits(formatted, digits_before))
        self._update_hint()

    def _update_hint(self):
        if self._hint is None:
            return
        text = self._var.get().strip()
        if not text:
            self._hint.config(text=self.empty_hint(), foreground="#666666")
            return
        try:
            parsed = datetime.strptime(text, "%Y-%m-%d")
        except ValueError:
            self._hint.config(text="日期還沒填完整", foreground="#666666")
            return
        weekday = scheduler.WEEKDAY_NAMES[parsed.weekday()]
        self._hint.config(text=f"星期{weekday}", foreground="#0a5")


def run_modal(window) -> None:
    """把對話框鎖成獨占：關掉之前其他視窗都點不到，關掉之後才回到呼叫端。

    Tk 的 grab 一次只有一個視窗能拿，對話框裡再開對話框時，裡面那個一關，
    grab 就整個放掉了，不會還給外面那個——外面那個還開著，主視窗卻又能點了。
    所以先記下原本拿著 grab 的視窗，等這個關掉再還給它。
    """
    try:
        previous = window.grab_current()
    except (KeyError, tk.TclError):
        previous = None
    try:
        window.grab_set()
    except tk.TclError:
        pass
    window.wait_window(window)
    try:
        if previous is not None and previous.winfo_exists():
            previous.grab_set()
    except tk.TclError:
        pass


def center_on(window, parent) -> None:
    """把 window 移到 parent 的正中央，一開始的大小不超過主視窗。

    只限制「剛打開」的大小；之後使用者要拉得比主視窗大或小都可以，
    所以不動 maxsize，minsize 也只往小調（不然 Tk 會照 minsize 撐回去）。

    Tk 預設會把新視窗開在螢幕左上角，離主視窗很遠。
    要先 update_idletasks() 才量得到實際尺寸，否則拿到的是預設的 1x1。
    """
    window.update_idletasks()
    top = parent.winfo_toplevel()
    width, height = window.winfo_width(), window.winfo_height()
    size = ""
    # 上限看主視窗，不看 parent：從對話框再開的對話框（道具清單 → 新增）
    # 比 parent 寬是正常的，壓成 parent 的寬度反而把右邊的說明切掉
    main = window._root()
    if top is not window and main.winfo_viewable():
        # 剛打開時不超過主視窗的寬高（四周再各留一點，看得出是疊在上面的）：
        # 內容多的對話框都包在 ScrollableFrame 裡，縮小了就是裡面捲動。
        # 之後使用者可以自由拉大拉小，不設 maxsize
        limit_w = max(px(200), main.winfo_width() - px(_DIALOG_MARGIN) * 2)
        limit_h = max(px(150), main.winfo_height() - px(_DIALOG_MARGIN) * 2)
        min_w, min_h = window.minsize()
        window.minsize(min(min_w, limit_w, px(200)), min(min_h, limit_h, px(150)))
        if width > limit_w or height > limit_h:
            width, height = min(width, limit_w), min(height, limit_h)
            height = min(limit_h, height + _regrow_after_narrowing(window, width, height))
            size = f"{width}x{height}"
    # geometry 的 +x+y 是「外框」左上角，不是內容區；要扣掉邊框和標題列，
    # 內容區才會真的置中（不扣的話整個往右下偏一個邊框寬）
    source = window if window.winfo_ismapped() else top
    border = max(0, source.winfo_rootx() - source.winfo_x())
    title = max(0, window.winfo_rooty() - window.winfo_y())         if window.winfo_ismapped() else border + px(_TITLE_BAR)
    x = top.winfo_rootx() + (top.winfo_width() - width) // 2 - border
    y = top.winfo_rooty() + (top.winfo_height() - height) // 2 - title
    if main.winfo_viewable() and window is not main:
        # 比 parent 寬的子對話框照 parent 置中可能跑出主視窗，推回主視窗範圍內
        x = max(main.winfo_rootx() - border,
                min(x, main.winfo_rootx() + main.winfo_width() - width - border))
        y = max(main.winfo_rooty() - title,
                min(y, main.winfo_rooty() + main.winfo_height() - height - title))
    # 夾在螢幕範圍內，免得主視窗貼邊時對話框跑到畫面外
    x = max(0, min(x, window.winfo_screenwidth() - width))
    y = max(0, min(y, window.winfo_screenheight() - height))
    window.geometry(f"{size}+{x}+{y}")
    # 移好位置（系統處理完移動）才現身，見 hide_until_centered
    _settle_window(window)
    try:
        window.attributes("-alpha", _SHOWN_ALPHA)
    except tk.TclError:
        pass


# 對話框現身時的透明度。不用 1.0：Windows 版 Tk 設回 1.0 時會拿掉視窗的分層
# 屬性，接著把整個視窗連同所有子元件擦掉重畫（每個元件都是一個子視窗），
# 看起來就像元件一個一個畫出來。0.999 換算成 254/255，肉眼看不出半透明，
# 視窗一直維持分層，透明期間已經畫好的內容直接顯示出來。
_SHOWN_ALPHA = 0.999


def hide_until_centered(window) -> None:
    """對話框建好、還沒擺到中間前先完全透明。

    Tk 會在閒置時把新視窗顯示在預設位置（螢幕左上角），center_on 再搬到
    主視窗中間，使用者就會看到它在左上角閃一下。透明的期間照樣排版、量大小，
    center_on 擺好位置後才把透明度調回來。建構子一開頭就要呼叫。
    """
    try:
        window.attributes("-alpha", 0.0)
    except tk.TclError:
        pass


def _regrow_after_narrowing(window, width, height) -> int:
    """對話框被壓窄之後，內容會長高多少。

    壓窄後說明文字多折一行、表格冒出自己的橫向捲軸，內容就變高；
    對話框高度還是原本「剛好放得下」的高度的話，最底下（常常就是表格的
    橫向捲軸）會被擠到看不到的地方。回傳多出來的高度，讓呼叫端把視窗加高。
    """
    scrollers = list(_descendants(window, ScrollableFrame))
    before = {sf: sf.inner.winfo_reqheight() for sf in scrollers}
    window.geometry(f"{width}x{height}")
    # 視窗大小要等系統回報（視窗事件）才真的改，光跑 idle 量到的還是舊寬度
    window.update_idletasks()
    _drain_window_events(window)
    window.update_idletasks()
    _refresh_tree_scrollbars(window)
    for sf in scrollers:
        sf.settle()
    window.update_idletasks()
    return max([sf.inner.winfo_reqheight() - before[sf] for sf in scrollers] + [0])


def parse_geometry(text: str):
    """Tk 的 "寬x高+x+y" 拆成 (x, y, 寬, 高)；座標可能是負的（"+-8"）。拆不動回 None。"""
    match = re.fullmatch(r"(\d+)x(\d+)\+?(-?\d+)\+?(-?\d+)", text.strip())
    if not match:
        return None
    width, height, x, y = (int(group) for group in match.groups())
    return (x, y, width, height)


def work_area(rect=None, screen=None) -> tuple:
    """螢幕扣掉工作列之後可以放視窗的範圍 (x, y, 寬, 高)，實際像素。

    rect＝(x, y, 寬, 高) 時取離它最近的那個螢幕（多螢幕、上次開在副螢幕上），
    沒給就是主螢幕。不是 Windows 或查不到時，用 screen＝(寬, 高) 估：
    整個螢幕扣掉底下一條工作列。
    """
    try:
        user32 = ctypes.windll.user32

        class RECT(ctypes.Structure):
            _fields_ = [("left", ctypes.c_long), ("top", ctypes.c_long),
                        ("right", ctypes.c_long), ("bottom", ctypes.c_long)]

        class MONITORINFO(ctypes.Structure):
            _fields_ = [("cbSize", ctypes.c_ulong), ("rcMonitor", RECT),
                        ("rcWork", RECT), ("dwFlags", ctypes.c_ulong)]

        if rect is None:
            area = RECT()
            # SPI_GETWORKAREA：主螢幕的工作區域
            if not user32.SystemParametersInfoW(0x30, 0, ctypes.byref(area), 0):
                raise OSError
        else:
            x, y, width, height = rect
            target = RECT(x, y, x + width, y + height)
            user32.MonitorFromRect.restype = ctypes.c_void_p
            user32.GetMonitorInfoW.argtypes = [ctypes.c_void_p,
                                               ctypes.POINTER(MONITORINFO)]
            # MONITOR_DEFAULTTONEAREST：完全不在任何螢幕上也給最近的那一個
            monitor = user32.MonitorFromRect(ctypes.byref(target), 2)
            info = MONITORINFO()
            info.cbSize = ctypes.sizeof(MONITORINFO)
            if not monitor or not user32.GetMonitorInfoW(monitor, ctypes.byref(info)):
                raise OSError
            area = info.rcWork
        if area.right <= area.left or area.bottom <= area.top:
            raise OSError
        return (area.left, area.top, area.right - area.left, area.bottom - area.top)
    except (AttributeError, OSError, ValueError):
        width, height = screen or (1920, 1080)
        return (0, 0, width, max(1, height - dp(48)))


def plan_main_window(desired, minimum, saved, area_of, frame) -> dict:
    """主視窗剛打開時的大小、位置、要不要最大化。

    desired／minimum：(寬, 高) 內容區的預設與最小尺寸。saved：上次關閉時存的
    （storage.get_window_geometry），沒有就 None。area_of(rect 或 None)：
    回傳工作區域，見 work_area。frame：(左右邊框合計, 標題列＋上下邊框)，
    geometry 的寬高只算內容區，外框要另外加。

    回傳 {"width","height","x","y","zoomed"}，x、y 是外框左上角。

    * 有存過：照上次的大小，但不能超出那個螢幕的工作區域；標題列不在任何
      螢幕上（拔掉了副螢幕、換了解析度）就不用上次的位置，改成在主螢幕置中。
      上次是最大化就照樣最大化。
    * 沒存過：預設大小最多佔主螢幕工作區域的 90%，置中。
    * 工作區域連最小尺寸都放不下（例如 1366×768、或 1920×1080 開 150%）：
      直接最大化，不然視窗底部會被工作列擋住。
    """
    extra_w, extra_h = frame
    min_w, min_h = minimum
    if saved:
        width, height = saved["width"], saved["height"]
        x, y = saved["x"], saved["y"]
        ax, ay, aw, ah = area_of((x, y, width + extra_w, height + extra_h))
        # 標題列（外框最上面那條）至少要有一段在這個螢幕的工作區域裡，
        # 不然使用者抓不到視窗、也搬不回來
        grab = min(width + extra_w, max(1, extra_w * 10))
        visible = (x + width + extra_w - grab >= ax and x + grab <= ax + aw
                   and ay <= y <= ay + ah - extra_h)
        if not visible:
            ax, ay, aw, ah = area_of(None)
        limit_w, limit_h = aw - extra_w, ah - extra_h
        zoomed = saved["zoomed"] or limit_w < min_w or limit_h < min_h
        width = max(min(width, limit_w), min(min_w, limit_w))
        height = max(min(height, limit_h), min(min_h, limit_h))
        if visible:
            # 夾回工作區域內：大小剛剛可能被縮過，原本的位置會讓右下角跑出去
            x = max(ax, min(x, ax + aw - width - extra_w))
            y = max(ay, min(y, ay + ah - height - extra_h))
        else:
            x = ax + max(0, (aw - width - extra_w) // 2)
            y = ay + max(0, (ah - height - extra_h) // 2)
        return {"width": width, "height": height, "x": x, "y": y,
                "zoomed": zoomed}

    ax, ay, aw, ah = area_of(None)
    limit_w = int(aw * 0.9) - extra_w
    limit_h = int(ah * 0.9) - extra_h
    zoomed = limit_w < min_w or limit_h < min_h
    width = max(min(desired[0], limit_w), min(min_w, aw - extra_w))
    height = max(min(desired[1], limit_h), min(min_h, ah - extra_h))
    return {"width": width, "height": height,
            "x": ax + max(0, (aw - width - extra_w) // 2),
            "y": ay + max(0, (ah - height - extra_h) // 2),
            "zoomed": zoomed}


_DIALOG_MARGIN = 16    # 彈出視窗離原視窗邊緣至少這麼多（100% 時的像素）
_MAIN_SIZE = (1060, 760)   # 主視窗預設的內容區大小（100% 時的像素）
_TITLE_BAR = 23         # 還沒顯示、量不到時估的標題列高度（100% 時）


class _MessageDialog(tk.Toplevel):
    """取代 tkinter.messagebox 的對話框，字跟著畫面縮放。

    tkinter.messagebox 在 Windows 上是系統的 MessageBox，字是系統畫的，
    程式縮放到 150% 它還是原本大小。這裡用 Tk 自己畫，字型是 TkDefaultFont。
    """

    _ICONS = {"info": "::tk::icons::information", "warning": "::tk::icons::warning",
              "error": "::tk::icons::error", "question": "::tk::icons::question"}
    _LABELS = {"ok": "確定", "yes": "是(Y)", "no": "否(N)", "cancel": "取消"}

    def __init__(self, parent, title, message, icon, buttons, default, cancel,
                 link=None):
        super().__init__(parent)
        hide_until_centered(self)
        self.title(title)
        # 訊息框不給拉：內容是一段固定折好的文字，拉大拉小都沒有意義
        self.resizable(False, False)
        self.result = cancel
        top = parent.winfo_toplevel() if parent is not None else None
        # 主視窗藏起來時不能 transient，不然對話框跟著一起看不見、程式卡住
        if top is not None and top.winfo_viewable():
            self.transient(top)

        body = tk.Frame(self, background="white", padx=px(20), pady=px(18))
        # 按鈕列等一下用 pack(before=body) 排在它前面：拉矮時先被擠掉的是內文
        body.pack(fill="both", expand=True)
        name = self._ICONS.get(icon or "", self._ICONS["info"])
        try:
            tk.Label(body, image=name, background="white").pack(
                side="left", anchor="n", padx=(0, px(14)))
        except tk.TclError:
            pass
        column = tk.Frame(body, background="white")
        column.pack(side="left", fill="both", expand=True)
        prewrap(tk.Label(column, text=message, justify="left", anchor="w",
                         background="white", font="TkDefaultFont"), px(460)).pack(
                     fill="x")
        if link:
            # 可以點的網址：藍字加底線，滑過去變手指，點了用預設瀏覽器打開
            self._link_font = tkfont.nametofont("TkDefaultFont").copy()
            self._link_font.configure(underline=True)
            label = tk.Label(column, text=link, anchor="w", background="white",
                             foreground="#1d4ed8", cursor="hand2",
                             font=self._link_font)
            label.pack(fill="x", pady=(px(8), 0))
            label.bind("<Button-1>", lambda _e: _open_url(link))

        bar = ttk.Frame(self, padding=(px(12), px(10)))
        bar.pack(side="bottom", fill="x", before=body)
        focus = None
        for key in reversed(buttons):
            button = ttk.Button(bar, text=self._LABELS[key],
                                command=lambda k=key: self._close(k))
            button.pack(side="right", padx=(px(8), 0))
            if key == default:
                focus = button
        for key in buttons:
            if key in ("yes", "no"):
                letter = key[0]
                self.bind(f"<KeyPress-{letter}>", lambda _e, k=key: self._close(k))
                self.bind(f"<KeyPress-{letter.upper()}>", lambda _e, k=key: self._close(k))
        self.bind("<Escape>", lambda _e: self._close(cancel))
        # Enter 按下目前有焦點的那顆（用 Tab 換過焦點就是換過的那顆）
        self.bind("<Return>", lambda _e: self._press_focused(default))
        self.protocol("WM_DELETE_WINDOW", lambda: self._close(cancel))

        if icon in ("warning", "error"):
            self.bell()
        center_on(self, top or self)
        (focus or self).focus_set()
        run_modal(self)

    def _close(self, key):
        self.result = key
        self.destroy()

    def _press_focused(self, default):
        widget = self.focus_get()
        if isinstance(widget, ttk.Button):
            widget.invoke()
        else:
            self._close(default)


class _ScaledMessageBox:
    """跟 tkinter.messagebox 同樣的呼叫方式（showinfo／askyesno…），用 _MessageDialog 顯示。"""

    @staticmethod
    def _ask(title, message, icon, buttons, default, cancel, options):
        parent = options.get("parent") or tk._default_root
        icon = options.get("icon") or icon
        default = options.get("default") or default
        return _MessageDialog(parent, title or "", message or "", icon, buttons,
                              default, cancel, link=options.get("link")).result

    def showinfo(self, title=None, message=None, **options):
        return self._ask(title, message, "info", ["ok"], "ok", "ok", options)

    def showwarning(self, title=None, message=None, **options):
        return self._ask(title, message, "warning", ["ok"], "ok", "ok", options)

    def showerror(self, title=None, message=None, **options):
        return self._ask(title, message, "error", ["ok"], "ok", "ok", options)

    def askyesno(self, title=None, message=None, **options):
        return self._ask(title, message, "question", ["yes", "no"], "yes", "no",
                         options) == "yes"

    def askokcancel(self, title=None, message=None, **options):
        return self._ask(title, message, "question", ["ok", "cancel"], "ok", "cancel",
                         options) == "ok"

    def askyesnocancel(self, title=None, message=None, **options):
        result = self._ask(title, message, "question", ["yes", "no", "cancel"], "yes",
                           "cancel", options)
        return None if result == "cancel" else result == "yes"


messagebox = _ScaledMessageBox()


def flash_if_inactive(window) -> None:
    """視窗不在最前面時讓工作列上的圖示閃爍，切回來就停（只有 Windows）。

    計算要跑好幾分鐘，使用者常常切去別的程式；算完跳出的訊息框在背後看不到，
    工作列閃一下才知道該回來看。
    """
    try:
        hwnd = int(window.winfo_toplevel().wm_frame(), 16)
        user32 = ctypes.windll.user32
        if user32.GetForegroundWindow() == hwnd:
            return

        class FLASHWINFO(ctypes.Structure):
            _fields_ = [("cbSize", ctypes.c_uint), ("hwnd", ctypes.c_void_p),
                        ("dwFlags", ctypes.c_uint), ("uCount", ctypes.c_uint),
                        ("dwTimeout", ctypes.c_uint)]

        # FLASHW_ALL（標題列＋工作列）| FLASHW_TIMERNOFG（閃到視窗回到最前面為止）
        info = FLASHWINFO(ctypes.sizeof(FLASHWINFO), hwnd, 0x3 | 0xC, 0, 0)
        user32.FlashWindowEx(ctypes.byref(info))
    except (AttributeError, OSError, ValueError, tk.TclError):
        pass        # 不是 Windows 或拿不到視窗：不閃，訊息框照樣會出現


def _open_url(url: str) -> None:
    """用預設瀏覽器打開網址；打不開就把網址顯示出來讓使用者自己複製。"""
    import webbrowser
    try:
        opened = webbrowser.open(url)
    except Exception:       # 各平台的瀏覽器呼叫失敗方式不一，一律當作沒打開
        opened = False
    if not opened:
        messagebox.showwarning("打開網頁", f"沒辦法自動打開瀏覽器，請自己到這個網址：\n{url}")


class _StringDialog(tk.Toplevel):
    """輸入一行文字的對話框（取代 simpledialog.askstring），外觀跟 _MessageDialog 一致。"""

    def __init__(self, parent, title, prompt, initial):
        super().__init__(parent)
        hide_until_centered(self)
        self.title(title)
        # 輸入名稱的小視窗不給拉，跟訊息框一致
        self.resizable(False, False)
        self.result = None
        top = parent.winfo_toplevel()
        if top.winfo_viewable():
            self.transient(top)

        body = tk.Frame(self, background="white", padx=px(20), pady=px(18))
        body.pack(fill="both", expand=True)
        prewrap(tk.Label(body, text=prompt, justify="left", anchor="w",
                         background="white", font="TkDefaultFont"), px(460)).pack(fill="x")
        self._var = tk.StringVar(value=initial or "")
        entry = ttk.Entry(body, textvariable=self._var, width=36)
        entry.pack(fill="x", pady=(px(8), 0))

        bar = ttk.Frame(self, padding=(px(12), px(10)))
        bar.pack(side="bottom", fill="x", before=body)
        ttk.Button(bar, text="取消", command=self.destroy).pack(side="right", padx=(px(8), 0))
        ttk.Button(bar, text="確定", command=self._ok).pack(side="right")
        self.bind("<Return>", lambda _e: self._ok())
        self.bind("<Escape>", lambda _e: self.destroy())

        center_on(self, top)
        entry.focus_set()
        entry.select_range(0, "end")
        run_modal(self)

    def _ok(self):
        self.result = self._var.get()
        self.destroy()


def ask_string(title, prompt, parent, initialvalue=None):
    """跟 simpledialog.askstring 一樣：按確定回傳輸入的字，取消回傳 None。"""
    return _StringDialog(parent, title, prompt, initialvalue).result


def parse_int(text: str, label: str, minimum: int | None = None) -> int:
    text = (text or "").strip()
    if not text:
        raise FieldError(f"「{label}」不能空白")
    try:
        value = int(text)
    except ValueError:
        raise FieldError(f"「{label}」必須是整數：{text}")
    if minimum is not None and value < minimum:
        raise FieldError(f"「{label}」不能小於 {minimum}")
    return value


def parse_percent(text: str, label: str) -> float:
    """加成百分比。允許小數，空白視為 0。"""
    text = (text or "").strip().rstrip("%％").strip()
    if not text:
        return 0.0
    try:
        value = float(text)
    except ValueError:
        raise FieldError(f"「{label}」必須是數字：{text}")
    if value < 0:
        raise FieldError(f"「{label}」不能是負數")
    return value


def trim_number(value) -> str:
    """20.0 顯示成 20、20.5 就照原樣。"""
    number = float(value or 0)
    return str(int(number)) if number == int(number) else str(number)


def parse_int_list(text: str, label: str, minimum: int, maximum: int) -> list[int]:
    """「5,11,17,23」→ [5, 11, 17, 23]。逗號（半形全形）、頓號、空白都當分隔符。

    去重排序後回傳——同一號寫兩次只會發一次，順序也不影響結果，
    存進去先正規化，之後比對與顯示才不會因為打字順序不同而有差。
    """
    cleaned = (text or "")
    for token in ("、", ",", "，", "/"):
        cleaned = cleaned.replace(token, " ")
    parts = cleaned.split()
    if not parts:
        raise FieldError(f"「{label}」不能空白")
    values = set()
    for part in parts:
        value = parse_int(part, label, minimum)
        if value > maximum:
            raise FieldError(f"「{label}」不能大於 {maximum}：{part}")
        values.add(value)
    return sorted(values)


def parse_stage_groups(text: str, label: str) -> list[list[int]]:
    """「35、40、45；50、55、60；61~63」→ [[35, 40, 45], [50, 55, 60], [61, 62, 63]]。

    分號（半形全形）或換行隔開各組；組內跟 parse_int_list 一樣用頓號、逗號、
    空白隔開；「61~63」「61-63」「61～63」是範圍。留白＝沒有分組。
    同一關不能出現在兩組。
    """
    cleaned = (text or "").replace("；", ";").replace("\n", ";")
    groups, seen = [], set()
    for chunk in cleaned.split(";"):
        chunk = chunk.strip()
        if not chunk:
            continue
        for token in ("～", "~"):
            chunk = chunk.replace(token, "-")
        stages = set()
        for part in parse_list_tokens(chunk):
            if "-" in part:
                lo_text, _sep, hi_text = part.partition("-")
                lo = parse_int(lo_text, label, 1)
                hi = parse_int(hi_text, label, 1)
                if hi < lo:
                    raise FieldError(f"「{label}」的範圍寫反了：{part}")
                stages.update(range(lo, hi + 1))
            else:
                stages.add(parse_int(part, label, 1))
        dup = stages & seen
        if dup:
            raise FieldError(f"「{label}」裡第 {min(dup)} 關出現在兩組")
        seen |= stages
        groups.append(sorted(stages))
    return groups


def format_stages(stages) -> str:
    """[61, 62, 63, 65] → 「61~63、65」：連續的縮成範圍，清單和輸入框都用這個寫法。"""
    stages = sorted(int(x) for x in stages)
    parts, start = [], None
    for index, value in enumerate(stages):
        if start is None:
            start = value
        if index + 1 < len(stages) and stages[index + 1] == value + 1:
            continue
        # 一個就寫一個、兩個寫成「61、62」，三個以上才縮成「61~63」
        if value - start >= 2:
            parts.append(f"{start}~{value}")
        else:
            parts.extend(str(x) for x in range(start, value + 1))
        start = None
    return "、".join(parts)


def format_stage_groups(groups) -> str:
    return "；".join(format_stages(group) for group in groups or [])


def parse_list_tokens(text: str) -> list[str]:
    """逗號（半形全形）、頓號、斜線、空白都當分隔符，回傳非空的片段。"""
    for token in ("、", ",", "，", "/"):
        text = text.replace(token, " ")
    return text.split()


def parse_date_list(text: str, label: str) -> list[str]:
    """「20261025、2026-10-28」→ ["2026-10-25", "2026-10-28"]。

    分隔符跟 parse_int_list 一樣（逗號、頓號、空白、斜線）；每個日期打 8 碼
    數字或 YYYY-MM-DD 都行。去重排序後回傳。
    """
    cleaned = (text or "")
    for token in ("、", ",", "，", "/"):
        cleaned = cleaned.replace(token, " ")
    parts = cleaned.split()
    if not parts:
        raise FieldError(f"「{label}」不能空白")
    values = set()
    for part in parts:
        try:
            if sum(ch.isdigit() for ch in part) != 8:
                raise ValueError(part)
            values.add(datetime.strptime(format_date_digits(part),
                                         "%Y-%m-%d").date().isoformat())
        except ValueError:
            raise FieldError(
                f"「{label}」裡有一個不是完整的日期（每個打 8 碼數字即可）：{part}")
    return sorted(values)


def parse_opt_int(text: str, label: str, minimum: int | None = None) -> int | None:
    """空白代表「沒有這個限制」，回傳 None。"""
    if not (text or "").strip():
        return None
    return parse_int(text, label, minimum)


# --------------------------------------------------------------------------
# 通用元件
# --------------------------------------------------------------------------

class EventDateMixin:
    """日期 ↔ 相對某一檔活動起始日的偏移量。

    介面上用實際日期輸入（使用者知道的是 9/10 而不是「第 15 天」），
    存檔時換算成偏移量，這樣換一檔活動時整組規則會跟著移動。
    多活動並行之後，每一條規則都要講清楚是「相對哪一檔活動」，
    所以這些函式一律要指定 event_id（省略就用第一檔）。
    """

    def _event_bounds(self, event_id=None):
        event = (storage.find_event(self.app.shared, event_id)
                 if event_id else None)
        if event is None:
            # 省略 event_id 時退到第一檔**真**活動，跟 `_first_event_id()` 一致。
            # 用 events_of 的話，常駐關卡只要排在 events 第一位就會回傳
            # (None, None)，整組規則被當成「算不出日期」而默默略過。
            events = storage.real_events(self.app.shared)
            event = events[0] if events else None
        if event is None:
            return None, None
        try:
            start = datetime.strptime(event["start_date"], "%Y-%m-%d").date()
            end = datetime.strptime(event["end_date"], "%Y-%m-%d").date()
        except (KeyError, TypeError, ValueError):
            return None, None
        return start, end

    def _offset_to_date(self, offset, event_id=None):
        # 一律從活動起始日算，跟 _date_to_offset 互為反函式。
        # 用 resolve_day_offset 會把負數（起始日之前的日期）解讀成
        # 「從最後一天往回算」，日期讀回來就跑掉了。
        start, _end = self._event_bounds(event_id)
        if start is None or offset is None:
            return ""
        return scheduler.offset_from_start(int(offset), start).isoformat()

    def _date_to_offset(self, text, event_id=None):
        start, _end = self._event_bounds(event_id)
        if start is None:
            # 三檔活動並行時，光說「填好活動起訖日」使用者不知道是哪一檔。
            event = storage.find_event(self.app.shared, event_id) if event_id else None
            which = f"「{scheduler.event_label(event)}」" if event else "那一檔活動"
            raise FieldError(f"要先在「活動設定」填好{which}的起訖日，才能用日期換算")
        return (datetime.strptime(text, "%Y-%m-%d").date() - start).days

    def _event_choices(self):
        return [(ev["id"], scheduler.event_label(ev))
                for ev in storage.events_of(self.app.shared)]


class RecordDialog(tk.Toplevel):
    """依 specs 產生欄位的小型輸入對話框，結果放在 self.result。"""

    # 對話框最高長到這裡，超過就捲。每日紀錄要一次列出三檔活動的所有關卡，
    # 不捲的話會長到超出螢幕、按不到「確定」。
    #
    # 要不要捲看的是高度，不是欄位數：欄位高度差很多（multi_choice 的 Listbox
    # 一個就佔 100px）。一律走捲動容器，放得下就跟不捲的版面長得一模一樣。
    MAX_HEIGHT = 520
    # 提示文字的折行寬度。第 2 欄的提示最長到 640px，不折行就把對話框撐爆。
    HINT_WRAP = 320

    def __init__(self, parent, title, specs, initial=None, total_of=None,
                 headers=None, heading=None, width=None, validate=None, ok_text=None,
                 stretch=None):
        """total_of：拿目前各欄位的原始字串算出一行摘要，即時顯示在按鈕上方。

        限時體力用數量輸入（幾個 100/30/10），使用者需要邊填邊看到換算後的點數，
        不然要按下確定、回到清單才知道填對沒有。

        headers：欄位標題列（給 pair_int 那種多欄的版面用），從 grid 第 1 欄排起。

        specs 可以是固定清單，也可以是「依目前記錄算出欄位」的函式。後者是必要的
        ——任務的「週期」「達成條件」決定要有哪幾格（每月才有入帳幾號、活動才有
        期限……），而那兩格就在對話框裡面，改了之後欄位必須跟著重算。

        heading：這一筆是在改誰（任務進度的欄位裡沒有任務名稱，不標出來
        使用者根本不知道自己在改哪一個任務）。

        width：對話框一開始的寬度，欄位放不下就出現橫向捲軸；之後可以自由拉。
        沒給就照欄位需要的寬度。

        validate：拿整筆結果檢查欄位之間的關係（例如結束日不能早於起始日），
        有問題回傳錯誤訊息、不關窗；沒問題回 None。ok_text：確定鈕的字。

        stretch：拉寬對話框時哪一欄跟著變寬。預設沒有——輸入框維持原本的寬度，
        多出來的寬度拿去攤開右邊的提示（見 _hint）。任務狀態那種沒有提示、
        欄位名稱又長的，給 0 讓名稱那欄變寬。
        """
        self._validate = validate
        self._ok_text = ok_text
        super().__init__(parent)
        hide_until_centered(self)
        self.title(title)
        self.result = None
        # pair_int 的「這次」單獨留一份。result 是相加後的總量，但每日紀錄要
        # 知道「這一次新增了多少」才能存成一筆帶時刻的分筆紀錄。
        self.added = {}
        self._vars = {}
        self._widgets = {}
        self._specs = []
        self._headers = headers
        self._total_of = total_of
        self._rebuilding = False
        self._specs_of = specs if callable(specs) else (lambda _record: specs)
        self._record = dict(initial or {})

        if width:
            # 限寬時提示再折窄一點：實際打法那格「時間」的提示排在最右欄，
            # 照預設寬度折會剛好多出一截、平白冒出橫向捲軸
            self.HINT_WRAP = 260
        # 這幾個像素數都是 100% 時的值，跟著畫面縮放走（見 apply_zoom）
        self.HINT_WRAP = px(self.HINT_WRAP)
        self.MAX_HEIGHT = min(px(self.MAX_HEIGHT), self.winfo_screenheight() - dp(160))
        if width:
            # 只是一開始的寬度（給 ScrollableFrame 當內容寬），之後可以自由拉
            width = min(px(width), self.winfo_screenwidth() - dp(40))
        outer = ttk.Frame(self, padding=dp(12))
        outer.pack(fill="both", expand=True)
        # 跟摘要、按鈕一樣放在捲動區外面：不會被捲走，也不會跟著欄位被重建
        self.heading_label = None
        if heading:
            # Font 物件要留著參照，被回收的話標籤會退回預設字型
            self._heading_font = tkfont.Font(font="TkDefaultFont")
            self._heading_font.configure(weight="bold")
            self.heading_label = prewrap(ttk.Label(
                outer, text=heading, font=self._heading_font), self.HINT_WRAP * 2)
            self.heading_label.pack(anchor="w", pady=(0, dp(8)))
        scroller = ScrollableFrame(outer, height=self.MAX_HEIGHT,
                                   fit_content=True,
                                   width=width - 24 - 18 if width else None)
        scroller.pack(fill="both", expand=True)
        # 欄位實際放在哪個 frame 裡、摘要與按鈕又在哪一個。版面改過好幾次
        # （有沒有捲動、包幾層），測試不該自己去猜 winfo_children()[0]。
        self.body = scroller.inner
        self._scroller = scroller
        # 不給輸入框那欄 weight：拉寬時輸入框、下拉選單不跟著變長
        self._stretch = stretch
        if stretch is not None:
            self.body.columnconfigure(stretch, weight=1)
        # 摘要與按鈕放在捲動區外面，捲到哪裡都看得到「確定」；
        # 它們也不能跟著欄位一起被重建，所以在這裡就建好。
        self.footer = ttk.Frame(outer)
        # 排在捲動區「之前」（pack 的分配順序）、貼底：視窗不夠高時被壓縮的是
        # 捲動區（裡面捲），按鈕不會被切掉。建立順序不變，Tab 鍵的順序照舊
        self.footer.pack(side="bottom", fill="x", before=scroller)

        self._total_label = None
        if total_of:
            self._total_label = ttk.Label(self.footer, foreground="#0a5")
            self._total_label.pack(anchor="w", pady=(dp(10), 0))

        buttons = ttk.Frame(self.footer)
        buttons.pack(anchor="e", pady=(dp(14), 0))
        ttk.Button(buttons, text=self._ok_text or "確定", command=self._on_ok).pack(
            side="left", padx=(0, dp(6)))
        ttk.Button(buttons, text="取消", command=self.destroy).pack(side="left")

        self._render(self._record)

        self.bind("<Return>", lambda _e: self._on_ok())
        self.bind("<Escape>", lambda _e: self.destroy())
        self.transient(parent)
        center_on(self, parent)
        run_modal(self)

    # -- 欄位 --------------------------------------------------------------
    def _render(self, record, offscreen=False):
        """依目前的記錄算出欄位並鋪上去；重建時會再跑一次。

        offscreen：重建用。新欄位先鋪在一個還沒放上畫面的框裡、排好版，
        再整個換掉舊的——拆一個、鋪一個的中間過程不會被畫出來。
        """
        self._rebuilding = True
        try:
            if offscreen:
                old = self.body
                self.body = ttk.Frame(old.master)
                if self._stretch is not None:
                    self.body.columnconfigure(self._stretch, weight=1)
            else:
                for child in self.body.winfo_children():
                    child.destroy()
            self._vars.clear()
            self._widgets.clear()
            self._hint_labels = {}
            self._rows = {}
            self._specs = specs = self._specs_of(record)
            self._build_fields(specs, record)
            # 每一列有哪些元件先記下來：收起來（grid_remove）之後 grid_slaves 就找不到了
            self._row_widgets = {key: self.body.grid_slaves(row=row)
                                 for key, row in self._rows.items()}
            # 每一格在第幾欄、左右留白多少：收起來（grid_remove）之後 grid_info 就問不到了
            self._cells = []
            for widgets in self._row_widgets.values():
                for widget in widgets:
                    info = widget.grid_info()
                    padx = info.get("padx", 0)      # 一個數字，或左右兩個的 tuple
                    pad = sum(int(float(str(x))) for x in (
                        padx if isinstance(padx, (tuple, list)) else str(padx).split()))
                    self._cells.append((widget, int(info.get("column", 0)), pad))
            self._has_hidden = any(spec.get("hidden") for spec in specs)
            self._pin_columns()
            hidden = [spec["key"] for spec in specs if spec.get("hidden")]
            for key in hidden:
                self._show_row(key, False)
            if hidden:
                # 捲動區的高度是收起來之前量的，照收起來之後的內容重量一次，
                # 不然一打開底下就空一塊
                self.body.update_idletasks()
                self._scroller._on_inner_configure()
            self._wire_derived(specs)
            self._wire_total(specs)
            self._wire_rebuild(specs)
            if offscreen:
                self.update_idletasks()      # 在看不見的框裡排好版
                self._scroller.swap_inner(self.body)
        finally:
            self._rebuilding = False

    def _build_fields(self, specs, initial):
        body = self.body
        # `above_headers` 的欄位排在標題列**上面**：每日紀錄的「時間」是整筆共用的，
        # 塞進 計畫／前次／這次 那三欄底下會對錯欄，看起來像填錯格子。
        lead = [spec for spec in specs if spec.get("above_headers")]
        ordered = lead + [spec for spec in specs
                          if not spec.get("above_headers")]
        if self._headers:
            for index, text in enumerate(self._headers):
                ttk.Label(body, text=text, foreground="#666666").grid(
                    row=len(lead), column=index + 1, sticky="", padx=(dp(10), 0))

        for index, spec in enumerate(ordered):
            row = index + (1 if self._headers and index >= len(lead) else 0)
            key, kind = spec["key"], spec["type"]
            self._rows[key] = row
            ttk.Label(body, text=spec["label"]).grid(
                row=row, column=0, sticky="w", padx=(0, dp(10)), pady=dp(5))

            if kind == "time":
                # 窄一點的輸入框＋「現在」，跟計算頁的查詢時間同一套操作習慣
                var = tk.StringVar(value=initial.get(key) or "")
                entry = ttk.Entry(body, textvariable=var, width=8,
                                  justify="center")
                entry.grid(row=row, column=1, sticky="w")
                ttk.Button(body, text="現在", width=6,
                           command=lambda v=var: v.set(
                               datetime.now().strftime("%H:%M"))).grid(
                    row=row, column=2, sticky="w", padx=(dp(10), 0))
                self._vars[key] = var
                self._widgets[key] = entry
                if spec.get("hint"):
                    self._hint(body, spec["hint"]).grid(
                        row=row, column=3, columnspan=2, sticky="w",
                        padx=(dp(10), 0))
                continue

            if kind == "pair_int":
                # 「前次 ＋ 這次」：前次是已經記錄的量（可修正），這次是剛打完的量。
                # 兩欄相加才是當天的實際打法——只給一格總數的話，使用者得自己心算。
                ttk.Label(body, text=spec.get("note", ""), foreground="#666666",
                          width=6, anchor="e").grid(row=row, column=1, padx=(dp(10), 0))
                prev_var = tk.StringVar(value=str(initial.get(key, 0) or 0))
                entry = ttk.Entry(body, textvariable=prev_var, width=6,
                                  justify="center")
                # 每日紀錄把「前次」鎖起來：那一欄是既有分筆的加總，直接改它
                # 會跟分筆對不起來。要修正既有的量請走「分筆紀錄」。
                if spec.get("locked_prev"):
                    entry.config(state="readonly")
                entry.grid(row=row, column=2, padx=(dp(10), 0))
                add_var = tk.StringVar(value="0")
                stepper_box(body, add_var, 0).grid(row=row, column=3,
                                                   padx=(dp(10), 0))
                self._vars[key] = (prev_var, add_var)
                self._widgets[key] = entry
                continue

            if kind == "date":
                var = tk.StringVar(value=initial.get(key) or "")
                # 日期欄自己的提示（星期幾）放上面；spec 另外給了說明的話放在下一行，
                # 不然像「留白＝一直有效」這種只在某些關卡才有的說明會看不到。
                # 不並排：上面那句會在「星期日」「只要打數字，例如（今天）」之間
                # 換來換去，並排的話整塊寬度跟著變，清空日期的瞬間整個對話框重排、
                # 抖一下。上下疊的話寬度由折好的說明決定，換字不影響。
                hint_box = ttk.Frame(body)
                hint_box.grid(row=row, column=2, sticky="w", padx=(dp(10), 0))
                hint = ttk.Label(hint_box, foreground="#666666")
                hint.pack(anchor="w")
                if spec.get("hint"):
                    self._hint_labels[key] = self._hint(hint_box, spec["hint"])
                    self._hint_labels[key].pack(anchor="w")
                entry = DateEntry(body, var, hint, width=14)
                entry.grid(row=row, column=1, sticky="w")
                self._vars[key] = var
                self._widgets[key] = entry
                continue
            if kind == "multi_choice":
                # 可以複選的清單（任務的「指定關卡」）。什麼都不選＝用預設範圍。
                frame = ttk.Frame(body)
                frame.grid(row=row, column=1, sticky="we")
                choices = spec["choices"]
                box = tk.Listbox(frame, selectmode="extended",
                                 height=spec.get("height", 6), exportselection=False)
                for _value, label in choices:
                    box.insert("end", label)
                box.pack(side="left", fill="both", expand=True)
                bar = ttk.Scrollbar(frame, orient="vertical", command=box.yview)
                box.configure(yscrollcommand=bar.set)
                bar.pack(side="left", fill="y")
                selected = set(initial.get(key) or [])
                for position, (value, _label) in enumerate(choices):
                    if value in selected:
                        box.selection_set(position)
                self._vars[key] = (box, choices)
                self._widgets[key] = box
                if spec.get("hint"):
                    self._hint(body, spec["hint"]).grid(
                        row=row, column=2, sticky="w", padx=(dp(10), 0))
                continue
            if kind == "day_ref":
                # 活動日期用「從第一天／從最後一天　第 N 天」兩格表示，
                # 使用者不必自己想負號要怎麼寫。存進 JSON 時才換算成 day_offset。
                value = initial.get(key)
                value = 0 if value is None else int(value)
                frame = ttk.Frame(body)
                frame.grid(row=row, column=1, sticky="w")
                anchor_var = tk.StringVar(
                    value=DAY_FROM_END if value < 0 else DAY_FROM_START)
                anchor_box = ttk.Combobox(
                    frame, textvariable=anchor_var, state="readonly",
                    width=10, values=[DAY_FROM_START, DAY_FROM_END])
                anchor_box.pack(side="left")
                ttk.Label(frame, text="第").pack(side="left", padx=(dp(6), dp(2)))
                number_var = tk.StringVar(
                    value=str(-value if value < 0 else value + 1))
                ttk.Spinbox(frame, textvariable=number_var, from_=1, to=999,
                            width=5).pack(side="left")
                ttk.Label(frame, text="天").pack(side="left", padx=(dp(2), 0))
                var = (anchor_var, number_var)
                widget = anchor_box
            elif kind == "bool":
                var = tk.BooleanVar(
                    value=bool(initial.get(key, spec.get("default", True))))
                widget = ttk.Checkbutton(body, variable=var)
                widget.grid(row=row, column=1, sticky="w")
            elif kind == "choice":
                mapping = dict(spec["choices"])
                current = initial.get(key, spec["choices"][0][0])
                var = tk.StringVar(
                    value=mapping.get(current, spec["choices"][0][1]))
                widget = ttk.Combobox(
                    body, textvariable=var, width=22,
                    state="disabled" if spec.get("disabled") else "readonly",
                    values=[label for _, label in spec["choices"]])
                widget.grid(row=row, column=1, sticky="we")
            elif spec.get("stepper"):
                value = initial.get(key, spec.get("default"))
                var = tk.StringVar(value="" if value is None else str(value))
                widget = stepper_box(body, var, spec.get("minimum", 0))
                widget.grid(row=row, column=1, sticky="w")
            else:
                value = initial.get(key, spec.get("default"))
                if kind == "int_list":
                    value = "、".join(str(int(x)) for x in (value or []))
                elif kind == "date_list":
                    value = "、".join(str(x) for x in (value or []))
                elif kind == "stage_groups":
                    value = format_stage_groups(value)
                var = tk.StringVar(value="" if value is None else str(value))
                widget = ttk.Entry(body, textvariable=var, width=24)
                widget.grid(row=row, column=1, sticky="we")
                if spec.get("readonly"):
                    # 看得到、選得起來複製，但改不了（常駐關卡的基本盤不能改名）
                    widget.config(state="readonly")

            self._vars[key] = var
            self._widgets[key] = widget
            if spec.get("hint"):
                self._hint_labels[key] = self._hint(body, spec["hint"])
                self._hint_labels[key].grid(
                    row=row, column=2, sticky="w", padx=(dp(10), 0))

    def _hint(self, master, text):
        """欄位右邊的灰色提示。

        剛打開時照 HINT_WRAP 折好，不然一句長的就把整個對話框撐到將近
        1000px 寬；之後對話框拉寬，提示跟著攤開（夠寬就變成一行），
        拉回去最窄也只折回 HINT_WRAP，再窄就出橫向捲軸。
        """
        label = prewrap(ttk.Label(master, text=text, foreground="#666666"),
                        self.HINT_WRAP)
        # 右邊要留 wrap_cjk 行尾可能多掛的標點（「」，」這種可以連掛兩個），
        # 照字型實際量、跟著縮放走。留不夠的話內容比可見範圍寬一點點，
        # 橫向捲軸冒出來又牽動直向捲軸，視窗就在那裡來回跳
        font = tkfont.Font(font=str(label.cget("font")) or "TkDefaultFont")
        right = font.measure("」，") + dp(8)
        self._scroller.wrap_label(label, right=right, minimum=self.HINT_WRAP,
                                  original=text)
        return label

    def _each_var(self, key):
        """一格底下實際有幾個可以掛 trace 的變數。

        multi_choice 是 Listbox，沒有 var 可以掛（選取沒有 trace），跳過。
        """
        var = self._vars[key]
        if isinstance(var, tuple) and isinstance(var[0], tk.Listbox):
            return ()
        return var if isinstance(var, tuple) else (var,)

    def _wire_derived(self, specs):
        """衍生欄位：來源欄一變就重算目標欄（基礎積分 → 取得積分）。

        使用者之後手動覆蓋目標欄仍然有效，直到下次來源欄再變為止。
        """
        for spec in specs:
            if not spec.get("derive"):
                continue
            target = self._vars[spec["key"]]
            derive = spec["derive"]

            def refresh_derived(*_args, _target=target, _derive=derive):
                _target.set(_derive(self._raw_values()))

            for source_key in spec.get("derive_from") or []:
                for one in self._each_var(source_key):
                    one.trace_add("write", refresh_derived)

    def _wire_total(self, specs):
        if not self._total_of or self._total_label is None:
            return

        def refresh_total(*_args):
            self._total_label.config(text=self._total_of(self._raw_values()))

        for spec in specs:
            for one in self._each_var(spec["key"]):
                one.trace_add("write", refresh_total)
        refresh_total()

    def _wire_rebuild(self, specs):
        """標了 rebuild 的欄位一改，整組欄位重算。"""
        for spec in specs:
            if not spec.get("rebuild"):
                continue
            for one in self._each_var(spec["key"]):
                one.trace_add("write",
                              lambda *_a, _key=spec["key"]:
                              self._schedule_rebuild(_key))

    def _schedule_rebuild(self, key):
        # 不要在 combobox 自己的 trace 裡直接 destroy 它——那等於在事件處理
        # 中途砍掉正在觸發事件的元件。排到 idle 再做。
        if self._rebuilding:
            return
        self._rebuilding = True      # 同一批變更只排一次
        self.after_idle(lambda: self._rebuild(key))

    def _rebuild(self, key=None):
        self._rebuilding = False
        if not self.winfo_exists():
            return
        record = self._current_record()
        # 換了值但要有的欄位沒變（例如換到另一個一樣沒有難度分組的關卡）就不重建：
        # 整組拆掉重鋪會看到畫面明顯閃一下。要跟著換的值由衍生欄位自己更新
        new_specs = self._specs_of(record)
        if self._spec_signature(new_specs) == self._spec_signature(self._specs):
            return
        if self._patch_in_place(new_specs):
            return
        # 拆掉重鋪、對話框跟著改大小的中間過程不要畫出來：排完才一次畫（見 _frozen_redraw）。
        # 凍結擋得住內容，擋不住外框：重建到一半 Tk 就會照新內容改視窗大小，
        # 外框先縮、裡面還是凍住的舊畫面（底下被切掉一截），要等排完才換。
        # 所以排的期間先把大小釘住，排好了最後才一次改成新的大小。
        # 視窗原本不是照內容的大小（使用者拉過、或開的時候被壓小）就維持原樣。
        self.update_idletasks()
        width, height = self.winfo_width(), self.winfo_height()
        follows = (width, height) == (self.winfo_reqwidth(), self.winfo_reqheight())
        with _frozen_redraw(self):
            self.geometry(f"{width}x{height}")
            self._render(record, offscreen=True)
            _settle_window(self)
            if follows:
                self._fit_to_content()
        # 焦點留在剛剛改的那一格，不然選完「每月」焦點就不知道跑哪去了
        widget = self._widgets.get(key)
        if widget is not None and widget.winfo_exists():
            widget.focus_set()

    def _fit_to_content(self):
        """視窗交還給 Tk 照內容決定大小（原本就是照內容的才呼叫）。

        不寫死成數字：寫死的話畫面縮放時對話框不會照新的字型重算大小，
        之後每換一次關卡才慢慢縮回去。重建期間暫時釘住的大小（見 _rebuild）也在這裡放掉。
        """
        self.geometry("")
        self._scroller.settle()
        _settle_window(self)

    def refit_after_zoom(self):
        """畫面縮放後照新字型重量大小。

        捲動區的寬度記著縮放前的內容寬度，平常只有高度變了才會順便縮回來；
        不重量的話縮放後每換一次關卡才窄一點，看起來就是對話框寬度一直在變。
        使用者拉過大小的（不是照內容的）就不動。
        """
        if not self.winfo_exists():
            return
        self._pin_columns()
        scroller = self._scroller
        for _ in range(6):
            before = (self.winfo_reqwidth(), self.winfo_reqheight())
            scroller._on_inner_configure()
            scroller.settle()
            _settle_window(self)
            if (self.winfo_reqwidth(), self.winfo_reqheight()) == before:
                break

    def _pin_columns(self):
        """有收起來的列時，欄位名稱和輸入框那兩欄的寬度照「包含收起來的」釘住。

        收起來的名稱剛好最長（「代幣最多存幾個」）時，不釘的話左欄跟著變窄，
        輸入框和右邊的說明整排左右挪。用元件自己要的寬度算（收起來的也量得到），
        畫面縮放後再算一次（見 App._apply_zoom_now），字變大變小欄寬跟著走。
        """
        if not getattr(self, "_has_hidden", False):
            return
        for column in (0, 1):
            widths = [widget.winfo_reqwidth() + pad
                      for widget, col, pad in self._cells
                      if col == column and widget.winfo_exists()]
            self.body.columnconfigure(column, minsize=max(widths, default=0))

    def _show_row(self, key, shown: bool):
        """整列（名稱、輸入框、提示）收起來或放回去。grid_remove 會記住位置。"""
        for widget in self._row_widgets.get(key, ()):
            widget.grid() if shown else widget.grid_remove()

    # 這幾項變了可以在原本的元件上直接改，不必整組拆掉重鋪
    _PATCHABLE = {"choices", "disabled", "hint", "hidden"}

    def _patch_in_place(self, new_specs) -> bool:
        """欄位還是那幾格、只有下拉選項／能不能選／提示字不一樣時，直接改在原地。

        整組拆掉重鋪一定看得到畫面在動（Windows 搬動子視窗時會直接複製像素，
        凍結重繪也擋不住），能不重建就不重建。改得了回傳 True。
        """
        old_specs = self._specs
        if len(old_specs) != len(new_specs):
            return False
        for old, new in zip(old_specs, new_specs):
            if old["key"] != new["key"] or old.get("type") != new.get("type"):
                return False
            changed = {name for name in set(old) | set(new)
                       if not callable(old.get(name)) and not callable(new.get(name))
                       and old.get(name) != new.get(name)}
            if not changed <= self._PATCHABLE:
                return False
            if "hint" in changed and (bool(old.get("hint")) != bool(new.get("hint"))
                                      or old["key"] not in self._hint_labels):
                return False
            if changed & {"choices", "disabled"} and new.get("type") != "choice":
                return False
        self.update_idletasks()
        follows = ((self.winfo_width(), self.winfo_height())
                   == (self.winfo_reqwidth(), self.winfo_reqheight()))
        resized = False
        for old, new in zip(old_specs, new_specs):
            key = new["key"]
            if bool(old.get("hidden")) != bool(new.get("hidden")):
                self._show_row(key, not new.get("hidden"))
                resized = True
            if new.get("type") == "choice":
                box, var = self._widgets[key], self._vars[key]
                labels = [label for _value, label in new["choices"]]
                box.configure(values=labels,
                              state="disabled" if new.get("disabled") else "readonly")
                if var.get() not in labels:
                    var.set(labels[0])
            if old.get("hint") != new.get("hint"):
                self._set_hint(self._hint_labels[key], new["hint"])
        self._specs = new_specs
        if resized and follows:
            # 收起／放回整列，視窗跟著變高變矮（使用者拉過大小的就不動）
            self._scroller.settle()
            _settle_window(self)
            self._fit_to_content()
        return True

    def _set_hint(self, label, text):
        """換提示字，照它現在的折行寬度折好（見 ScrollableFrame.wrap_label）。

        不另外重排整個對話框：那會照當下的視窗寬度把所有提示重折一次，
        對話框跟著變寬、再折更寬，換幾次關卡就越來越寬。
        """
        state = next((state for widget, state in self._scroller._wrapped
                      if widget is label), None)
        width = state[3][0] if state and state[3] else self.HINT_WRAP
        font = tkfont.Font(font=str(label.cget("font")) or "TkDefaultFont")
        shown = wrap_cjk(text, font, width)
        label.configure(text=shown, justify="left", wraplength=0)
        if state is not None:
            state[1], state[2] = text, shown

    @staticmethod
    def _spec_signature(specs) -> list:
        """欄位長什麼樣子（函式不算，每次算欄位都是新的一個）。"""
        return [{key: value for key, value in spec.items() if not callable(value)}
                for spec in specs]

    def _current_record(self) -> dict:
        """畫面上的值轉回「記錄」的形式，轉不動的就沿用上一份。

        重建欄位時用——**不能把使用者打到一半的東西洗掉**。
        """
        record = dict(self._record)
        for spec in self._specs:
            try:
                record[spec["key"]] = self._value_of(spec)
            except (FieldError, ValueError, KeyError, tk.TclError):
                pass          # 還沒填完的欄位維持原值
        self._record = record
        return record

    @staticmethod
    def _int_or_zero(text) -> int:
        try:
            return int((text or "0").strip() or 0)
        except (TypeError, ValueError):
            return 0

    def _raw_values(self) -> dict:
        """各欄位目前的原始輸入（給即時摘要用，不做驗證）。

        pair_int 給的是**加總後**的數字字串——摘要要看的是「今天總共打了多少」，
        不是其中一欄。
        """
        values = {}
        for spec in self._specs:
            var = self._vars[spec["key"]]
            if spec["type"] == "pair_int":
                values[spec["key"]] = str(self._int_or_zero(var[0].get())
                                          + self._int_or_zero(var[1].get()))
            elif spec["type"] == "multi_choice":
                box, choices = var
                values[spec["key"]] = [choices[i][0] for i in box.curselection()]
            elif isinstance(var, tuple):
                values[spec["key"]] = var[1].get()
            else:
                values[spec["key"]] = var.get()
        return values

    def _value_of(self, spec):
        """一格的值，轉成存進記錄的形式；格式不對丟 FieldError。

        `_on_ok`（按確定）與 `_current_record`（重建欄位時保住已填的值）
        共用這一份，不要再寫第二套——兩套遲早會對不起來。
        """
        key, kind = spec["key"], spec["type"]
        if kind == "date":
            text = self._vars[key].get().strip()
            if not text and spec.get("optional"):
                return ""             # 用不到這一欄時可以留白
            try:
                datetime.strptime(text, "%Y-%m-%d")
            except ValueError:
                raise FieldError(
                    f"「{spec['label']}」不是完整的日期（打 8 碼數字即可）：{text}")
            return text
        if kind == "pair_int":
            prev_var, add_var = self._vars[key]
            prev = parse_opt_int(prev_var.get(), f"{spec['label']}（前次）", 0)
            add = parse_opt_int(add_var.get(), f"{spec['label']}（這次）", 0)
            return (prev or 0) + (add or 0)
        if kind == "multi_choice":
            box, choices = self._vars[key]
            picked = [choices[i][0] for i in box.curselection()]
            if not picked and spec.get("required"):
                raise FieldError(f"「{spec['label']}」至少要選一個")
            return picked
        if kind == "day_ref":
            anchor_var, number_var = self._vars[key]
            number = parse_int(number_var.get(), spec["label"], 1)
            return -number if anchor_var.get() == DAY_FROM_END else number - 1
        raw = self._vars[key].get()
        if kind == "bool":
            return bool(raw)
        if kind == "choice":
            reverse = {label: value for value, label in spec["choices"]}
            if raw not in reverse:
                raise FieldError(f"「{spec['label']}」的選項不認得：{raw}")
            return reverse[raw]
        if kind == "int":
            return parse_int(raw, spec["label"], spec.get("minimum"))
        if kind == "opt_int":
            return parse_opt_int(raw, spec["label"], spec.get("minimum"))
        if kind == "int_list":
            return parse_int_list(raw, spec["label"], spec.get("minimum", 1),
                                  spec.get("maximum", 31))
        if kind == "date_list":
            return parse_date_list(raw, spec["label"])
        if kind == "stage_groups":
            return parse_stage_groups(raw, spec["label"])
        if kind == "opt_str":
            return (raw or "").strip()
        if kind == "time":
            text = (raw or "").strip()
            try:
                datetime.strptime(text, "%H:%M")
            except ValueError:
                raise FieldError(
                    f"「{spec['label']}」格式需為 HH:MM（例如 15:00）：{text}")
            return text
        value = (raw or "").strip()
        if not value:
            raise FieldError(f"「{spec['label']}」不能空白")
        return value

    def _on_ok(self):
        record = {}
        added = {}
        try:
            for spec in self._specs:
                record[spec["key"]] = self._value_of(spec)
                if spec["type"] == "pair_int":
                    added[spec["key"]] = parse_opt_int(
                        self._vars[spec["key"]][1].get(),
                        f"{spec['label']}（這次）", 0) or 0
        except FieldError as exc:
            messagebox.showerror("輸入有誤", str(exc), parent=self)
            return
        problem = self._validate(record) if self._validate else None
        if problem:
            messagebox.showerror("輸入有誤", problem, parent=self)
            return
        self.result = record
        self.added = added
        self.destroy()


# 自己折行時當成一整塊、不從中間拆開的東西：半形英數連在一起的（日期、
# 時刻、HH:MM、數字），其餘一個字一塊
_WRAP_TOKEN = re.compile(r"[\x21-\x7e]+|.", re.S)
# 不放在行首的標點——擠到行首的話跟上一行黏回去，寧可那一行稍微超出
_NO_LINE_START = set("，。、；：？！）」』》〉】,.;:?!)")
_NO_LINE_END = set("「『（(《〈【〔")


def wrap_cjk(text: str, font, width: int) -> str:
    """照像素寬度把中文說明折成多行，回傳插好換行的文字。

    Tk 的 wraplength 只會在半形空格斷行，中文句子沒有空格，夾一個
    「每 5 分鐘」就會變成「體力每 5」自己一行、後面整串再硬切。
    所以自己量：一個字一個字排，半形英數整塊不拆。
    """
    lines = []
    for para in text.split("\n"):
        line = ""
        for token in _WRAP_TOKEN.findall(para):
            if (not line.strip() or token in _NO_LINE_START
                    or font.measure(line + token) <= width):
                line += token
            else:
                line = line.rstrip()
                # 開頭的括號不留在行尾（「…選「」接著換行），跟著下一個字走
                carry = ""
                while line and line[-1] in _NO_LINE_END:
                    carry = line[-1] + carry
                    line = line[:-1]
                lines.append(line)
                line = carry + token.lstrip()
        lines.append(line)
    return "\n".join(lines)


# 狀態列的「放不下時優先在這裡換行」記號（見 wrap_status）
SOFT_BREAK = "\x1f"


def wrap_status(text: str, font, width: int) -> str:
    """狀態列的字：一行放得下就一行，放不下先在 SOFT_BREAK 換行，再不夠才硬折。

    text 裡本來就有的換行照留，每一行各自量。
    width 是 0（還量不到寬度）時不折，記號換成全形空白。
    """
    one_line = text.replace(SOFT_BREAK, "　")
    if width <= 0 or all(font.measure(line) <= width for line in one_line.split("\n")):
        return one_line
    return wrap_cjk(text.replace(SOFT_BREAK, "\n"), font, width)


def prewrap(label, width: int):
    """用 wrap_cjk 先把說明折好，取代 Tk 的 wraplength。

    wraplength 只會在半形空格斷行：「第 N 天」會在 N 後面斷開、
    「」」這種收尾標點會跑到下一行開頭。寬度固定的地方（對話框的提示、
    訊息框）建立時折一次就好；會跟著視窗變寬窄的用 ScrollableFrame.wrap_label。
    """
    try:
        named = label.cget("font")
    except tk.TclError:
        named = ""
    font = tkfont.Font(font=named or "TkDefaultFont")
    label.configure(text=wrap_cjk(str(label.cget("text")), font, width),
                    justify="left", wraplength=0)
    return label


def fill_wrapped_text(box, text: str):
    """把報告放進唯讀文字框，照文字框的寬度用 wrap_cjk 折行。

    Text 的 wrap="word" 跟 Label 的 wraplength 一樣只在半形空格斷行：
    「目標 30,435」會從空格斷開、中文長句硬切。這裡改成 wrap="none"，
    每次文字框寬度變了就用原文重新折一次。「複製全部」用的是原文，不受影響；
    反白後 Ctrl+C 會帶到畫面上的換行。
    """
    box.configure(wrap="none")
    font = tkfont.Font(font=box.cget("font") or "TkFixedFont")
    last = {"width": None}

    def rewrap(_event=None):
        try:
            inset = 2 * (int(str(box.cget("padx"))) + int(str(box.cget("borderwidth")))
                         + int(str(box.cget("highlightthickness"))))
            width = box.winfo_width() - inset - font.measure("0")
            if width <= font.measure("0") * 8 or width == last["width"]:
                return
            last["width"] = width
            top = box.yview()[0]
            state = box.cget("state")
            box.configure(state="normal")
            box.delete("1.0", "end")
            box.insert("1.0", wrap_cjk(text, font, width))
            box.configure(state=state)
            box.yview_moveto(top)
        except tk.TclError:
            pass

    box.insert("1.0", text)
    box.bind("<Configure>", rewrap, add="+")


class ScrollableFrame(ttk.Frame):
    """可捲動的容器；內容放進 .inner。直向、橫向捲軸都是放不下才出現。

    條件種類已經多到一個視窗放不下，沒有捲軸的話最下面的清單會被切掉
    而且沒辦法操作；視窗拉窄時右邊的欄位也一樣，所以兩個方向都要能捲。

    兩種模式：

    * 預設（`fit_content=False`）—— 內容跟著 canvas 拉寬。整頁捲動用這個，
      這樣裡面的清單會撐滿分頁寬度。`fill_height=True` 時高度也跟著撐滿
      （表格要隨視窗長高的分頁用），放不下才捲。
    * `fit_content=True` —— **canvas 跟著內容走**：寬度取內容需要的寬度
      （有給 `width` 就固定那個寬度）、高度取 `min(max_height, 內容高度)`，
      只在放不下時才捲。對話框用這個。

    > **絕對不要把內容壓得比它需要的還窄。** 內容框比 grid 需要的寬度窄時，
    > Tk 的 grid 會把放不下的元件直接 **unmap**——不是切掉一半，是整個消失。
    > 任務對話框就是這樣壞掉的：第 0 欄的標籤排得下，第 1 欄的輸入框全部
    > 被丟掉，看起來就像「欄位不能修改」。所以內容框一律取
    > `max(canvas 寬, 內容需要的寬)`，多出來的交給橫向捲軸。
    """

    # 內容需要的大小變了，Tk 不會發任何事件（<Configure> 只在實際大小變了才發，
    # 而實際大小是我們自己設的）。定時看一下，才不會內容變寬了卻被切掉。
    WATCH_MS = 300

    def __init__(self, master, height=None, fit_content=False, fill_height=False,
                 width=None, **kwargs):
        super().__init__(master, **kwargs)
        self._fit_content = fit_content
        self._fill_height = fill_height
        self._max_height = height
        self._fixed_width = width
        self._wrapped: list = []
        self._last_req = None
        self._last_canvas = None
        self._relayout_pending = False
        self._in_relayout = False
        # wrap_long_labels 開了才有：內容大小變了就重新掃一次長說明。
        # 只在建立時掃一次的話，之後才顯示（換活動類型時才出現的勾選框）或
        # 才換成長文字（限期關卡的說明）的那幾行不會折，會把整頁撐寬、
        # 表格右邊的按鈕被推出畫面。
        self._scan_long_labels = None
        self._canvas = tk.Canvas(self, highlightthickness=0)
        if height and not fit_content:
            self._canvas.configure(height=height)
        if width and fit_content:
            self._canvas.configure(width=width)
        self._canvas.grid(row=0, column=0, sticky="nsew")
        self._bar = ttk.Scrollbar(self, orient="vertical",
                                  command=self._canvas.yview)
        self._bar.grid(row=0, column=1, sticky="ns")
        self._hbar = ttk.Scrollbar(self, orient="horizontal",
                                   command=self._canvas.xview)
        self._hbar.grid(row=1, column=0, sticky="we")
        self._hbar.grid_remove()
        self._canvas.configure(yscrollcommand=self._bar.set,
                               xscrollcommand=self._hbar.set)
        self.rowconfigure(0, weight=1)
        self.columnconfigure(0, weight=1)

        self.inner = ttk.Frame(self._canvas)
        self._window = self._canvas.create_window((0, 0), window=self.inner,
                                                  anchor="nw")
        self.inner.bind("<Configure>", self._on_inner_configure)
        self._canvas.bind("<Configure>", self._on_canvas_configure)
        # 分頁切過來時馬上檢查一次（見 _apply_stale_size），不等 _watch
        self._canvas.bind("<Map>", lambda _e: self._schedule_relayout(), add="+")
        self.bind("<Configure>", lambda _e: self._update_bars())
        self.bind("<Enter>", lambda _e: self._bind_wheel(True))
        self.bind("<Leave>", lambda _e: self._bind_wheel(False))
        self.after(self.WATCH_MS, self._watch)

    def swap_inner(self, new_inner):
        """把內容框整個換成 new_inner（canvas 的子元件、還沒放上畫面），舊的拆掉。

        對話框重建欄位時用：新內容先在看不見的地方排好，一次換上來。
        """
        old = self.inner
        self.inner = new_inner
        new_inner.bind("<Configure>", self._on_inner_configure)
        self._canvas.itemconfigure(self._window, window=new_inner)
        old.destroy()
        self._wrapped = [(label, state) for label, state in self._wrapped
                         if label.winfo_exists()]
        self._last_req = None

    def request_natural_size(self, max_height=None):
        """先跟視窗要「內容剛好放得下」的大小（對話框打開時用）。

        canvas 預設只要求 Tk 的預設尺寸，不設的話對話框一打開就是一小塊、
        還掛著捲軸。之後使用者把對話框拉小，才輪到捲軸出場。
        """
        self.update_idletasks()
        height = self.inner.winfo_reqheight()
        if max_height:
            height = min(height, max_height)
        # 多要 wrap_label 預留的右側留白，剛打開時說明文字才不會先被折行、
        # 反而長高到要捲
        margin = max((state[0] for _label, state in self._wrapped), default=0)
        self._canvas.configure(width=self.inner.winfo_reqwidth() + margin,
                               height=height)

    def wrap_label(self, label, right=None, minimum=None, original=None):
        """讓說明文字跟著可見寬度折行，不要因為它一行太長撐出橫向捲軸。

        用 canvas 的寬度算（不是內容框的）——內容框是被內容撐寬的，
        拿它來算會變成自己決定自己。right 要留到外框右邊的 padding，
        再加上行尾標點可能多出的一個字。

        minimum：最窄折到多寬。對話框的提示用這個釘住「剛打開時的寬度」，
        視窗只會越拉越寬時才把字攤開；不釘的話折窄 → 內容變窄 → 對話框
        跟著縮 → 再折更窄，一路縮下去。original：label 已經先折好行時，
        要把沒折過的原文給進來，不然會拿折好的字當原文、拉寬也攤不開。
        """
        if right is None:
            right = dp(40)
        if label.winfo_class() == "TLabel":
            label.configure(justify="left", wraplength=0)
        else:
            right += dp(24)     # 勾選框的方塊也佔寬度
        # 對話框重建欄位時舊的 label 都砍掉了，順手清掉，不要越積越多
        self._wrapped = [(w, s) for w, s in self._wrapped if w.winfo_exists()]
        shown = str(label.cget("text")) if original is not None else None
        # [右邊留白, 原文, 上次排出來的字, 上次的寬度, 最窄寬度]
        self._wrapped.append((label, [right, original, shown, None, minimum]))
        self.after_idle(self._rewrap)

    def wrap_long_labels(self, longer_than=420):
        """把內容裡一行超過 `longer_than` px 的說明文字（含勾選框的字）
        都交給 wrap_label。

        說明文字散在各區塊裡、數量又多，一個一個掛太囉嗦；
        短的（欄位名稱、單位）不動，免得它們被折成好幾行。
        """
        self._wrap_longer_than = longer_than

        def scan(widget):
            for child in widget.winfo_children():
                if (child.winfo_class() in ("TLabel", "TCheckbutton")
                        and child.cget("text")
                        and child.winfo_reqwidth() > px(longer_than)
                        and all(child is not w for w, _r in self._wrapped)):
                    self.wrap_label(child)
                scan(child)
        self._scan_long_labels = lambda: scan(self.inner)
        # 要等排版算完才量得到 reqwidth
        self.after_idle(lambda: self.winfo_exists() and scan(self.inner))

    def _rewrap(self):
        try:
            visible = self._canvas.winfo_width()
            if visible <= 1:
                return
            base = self.inner.winfo_rootx()
            for label, state in self._wrapped:
                if not label.winfo_exists():
                    continue
                right, original, shown, last_width, minimum = state
                if minimum is not None and not label.winfo_ismapped():
                    # 對話框裡收起來的提示（代幣那兩格）量不到它在第幾欄，照 0 算會
                    # 折得特別寬，放回來時把整個說明欄撐開。等它顯示了再折
                    continue
                text = str(label.cget("text"))
                if text != shown:
                    original = text     # 別處換了文字（今日待辦、統計之類）
                offset = label.winfo_rootx() - base if label.winfo_ismapped() else 0
                room = visible
                if minimum is not None:
                    # 對話框的提示：寬度一律當作直向捲軸「在」來算。照 canvas
                    # 實際寬度算的話，捲軸一出一收寬度就差一條，折行跟著改、
                    # 內容高度又讓捲軸再出再收，縮小視窗時會這樣來回跳到當掉
                    room = max(1, self.winfo_width() - self._bar.winfo_reqwidth())
                width = max(minimum or px(160), room - max(offset, 0) - right)
                # 沒指定字型（cget 是空字串）或根本沒有 font 選項（勾選框）時，
                # 實際用的是 TkDefaultFont
                try:
                    named = str(label.cget("font"))
                except tk.TclError:
                    named = ""
                named = named or "TkDefaultFont"
                # 字型大小也要算進去：縮放時寬度沒變、字變大了，不重折的話
                # 舊的換行位置會讓一行超出畫面（今日待辦就是這樣把整頁撐寬）
                key = (width, self.tk.call("font", "actual", named, "-size"))
                if text == shown and key == last_width:
                    continue
                font = tkfont.Font(font=named)
                shown = wrap_cjk(original, font, width)
                if shown != text:
                    label.configure(text=shown)
                state[1:4] = [original, shown, key]
        except tk.TclError:
            pass

    def settle(self):
        """馬上做完 _watch 下一輪會做的事（折行、內容框大小、捲軸）。

        縮放時用：不等 _watch 的 300ms，免得畫面縮放完又自己再跳一次。
        """
        try:
            self._relayout(force=True)
        except tk.TclError:
            pass

    def _relayout(self, force=False):
        """折行 → 量內容 → 調內容框，一路做到不再變為止。

        折行改了字，內容需要的寬度要等 Tk 重排過才量得到新的；內容框寬度變了，
        折行又要照新的寬度重算。一輪 _watch 只走一步的話，切到一個在背景時
        排過版的分頁（例如縮放後才第一次打開「排程設定」），要好幾個 300ms
        才排好，中間右邊的按鈕會被推出畫面。所以當場來回幾次直到穩定。
        """
        if self._in_relayout:
            return
        self._in_relayout = True
        try:
            self._relayout_rounds(force)
        finally:
            self._in_relayout = False

    def _relayout_rounds(self, force):
        changed = force
        for _round in range(5):
            # 會變的說明（今日待辦、統計）換了文字也要重新換掉空格
            self._rewrap()
            self.update_idletasks()
            req = (self.inner.winfo_reqwidth(), self.inner.winfo_reqheight())
            if req != self._last_req and self._scan_long_labels:
                before = len(self._wrapped)
                self._scan_long_labels()
                if len(self._wrapped) != before:
                    self._rewrap()
                    self.update_idletasks()
                    req = (self.inner.winfo_reqwidth(),
                           self.inner.winfo_reqheight())
            # canvas 自己變大小也要重排：分頁還沒顯示時就被撐大的話，
            # <Configure> 不一定會再來一次，fill_height 的表格就長不高
            canvas = (self._canvas.winfo_width(), self._canvas.winfo_height())
            self._apply_stale_size()
            if not changed and req == self._last_req and canvas == self._last_canvas:
                return
            changed = False
            self._last_req, self._last_canvas = req, canvas
            self._fit_window()
            self.update_idletasks()
            # 視窗跟著改大小要等系統的大小事件處理完，canvas 才量得到新的寬高；
            # 不處理的話下一圈量到舊的，以為已經排好就收工了（縮放時對話框只排一半）
            _drain_window_events(self)

    def _watch(self):
        try:
            self._relayout()
            self.after(self.WATCH_MS, self._watch)
        except tk.TclError:
            pass        # 已經被砍掉了

    def _apply_stale_size(self):
        """內容框實際大小跟 canvas 給它的對不上時，逼 Tk 重新套一次。

        分頁在背景時改了內容框寬度（例如在「活動設定」把視窗拉寬再拉窄），
        Tk 只記下新的值，要等 canvas 重畫才真的套上去；切過來時 canvas 沒有
        重畫的理由，內容就一直維持舊的寬度、右邊被切掉，捲一下才排好。
        重設一次座標會讓 Tk 重新擺放內容框，效果跟捲動一樣。
        """
        if not self.inner.winfo_ismapped():
            return
        want_w = int(float(self._canvas.itemcget(self._window, "width") or 0))
        want_h = int(float(self._canvas.itemcget(self._window, "height") or 0))
        if ((want_w and self.inner.winfo_width() != want_w)
                or (want_h and self.inner.winfo_height() != want_h)):
            self._canvas.coords(self._window, *self._canvas.coords(self._window))
            self.update_idletasks()

    def _fit_window(self):
        """內容框的大小：至少跟 canvas 一樣大，內容需要更大就照內容。"""
        width = max(self._canvas.winfo_width(), self.inner.winfo_reqwidth())
        options = {"width": width}
        if self._fill_height:
            options["height"] = max(self._canvas.winfo_height(),
                                    self.inner.winfo_reqheight())
        self._canvas.itemconfigure(self._window, **options)
        if not self._fit_content:
            self._sync_region()
        self._update_bars()

    def _sync_region(self):
        """捲動範圍至少跟 canvas 一樣大。

        內容比視窗矮時，scrollregion 比 canvas 小，Tk 會讓它往上捲——
        內容被推到底下，分頁標籤跟內容之間空出一大塊。
        """
        box = self._canvas.bbox("all")
        if not box:
            return
        x0, y0, x1, y1 = box
        self._canvas.configure(scrollregion=(
            x0, y0, max(x1, x0 + self._canvas.winfo_width()),
            max(y1, y0 + self._canvas.winfo_height())))

    def _update_bars(self):
        """兩條捲軸要不要出現，一次用外框大小算完。

        分開各算各的會互相牽動：橫的出現 → 可見高度變矮 → 直的出現 →
        可見寬度變窄……一路抖下去。
        """
        req_w = self.inner.winfo_reqwidth()
        req_h = self.inner.winfo_reqheight()
        if self._fit_content:
            # 看 canvas 實際多高：使用者把對話框拉矮、或 center_on 壓矮時都要有捲軸
            shown_h = self._canvas.winfo_height()
            need_v = req_h > (shown_h if shown_h > 1 else (self._max_height or req_h))
            # 對話框可能被 minsize/maxsize 釘成別的寬度，看 canvas 實際多寬
            # 被 center_on 壓得比內容窄時也要有橫向捲軸，不然右邊直接被切掉
            shown = self._canvas.winfo_width()
            need_h = req_w > (shown if shown > 1 else (self._fixed_width or req_w))
        else:
            full_w, full_h = self.winfo_width(), self.winfo_height()
            if full_w <= 1 or full_h <= 1:
                return          # 還沒排版
            bar_w = self._bar.winfo_reqwidth()
            bar_h = self._hbar.winfo_reqheight()
            need_h = req_w > full_w
            need_v = req_h > full_h - (bar_h if need_h else 0)
            need_h = req_w > full_w - (bar_w if need_v else 0)
            need_v = req_h > full_h - (bar_h if need_h else 0)
        for bar, need in ((self._bar, need_v), (self._hbar, need_h)):
            if need and not bar.winfo_manager():
                bar.grid()
            elif not need and bar.winfo_manager():
                bar.grid_remove()

    def _on_inner_configure(self, _event=None):
        if not self._fit_content:
            self._sync_region()
            self._update_bars()
            return
        self._canvas.configure(scrollregion=self._canvas.bbox("all"))
        needed = self.inner.winfo_reqheight()
        limit = self._max_height or needed
        self._canvas.configure(
            width=self._fixed_width or self.inner.winfo_reqwidth(),
            height=min(limit, needed))
        # 放得下就把捲軸收起來，免得每個小對話框右邊都掛一條沒用的
        self._update_bars()

    def _on_canvas_configure(self, _event):
        self._fit_window()
        # 分頁剛切過來時 canvas 才拿到真正的大小：馬上排到穩定，不等 _watch
        self._schedule_relayout()

    def _schedule_relayout(self):
        if not self._relayout_pending:
            self._relayout_pending = True
            self.after_idle(self._relayout_idle)

    def _relayout_idle(self):
        self._relayout_pending = False
        if self._in_relayout:
            # _relayout 裡的 update_idletasks 會把這裡排的 idle 當場跑掉；
            # 外層那一圈本來就會重排到穩定，這裡再進去就是一層套一層，
            # 尺寸來回變時會一路套到 RecursionError、整個程式掛掉
            return
        try:
            self._relayout()
        except tk.TclError:
            pass

    def _bind_wheel(self, active):
        if active:
            self._canvas.bind_all("<MouseWheel>", self._on_wheel)
            self._canvas.bind_all("<Shift-MouseWheel>", self._on_shift_wheel)
        else:
            self._canvas.unbind_all("<MouseWheel>")
            self._canvas.unbind_all("<Shift-MouseWheel>")

    def _inner_scroller(self, event, view):
        """游標下的表格／文字框自己還捲得動的話，滾輪留給它，整頁不要跟著動。"""
        try:
            widget = self.winfo_containing(event.x_root, event.y_root)
            if widget is None or widget.winfo_class() not in (
                    "Treeview", "Text", "Listbox"):
                return False
            return tuple(getattr(widget, view)()) != (0.0, 1.0)
        except (tk.TclError, KeyError, AttributeError):
            return False

    def _alive(self):
        # 對話框關掉時游標若還在裡面，<Leave> 不會觸發，bind_all 就留著指向
        # 已經被砍掉的 canvas——下一次滾輪會丟 TclError。自己解掉。
        if not self._canvas.winfo_exists():
            self.unbind_all("<MouseWheel>")
            self.unbind_all("<Shift-MouseWheel>")
            return False
        return True

    def _on_wheel(self, event):
        if not self._alive() or self._inner_scroller(event, "yview"):
            return
        if self._bar.winfo_manager():
            self._canvas.yview_scroll(int(-event.delta / 120), "units")

    def _on_shift_wheel(self, event):
        if not self._alive() or self._inner_scroller(event, "xview"):
            return
        if self._hbar.winfo_manager():
            self._canvas.xview_scroll(int(-event.delta / 120), "units")


def loosen_width(frame, width, part=None):
    """讓自己有橫向捲軸的表格框不要把整頁撐寬。

    Treeview 要求的寬度是所有欄寬相加，不壓的話整頁會一直掛著橫向捲軸，
    表格自己那條反而永遠用不到。改成只要求 `width`，高度照原本需要的；
    分頁比較寬時照樣靠 sticky 撐滿。

    part：只壓框裡的這一塊（表格），旁邊的按鈕照原本的寬度留著——
    整框要求的寬度 = 原本 − 這塊原本的寬 + min(這塊原本的寬, width)。
    """
    def apply():
        if not frame.winfo_exists():
            return
        wanted = px(width)
        if part is not None:
            own = part.winfo_reqwidth()
            wanted = frame.winfo_reqwidth() - own + min(own, px(width))
        frame.configure(width=wanted, height=frame.winfo_reqheight())
        frame.grid_propagate(False)
    # 縮放之後要重量一次（見 reloosen_all）：固定住的高度是建立當下的字型量的，
    # 放大到 200% 時表格與右邊那排按鈕會被壓扁
    frame._loosen_apply = apply
    _LOOSENED.append(frame)
    frame.after_idle(apply)


_LOOSENED: list = []


def reloosen_all(root) -> None:
    """畫面縮放之後，把 loosen_width 固定住的表格框照新的字型大小重新量過。"""
    alive = [f for f in _LOOSENED if f.winfo_exists()]
    _LOOSENED[:] = alive
    if not alive:
        return
    for frame in alive:
        frame.grid_propagate(True)      # 先放開，才量得到現在真正需要多大
    root.update_idletasks()
    for frame in alive:
        frame._loosen_apply()


def fit_tree_columns(tree, pad=24, max_width=480):
    """把 Treeview 每一欄的寬度調成剛好放得下標題與目前畫出來的內容。

    max_width：單欄最寬到這裡，免得一格超長的文字把整張表撐爆
    （超過的部分表格自己會出橫向捲軸）。
    """
    style = ttk.Style(tree)
    body = tkfont.nametofont(style.lookup("Treeview", "font") or "TkDefaultFont")
    head = tkfont.nametofont(style.lookup("Treeview.Heading", "font")
                             or "TkHeadingFont")
    rows = [tree.item(iid, "values") for iid in tree.get_children()]
    for index, column in enumerate(tree["columns"]):
        width = head.measure(tree.heading(column, "text"))
        for values in rows:
            if index < len(values):
                width = max(width, body.measure(str(values[index])))
        tree.column(column, width=min(width + dp(pad), px(max_width)))
    _remember_tree_widths(tree)


def limited_progress(event: dict, data: dict, counts_list) -> list[tuple]:
    """限期關卡每一關這個帳號已打幾次、上限多少：[(關卡, 已打, 上限或 None)]。

    `counts_list` 是每一天的 counts 字典。本帳號取消「計算」的關不列——
    那多半是上限設成 0，列出來的 0 / 0 看起來像是已經打完。
    上限以本帳號改過的為準。「目前狀態」與「每日紀錄」共用。
    """
    counts_list = list(counts_list)
    caps = data.get("level_max_total") or {}
    enabled = data.get("level_enabled") or {}
    rows = []
    for level in event.get("levels") or []:
        if enabled.get(level["id"], True) is False:
            continue
        key = scheduler.level_key(event["id"], level["id"])
        done = (sum(int((counts or {}).get(key) or 0) for counts in counts_list)
                + int((data.get("baseline_levels") or {}).get(level["id"]) or 0))
        cap = caps.get(level["id"])
        if cap is None:
            cap = level.get("max_total")
        rows.append((level, done, cap))
    return rows


def events_by_remaining(events: list[dict], now: datetime | None = None) -> list[dict]:
    """依剩餘時間排：還沒結束的（含還沒開始的）快結束的在前；
    已結束的排在後面，剛結束的在前；常駐關卡、還沒填起訖日的最後。

    「目前狀態」的活動進度與「活動設定」的活動選單共用這個順序。
    只影響畫面怎麼列，存檔裡的活動順序不動。
    """
    now = now or datetime.now()

    def key(event):
        if storage.is_standing(event):
            return (2, 0.0)
        try:
            _start_dt, end_dt = scheduler.event_bounds(event)
        except scheduler.PlanError:
            return (3, 0.0)
        left = (end_dt - now).total_seconds()
        # 跟「剩餘」欄同一個判斷：結束時刻到了就算已結束
        return (1, -left) if end_dt <= now else (0, left)
    return sorted(events, key=key)      # sorted 是穩定排序，同鍵維持原順序


# 進度條空白段的候選字元，越前面越像「還沒填滿」
PROGRESS_EMPTY_CHOICES = ("░", "▒", "─", "━", "·", "-")


def progress_empty_char(tree) -> str:
    """挑一個在這張 Treeview 的字型裡跟實心段「█」一樣寬的空白段字元。

    寬度不同的話，越空的進度條越長（微軟正黑體裡「█」9、「░」12 像素）。
    都對不上時挑寬度最接近的。
    """
    body = tkfont.nametofont(ttk.Style(tree).lookup("Treeview", "font")
                             or "TkDefaultFont")
    full = body.measure(scheduler.PROGRESS_FILL)
    return min(PROGRESS_EMPTY_CHOICES,
               key=lambda ch: abs(body.measure(ch) - full))   # 同差距時取前面的


def autohide(bar):
    """給 xscrollcommand 用：整張表都看得到時把捲軸收起來。"""
    def update(first, last):
        if float(first) <= 0.0 and float(last) >= 1.0:
            bar.grid_remove()
        else:
            bar.grid()
        bar.set(first, last)
    return update


class ButtonColumns:
    """讓好幾排右側按鈕一樣寬，上下切齊。

    下拉按鈕（新增、加入）的箭頭是固定幾個像素、不跟字型縮放，同樣 width=8
    還是比一般按鈕寬一點，所在那排就會往左凸出去。這裡在每排塞一條看不見的
    撐寬用 frame，寬度取所有排裡最寬的那顆；按鈕一律 fill="x" 撐滿。
    縮放時按鈕大小變了會觸發 <Configure>，再重算一次。
    """

    def __init__(self):
        self._columns: list = []       # [(按鈕 frame, 撐寬 frame)]
        self._job = None

    def add(self, frame):
        spacer = ttk.Frame(frame, width=0, height=0)
        spacer.pack(side="bottom")
        self._columns.append((frame, spacer))
        for child in frame.winfo_children():
            if child is not spacer:
                child.pack_configure(fill="x")
                child.bind("<Configure>", self._schedule, add="+")
        self._schedule()

    def _schedule(self, _event=None):
        if self._job is None and self._columns:
            self._job = self._columns[0][0].after_idle(self._sync)

    def _sync(self):
        self._job = None
        try:
            widest = max((child.winfo_reqwidth()
                          for frame, spacer in self._columns
                          for child in frame.winfo_children() if child is not spacer),
                         default=0)
            for _frame, spacer in self._columns:
                if int(spacer.cget("width")) != widest:
                    spacer.configure(width=widest)
        except tk.TclError:
            pass


def default_level_name(records) -> str:
    """新關卡的預設名稱「關卡N」，跳過已經有人用的（刪過關卡後 N 可能撞名）。"""
    used = {str(record.get("name") or "").strip() for record in records}
    number = len(records) + 1
    while f"關卡{number}" in used:
        number += 1
    return f"關卡{number}"


def check_level_name(result, others):
    """關卡名稱不能跟同一組的其他關卡重複（ListEditor 的 validate）。

    排程報表、每日紀錄、規則的下拉選單都靠名稱分辨關卡，類型預設套用到
    活動時也是照名稱對；兩關同名就分不出誰是誰。
    """
    name = str(result.get("name") or "").strip()
    if not name:
        return "關卡名稱要填"
    if any(str(other.get("name") or "").strip() == name for other in others):
        return f"已經有叫「{name}」的關卡了，請換一個名稱"
    return None


class ListEditor(ttk.Frame):
    """Treeview ＋ 新增/編輯/刪除/上下移 的清單編輯器。"""

    def __init__(self, master, columns, specs, to_row, make_default=None,
                 reorderable=False, on_change=None, height=8, row_tags=None,
                 total_of=None, add_menu=None, fixed_rows=False,
                 heading_of=None, visible=None, auto_width=False,
                 delete_warning=None, extra_buttons=(), delete_blocked=None,
                 validate=None):
        """extra_buttons：[(按鈕文字, command), ...]，排在「刪除」下面。

        validate：新增／編輯按確定時檢查。拿 (對話框的結果, 其他筆記錄) 算出
        錯誤訊息（沒問題回 None）；有錯就跳出來、對話框不關。

        delete_blocked：拿要刪的那筆記錄算出「為什麼不能刪」（可以刪就回 None）；
        有理由的話只跳說明、不刪。

        fixed_rows：列是別處決定的（任務進度＝一個任務一列），只能編輯，
        不給新增／刪除——新增出來的那筆對不到任何任務，存檔時只會被丟掉。

        delete_warning：拿要刪的那筆記錄算出一段警告（不用警告就回 None）；
        有警告時確認對話框改成警告圖示、預設按鈕是「否」。

        visible：拿記錄判斷這一列要不要畫出來。只影響畫面，
        get_records() 照樣回傳全部（收起來的設定存檔時不會弄丟）。

        auto_width：每次重畫後，欄寬照內容調（見 fit_tree_columns）；
        不開就用 columns 裡給的固定寬度。

        heading_of：拿記錄算出「這一筆是誰」，顯示在編輯對話框最上面。
        """
        super().__init__(master)
        self._heading_of = heading_of
        self._specs = specs
        self._to_row = to_row
        self._make_default = make_default
        self._on_change = on_change
        self._row_tags = row_tags
        self._visible = visible
        self._auto_width = auto_width
        self._delete_warning = delete_warning
        self._delete_blocked = delete_blocked
        self._validate = validate
        self._total_of = total_of
        self.records: list[dict] = []

        keys = [c[0] for c in columns]
        self.tree = ttk.Treeview(self, columns=keys, show="headings", height=height)
        for key, heading, width, anchor in columns:
            self.tree.heading(key, text=heading)
            self.tree.column(key, width=px(width), anchor=anchor, stretch=False)
        self.tree.grid(row=0, column=0, sticky="nsew")
        self.tree.bind("<Double-1>", lambda _e: self.edit_selected())
        # 停用的列淡掉（目前用在「這次不算」的關卡與停用的任務）
        self.tree.tag_configure("disabled", foreground="#999999")

        scroll = ttk.Scrollbar(self, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=scroll.set)
        scroll.grid(row=0, column=1, sticky="ns")
        # 欄寬加起來常比視窗寬。表格自己橫捲，右邊那排按鈕才不會被擠出畫面
        hscroll = ttk.Scrollbar(self, orient="horizontal", command=self.tree.xview)
        self.tree.configure(xscrollcommand=autohide(hscroll))
        hscroll.grid(row=1, column=0, sticky="we")

        buttons = self.button_frame = ttk.Frame(self)
        buttons.grid(row=0, column=2, sticky="n", padx=(dp(8), 0))
        if add_menu and not fixed_rows:
            # 有好幾種要新增的東西時（體力來源就是），「新增」改成下拉選單，
            # 選了哪一種就帶入那一種的預設值。
            adder = ttk.Menubutton(buttons, text="新增", width=8)
            menu = tk.Menu(adder, tearoff=False)
            for label, maker in add_menu:
                menu.add_command(label=label,
                                 command=lambda m=maker: self.add(m()))
            adder["menu"] = menu
            self.add_menu_widget = menu
            adder.pack(pady=dp(2))
        elif not fixed_rows:
            ttk.Button(buttons, text="新增", width=8, command=self.add).pack(pady=dp(2))
        ttk.Button(buttons, text="編輯", width=8, command=self.edit_selected).pack(pady=dp(2))
        if not fixed_rows:
            ttk.Button(buttons, text="刪除", width=8,
                       command=self.delete_selected).pack(pady=dp(2))
        for text, command in extra_buttons:
            # 兩行字（「清除\n已失效」）要置中，見 TwoLine.TButton
            ttk.Button(buttons, text=text, command=command, width=8,
                       style="TwoLine.TButton" if "\n" in text else "TButton").pack(
                pady=(dp(10), dp(2)), fill="x")
        if reorderable:
            ttk.Button(buttons, text="上移", width=8,
                       command=lambda: self._move(-1)).pack(pady=(dp(10), dp(2)))
            ttk.Button(buttons, text="下移", width=8,
                       command=lambda: self._move(1)).pack(pady=dp(2))

        self.columnconfigure(0, weight=1)
        self.rowconfigure(0, weight=1)
        loosen_width(self, 320, part=self.tree)

    # -- 資料 ------------------------------------------------------------
    def set_specs(self, specs: list[dict]) -> None:
        """關卡清單會變動，對話框欄位得跟著重建。"""
        self._specs = specs

    def set_records(self, records: list[dict]) -> None:
        self.records = [copy.deepcopy(r) for r in records]
        self.refresh()

    def _changed(self) -> None:
        self.refresh()
        if self._on_change:
            self._on_change()

    def get_records(self) -> list[dict]:
        return [copy.deepcopy(r) for r in self.records]

    def refresh(self) -> None:
        self.tree.delete(*self.tree.get_children())
        for index, record in enumerate(self.records):
            if self._visible and not self._visible(record):
                continue      # iid 還是用 index，選取／編輯照樣對得回 self.records
            tags = self._row_tags(record) if self._row_tags else ()
            self.tree.insert("", "end", iid=str(index), tags=tags,
                             values=self._to_row(record))
        if self._auto_width:
            fit_tree_columns(self.tree)

    def _selected_index(self) -> int | None:
        selection = self.tree.selection()
        return int(selection[0]) if selection else None

    # -- 操作 ------------------------------------------------------------
    def specs_source(self):
        """交給 RecordDialog 的欄位來源。

        **是 callable 就原樣傳過去**，對話框才有辦法在使用者改了週期／達成條件
        之後重算欄位——只傳「開啟當下算好的那一份」的話，新增一條每月任務時
        永遠長不出「獎勵入帳幾號」。
        """
        return self._specs

    def add(self, initial=None) -> None:
        if initial is None:
            initial = self._make_default(self.records) if self._make_default else None
        dialog = RecordDialog(self.winfo_toplevel(), "新增",
                              self.specs_source(), initial,
                              total_of=self._total_of,
                              validate=self._validator(None))
        if dialog.result is not None:
            merged = dict(initial or {})
            merged.update(dialog.result)
            self.records.append(merged)
            self._changed()

    def edit_selected(self) -> None:
        index = self._selected_index()
        if index is None:
            return
        heading = (self._heading_of(self.records[index])
                   if self._heading_of else None)
        dialog = RecordDialog(self.winfo_toplevel(),
                              f"編輯：{heading}" if heading else "編輯",
                              self.specs_source(),
                              self.records[index], total_of=self._total_of,
                              heading=heading, validate=self._validator(index))
        if dialog.result is not None:
            self.records[index].update(dialog.result)
            self._changed()

    def _validator(self, index):
        """給 RecordDialog 的 validate：拿掉正在編輯的那一筆，其他的拿來比。"""
        if self._validate is None:
            return None
        others = [record for position, record in enumerate(self.records)
                  if position != index]
        return lambda result: self._validate(result, others)

    def delete_selected(self) -> None:
        index = self._selected_index()
        if index is None:
            return
        blocked = (self._delete_blocked(self.records[index])
                   if self._delete_blocked else None)
        if blocked:
            messagebox.showinfo("無法刪除", blocked, parent=self)
            return
        warning = (self._delete_warning(self.records[index])
                   if self._delete_warning else None)
        if warning:
            ok = messagebox.askyesno("確認刪除", f"確定要刪除這一筆嗎？\n\n{warning}",
                                     icon="warning", default="no", parent=self)
        else:
            ok = messagebox.askyesno("確認", "確定要刪除這一筆嗎？", parent=self)
        if ok:
            del self.records[index]
            self._changed()

    def _move(self, delta: int) -> None:
        index = self._selected_index()
        if index is None:
            return
        target = index + delta
        if not 0 <= target < len(self.records):
            return
        self.records[index], self.records[target] = self.records[target], self.records[index]
        self.refresh()
        self.tree.selection_set(str(target))


# --------------------------------------------------------------------------
# 任務：活動任務與固定任務共用同一組欄位
# --------------------------------------------------------------------------

def reward_specs(items) -> list[dict]:
    """獎勵欄位：一個道具一格數量。道具清單在「設定 → 獎勵道具」維護。"""
    return [{"key": f"reward_{it['id']}", "label": f"獎勵：{it['name']}",
             "type": "int", "minimum": 0, "default": 0}
            for it in items]


def rewards_from_record(record, items) -> list[dict]:
    out = []
    for item in items:
        qty = int(record.get(f"reward_{item['id']}") or 0)
        if qty:
            out.append({"item": item["id"], "qty": qty})
    return out


def record_from_rewards(rewards, items) -> dict:
    counts = {r.get("item"): int(r.get("qty") or 0) for r in rewards or []}
    return {f"reward_{it['id']}": counts.get(it["id"], 0) for it in items}


def reward_summary(record, items) -> str:
    names = {it["id"]: it["name"] for it in items}
    parts = []
    for item in items:
        qty = int(record.get(f"reward_{item['id']}") or 0)
        if qty:
            parts.append(f"{names.get(item['id'], item['id'])}×{qty}")
    return "、".join(parts) or "—"


class TaskEditorMixin:
    """任務清單編輯器的共用部分（活動任務與固定任務長得一樣）。"""

    TASK_COLUMNS = [("name", "任務名稱", 170, "w"),
                    ("cycle", "週期", 60, "center"),
                    ("metric", "條件", 90, "w"),
                    ("amount", "數量", 70, "e"),
                    ("scope", "範圍", 130, "w"),
                    ("rewards", "獎勵", 160, "w"),
                    ("enforce", "算進計算", 70, "center"),
                    ("assume", "預設完成", 70, "center")]

    def _items(self):
        return self.app.shared.get("items") or []

    def _level_choices(self):
        """所有活動的關卡，顯示成「活動·關卡」（限期關卡帶期數）。"""
        return storage.level_choices(self.app.shared)

    def _task_specs(self, record) -> list[dict]:
        cycle = record.get("cycle") or "event"
        metric = record.get("metric") or "manual"
        specs = [
            {"key": "name", "label": "任務名稱", "type": "str"},
            # 這兩格決定底下要有哪些欄位（每月才有入帳幾號、活動才有期限……），
            # 所以標 rebuild：一改就整組重算
            {"key": "cycle", "label": "週期", "type": "choice",
             "choices": storage.TASK_CYCLES, "rebuild": True,
             "hint": "公會任務跟每日一樣是每天重置"},
            {"key": "metric", "label": "達成條件", "type": "choice",
             "choices": storage.TASK_METRICS, "rebuild": True,
             "hint": "手動勾選＝程式看不出來（登入、簽到）"},
        ]
        # 手動勾選只有「做到／沒做到」，數量用不到（排程與進度都不看它），不顯示
        if metric != "manual":
            specs.append({"key": "amount", "label": "需要數量", "type": "int",
                          "minimum": 0})
        if cycle == "event":
            specs.append({"key": "deadline_offset", "label": "期限",
                          "type": "day_ref"})
        else:
            specs += [
                {"key": "from_date", "label": "只算這段期間（起）", "type": "date",
                 "optional": True,
                 "hint": "留空＝整段期間（活動任務＝那檔活動；"
                         "固定任務＝所有活動涵蓋的範圍）"},
                {"key": "to_date", "label": "只算這段期間（訖）", "type": "date",
                 "optional": True},
            ]
        if metric in ("clears", "points", "enemies", "drops"):
            specs.append({
                "key": "scope", "label": "指定關卡", "type": "multi_choice",
                "choices": self._level_choices() or [("", "（尚未設定關卡）")],
                "hint": "不選＝預設範圍（積分／關卡次數算這檔活動的，"
                        "耗體與敵人數跨活動一起算；取得道具算這檔活動"
                        "有填道具數量的關卡）"})
        if cycle == "weekly":
            specs.append({"key": "reward_weekday", "label": "獎勵入帳星期幾",
                          "type": "choice", "choices": WEEKDAY_CHOICES,
                          "hint": "體力獎勵算在這一天拿到；記成週日最保守"})
            specs.append({"key": "grant_on_done", "label": "出現時間不固定",
                          "type": "bool", "default": False,
                          "hint": "勾了＝做到那天到「每日紀錄」選「今天做到了」，那週的"
                                  "獎勵就算在勾的那天（已經在包包裡）；沒勾的週照舊"
                                  "算在上面那個星期幾。商店購買這種一週一定出現一次、"
                                  "但哪天不一定的用這個"})
        if cycle == "monthly":
            specs.append({"key": "reward_days", "label": "獎勵入帳幾號",
                          "type": "int_list", "minimum": 1, "maximum": 31,
                          "hint": "用頓號隔開，例如 5、11、17、23"})
        # 手動勾選的任務程式看不出有沒有做到，排程也排不出「去簽到」，一律不進求解
        # （storage._normalise_task 會清掉這個勾）。顯示出來只會讓人以為漏勾了
        if metric != "manual":
            specs.append({"key": "enforce", "label": "算進排程計算", "type": "bool",
                          "default": True,
                          "hint": "取消＝只記錄進度與獎勵，不強迫排程去達成。"
                                  "有體力獎勵的話建議勾起來，否則排程會算你拿得到、"
                                  "卻不保證排得出來"})
        specs.append({"key": "assume_done", "label": "預設完成", "type": "bool",
                      "default": metric == "manual",
                      "hint": ("手動勾選的任務不會算進排程計算（程式看不出你有沒有做到）。"
                               "勾了就當你每次都會做到，體力獎勵照入帳日算進排程；"
                               "真的沒做到再到「每日紀錄」標記那一天"
                               if metric == "manual" else
                               "勾了就當你每次都會做到，不用每天去勾；"
                               "真的沒做到再到「每日紀錄」標記那一天")})
        return specs + reward_specs(self._items())

    def _task_row(self, record):
        items = self._items()
        metric = record.get("metric")
        scope = record.get("scope") or []
        names = dict(storage.level_choices(self.app.shared, include_archived=True))
        if metric == "manual":
            amount = "—"
        else:
            amount = record.get("amount", 0)
        if scope:
            scope_text = "、".join(names.get(k, k) for k in scope[:2])
            if len(scope) > 2:
                scope_text += f"…（{len(scope)} 關）"
        else:
            scope_text = "預設"
        return (record.get("name", ""),
                storage.TASK_CYCLE_LABELS.get(record.get("cycle"), ""),
                storage.TASK_METRIC_LABELS.get(metric, ""),
                amount, scope_text, reward_summary(record, items),
                # 手動勾選的不進求解，沒有是或否可言
                "—" if metric == "manual"
                else ("是" if record.get("enforce", True) else "否"),
                "是" if record.get("assume_done") else "否")

    def _task_editor(self, master, height=6, on_change=None):
        return ListEditor(
            master,
            columns=self.TASK_COLUMNS,
            specs=self._task_specs,
            to_row=self._task_row,
            make_default=self._default_task,
            # 沒算進排程的變灰；手動勾選的本來就不進求解，不算「沒勾」，不變灰
            row_tags=lambda r: (() if r.get("enforce", True) or r.get("metric") == "manual"
                                else ("disabled",)),
            reorderable=True,
            on_change=on_change,
            height=height,
            # 欄寬照內容調：任務名稱、獎勵長短差很多，固定寬度不是切掉就是空一大截
            auto_width=True,
        )

    def _task_from_json(self, task, event_id=None) -> dict:
        record = {
            "id": task.get("id"),
            "name": task.get("name", ""),
            "cycle": task.get("cycle", "event"),
            "metric": task.get("metric", "manual"),
            "amount": task.get("amount", 0),
            "deadline_offset": task.get("deadline_offset", -1),
            "scope": list(task.get("scope") or []),
            # 手動勾選的存檔裡一定是 False（不進求解）；編輯時當成預設的 True，
            # 改成別種達成條件時「算進排程計算」才會照預設勾著
            "enforce": (bool(task.get("enforce", True))
                        or task.get("metric", "manual") == "manual"),
            "assume_done": bool(task.get("assume_done")),
            "grant_on_done": bool(task.get("grant_on_done")),
            "reward_weekday": int(task.get("reward_weekday", 6)),
            "reward_days": list(task.get("reward_days") or DEFAULT_MONTH_DAYS),
            **record_from_rewards(task.get("rewards"), self._items()),
        }
        if event_id is None:
            # 固定任務存的是絕對日期
            for key in ("from_date", "to_date"):
                if task.get(key):
                    record[key] = task[key]
            return record
        if task.get("from_offset") is not None:
            record["from_date"] = self._offset_to_date(task["from_offset"], event_id)
        if task.get("to_offset") is not None:
            record["to_date"] = self._offset_to_date(task["to_offset"], event_id)
        return record

    def _task_to_json(self, record, event_id=None) -> dict:
        metric = record.get("metric", "manual")
        # 對話框只在這幾種達成條件才列「指定關卡」。改成別種之後舊的選取還留在
        # 記錄裡，照寫出去的話排程會偷偷只算那幾關，畫面上卻沒有地方改。
        scoped = metric in ("clears", "points", "enemies", "drops")
        out = {
            "id": record.get("id"),
            "name": record.get("name", ""),
            "cycle": record.get("cycle", "event"),
            "metric": metric,
            # 手動勾選沒有數量欄（畫面藏起來了），一律存 1，不留新增時的預設值
            "amount": 1 if metric == "manual" else int(record.get("amount") or 0),
            "deadline_offset": int(record.get("deadline_offset", -1)),
            "scope": (list(record.get("scope") or []) or None) if scoped else None,
            "enforce": bool(record.get("enforce", True)) and metric != "manual",
            "assume_done": bool(record.get("assume_done")),
            "grant_on_done": (bool(record.get("grant_on_done"))
                              and record.get("cycle") == "weekly"),
            "reward_weekday": int(record.get("reward_weekday", 6)),
            "reward_days": list(record.get("reward_days") or DEFAULT_MONTH_DAYS),
            "rewards": rewards_from_record(record, self._items()),
        }
        for key, target in (("from_date", "from_offset"), ("to_date", "to_offset")):
            text = (record.get(key) or "").strip()
            if event_id is None:
                # 固定任務直接存日期：它不屬於任何一檔活動，沒有穩定的基準可以相對
                out[key] = text or None
                out[target] = None
            else:
                out[target] = self._date_to_offset(text, event_id) if text else None
        return out


# --------------------------------------------------------------------------
# 分頁
# --------------------------------------------------------------------------

class StatusTab(ttk.Frame):
    """目前狀態：帳號設定 ＋ 各活動的進度總覽與倒數。"""

    def __init__(self, master, app):
        super().__init__(master)
        # 視窗縮小時整頁可以兩個方向捲（見 ScrollableFrame）
        self.scroller = ScrollableFrame(self, fill_height=True)
        self.scroller.pack(fill="both", expand=True)
        page = self.scroller.inner
        page.configure(padding=dp(16))
        self.app = app
        self.name_var = tk.StringVar()
        self.cap_var = tk.StringVar()

        ttk.Label(page, text="帳號名稱").grid(row=0, column=0, sticky="w",
                                             pady=dp(6), padx=(0, dp(12)))
        ttk.Entry(page, textvariable=self.name_var, width=20).grid(
            row=0, column=1, sticky="w")
        ttk.Label(page, text="", foreground="#666666").grid(
            row=0, column=2, sticky="w", padx=(dp(12), 0))

        ttk.Label(page, text="體力上限").grid(row=1, column=0, sticky="w",
                                           pady=dp(6), padx=(0, dp(12)))
        ttk.Entry(page, textvariable=self.cap_var, width=20).grid(
            row=1, column=1, sticky="w")
        ttk.Label(page, text="各帳號獨立",
                  foreground="#666666").grid(row=1, column=2, sticky="w",
                                             padx=(dp(12), 0))

        ttk.Separator(page, orient="horizontal").grid(
            row=2, column=0, columnspan=3, sticky="we", pady=dp(14))
        ttk.Label(page, text="活動進度　（積分與已打關卡數由「每日紀錄」自動推導）"
                  ).grid(row=3, column=0, columnspan=3, sticky="w", pady=(0, dp(6)))

        columns = [("name", "活動", 150, "w"),
                   ("type", "類型", 60, "center"),
                   ("period", "期間", 220, "w"),
                   ("left", "剩餘", 110, "w"),
                   ("progress", "積分進度", 140, "w"),
                   ("points", "積分", 150, "w"),
                   ("clears", "已打關卡", 90, "e"),
                   ("tasks", "任務", 160, "w")]
        # 欄位是固定寬度、加起來比視窗寬（多活動時更擠），所以兩個方向的捲軸
        # 都要有——沒有水平捲軸的話最右邊那幾欄直接看不到也拉不出來。
        table = ttk.Frame(page)
        table.grid(row=4, column=0, columnspan=3, sticky="nsew")
        table.rowconfigure(0, weight=1)
        table.columnconfigure(0, weight=1)

        self.tree = ttk.Treeview(table, columns=[c[0] for c in columns],
                                 show="headings", height=6)
        for key, heading, width, anchor in columns:
            self.tree.heading(key, text=heading)
            self.tree.column(key, width=px(width), anchor=anchor, stretch=False)
        self.tree.grid(row=0, column=0, sticky="nsew")
        vbar = ttk.Scrollbar(table, orient="vertical", command=self.tree.yview)
        vbar.grid(row=0, column=1, sticky="ns")
        hbar = ttk.Scrollbar(table, orient="horizontal", command=self.tree.xview)
        hbar.grid(row=1, column=0, sticky="we")
        self.tree.configure(yscrollcommand=vbar.set, xscrollcommand=hbar.set)
        self.tree.tag_configure("ended", foreground="#999999")
        self.tree.tag_configure("urgent", foreground="#b45309")
        # 積分進度條的空白段要跟實心段等寬，每條才會一樣長
        self._bar_empty = progress_empty_char(self.tree)
        loosen_width(table, 300)

        self.note = ttk.Label(page, text="", foreground="#0a5", justify="left")
        self.note.grid(row=5, column=0, columnspan=3, sticky="w", pady=(dp(10), 0))

        ttk.Separator(page, orient="horizontal").grid(
            row=6, column=0, columnspan=3, sticky="we", pady=dp(12))
        self.todo = ttk.Label(page, text="", justify="left")
        self.todo.grid(row=7, column=0, columnspan=3, sticky="w")
        self.scroller.wrap_label(self.note)
        self.scroller.wrap_label(self.todo)

        page.rowconfigure(4, weight=1)
        page.columnconfigure(2, weight=1)

    def load(self):
        profile = self.app.profile
        self.name_var.set(profile.get("profile_name") or "")
        self.cap_var.set(str(profile.get("stamina_cap") or ""))
        self.refresh_derived()

    def refresh_derived(self):
        """只重畫由紀錄推導的部分（活動進度、今日待辦），不動上面兩格輸入框。

        每日紀錄一存檔就會叫到這裡；整頁 load() 的話，還沒按「儲存」的
        帳號名稱／體力上限會被洗回去。
        """
        profile = self.app.profile
        self.tree.delete(*self.tree.get_children())
        now = datetime.now()
        lines = []
        day_counts = [e.get("counts") or {} for e in self.app.log_entries()]
        for event in events_by_remaining(storage.visible_events(self.app.shared), now):
            data = storage.profile_event(profile, event["id"])
            try:
                start_dt, end_dt = scheduler.event_bounds(event)
            except scheduler.PlanError:
                self.tree.insert("", "end", values=(
                    scheduler.event_label(event),
                    storage.EVENT_TYPE_LABELS.get(event.get("type"), ""),
                    "（尚未填起訖日）", "", "", "", "", ""))
                continue
            tags = ()
            period = f"{start_dt:%m/%d %H:%M} ~ {end_dt:%m/%d %H:%M}"
            if storage.is_standing(event):
                # 常駐關卡沒有起訖日（event_bounds 給的是涵蓋一切的區間），
                # 照算會顯示「2912144 天」這種沒意義的倒數
                left = "常駐"
                period = "—"
            elif end_dt <= now:
                left = "已結束"
                tags = ("ended",)
            else:
                left = scheduler.format_countdown(end_dt, now)
            target = self._points_target(event)
            current = int(data.get("current_points") or 0)
            limited = (limited_progress(event, data, day_counts)
                       if storage.is_limited(event) else None)
            # 快結束了才提醒，而且只提醒這個帳號還有事要做的（打完／達標就不吵）
            if (not tags and left != "常駐" and (end_dt - now).days < 2
                    and self._has_work_left(limited, current, target)):
                tags = ("urgent",)
            if storage.is_standing(event):
                clears = ""           # 常駐關卡沒有關卡數任務，數字沒有意義
            elif limited is None:
                clears = data.get("current_clears") or 0
            elif not limited:
                clears = "不打"       # 每一關都被這個帳號取消「計算」
            else:
                done = sum(d for _lv, d, _c in limited)
                caps = [c for _lv, _d, c in limited]
                clears = (f"{done} / {sum(caps)}" if None not in caps else str(done))
            points = (f"{current} / {target}" + (f"（差 {target - current}）"
                                                 if current < target else "（達標）")
                      if target else str(current))
            tasks = self._task_summary(event)
            self.tree.insert("", "end", tags=tags, values=(
                scheduler.event_label(event),
                # 常駐關卡存檔裡的類型是借來的（多半是「當期」），顯示它反而誤導
                "常駐" if storage.is_standing(event)
                else storage.EVENT_TYPE_LABELS.get(event.get("type"), ""),
                period,
                left, scheduler.progress_bar(current, target, empty=self._bar_empty),
                points, clears, tasks))
            if tags == ("urgent",) and end_dt > now:
                lines.append(f"「{scheduler.event_label(event)}」"
                             f"{end_dt:%m/%d %H:%M} 就截止了，記得在那之前打完")
        # 欄寬照內容調：活動名稱、期間、任務摘要長短差很多
        fit_tree_columns(self.tree)
        self.note.config(text="\n".join(lines))
        self.todo.config(text="\n".join(self._todo_lines(now)))

    def _todo_lines(self, now) -> list[str]:
        """今日待辦：今天還要打什麼、還有哪些任務沒勾，以及各週期何時重置。

        任務只列「今天有效」的（見 _manual_tasks）：已封存活動的、這個帳號停用的、
        今天不在任務期間的都不列；一次性的活動任務勾過「做到了」就不再列。
        """
        shared = self.app.shared
        reset = scheduler.parse_clock(shared.get("daily_reset_time"), "05:00")
        today = scheduler.task_day_of(now, reset).isoformat()
        log = storage.load_log(self.app.profile_id)
        entry = storage.entry_for(log, today) or {}
        ticked = set(entry.get("tasks_done") or [])

        lines = [f"今日待辦（{today}）",
                 "　" + self.app.remaining_today(now)[0]]

        # 「預設完成」的任務不催你——那就是它存在的理由。
        # 一次性的活動任務哪一天勾的都算數，不只看今天那筆
        ever_done = {key for e in log.get("entries") or []
                     for key in e.get("tasks_done") or []}
        tasks = [(key, label, assume)
                 for key, label, assume, once in self._manual_tasks(
                     scheduler.task_day_of(now, reset))
                 if assume or not (once and key in ever_done)]
        assumed = [label for _k, label, assume in tasks if assume]
        pending = [label for key, label, assume in tasks
                   if not assume and key not in ticked]
        if pending:
            lines.append("　還沒勾的任務：" + "、".join(pending))
        elif any(not assume for _k, _l, assume in tasks):
            lines.append("　要勾的任務都勾完了 ✓")
        if assumed:
            missed = set(entry.get("tasks_missed") or [])
            note = ("　預設完成的任務："
                    + "、".join(assumed)
                    + "（沒做到的話到「每日紀錄」標記那一天）")
            if missed:
                names = {k: label for k, label, _a in tasks}
                note += "　今天已標記沒做到：" + "、".join(
                    names.get(k, k) for k in sorted(missed))
            lines.append(note)

        # 出現時間不固定的每週任務（商店購買）：這週（Mon–Sun）還沒標「做到了」就提醒，
        # 勾了排程才知道那份獎勵已經在包包裡
        day = date.fromisoformat(today)
        monday = (day - timedelta(days=day.weekday())).isoformat()
        week_done = {key for e in log.get("entries") or []
                     if monday <= (e.get("date") or "") <= today
                     for key in e.get("tasks_done") or []}
        flexible = {key for task, _owner, key in scheduler.iter_tasks(shared)
                    if task.get("grant_on_done") and task.get("cycle") == "weekly"}
        not_yet = [label for key, label, _a in tasks
                   if key in flexible and key not in week_done]
        if not_yet:
            lines.append("　本週還沒標做到了：" + "、".join(not_yet)
                         + "（做到那天到「每日紀錄」→ 任務狀態選「今天做到了」）")

        weekly = shared.get("weekly_reset") or {}
        monthly = shared.get("monthly_reset") or {}
        lines.append(
            "　重置倒數："
            f"每日／公會 {scheduler.format_countdown(scheduler.next_reset(now, reset), now)}"
            f"　每週 {scheduler.format_countdown(scheduler.next_reset(now, reset, weekday=int(weekly.get('weekday', 0) or 0)), now)}"
            f"　每月 {scheduler.format_countdown(scheduler.next_reset(now, reset, month_day=int(monthly.get('day', 1) or 1)), now)}")
        return lines

    def _manual_tasks(self, day):
        """今天要記錄的任務，跟「每日紀錄」的那份同一套規則，再加上日期範圍。

        日期範圍走 scheduler._task_span：活動任務＝活動開始到期限；固定任務＝
        「只算這段期間」，沒填就是所有活動涵蓋的期間。算不出範圍的照舊列出。

        回傳 [(任務鍵, 顯示名稱, 是否預設完成, 是否一次性的活動任務)]。
        """
        shared = self.app.shared
        overall = scheduler._overall_span(shared)
        rows = []
        for task, owner, key in scheduler.iter_tasks(shared):
            if owner is not None and storage.is_archived(owner):
                continue      # 已封存的活動，任務也跟著收起來
            if task.get("metric") != "manual" and not task.get("assume_done"):
                continue
            state = (self.app.profile.get("task_state") or {}).get(key) or {}
            if state.get("enabled") is False:
                continue
            span = scheduler._task_span(task, owner, overall)
            if span is not None:
                base, first, last = span
                if not (base + timedelta(days=first) <= day
                        <= base + timedelta(days=last)):
                    continue
            where = f"{owner.get('name') or owner['id']}／" if owner else ""
            rows.append((key, where + (task.get("name") or key),
                         bool(task.get("assume_done")),
                         task.get("cycle") == "event"))
        return rows

    @staticmethod
    def _has_work_left(limited, current, target) -> bool:
        """這個帳號在這檔還有沒有事要做（決定要不要截止提醒）。

        限期關卡：還有哪一關沒打到上限。沒有上限的關不知道打夠了沒，不算。
        一般活動：有積分目標就看達標了沒；沒有目標的不知道完成了沒，照舊提醒。
        """
        if limited is not None:
            return any(cap is not None and done < cap for _lv, done, cap in limited)
        if target:
            return current < target
        return True

    def _points_target(self, event) -> int:
        """這檔活動的積分任務目標（各帳號可以自己改數字）。"""
        best = 0
        for task in event.get("tasks") or []:
            if task.get("metric") != "points":
                continue
            state = (self.app.profile.get("task_state") or {}).get(
                f"{event['id']}/{task.get('id')}") or {}
            if state.get("enabled") is False:
                continue
            amount = state.get("amount_override")
            amount = int(amount) if amount not in (None, "") else int(task.get("amount") or 0)
            best = max(best, amount)
        return best

    def _task_summary(self, event) -> str:
        tasks = event.get("tasks") or []
        if not tasks:
            return "（尚未設定）"
        enforced = sum(1 for t in tasks if t.get("enforce"))
        return f"{len(tasks)} 條（{enforced} 條進計算）"

    def collect(self) -> bool:
        try:
            name = self.name_var.get().strip()
            if not name:
                raise FieldError("「帳號名稱」不能空白")
            if profile_name_taken(name, except_id=self.app.profile_id):
                raise FieldError(f"已經有叫「{name}」的帳號了，請換一個名稱"
                                 "（同名的帳號在上方的帳號選單分不出來）")
            self.app.profile["profile_name"] = name
            self.app.profile["stamina_cap"] = parse_int(
                self.cap_var.get(), "體力上限", 1)
        except FieldError as exc:
            messagebox.showerror("輸入有誤", str(exc), parent=self)
            return False
        return True


class EventsTab(EventDateMixin, TaskEditorMixin, ttk.Frame):
    """活動設定：並行活動的清單，以及選中那一檔的關卡結構與活動任務。"""

    def __init__(self, master, app):
        super().__init__(master, padding=dp(16))
        self.app = app
        self._current_id = None
        self._box_ids: list[str] = []     # 活動選單每一項對應的活動 id
        self._switching = False

        self.name_var = tk.StringVar()
        self.type_var = tk.StringVar()
        self.start_var = tk.StringVar()
        self.end_var = tk.StringVar()
        self.start_time_var = tk.StringVar()
        self.end_time_var = tk.StringVar()
        self.bonus_var = tk.StringVar()
        self.bonus_applies_var = tk.BooleanVar(value=True)
        self.points_cap_var = tk.StringVar()
        self.early_date_var = tk.StringVar()
        self.early_surplus_var = tk.BooleanVar(value=True)
        self.skip_last_var = tk.BooleanVar(value=False)
        # 起始積分、起始關卡數。其他起始值（耗體、敵人、道具、關卡已打次數）只在
        # 「補登開始前的進度」填——那些只有半途開始用時要補一次，常駐在這頁是雜訊。
        # 這兩格留著是因為記錯時也用得到（填負的積分把差額扣回來）。
        self.base_vars = {kind: tk.StringVar() for kind in ("points", "clears")}
        self.base_points_var = self.base_vars["points"]
        self._base_loaded = None    # (event_id, {種類: 起始值})：載入時的值

        # fill_height：視窗拉高時，最下面那張表格把多出來的高度吃掉
        # （哪一張見 _apply_visibility）
        scroller = self._scroller = ScrollableFrame(self, fill_height=True)
        scroller.pack(fill="both", expand=True)
        # 長說明跟著視窗寬度折行（見 ScrollableFrame.wrap_long_labels）
        scroller.wrap_long_labels()
        body = self._body = scroller.inner

        # 頂部兩排：第一排管整份活動清單（跟選哪一檔無關），
        # 分隔線下面那排才是對目前這一檔的操作
        top = ttk.Frame(body)
        top.grid(row=0, column=0, columnspan=3, sticky="we", pady=(0, dp(4)))
        bar = ttk.Frame(top)
        bar.pack(anchor="w")
        ttk.Label(bar, text="活動").pack(side="left")
        self.event_box = ttk.Combobox(bar, state="readonly", width=24)
        self.event_box.pack(side="left", padx=(dp(6), dp(12)))
        self.event_box.bind("<<ComboboxSelected>>", self._on_event_selected)
        ttk.Button(bar, text="新增活動", command=self.add_event).pack(side="left")
        ttk.Button(bar, text="新增限期系列", command=self.add_limited_event).pack(
            side="left", padx=(dp(6), 0))
        archived = ttk.Menubutton(bar, text="已封存")
        # 選單在打開的當下才建：封存清單會隨操作變動
        self.archived_menu = tk.Menu(
            archived, tearoff=False, postcommand=self._fill_archived_menu)
        archived["menu"] = self.archived_menu
        archived.pack(side="left", padx=(dp(6), 0))
        ttk.Separator(top, orient="horizontal").pack(fill="x", pady=(dp(10), dp(8)))
        # 按鈕等下面的 event_only() 那幾個收合清單建好才放得進去
        actions = self._actions_row = ttk.Frame(top)
        actions.pack(anchor="w")

        # 第 2 欄是會伸展的提示欄，輸入元件一律放第 1 欄，否則會被推到最右邊
        ttk.Label(body, text="活動名稱").grid(row=1, column=0, sticky="w",
                                           pady=dp(6), padx=(0, dp(12)))
        name_box = ttk.Frame(body)
        name_box.grid(row=1, column=1, sticky="w")
        self.name_entry = ttk.Entry(name_box, textvariable=self.name_var, width=22)
        self.name_entry.pack(side="left")
        # 限期關卡的期數：跟名稱分開存，顯示時才接在一起（scheduler.event_label）
        self.period_var = tk.StringVar()
        self._period_box = ttk.Frame(name_box)
        ttk.Label(self._period_box, text="期數").pack(side="left", padx=(dp(10), dp(4)))
        ttk.Entry(self._period_box, textvariable=self.period_var, width=5).pack(
            side="left")
        self.name_hint = ttk.Label(body, text="紀錄依活動分區；改名稱不影響紀錄",
                                   foreground="#666666")
        self.name_hint.grid(row=1, column=2, sticky="w", padx=(dp(12), 0))

        # 常駐關卡沒有類型、起訖日、加成、活動任務——選到它時這幾排整個收起來。
        # 留著空欄位只會讓人以為是還沒填。
        self._event_only: list = []

        def event_only(widget):
            self._event_only.append(widget)
            return widget

        # 限期關卡（檢定、忘卻）有類型與起訖日，但沒有加成、積分上限、活動任務
        self._activity_only: list = []

        def activity_only(widget):
            self._activity_only.append(widget)
            return event_only(widget)

        # 活動加成、積分上限、盡量提早、起始積分：只有當期、復刻這種有積分的活動才有。
        # 音像、蜜意蒐羅、祕寶探尋跟限期關卡一樣收起來（見 storage.NO_POINTS_TYPES）
        self._points_only: list = []

        def points_only(widget):
            self._points_only.append(widget)
            return activity_only(widget)

        # 反過來：只有限期關卡才有的設定
        self._limited_only: list = []

        def limited_only(widget):
            self._limited_only.append(widget)
            return widget

        # 這一檔的操作。用 grid 固定欄位：收起來的按鈕不佔位，其他的順序不變。
        # 常駐關卡不能複製／刪除／封存、沒有任務可分析；目標分析只看一般活動
        # （限期關卡沒有活動任務）；接下一期只給限期關卡。
        # 限期關卡是一期一期輪替，改叫「這一期」（見 _apply_visibility）
        self._actions_label = event_only(ttk.Label(actions, text="這一檔："))
        self._actions_label.grid(row=0, column=0, padx=(0, dp(6)))
        for column, (text, command, wrap) in enumerate((
                # 限期關卡換期用「接下一期」，不給複製（複製會把系列名稱改掉）
                ("複製", self.duplicate_event, activity_only),
                ("刪除", self.delete_event, event_only),
                ("封存", self.archive_event, event_only),
                ("目標分析", self.analyze_targets, activity_only),
                ("接下一期", self.next_period, limited_only)), start=1):
            wrap(ttk.Button(actions, text=text, command=command)).grid(
                row=0, column=column, padx=(0, dp(6)))

        event_only(ttk.Label(body, text="活動類型")).grid(
            row=2, column=0, sticky="w", pady=dp(6), padx=(0, dp(12)))
        type_box = event_only(ttk.Frame(body))
        type_box.grid(row=2, column=1, sticky="w")
        self.type_combo = ttk.Combobox(
            type_box, textvariable=self.type_var, state="readonly", width=10,
            values=[label for _key, label in storage.EVENT_TYPES])
        self.type_combo.pack(side="left")
        self.type_combo.bind("<<ComboboxSelected>>",
                             lambda _e: self._apply_visibility())
        ttk.Button(type_box, text="套用類型預設", width=13,
                   command=self.apply_type_defaults).pack(side="left", padx=(dp(6), 0))
        event_only(ttk.Label(body, text="類型只是預設值的來源：按右邊那顆才會帶入"
                                        "對應的基礎積分表與加成開關，之後仍可逐欄改",
                             foreground="#666666")).grid(
            row=2, column=2, sticky="w", padx=(dp(12), 0))

        event_only(ttk.Label(body, text="活動起始")).grid(
            row=3, column=0, sticky="w", pady=dp(6), padx=(0, dp(12)))
        start_box = event_only(ttk.Frame(body))
        start_box.grid(row=3, column=1, sticky="w")
        self.start_hint = event_only(ttk.Label(body, text="", foreground="#666666"))
        self.start_hint.grid(row=3, column=2, sticky="w", padx=(dp(12), 0))
        DateEntry(start_box, self.start_var, self.start_hint, width=12).pack(side="left")
        ttk.Entry(start_box, textvariable=self.start_time_var, width=7).pack(
            side="left", padx=(dp(6), 0))

        event_only(ttk.Label(body, text="活動結束")).grid(
            row=4, column=0, sticky="w", pady=dp(6), padx=(0, dp(12)))
        end_box = event_only(ttk.Frame(body))
        end_box.grid(row=4, column=1, sticky="w")
        self.end_hint = event_only(ttk.Label(body, text="", foreground="#666666"))
        self.end_hint.grid(row=4, column=2, sticky="w", padx=(dp(12), 0))
        DateEntry(end_box, self.end_var, self.end_hint, width=12).pack(side="left")
        ttk.Entry(end_box, textvariable=self.end_time_var, width=7).pack(
            side="left", padx=(dp(6), 0))
        hint_box = event_only(ttk.Frame(body))
        hint_box.grid(row=5, column=0, columnspan=3, sticky="w", pady=(0, dp(4)))
        ttk.Label(hint_box, text="時間格式 HH:MM。預設起始日 15:00 開始、"
                                 "結束日 12:00 結束——最後一天要在中午前打完",
                  foreground="#666666").pack(anchor="w")
        # 本帳號「每檔活動自動套用的規則」落在這一檔的哪幾天（唯讀，到排程設定改）
        self.auto_rule_label = ttk.Label(hint_box, text="", foreground="#b45309",
                                         justify="left")
        self.auto_rule_label.pack(anchor="w", pady=(dp(2), 0))
        for var in (self.start_var, self.end_var, self.type_var):
            var.trace_add("write", lambda *_a: self.refresh_auto_rules())

        points_only(ttk.Label(body, text="活動加成")).grid(
            row=6, column=0, sticky="w", pady=dp(6), padx=(0, dp(12)))
        bonus_box = points_only(ttk.Frame(body))
        bonus_box.grid(row=6, column=1, sticky="w")
        ttk.Entry(bonus_box, textvariable=self.bonus_var, width=8).pack(side="left")
        ttk.Label(bonus_box, text="％").pack(side="left", padx=(dp(4), 0))
        points_only(ttk.Label(body, text="本帳號專屬（隊伍加成各帳號不同）；"
                                        "改了會依基礎積分重算下面的積分",
                             foreground="#666666")).grid(
            row=6, column=2, sticky="w", padx=(dp(12), 0))
        self.bonus_var.trace_add("write", lambda *_a: self._recompute_points())

        points_only(ttk.Checkbutton(
            body, variable=self.bonus_applies_var,
            text="這檔活動套用活動加成（復刻等無加成活動請取消）",
            command=self._recompute_points)).grid(
            row=7, column=1, columnspan=2, sticky="w", pady=(0, dp(4)))

        points_only(ttk.Label(body, text="積分上限")).grid(
            row=8, column=0, sticky="w", pady=dp(6), padx=(0, dp(12)))
        cap_box = points_only(ttk.Frame(body))
        cap_box.grid(row=8, column=1, sticky="w")
        ttk.Entry(cap_box, textvariable=self.points_cap_var, width=8).pack(side="left")
        ttk.Label(cap_box, text="分").pack(side="left", padx=(dp(4), 0))
        points_only(ttk.Label(body, text="獎勵表最後一階的積分（加成後、所有帳號共用）；"
                                        "留空＝沒有上限。超過就不再為它排計分關卡",
                             foreground="#666666")).grid(
            row=8, column=2, sticky="w", padx=(dp(12), 0))

        points_only(ttk.Label(body, text="盡量提早")).grid(
            row=9, column=0, sticky="w", pady=dp(6), padx=(0, dp(12)))
        early_box = points_only(ttk.Frame(body))
        early_box.grid(row=9, column=1, sticky="w")
        # 寬度固定成最長那句提示：這格跟輸入框同在第 1 欄，提示在「只要打數字…」
        # 「日期還沒填完整」「星期X」之間換來換去，欄寬就跟著變，右邊那欄的說明
        # 全部重新折行、行數一變，整頁就上下抖一下
        early_hint = ttk.Label(early_box, text="", foreground="#666666",
                               width=text_width_chars(DateEntry.empty_hint()))
        DateEntry(early_box, self.early_date_var, early_hint, width=12).pack(side="left")
        early_hint.pack(side="left", padx=(dp(6), 0))
        points_only(ttk.Label(body, text="這天之前盡量把積分拿完（填下一檔活動預計開始的"
                                        "日子、所有帳號共用）；留空＝不提早。"
                                        "不會因此多花或多買體力",
                             foreground="#666666")).grid(
            row=9, column=2, sticky="w", padx=(dp(12), 0))
        early_check = points_only(ttk.Checkbutton(
            body, variable=self.early_surplus_var,
            text="那天之前，多餘的體力先打這檔的計分關卡"
                 "（取消＝常駐加碼照打，只挪加碼用不完的體力）"))
        early_check.grid(row=10, column=1, columnspan=2, sticky="w", pady=(0, dp(4)))
        # 限期關卡時「盡量提早」那排整個收起來，同一列給這個勾選用。
        # 從第 0 欄開始，跟「活動名稱」那些欄位名稱切齊
        limited_only(ttk.Checkbutton(
            body, variable=self.skip_last_var,
            text="結束當天不打（這一期的次數要在前一天打完；下一期照常；所有帳號共用，"
                 "接下一期會帶過去）")).grid(row=9, column=0, columnspan=3,
                                              sticky="w", pady=dp(6))

        # 沒填日期時這個勾選沒有作用，變灰免得以為它自己就會生效
        def sync_early_check(*_args):
            early_check.state(["!disabled"] if self.early_date_var.get().strip()
                              else ["disabled"])
        self.early_date_var.trace_add("write", sync_early_check)
        sync_early_check()

        # 起始值存在紀錄檔（見 App.set_log_baselines），本帳號專屬。
        # 音像不看積分也不看關卡數，整列收起來（見 _apply_visibility）
        self._base_row = []

        def base_row(widget):
            self._base_row.append(widget)
            return activity_only(widget)

        base_row(ttk.Label(body, text="起始值")).grid(
            row=11, column=0, sticky="w", pady=dp(6), padx=(0, dp(12)))
        base_box = base_row(ttk.Frame(body))
        base_box.grid(row=11, column=1, sticky="w")
        # 每一種包成一塊：沒有積分的類型把積分那塊收起來（見 _apply_visibility）
        self._base_parts = {}
        for kind, label, width in (("points", "積分", 8), ("clears", "關卡數", 6)):
            part = self._base_parts[kind] = ttk.Frame(base_box)
            part.pack(side="left", padx=(0, dp(10)))
            ttk.Label(part, text=label).pack(side="left")
            ttk.Entry(part, textvariable=self.base_vars[kind], width=width).pack(
                side="left", padx=(dp(4), 0))
        self._base_points_part = self._base_parts["points"]
        self._base_clears_label = self._base_parts["clears"]
        base_row(ttk.Label(body, text="本帳號專屬：開始記錄之前就有的量；"
                                        "目前值＝起始值＋每日紀錄累計。耗體、敵人、道具、"
                                        "關卡已打次數在「設定 → 補登開始前的進度」填",
                             foreground="#666666")).grid(
            row=11, column=2, sticky="w", padx=(dp(12), 0))

        ttk.Separator(body, orient="horizontal").grid(
            row=12, column=0, columnspan=3, sticky="we", pady=dp(14))
        # 標題與工具按鈕包在同一個跨滿三欄的 frame 裡。用 columnspan=2 只跨欄 0~1
        # 的話，那條長標題會把第 0 欄撐寬，上面所有輸入框都被往右推。
        header = ttk.Frame(body)
        header.grid(row=13, column=0, columnspan=3, sticky="we", pady=(0, dp(6)))
        ttk.Label(header, text="關卡結構　（消耗體力/敵人數/計分 為所有帳號共用；"
                               "積分與「計算」僅屬目前帳號。"
                               "上移／下移只排順序）").pack(anchor="w")
        # 工具按鈕放在標題下一列：擠在同一列的話視窗縮到最小時會被推出畫面，
        # 還把整頁撐寬
        # 只有當期、復刻有積分表可以套，其他類型整排收起來（見 _apply_visibility）
        tools = self._level_tools = ttk.Frame(header)
        tools.pack(anchor="w", pady=(dp(6), 0))
        ttk.Button(tools, text="由積分反推基礎積分",
                   command=self._derive_base_points).pack(side="left", padx=(0, dp(6)))
        preset = ttk.Menubutton(tools, text="套用常見表")
        menu = tk.Menu(preset, tearoff=False)
        for name, applies, table in BASE_POINT_TABLES:
            menu.add_command(
                label=f"{name}　" + "　".join(f"{cost}→{pt}"
                                              for cost, pt in table.items()),
                command=lambda n=name, a=applies, t=table:
                    self._apply_base_table(n, a, t))
        preset["menu"] = menu
        self.preset_menu = menu
        preset.pack(side="left")

        self.editor = ListEditor(
            body,
            columns=[("name", "關卡名稱", 120, "w"),
                     ("cost", "體力", 55, "e"),
                     ("enemies", "敵人", 55, "e"),
                     ("drops", "道具", 55, "e"),
                     ("kind", "類型", 80, "center"),
                     ("enabled", "計算", 50, "center"),
                     ("window", "開放", 130, "w"),
                     ("base_points", "基礎積分", 70, "e"),
                     ("points", "積分（本帳號）", 100, "e"),
                     ("cp", "CP", 55, "e")],
            specs=self._level_specs,
            to_row=self._level_row,
            make_default=lambda records: {
                # 跳過這檔刪掉的關卡留在紀錄裡的代號，舊紀錄才不會算到新關卡上
                "id": storage.next_level_id(records, self._current_id),
                "name": default_level_name(records),
                "stamina_cost": 10, "enemies": 0, "drops": 0,
                # 常駐關卡沒有積分，新關卡預設「只算次數」
                "scoring": not self._is_standing(), "counts_clears": True,
                "kind": "count_only" if self._is_standing() else "scoring",
                "enabled": True,
                "available_from": None, "max_total": None, "must_finish": False,
                "same_day": False, "unlock_first": False, "group": None,
                "base_points": None, "points": None,
            },
            row_tags=lambda r: () if r.get("enabled", True) else ("disabled",),
            validate=check_level_name,
            delete_warning=self._level_delete_warning,
            delete_blocked=lambda r: (
                f"「{r.get('name')}」是常駐關卡的基本關卡，不能刪除。\n"
                "不想排它的話，把它的「這次計算要算」取消勾選。"
                if storage.is_locked_standing_level(self._current_event(), r) else None),
            reorderable=True,
            height=7,       # 視窗拉高時限期關卡會自己長高
        )
        self.editor.grid(row=14, column=0, columnspan=3, sticky="nsew")

        activity_only(ttk.Separator(body, orient="horizontal")).grid(
            row=15, column=0, columnspan=3, sticky="we", pady=dp(14))
        activity_only(ttk.Label(
            body, text="活動任務　（積分、關卡次數、累計耗體……都是任務；"
                       "耗體類的任務跨活動一起累計。"
                       "上移／下移只排順序，不會改變要打什麼）")).grid(
            row=16, column=0, columnspan=3, sticky="w", pady=(0, dp(6)))
        self.task_editor = activity_only(self._task_editor(body, height=6))
        self.task_editor.grid(row=17, column=0, columnspan=3, sticky="nsew")

        body.columnconfigure(2, weight=1)

    def _level_specs(self, record):
        """關卡編輯欄位。常駐關卡少三欄——見下面的註解。"""
        standing = self._is_standing()
        locked = storage.is_locked_standing_level(self._current_event(), record)
        specs = [
            {"key": "name", "label": "關卡名稱", "type": "str", "readonly": locked,
             **({"hint": "常駐關卡的基本關卡，不能改名也不能刪除"} if locked else {})},
            {"key": "stamina_cost", "label": "消耗體力", "type": "int", "minimum": 1},
            {"key": "enemies", "label": "敵人人數", "type": "int", "minimum": 0,
             "hint": "所有帳號共用；沒有敵人的關卡填 0"},
            {"key": "drops", "label": "取得道具", "type": "int", "minimum": 0,
             "default": 0,
             "hint": "打一次拿到幾個活動道具（所有帳號共用），給「取得道具」類的任務用；"
                     "沒有就填 0"},
            # 常駐關卡沒有積分，類型裡不列「計分」
            {"key": "kind", "label": "類型", "type": "choice",
             "choices": ([c for c in LEVEL_KIND_CHOICES if c[0] != "scoring"]
                         if standing else LEVEL_KIND_CHOICES),
             "hint": ("常駐關卡沒有積分。只算次數＝算進「關卡次數」類的任務"
                      if standing else
                      "只算次數＝沒有積分但算進「關卡次數」類的任務（活動BOSS關）")},
        ]
        # 「開放起日」是相對活動起始日、「總次數上限／必打滿」是整檔活動的總量，
        # 常駐關卡沒有起訖日可以相對。要限次數請用「排程設定」的指定關卡次數限制。
        limited = self._is_limited()
        if not self._is_standing():
            specs += [
                {"key": "available_from_date", "label": "開放起日",
                 "type": "date", "optional": True,
                 "hint": "這天才開放，之後到活動結束；留空＝整檔活動都能打"},
                {"key": "max_total", "label": "總共最多幾次", "type": "opt_int",
                 "minimum": 1,
                 "hint": ("這一期的預設上限（所有帳號共用）；帳號不同的話填下面那欄"
                          if limited else
                          "整檔活動的總次數（不是每天）；留空＝沒有上限")},
                {"key": "must_finish", "label": "一定要打滿", "type": "bool",
                 "default": False,
                 "hint": "活動結束前必須打滿上面那個次數（活動BOSS關）"},
                {"key": "same_day", "label": "同一天打完", "type": "bool",
                 "default": False,
                 "hint": "上面那個次數要集中在同一天打，不拆成好幾天"
                         "（活動BOSS關一口氣打掉）；要先填「總共最多幾次」"},
                {"key": "unlock_first", "label": "開場先打一次", "type": "bool",
                 "default": False,
                 "hint": "遊戲的解鎖鏈：勾起來的關卡會照消耗體力由小到大各先打"
                         "一次，便宜的那關沒打過之前比它貴的完全不能打。"
                         "跟「總共最多幾次」無關——這是「至少一次」，之後還能猛打"},
                {"key": "group", "label": "組別", "type": "opt_int", "minimum": 1,
                 "hint": "解鎖鏈分組：同一組內照消耗體力由小到大解鎖，不同組互不相干"
                         "（蜜意蒐羅的第 1~11 組）。留空＝跟這檔活動其他沒填組別的"
                         "關卡同一條鏈"},
            ]
        if limited:
            specs += [
                {"key": "profile_max_total", "label": "本帳號這期上限",
                 "type": "opt_int", "minimum": 0,
                 "hint": "本帳號專屬；留空＝用上面的預設上限"},
                {"key": "tiers", "label": "難度分組", "type": "stage_groups",
                 "hint": "依序解鎖的第幾關（所有帳號共用）。分號隔開各組，"
                         "例如 35、40、45；50、55、60；61~63。沒分到的算「其他關」。"
                         "各帳號到「排程設定」的指定關卡次數限制選難度、設星期幾"},
            ]
        specs.append(
            {"key": "enabled", "label": "這次計算要算", "type": "bool",
             "default": True,
             "hint": "取消勾選＝這次排程不排這關（本帳號專屬）"})
        if self._levels_have_no_points():
            # 音像、蜜意蒐羅、祕寶探尋、限期關卡、常駐關卡沒有積分，基礎積分／取得積分兩欄不出現
            return specs
        specs += [
            {"key": "base_points", "label": "基礎積分", "type": "opt_int",
             "minimum": 0,
             "hint": "沒有活動加成的原始積分（所有帳號共用）；留空代表積分自己填"},
            {"key": "points", "label": "取得積分", "type": "opt_int", "minimum": 0,
             "hint": "本帳號專屬；填了基礎積分就會自動算，仍可手動改",
             "derive_from": ["base_points", "kind"],
             "derive": lambda values: self._derive_points(values)},
        ]
        return specs

    def _is_standing(self) -> bool:
        return storage.is_standing(self._current_event() or {})

    def _levels_have_no_points(self) -> bool:
        """關卡沒有積分：沒有積分的活動類型、限期關卡，或常駐關卡。"""
        return self._is_standing() or self._is_limited() or self._has_no_points()

    def _has_no_points(self) -> bool:
        """這檔是沒有積分的活動類型（看下拉的即時值，見 storage.NO_POINTS_TYPES）。"""
        return not self._is_standing() and self._type_key() in storage.NO_POINTS_TYPES

    def _is_limited(self) -> bool:
        # 看下拉的即時值而不是存檔值：剛把類型切成限期關卡、還沒存，
        # 關卡對話框就該出現「本帳號這期上限」
        return not self._is_standing() and self._type_key() == "limited"

    def _apply_visibility(self):
        standing = self._is_standing()
        limited = self._is_limited()
        # 按鈕全收掉時 frame 還是保留原本的高度，整排要自己拿掉
        if standing:
            self._actions_row.pack_forget()
        else:
            self._actions_row.pack(anchor="w")
        for widget in self._event_only:
            widget.grid_remove() if standing else widget.grid()
        no_points = limited or self._has_no_points()
        media = self._type_key() == "media"
        # 常駐關卡不能改名（storage 讀檔時也會改回「常駐關卡」）
        self.name_entry.config(state="readonly" if standing else "normal")
        # 關卡表：沒有積分的活動與常駐關卡不顯示基礎積分、積分、CP 三欄
        tree = self.editor.tree
        tree["displaycolumns"] = (
            [c for c in tree["columns"] if c not in ("base_points", "points", "cp")]
            if self._levels_have_no_points() else "#all")
        if not standing:
            for widget in self._activity_only:
                hide = (limited or (no_points and widget in self._points_only)
                        or (media and widget in self._base_row))
                widget.grid_remove() if hide else widget.grid()
        if no_points:
            self._base_points_part.pack_forget()
        elif not self._base_points_part.winfo_manager():
            self._base_points_part.pack(side="left", padx=(0, dp(10)),
                                        before=self._base_clears_label)
        for widget in self._limited_only:
            widget.grid() if limited and not standing else widget.grid_remove()
        self._actions_label.config(text="這一期：" if limited else "這一檔：")
        if limited:
            self._period_box.pack(side="left")
        else:
            self._period_box.pack_forget()
        if not standing and self._type_key() in ("current", "rerun"):
            self._level_tools.pack(anchor="w", pady=(dp(6), 0))
        else:
            self._level_tools.pack_forget()
        # 多出來的高度給最下面那張表格：一般活動是活動任務，
        # 限期／常駐關卡沒有活動任務，就給關卡表
        tasks_shown = not standing and not limited
        self._body.rowconfigure(14, weight=0 if tasks_shown else 1)
        self._body.rowconfigure(17, weight=1 if tasks_shown else 0)
        self.name_hint.config(
            text=("常駐關卡不隸屬任何活動，永遠打得到；沒有起訖日、加成與活動任務"
                  if standing else
                  "限期關卡（檢定、忘卻…）：名稱是系列、期數分辨第幾期，顯示時接在一起"
                  "（忘卻＋23＝忘卻23）。每期有總次數上限、不影響排程範圍。"
                  "換期請按「接下一期」，期數自動加 1"
                  if limited else "紀錄依活動分區；改名稱不影響紀錄"))
        self.editor.refresh()

    # -- 活動切換 ---------------------------------------------------------
    def _default_task(self, records):
        return {"id": storage.next_task_id(records, "t"),
                "name": "活動任務", "cycle": "event", "metric": "points",
                "amount": 0, "deadline_offset": -1, "enforce": True,
                "assume_done": False, "scope": [], "reward_weekday": 6,
                "reward_days": list(DEFAULT_MONTH_DAYS)}

    def _current_event(self):
        return storage.find_event(self.app.shared, self._current_id)

    def analyze_targets(self):
        """這檔活動的任務目標分析：最少體力、積分範圍、誰是瓶頸。"""
        if not self.collect():
            return
        event = self._current_event()
        if event is None or storage.is_standing(event):
            messagebox.showinfo("目標分析", "常駐關卡沒有活動任務可以分析。")
            return
        try:
            result = scheduler.analyze_event_targets(
                self.app.shared, self.app.profile, event["id"])
        except scheduler.PlanError as exc:
            messagebox.showerror("目標分析", str(exc))
            return
        TargetAnalysisDialog(self, scheduler.format_event_analysis(result))

    def _on_event_selected(self, _event=None):
        if self._switching:
            return
        index = self.event_box.current()
        # 照選單「畫出來那一刻」的順序對回去——現算的話，中間剛好有活動
        # 跨過結束時刻，順序一變就會選錯
        if index < 0 or index >= len(self._box_ids):
            return
        new_id = self._box_ids[index]
        if new_id == self._current_id:
            return
        if not self.collect():
            self._refresh_event_box()
            return
        self._current_id = new_id
        self._load_event()

    def _refresh_event_box(self):
        # 跟「目前狀態」一樣照剩餘時間排，快結束的在最上面
        events = events_by_remaining(storage.visible_events(self.app.shared))
        self._box_ids = [ev["id"] for ev in events]
        self._switching = True
        self.event_box["values"] = [self._event_choice_label(ev) for ev in events]
        for index, ev in enumerate(events):
            if ev["id"] == self._current_id:
                self.event_box.current(index)
                break
        self._switching = False

    @staticmethod
    def _event_choice_label(event) -> str:
        return storage.event_choice_label(event)

    def _insert_event(self, event):
        """新活動插在常駐關卡前面（常駐固定排最後）。"""
        events = self.app.shared.setdefault("events", [])
        standing_at = next((i for i, ev in enumerate(events)
                            if storage.is_standing(ev)), len(events))
        events.insert(standing_at, event)

    def add_limited_event(self):
        if not self.app.collect_all():
            return
        events = self.app.shared.setdefault("events", [])
        event = storage.default_event(
            storage.next_event_id(events),
            next_limited_name(events), "limited")
        # 新的系列從第 1 期開始；名稱與期數之後都能改
        event["period_no"] = 1
        event["activity_bonus_applies"] = False
        event["levels"] = [{
            "id": "lv1", "name": "關卡1", "stamina_cost": 10, "enemies": 0,
            "drops": 0, "scoring": False, "counts_clears": False, "base_points": None,
            "available_from": None, "max_total": None, "must_finish": False,
            "same_day": False, "unlock_first": False}]
        self._insert_event(event)
        self._current_id = event["id"]
        self.app.on_events_changed()
        self._load_event()
        self.app.set_status(f"已新增「{scheduler.event_label(event)}」，記得填起訖日與每期上限")

    def next_period(self):
        """限期關卡換檔：關卡結構照抄，起始日接在上一檔的結束日。"""
        if not self.app.collect_all():
            return
        source = self._current_event()
        if source is None or not storage.is_limited(source):
            messagebox.showinfo("無法接下一期",
                                "「接下一期」只用在限期關卡（檢定、忘卻…）。\n"
                                "一般活動請用「複製這檔」。", parent=self)
            return
        if not source.get("end_date"):
            messagebox.showinfo("無法接下一期",
                                "這一期還沒填結束日，不知道下一期從哪天開始。",
                                parent=self)
            return
        clone = storage.next_period_event(self.app.shared, source)
        self._insert_event(clone)
        # 各帳號的「計算」開關沿用；上限每檔都可能不同，清空重填
        data = copy.deepcopy(storage.profile_event(self.app.profile, source["id"]))
        data["level_max_total"] = {}
        self.app.profile.setdefault("events", {})[clone["id"]] = data
        self._current_id = clone["id"]
        self.app.on_events_changed()
        self._load_event()
        self.app.set_status(
            f"已接上「{scheduler.event_label(clone)}」的下一期（{clone['start_date']} 起），"
            "請填結束日與這一期的上限")

    def add_event(self):
        """先問名稱、類型、起訖日，建好之後照類型套用預設（同「套用類型預設」）。"""
        if not self.app.collect_all():
            return
        events = self.app.shared.setdefault("events", [])


        def check(record):
            end = record.get("end_date")
            if end and end < record["start_date"]:
                return "結束日不能早於起始日。"
            return None

        dialog = RecordDialog(
            self.winfo_toplevel(), "新增活動", [
                {"key": "name", "label": "活動名稱", "type": "str",
                 "hint": "只是顯示用，之後可以改"},
                # 限期關卡另有「新增限期系列」，這裡不列
                {"key": "type", "label": "活動類型", "type": "choice",
                 "choices": DEFAULT_RULE_TYPE_CHOICES,
                 "hint": "建好之後會照這個類型帶入預設的關卡、任務與積分表"},
                {"key": "start_date", "label": "活動起始", "type": "date"},
                {"key": "end_date", "label": "活動結束", "type": "date",
                 "optional": True},
            ],
            {"name": f"活動{len(storage.real_events(self.app.shared)) + 1}",
             "type": "current", "start_date": "", "end_date": ""},
            validate=check, ok_text="建立並套用預設")
        result = dialog.result
        if result is None:
            return
        event_type = result["type"]
        name = (result.get("name") or "").strip()
        template = storage.type_default(self.app.shared, event_type)
        if template is not None:
            # 當期、復刻：關卡與任務整套照「設定 → 活動類型預設」的表建
            event = storage.event_from_template(storage.next_event_id(events), name,
                                                event_type, template)
        else:
            event = storage.default_event(storage.next_event_id(events), name, event_type)
            # 音像通常沒有自己的關卡，蜜意蒐羅、祕寶探尋的關卡整套由預設產生；
            # 任務交給「套用類型預設」補（才會講出加了什麼）
            event["tasks"] = []
            event["levels"] = []
        event["start_date"] = result["start_date"]
        event["end_date"] = result.get("end_date") or None
        self._insert_event(event)
        self._current_id = event["id"]
        # 新關卡的積分照本帳號的加成先算好（有基礎積分的）
        storage.sync_levels(self.app.profile, self.app.shared)
        self.app.on_events_changed()
        self._load_event()
        if template is None:
            self.apply_type_defaults(fresh=True)
        else:
            self._show_template_result(event, template)
        # 蜜意蒐羅、祕寶探尋沒填結束日的話，預設會帶起始日 7 天後，看表單上的值
        missing = "" if self.end_var.get().strip() else "，記得補上結束日"
        self.app.set_status(
            f"已新增「{scheduler.event_label(event)}」並套用類型預設{missing}")

    def _show_template_result(self, event, template):
        """照類型預設表建好新活動後，講一下帶了什麼。"""
        label = storage.EVENT_TYPE_LABELS.get(event["type"], event["type"])
        lines = [f"已照「{label}」的類型預設建好這檔活動：",
                 f"　關卡 {len(event['levels'])} 關：" + "、".join(
                     lv.get("name", "") for lv in event["levels"]),
                 f"　活動任務 {len(event['tasks'])} 條",
                 "　「這檔活動套用活動加成」" + ("勾選" if template["bonus_applies"]
                                               else "不勾選")]
        if template.get("points_cap") is not None:
            lines.append(f"　積分上限 {template['points_cap']}")
        opened = [lv for lv in event["levels"] if lv.get("available_from") is not None]
        for level in opened:
            when = self._open_date_text(level)
            lines.append(f"　「{level.get('name')}」開放起日 {when}" if when else
                         f"　「{level.get('name')}」的開放起日要等填了起始日才算得出來")
        lines += ["", "預設的內容在「設定 → 活動類型預設」改；這檔不同就直接在下面改。"]
        messagebox.showinfo("新增活動", "\n".join(lines), parent=self)

    def duplicate_event(self):
        if not self.app.collect_all():
            return
        source = self._current_event()
        if source is None:
            return
        if storage.is_standing(source):
            messagebox.showinfo("無法複製",
                                "「常駐關卡」只會有一組，不能複製。", parent=self)
            return
        if storage.is_limited(source):
            messagebox.showinfo("無法複製",
                                "限期關卡換期請用「接下一期」。", parent=self)
            return
        events = self.app.shared["events"]
        clone = copy.deepcopy(source)
        clone["id"] = storage.next_event_id(events)
        clone["name"] = (source.get("name") or "活動") + "（複製）"
        events.append(clone)
        # 積分與開關是各帳號的資料，一起複製一份，不然新活動的關卡全是空的
        data = copy.deepcopy(storage.profile_event(self.app.profile, source["id"]))
        self.app.profile.setdefault("events", {})[clone["id"]] = data
        self._current_id = clone["id"]
        self.app.on_events_changed()
        self._load_event()
        self.app.set_status(f"已複製成「{scheduler.event_label(clone)}」")

    def _first_visible_id(self):
        events = (storage.real_events(self.app.shared)
                  or storage.visible_events(self.app.shared))
        return events[0]["id"] if events else None

    def archive_event(self):
        """把已結束的活動收起來：各分頁不再列它，但紀錄照樣認得它的關卡。"""
        if not self.app.collect_all():
            return
        event = self._current_event()
        if event is None:
            return
        name = scheduler.event_label(event)
        if storage.is_standing(event):
            messagebox.showinfo("無法封存", "「常駐關卡」不是活動，不能封存。",
                                parent=self)
            return
        if not storage.period_ended(event):
            messagebox.showinfo(
                "無法封存",
                f"「{name}」還沒結束。\n封存是給已經結束的活動用的——"
                "還在進行的活動封存之後排程就不排它了。",
                parent=self)
            return
        if (not storage.is_limited(event)
                and len(storage.real_events(self.app.shared)) <= 1):
            messagebox.showinfo("無法封存", "至少要保留一檔活動。", parent=self)
            return
        event["archived"] = True
        self._current_id = self._first_visible_id()
        self.app.on_events_changed()
        self._load_event()
        self.app.set_status(
            f"已封存「{storage.event_choice_label(event)}」"
            "（要還原或刪除，按「已封存」）")

    def _fill_archived_menu(self):
        menu = self.archived_menu
        menu.delete(0, "end")
        events = storage.archived_events(self.app.shared)
        if not events:
            menu.add_command(label="（沒有封存的活動）", state="disabled")
            return
        for event in events:
            sub = tk.Menu(menu, tearoff=False)
            sub.add_command(label="還原",
                            command=lambda ev=event: self.restore_event(ev))
            sub.add_command(label="永久刪除…",
                            command=lambda ev=event: self.delete_event(ev))
            menu.add_cascade(label=self._archived_label(event), menu=sub)

    @staticmethod
    def _archived_label(event) -> str:
        """已封存清單一律帶期間——同名的活動（兩檔忘卻、每年的復刻）才分得出來。"""
        period = "～".join((event.get(k) or "?")[5:].replace("-", "/")
                          for k in ("start_date", "end_date"))
        return f"{scheduler.event_label(event)}（{period}）"

    def restore_event(self, event):
        if not self.app.collect_all():
            return
        event.pop("archived", None)
        self._current_id = event["id"]
        self.app.on_events_changed()
        self._load_event()
        self.app.set_status(f"已還原「{scheduler.event_label(event)}」")

    def delete_event(self, event=None):
        """刪除目前這檔；`event` 有給就是從「已封存」選單刪那一檔。"""
        events = storage.events_of(self.app.shared)
        from_archive = event is not None
        if event is None:
            event = self._current_event()
        if event is None:
            return
        if storage.is_standing(event):
            messagebox.showinfo(
                "無法刪除",
                "「常駐關卡」不是活動，不能刪除。\n"
                "不想排某一關的話，到關卡結構把它的「計算」取消勾選。",
                parent=self)
            return
        limited = storage.is_limited(event)
        if (not from_archive and not limited
                and len(storage.real_events(self.app.shared)) <= 1):
            messagebox.showinfo("無法刪除", "至少要保留一檔活動。", parent=self)
            return
        # 紀錄是拿關卡去對照的（storage.log_totals、排程的 measure）：關卡不在了，
        # 那幾天的打法與耗體就顯示不出來，本週／本月任務的進度也會少算。
        unit = "期" if limited else "檔"
        extra = (f"\n\n⚠ 每日紀錄裡這一{unit}的打法、耗體、積分會顯示不出來，"
                 "打過的體力也不再算進累計耗體與本週／本月的任務進度。"
                 + ("" if from_archive else
                    "\n只是想讓畫面乾淨的話，已結束的活動用「封存這檔」就好。"))
        if not messagebox.askyesno(
                "確認",
                f"確定要刪除「{scheduler.event_label(event)}」嗎？\n\n"
                "它的關卡、任務與各帳號的積分設定都會一起移除。\n"
                "每日紀錄裡這檔活動的資料會留著，不會被刪掉。" + extra,
                parent=self):
            return
        # 刪完會整批重載所有分頁，先把還沒存的編輯收回來。刪的是目前這檔時
        # 不收這一頁——它正要被刪，欄位填到一半也不該擋住刪除。
        if not self.app.collect_all(skip=None if from_archive else self):
            return
        self.app.shared["events"] = [ev for ev in events if ev["id"] != event["id"]]
        self.app.profile.get("events", {}).pop(event["id"], None)
        if not from_archive:
            self._current_id = self._first_visible_id()
        self.app.on_events_changed()
        self._load_event()
        self.app.set_status(f"已刪除活動「{scheduler.event_label(event)}」")

    def apply_type_defaults(self, fresh=False):
        """依活動類型帶入基礎積分表與「吃不吃加成」。

        fresh：剛用「新增活動」建好的，關卡是空的或預設的五關，直接取代、不必問。
        """
        key = self._type_key()
        if key in storage.GROUPED_EVENT_PRESETS:
            self._apply_grouped_defaults(key, confirm=not fresh)
            return
        if key == "media":
            # 只補任務、關掉加成；不碰關卡積分（見 storage.EVENT_TYPE_TABLE）
            self.bonus_applies_var.set(storage.EVENT_TYPE_BONUS["media"])
            self._recompute_points()
            if not self._add_media_tasks():
                messagebox.showinfo("音像任務", "音像的預設任務都已經有了。",
                                    parent=self)
            return
        if key in ("current", "rerun"):
            self._apply_event_defaults(key)
            return
        # 走到這裡的類型（限期關卡）什麼預設都沒有：積分表、任務、關卡都不帶
        messagebox.showinfo("沒有預設", "這個類型沒有預設的資料。", parent=self)

    def _apply_event_defaults(self, key):
        """當期／復刻：把「設定 → 活動類型預設」那張表合併到這檔活動
        （storage.apply_event_type_defaults），再把做了什麼講出來。"""
        tasks = self.task_editor.get_records()
        report = storage.apply_event_type_defaults(
            key, self.editor.records, tasks,
            points_cap=self.points_cap_var.get().strip() or None,
            event_id=self._current_id, is_scoring=level_is_scoring,
            template=storage.type_default(self.app.shared, key))
        extra = []
        if report["cap"] is not None:
            self.points_cap_var.set(str(report["cap"]))
            extra.append(f"積分上限帶入 {report['cap']}，不對就直接改。")
        for level in report["added_levels"]:
            # 編輯用的記錄另外要這幾格；開放日在畫面上是日期
            level.update(kind=level_kind_of(level), enabled=True, points=None,
                         profile_max_total=None,
                         available_from_date=self._open_date_text(level))
        self.bonus_applies_var.set(report["applies"])
        self._recompute_points()       # 也會重畫關卡表
        if report["tasks"]:
            self.task_editor.set_records(
                tasks + [self._task_from_json(t, self._current_id) for t in report["tasks"]])
        label = storage.EVENT_TYPE_LABELS.get(key, key)
        self._show_base_table_result(f"{label}預設", report["applies"],
                                     *report["base"], extra)
        self._show_event_defaults_result(report)

    def _open_date_text(self, level) -> str:
        """關卡的開放日（相對起始日的天數）換成畫面上的日期；起始日沒填就留白。"""
        if level.get("available_from") is None:
            return ""
        try:
            start = date.fromisoformat(self.start_var.get().strip())
        except ValueError:
            return ""
        return scheduler.offset_from_start(level["available_from"], start).isoformat()

    def _show_event_defaults_result(self, report):
        """把「套用類型預設」補上的活動任務、解鎖鏈、敵人數與關卡講出來。"""
        lines = []
        if report["tasks"]:
            item_names = {it.get("id"): it.get("name") or it.get("id")
                          for it in self.app.shared.get("items") or []}

            def reward_text(task):
                parts = [f"{item_names.get(r['item'], r['item'])}×{r['qty']}"
                         for r in task.get("rewards") or []]
                return f"（獎勵 {'、'.join(parts)}）" if parts else ""

            lines.append("已在活動任務加上：")
            for t in report["tasks"]:
                goal = ("" if t["metric"] == "manual" else
                        f"：{storage.TASK_METRIC_LABELS.get(t['metric'], t['metric'])} "
                        f"{t['amount']}")
                lines.append(f"　{t['name']}{goal}{reward_text(t)}")
        if report["chained"]:
            lines += ([""] if lines else []) + [
                "已把計分關卡設成解鎖鏈（開場先打一次，照耗體由小到大解鎖）：",
                "　" + "、".join(report["chained"])]
        if report["enemies"]:
            lines += ([""] if lines else []) + [
                "已帶入每關敵人數：", "　" + "、".join(report["enemies"])]
        for level in report["added_levels"]:
            if lines:
                lines.append("")
            lines.append(f"已在關卡加上「{level.get('name')}」：" + level_summary(level))
            if level.get("available_from") is not None:
                when = level.get("available_from_date")
                lines.append(f"　開放起日 {when}" if when else
                             "　還沒填起始日，開放起日請自己補上")
        if lines:
            lines += ["", "內容來自「設定 → 活動類型預設」，這檔不同就直接改；不需要就刪掉。"]
            messagebox.showinfo("活動任務與關卡", "\n".join(lines), parent=self)

    def _add_media_tasks(self):
        """音像：補上每日耗體 150／300 的任務；最後一天不做（見 DEFAULT_MEDIA_TASKS）。

        回傳有沒有加任何任務。
        """
        records = self.task_editor.get_records()
        added = storage.default_media_tasks(records)
        shop = storage.default_media_shop_task(
            records + [t for t, _l in added])
        if not added and not shop:
            return False
        try:
            end = date.fromisoformat(self.end_var.get().strip())
        except ValueError:
            end = None
        new_records, lines = [], ["已在活動任務加上每日任務："]
        for task, last_day in added:
            record = self._task_from_json(task, self._current_id)
            line = f"　每天耗體 {task['amount']}"
            if not last_day:
                if end is not None:
                    # 期間只到倒數第 2 天；存檔時換算成相對起始日的天數
                    record["to_date"] = (end - timedelta(days=1)).isoformat()
                    line += f"（只算到 {end - timedelta(days=1):%m/%d}，最後一天不做）"
                else:
                    line += "（還沒填結束日：「只算這段期間（訖）」請自己填倒數第 2 天）"
            new_records.append(record)
            lines.append(line)
        if not added:
            lines = []
        item_names = {it.get("id"): it.get("name") or it.get("id")
                      for it in self.app.shared.get("items") or []}
        for task in shop:
            new_records.append(self._task_from_json(task, self._current_id))
            rewards = "、".join(f"{item_names.get(r['item'], r['item'])}×{r['qty']}"
                                for r in task["rewards"])
            claim_by = (f"，最晚 {end + timedelta(days=scheduler.REWARD_CLAIM_DAYS):%m/%d} 前領"
                        if end is not None else "")
            lines += ([""] if lines else []) + [
                "已在活動任務加上：",
                f"　{task['name']}：取得道具 {task['amount']}（獎勵 {rewards}）",
                f"　不算進排程計算；獎勵跟復刻一樣在活動結束後 "
                f"{scheduler.REWARD_CLAIM_DAYS} 天內領{claim_by}"]
        self.task_editor.set_records(records + new_records)
        if added:
            lines += ["", "之後改了結束日，記得一起改每日任務的期間。"]
        messagebox.showinfo("音像任務", "\n".join(lines), parent=self)
        return True

    def _apply_grouped_defaults(self, key, confirm=True):
        """分組解鎖型活動（蜜意蒐羅、祕寶探尋）：一次產生整套關卡。

        每一組是 20→30→40 三關，組內照耗體解鎖、每關至少打一次（開場先打一次
        ＋組別），沒有積分也不算進「關卡次數」類的活動任務（都不算），但每日任務
        的關卡次數照算——那本來就算所有關卡。
        """
        preset = storage.GROUPED_EVENT_PRESETS[key]
        type_label = storage.EVENT_TYPE_LABELS[key]
        count = preset["groups"] * len(preset["costs"])
        if confirm and self.editor.records and not messagebox.askyesno(
                "套用類型預設",
                f"要把目前的 {len(self.editor.records)} 關換成「{type_label}」的 "
                f"{preset['groups']} 組 × {len(preset['costs'])} 關（共 {count} 關）嗎？\n"
                "原本的關卡會被取代（每日紀錄不受影響）。",
                parent=self):
            return
        names = preset.get("group_names") or ()
        records = []
        for group in range(1, preset["groups"] + 1):
            label = names[group - 1] if group <= len(names) else f"第{group}組"
            for cost in preset["costs"]:
                records.append({
                    "id": f"g{group}_{cost}",
                    "name": f"{label}·{cost}",
                    "stamina_cost": cost, "enemies": preset["enemies"],
                    "drops": 0,
                    "kind": "none", "scoring": False, "counts_clears": False,
                    "enabled": True,
                    "available_from": None, "available_from_date": "",
                    "max_total": preset.get("max_total"), "must_finish": False,
                    "same_day": False, "unlock_first": True, "group": group,
                    "base_points": None, "points": None,
                    "profile_max_total": None,
                })
        self.editor.set_records(records)
        self.bonus_applies_var.set(False)

        cap = preset.get("max_total")
        cap_line = (f"　• 整檔活動最多打 {cap} 次（要多打的話把該關「總共最多幾次」清空）"
                    if cap else "　• 沒有總次數上限，打過之後可以無限重複")
        lines = [f"已產生「{type_label}」的關卡：{preset['groups']} 組 × "
                 + "／".join(str(c) for c in preset["costs"])
                 + f" 體，共 {count} 關，每關敵人 {preset['enemies']}。",
                 "",
                 "每一關都設成：",
                 "　• 類型「都不算」（沒有積分）",
                 "　• 開場先打一次＋組別——同一組照耗體由小到大解鎖，每關至少打一次",
                 cap_line,
                 "",
                 "「這檔活動套用活動加成」已取消勾選。"]
        start = self.start_var.get().strip()
        if start and not self.end_var.get().strip():
            try:
                end = date.fromisoformat(start) + timedelta(
                    days=storage.GROUPED_EVENT_DAYS)
            except ValueError:
                end = None
            if end is not None:
                self.end_var.set(end.isoformat())
                lines.append(f"結束日帶入 {end:%Y-%m-%d}（{storage.GROUPED_EVENT_DAYS} 天後），"
                             "不對的話直接改。")
        messagebox.showinfo("套用類型預設", "\n".join(lines), parent=self)

    def refresh_auto_rules(self, *args, **kwargs):
        """更新自動套用規則那行；沒有內容時整行收起來。

        空的 Label 照樣佔一行高，限期關卡那幾排收起來之後，
        「時間格式」與下面的勾選框中間就會空出一大塊。
        """
        self._refresh_auto_rules_text(*args, **kwargs)
        label = getattr(self, "auto_rule_label", None)
        if label is None:
            return
        if str(label.cget("text")).strip():
            label.pack(anchor="w", pady=(dp(2), 0))
        else:
            label.pack_forget()

    def _refresh_auto_rules_text(self):
        """「本帳號自動套用」那一行：排程設定的自動套用規則落在這一檔的哪幾天、有沒有被蓋過。

        判斷規則跟排程一致（scheduler.default_rule_applies／special_rule_key）。
        用畫面上的起訖日與類型，改了馬上看得到。
        """
        label = getattr(self, "auto_rule_label", None)
        event = self._current_event()
        if label is None or event is None or storage.is_standing(event):
            return
        kind_key = self._type_key()
        rules = [r for r in self.app.profile.get("event_default_rules") or []
                 if scheduler.default_rule_applies(r, kind_key)]
        if not rules or kind_key == "limited":
            label.config(text="")
            return

        def parse(text):
            try:
                return date.fromisoformat(text.strip())
            except ValueError:
                return None

        start, end = parse(self.start_var.get()), parse(self.end_var.get())
        # 明確的特殊日規則落在哪天：{規則鍵: 數值}
        explicit = {}
        for entry in self.app.profile.get("special_days") or []:
            ref_id = entry.get("event_id")
            if ref_id == event["id"]:
                ref_start, ref_end = start, end
            else:
                ref_start, ref_end = self._event_bounds(ref_id)
            if ref_start is None or ref_end is None:
                continue
            try:
                day = scheduler.resolve_day_offset(
                    int(entry.get("day_offset")), ref_start, ref_end)
            except (TypeError, ValueError):
                continue
            kind = entry.get("type")
            value = special_from_json(entry)["value"]
            explicit[scheduler.special_rule_key(day, kind, ref_id)] = value

        parts = []
        for rule in rules:
            record = special_from_json(rule)
            kind = record["type"]
            name = SPECIAL_TYPE_LABELS.get(kind, kind)
            offset = int(record["day_offset"])
            if start is None or end is None:
                when = (f"第 {offset + 1} 天" if offset >= 0 else f"倒數第 {-offset} 天")
                parts.append(f"{when} {name} {record['value']}")
                continue
            day = scheduler.resolve_day_offset(offset, start, end)
            text = f"{day:%m/%d} {name} {record['value']}"
            key = scheduler.special_rule_key(day, kind, event["id"])
            if key in explicit:
                text += ("（特殊日規則也有一條同樣的，可以刪掉）"
                         if explicit[key] == record["value"]
                         else f"（特殊日規則改成 {explicit[key]}）")
            parts.append(text)
        label.config(text="本帳號自動套用：" + "；".join(parts)
                          + "　（到「排程設定」修改）")

    def _type_key(self) -> str:
        reverse = {label: key for key, label in storage.EVENT_TYPES}
        return reverse.get(self.type_var.get(), "current")

    # -- 積分＝基礎積分 × (1 + 活動加成%) ---------------------------------
    def _bonus(self) -> float:
        try:
            return parse_percent(self.bonus_var.get(), "活動加成")
        except FieldError:
            return 0.0

    def _effective_bonus(self) -> float:
        """實際套用的加成。這檔活動不吃加成（復刻／音像等）時就是 0。

        注意是回 0、不是把輸入框清掉——使用者填的 70 要留著，
        下一檔一般活動才不必重查。
        """
        return self._bonus() if self.bonus_applies_var.get() else 0.0

    def _derive_points(self, values) -> str:
        if values.get("kind") != "scoring":
            return ""                     # 不計分的關卡沒有積分
        try:
            base = parse_opt_int(values.get("base_points"), "基礎積分", 0)
        except FieldError:
            return ""
        points = scheduler.points_with_bonus(base, self._effective_bonus())
        return "" if points is None else str(points)

    def _derive_base_points(self):
        """由目前的積分反推基礎積分。

        反推是唯一解或無解（見 scheduler.base_points_for）。算不出整數的維持空白，
        不亂猜——那種多半是手填的數字，猜錯會連帶把積分改掉。
        """
        bonus = self._effective_bonus()
        done, failed, cleared = [], [], []
        for record in self.editor.records:
            if not level_is_scoring(record):
                # 不計分的關卡不該有積分，誤填的順手清掉
                if record.get("base_points") is not None or record.get("points"):
                    cleared.append(record.get("name", ""))
                record["base_points"] = None
                record["points"] = None
                continue
            if not record.get("points"):
                continue
            base = scheduler.base_points_for(record["points"], bonus)
            if base is None:
                failed.append(record.get("name", ""))
            else:
                record["base_points"] = base
                done.append(record.get("name", ""))
        self._recompute_points()
        lines = [f"用加成 {trim_number(bonus)}％ 反推了 {len(done)} 關的基礎積分。"]
        if done:
            lines.append("　" + "、".join(done))
        if failed:
            lines.append("")
            lines.append("這幾關算不出整數的基礎積分，維持空白（積分照原樣手填）：")
            lines.append("　" + "、".join(failed))
        if cleared:
            lines.append("")
            lines.append("這幾關是「計分＝否」，積分已清掉（不計分的關卡沒有積分）：")
            lines.append("　" + "、".join(cleared))
        if not done and not failed:
            lines = ["沒有任何關卡填了積分，沒東西可以反推。"]
        messagebox.showinfo("反推基礎積分", "\n".join(lines), parent=self)

    def _apply_base_table(self, name, applies, table, extra_lines=()):
        """依消耗體力套用常見的基礎積分表。

        extra_lines：呼叫端順便帶入別的欄位（例如積分上限）時，接在加成那段後面一起講，
        不必再多跳一個視窗。
        """
        done, skipped, cleared = storage.apply_base_table(
            self.editor.records, table, level_is_scoring)
        self.bonus_applies_var.set(applies)
        self._recompute_points()
        self._show_base_table_result(name, applies, done, skipped, cleared, extra_lines)

    def _show_base_table_result(self, name, applies, done, skipped, cleared,
                                extra_lines=()):
        lines = [f"已套用「{name}」的基礎積分表，填了 {len(done)} 關。"]
        if done:
            lines.append("　" + "、".join(done))
        lines.append("")
        lines.append("「這檔活動套用活動加成」已" + ("勾選" if applies else "取消勾選")
                     + f"（{name}" + ("要吃加成）" if applies else "的積分是固定的）"))
        lines += list(extra_lines)
        if skipped:
            lines.append("")
            lines.append("這幾關的消耗體力不在表裡，基礎積分已清空（積分改回手填）：")
            lines.append("　" + "、".join(skipped))
        if cleared:
            lines.append("")
            lines.append("這幾關是「計分＝否」，跳過並清掉積分：")
            lines.append("　" + "、".join(cleared))
        messagebox.showinfo("套用常見表", "\n".join(lines), parent=self)

    def _recompute_points(self):
        """加成一改，所有「有填基礎積分」的關卡都重算積分。

        使用者手動改過的值也會被蓋掉——這是刻意的：加成變了，舊的手改值一定過時。
        沒填基礎積分的關卡完全不碰，那些是純手填的。
        """
        bonus = self._effective_bonus()
        for record in self.editor.records:
            if not level_is_scoring(record):
                continue
            points = scheduler.points_with_bonus(record.get("base_points"), bonus)
            if points is not None:
                record["points"] = points
        self.editor.refresh()

    def _window_text(self, record) -> str:
        """「開放」欄：什麼時候開放、總共能打幾次。"""
        parts = []
        offset = record.get("available_from")
        # 對話框改的是「開放起日」那格日期，偏移量要等存檔（collect）才換算；
        # 有日期欄就照它顯示，按確定關掉編輯視窗表格就跟著變
        if "available_from_date" in record:
            date_text = (record.get("available_from_date") or "").strip()
            if not date_text:
                offset = None
        else:
            date_text = (None if offset is None
                         else self._offset_to_date(offset, self._current_id))
        if offset is None and not date_text:
            parts.append("全期")
        else:
            parts.append(f"{date_text[5:].replace('-', '/')} 起" if date_text
                         else f"第 {int(offset) + 1} 天起")
        cap = record.get("max_total")
        if record.get("profile_max_total") is not None and self._is_limited():
            cap = record["profile_max_total"]
        if cap is not None and (cap or record.get("profile_max_total") == 0):
            parts.append(("必打" if record.get("must_finish") else "共")
                         + f" {cap} 次")
            if record.get("same_day") and cap > 1:
                parts.append("同日")
        if record.get("group") is not None:
            parts.append(f"第{record['group']}組")
        if record.get("unlock_first"):
            parts.append("先解鎖")
        return "・".join(parts)

    def _level_delete_warning(self, record) -> str | None:
        """要刪的這一關，有哪個帳號的每日紀錄打過——有的話講出後果。

        紀錄是拿「活動/關卡」代號去對照關卡的：關卡刪掉，紀錄還在但對不到，
        那幾天就顯示成「（沒打）」，也不再算進任何累計值。所有帳號共用關卡，
        所以每個帳號的紀錄都要看。
        """
        if not self._current_id or not record.get("id"):
            return None
        key = storage.level_key(self._current_id, record["id"])
        played = []
        for pid, name in storage.list_profiles():
            try:
                entries = storage.load_log(pid).get("entries") or []
            except Exception:       # 紀錄讀不到就當沒打過，不擋刪除
                continue
            total = 0
            for entry in entries:
                try:
                    total += max(0, int((entry.get("counts") or {}).get(key) or 0))
                except (TypeError, ValueError):
                    continue
            if total:
                played.append(f"{name or pid} {total} 次")
        if not played:
            return None
        return ("⚠ 每日紀錄裡打過這一關：" + "、".join(played) + "。\n\n"
                "刪掉之後，那幾天的打法、耗體、積分會顯示不出來，"
                "也不再算進累計耗體與任務進度。\n\n"
                "只是不想排這一關的話，取消勾選「計算」就好。")

    def _level_row(self, record):
        cost = record.get("stamina_cost") or 0
        if not level_is_scoring(record):
            # 不計分的關卡本來就沒有積分可言。用破折號跟「計分但還沒填」
            # 那種「（未填）」區分開——不然會以為是自己漏填了。
            base_text, points_text, cp = "—", "—", "—"
        else:
            points = record.get("points")
            base_text = ("-" if record.get("base_points") is None
                         else record["base_points"])
            points_text = "（未填）" if points is None else points
            cp = f"{points / cost:.2f}" if points and cost else "-"
        return (
            record.get("name", ""), cost, record.get("enemies", 0),
            record.get("drops") or 0,
            LEVEL_KIND_LABELS.get(level_kind_of(record), ""),
            "是" if record.get("enabled", True) else "否",
            self._window_text(record), base_text, points_text, cp,
        )

    # -- 載入／儲存 -------------------------------------------------------
    def _collect_standing(self, event) -> bool:
        """常駐關卡只有名稱與關卡結構要收，日期／類型／加成／任務都不存在。"""
        try:
            records = self.editor.get_records()
        except (FieldError, ValueError) as exc:
            messagebox.showerror("輸入有誤", str(exc), parent=self)
            return False
        names = [r.get("name") for r in records]
        doubled = [n for n in storage.STANDING_LOCKED_LEVELS if names.count(n) > 1]
        if doubled:
            messagebox.showerror(
                "輸入有誤", f"常駐關卡裡有兩關都叫「{doubled[0]}」，請把新加的那關改個名字。",
                parent=self)
            return False
        # 名稱不收：常駐關卡不能改名（名稱欄是鎖住的）
        event["levels"] = [
            {"id": r["id"], "name": r["name"],
             "stamina_cost": r["stamina_cost"],
             "enemies": max(0, int(r.get("enemies") or 0)),
             "drops": max(0, int(r.get("drops") or 0)),
             # 常駐關卡一律沒有積分（storage 也會再擋一次）
             "scoring": False,
             "counts_clears": LEVEL_KIND_FLAGS[level_kind_of(r)][1],
             # 這幾個是活動概念，常駐一律留空（storage 也會再擋一次）
             "available_from": None, "max_total": None, "must_finish": False,
             "same_day": False, "unlock_first": False, "group": None,
             "base_points": None,
             "default_enabled": r.get("default_enabled") is not False}
            for r in records
        ]
        data = storage.profile_event(self.app.profile, event["id"])
        points = data.setdefault("level_points", {})
        enabled = data.setdefault("level_enabled", {})
        for r in records:
            points[r["id"]] = r.get("points")
            enabled[r["id"]] = bool(r.get("enabled", True))
        return True

    def load(self):
        # 還沒選過（或選的那檔被封存了）就預設選最快結束的那一檔
        events = events_by_remaining(storage.visible_events(self.app.shared))
        if self._current_id not in {ev["id"] for ev in events}:
            # 優先選真正的活動：第一次執行時「活動1」還沒填日期，照剩餘時間排會
            # 排在常駐關卡後面，但使用者第一件事就是幫它填起訖日
            real = [ev for ev in events
                    if not storage.is_standing(ev) and not storage.is_limited(ev)]
            pick = real or events
            self._current_id = pick[0]["id"] if pick else None
        self._load_event()

    def _load_event(self):
        self._refresh_event_box()
        event = self._current_event()
        if event is None:
            return
        data = storage.profile_event(self.app.profile, event["id"])
        self.name_var.set(event.get("name") or "")
        self.period_var.set("" if event.get("period_no") is None
                            else str(event["period_no"]))
        self.type_var.set(storage.EVENT_TYPE_LABELS.get(
            event.get("type"), storage.EVENT_TYPES[0][1]))
        self.start_var.set(event.get("start_date") or "")
        self.end_var.set(event.get("end_date") or "")
        self.start_time_var.set(event.get("start_time")
                                or storage.DEFAULT_EVENT_START_TIME)
        self.end_time_var.set(event.get("end_time")
                              or storage.DEFAULT_EVENT_END_TIME)
        # 先塞加成再塞關卡：trace 會觸發一次重算，但那時 records 還是空的，
        # 所以真正的重算是下面 set_records 之後那一次。
        self.bonus_var.set(trim_number(data.get("activity_bonus") or 0))
        self.bonus_applies_var.set(event.get("activity_bonus_applies") is not False)
        cap = event.get("points_cap")
        self.points_cap_var.set("" if cap is None else trim_number(cap))
        self.early_date_var.set(event.get("early_finish_date") or "")
        self.early_surplus_var.set(event.get("early_takes_surplus") is not False)
        self.skip_last_var.set(bool(event.get("skip_last_day")))
        # 還沒有紀錄區段的活動，起始值就是第一次記錄時會快照的目前值
        section = (storage.load_log(self.app.profile_id).get("events")
                   or {}).get(event["id"])
        if section is None:
            base = {"points": int(data.get("current_points") or 0),
                    "clears": int(data.get("current_clears") or 0)}
        else:
            base = {kind: int(section.get(f"baseline_{kind}") or 0)
                    for kind in self.base_vars}
        for kind, value in base.items():
            self.base_vars[kind].set(str(value))
        self._base_loaded = (event["id"], base)

        points = data.get("level_points") or {}
        enabled = data.get("level_enabled") or {}
        caps = data.get("level_max_total") or {}
        self._apply_visibility()
        self.editor.set_records([
            {**level, "points": points.get(level["id"]),
             "enabled": enabled.get(level["id"], True),
             "profile_max_total": caps.get(level["id"]),
             "kind": level_kind_of(level),
             "available_from_date": self._offset_to_date(
                 level.get("available_from"), event["id"])}
            for level in event.get("levels") or []
        ])
        self._recompute_points()
        self.task_editor.set_specs(self._task_specs)
        self.task_editor.set_records([
            self._task_from_json(task, event["id"])
            for task in event.get("tasks") or []])

    def collect(self) -> bool:
        event = self._current_event()
        if event is None:
            return True
        if storage.is_standing(event):
            return self._collect_standing(event)
        try:
            bonus = parse_percent(self.bonus_var.get(), "活動加成")
            points_cap = parse_opt_int(self.points_cap_var.get(), "積分上限", 0)
            early_date = self.early_date_var.get().strip() or None
            if early_date:
                try:
                    datetime.strptime(early_date, "%Y-%m-%d")
                except ValueError:
                    raise FieldError(
                        f"「盡量提早」的日期格式需為 YYYY-MM-DD：{early_date}")
            # 活動名稱可以留空——紀錄是依 event_id 分的，名稱只是顯示用。
            # 一開新程式就逼使用者先命名才存得了檔太煩。
            name = self.name_var.get().strip()
            # 限期關卡的期數一定要填：系列靠它分辨是哪一期（下拉、報表都只顯示「忘卻23」）
            period_no = (parse_int(self.period_var.get(), "期數", 1)
                         if self._is_limited() else None)
            # 起始積分允許負數：紀錄算出來比遊戲裡多、又找不到是哪筆記錯時，
            # 填負的起始值把差額扣回來。
            base = {"points": parse_int(self.base_vars["points"].get() or "0", "起始積分"),
                    "clears": parse_int(self.base_vars["clears"].get() or "0",
                                        "起始關卡數", 0)}
            for var, label in ((self.start_time_var, "活動起始時間"),
                               (self.end_time_var, "活動結束時間")):
                try:
                    datetime.strptime(var.get().strip(), "%H:%M")
                except ValueError:
                    raise FieldError(
                        f"「{label}」格式需為 HH:MM（例如 15:00）：{var.get()}")
            # 對話框用日期輸入開放起日，存檔換算成相對活動起始日的偏移量。
            # 日期先寫回活動再換算，不然改了起始日的那一次會用到舊的基準。
            #
            # 但只有使用者**親手改過**的日期才用新基準。沒動過的那幾格，畫面上
            # 還是「舊起始日＋原偏移量」，拿去跟新起始日相減就縮水了——套完預設
            # 再把活動往後挪 7 天，「只算這段期間」的 13 天會變成 6 天，後半段
            # 的每日任務整個不見。那幾格沿用原偏移量，等於跟著活動一起平移。
            try:
                old_start = datetime.strptime(
                    event.get("start_date") or "", "%Y-%m-%d").date()
            except ValueError:
                old_start = None
            old_levels = {lv.get("id"): lv for lv in event.get("levels") or []}
            old_tasks = {t.get("id"): t for t in event.get("tasks") or []}

            def offset_of(text, old_offset):
                if not text:
                    return None
                if (old_start is not None and old_offset is not None
                        and text == scheduler.offset_from_start(
                            int(old_offset), old_start).isoformat()):
                    return int(old_offset)
                return self._date_to_offset(text, event["id"])

            event["start_date"] = self.start_var.get().strip() or None
            event["end_date"] = self.end_var.get().strip() or None
            for record in self.editor.records:
                text = (record.get("available_from_date") or "").strip()
                record["available_from"] = offset_of(
                    text, old_levels.get(record.get("id"), {}).get("available_from"))
            # 關卡可以是空的——音像這種活動不一定有自己的關卡，
            # 它的任務可能純粹是「累計消耗體力 150／300」，靠打別檔活動的關卡
            # 就會累積（耗體類任務的預設範圍是所有關卡）。
            # 真的一關都沒有時由 compute_plan 擋，那邊才看得到全部活動。
            records = self.editor.get_records()
            tasks = []
            for r in self.task_editor.get_records():
                task = self._task_to_json(r, event["id"])
                old = old_tasks.get(task.get("id"), {})
                for key, target in (("from_date", "from_offset"),
                                    ("to_date", "to_offset")):
                    task[target] = offset_of((r.get(key) or "").strip(),
                                             old.get(target))
                tasks.append(task)
        except (FieldError, ValueError) as exc:
            messagebox.showerror("輸入有誤", str(exc), parent=self)
            return False

        # 積分上限低於積分任務的目標＝兩邊互相矛盾，那個任務永遠達不到。
        # 不擋死（可能只是還沒改完另一邊），但一定要問一聲。
        if points_cap is not None:
            over = [t for t in tasks
                    if t.get("metric") == "points" and t["amount"] > points_cap]
            if over and not messagebox.askokcancel(
                    "積分上限低於任務目標",
                    "\n".join(
                        [f"「積分上限」填了 {points_cap}，但這些任務的目標比它高："]
                        + [f"　{t['name']}　目標 {t['amount']}" for t in over]
                        + ["", "這樣那些任務永遠達不到。還是要存嗎？"]),
                    parent=self):
                return False

        event["name"] = name
        event["type"] = self._type_key()
        event["start_time"] = self.start_time_var.get().strip()
        event["end_time"] = self.end_time_var.get().strip()
        event["activity_bonus_applies"] = bool(self.bonus_applies_var.get())
        event["points_cap"] = points_cap
        event["early_finish_date"] = early_date
        event["early_takes_surplus"] = bool(self.early_surplus_var.get())
        if storage.is_limited(event):
            event["skip_last_day"] = bool(self.skip_last_var.get())
            event["period_no"] = period_no
        else:
            event.pop("skip_last_day", None)
            event["period_no"] = None
        event["levels"] = [
            {"id": r["id"], "name": r["name"],
             "stamina_cost": r["stamina_cost"],
             "enemies": max(0, int(r.get("enemies") or 0)),
             "drops": max(0, int(r.get("drops") or 0)),
             "scoring": LEVEL_KIND_FLAGS[level_kind_of(r)][0],
             "counts_clears": LEVEL_KIND_FLAGS[level_kind_of(r)][1],
             "available_from": r.get("available_from"),
             "max_total": r.get("max_total"),
             "must_finish": bool(r.get("must_finish")),
             "same_day": bool(r.get("same_day")),
             "unlock_first": bool(r.get("unlock_first")),
             "group": r.get("group"),
             # 沒有積分的活動類型那一欄不顯示，存空的
             "base_points": (None if self._type_key() in storage.NO_POINTS_TYPES
                             else r.get("base_points")),
             # 難度分組只有限期關卡有，其他類型存空的
             "tiers": (r.get("tiers") or []) if self._type_key() == "limited" else []}
            for r in records
        ]
        event["tasks"] = tasks
        if (self._type_key() != "limited"
                and self._base_loaded != (event["id"], base)):
            self.app.set_log_baselines(events={event["id"]: base})
            self._base_loaded = (event["id"], base)
        data = storage.profile_event(self.app.profile, event["id"])
        data["activity_bonus"] = bonus
        points = data.setdefault("level_points", {})
        enabled = data.setdefault("level_enabled", {})
        caps = data.setdefault("level_max_total", {})
        for r in records:
            points[r["id"]] = r.get("points")
            enabled[r["id"]] = bool(r.get("enabled", True))
            if event["type"] == "limited":
                caps[r["id"]] = r.get("profile_max_total")
        if event["type"] == "limited":
            # 限期關卡沒有加成、積分上限、任務（storage 讀檔時也會再清一次）
            event["activity_bonus_applies"] = False
            event["points_cap"] = None
            event["early_finish_date"] = None
            event["tasks"] = []
        elif event["type"] in storage.NO_POINTS_TYPES:
            # 沒有積分的活動：欄位收起來了，藏著的舊值也一併清掉（任務照留）
            event["activity_bonus_applies"] = False
            event["points_cap"] = None
            event["early_finish_date"] = None
        return True


class GlobalTab(EventDateMixin, ttk.Frame):
    """排程設定：體力來源、特殊日、指定關卡上限、活動優先序。

    作息（回復速率、重置時間、上線時段）在「設定」選單的重置與回復（ClocksDialog）。

    這些東西跨活動共用（體力池只有一個），所以不掛在任何一檔活動底下。
    """

    def __init__(self, master, app):
        super().__init__(master, padding=dp(16))
        self.app = app
        self.light_weekdays_var = tk.BooleanVar(value=True)
        self.simplify_days_var = tk.BooleanVar(value=True)
        self.expire_late_var = tk.BooleanVar(value=True)

        scroller = ScrollableFrame(self, fill_height=True)
        scroller.pack(fill="both", expand=True)
        # 長說明跟著視窗寬度折行（見 ScrollableFrame.wrap_long_labels）
        scroller.wrap_long_labels()
        body = scroller.inner

        ttk.Label(body, text="體力池是所有活動共用的，以下設定跨活動生效",
                  foreground="#b45309").grid(row=0, column=0, columnspan=3,
                                             sticky="w")

        ttk.Label(body, text="自然回復速率、重置時間與上線時段在「設定 → 重置與回復」",
                  foreground="#666666").grid(row=1, column=0, columnspan=3,
                                             sticky="w", pady=(dp(2), 0))

        # 排程的整理偏好（scheduler.LIGHT_WEEKDAYS）。跨滿三欄，才不會撐寬標籤欄。
        prefs = ttk.Frame(body)
        prefs.grid(row=3, column=0, columnspan=3, sticky="w", pady=(dp(10), 0))
        ttk.Checkbutton(
            prefs, variable=self.light_weekdays_var,
            text="週一到週六盡量只打每日任務要求的關數，多的集中到星期日"
        ).pack(anchor="w")
        ttk.Checkbutton(
            prefs, variable=self.simplify_days_var,
            text="每天打的關卡種類盡量少"
        ).pack(anchor="w")
        ttk.Checkbutton(
            prefs, variable=self.expire_late_var,
            text="多的限時體力留在晚到期的（先用快過期的，臨時有新關卡時手上還有）"
        ).pack(anchor="w")
        ttk.Label(prefs, text="三個都只在「一樣省」的排法裡挑，不會多花、多買或多浪費體力；"
                              "「盡量提早」的日期優先。各會讓計算多跑一個階段",
                  foreground="#666666", justify="left"
                  ).pack(anchor="w", pady=(dp(2), 0))

        self._row = 4

        row = self._section(
            body, "體力來源　（月卡、積分兌換……任務獎勵的體力不必填在這裡，"
                  "程式會自己從任務接過來）")
        self.source_editor = ListEditor(
            body,
            columns=[("preset", "來源", 90, "w"),
                     ("note", "說明", 120, "w"),
                     ("event", "依據活動", 110, "w"),
                     ("when", "期間", 180, "w"),
                     ("items", "100／30／10", 110, "center"),
                     ("each", "每次", 70, "e"),
                     ("total", "合計", 80, "e")],
            specs=self._source_specs,
            to_row=self._source_row,
            add_menu=[(label, (lambda k=key: self._default_source(k)))
                      for key, label, _kind, _defaults in STAMINA_SOURCE_PRESETS],
            total_of=item_total_text,
            height=8,
            extra_buttons=[("清除\n已失效", self._clear_stale_sources)],
            auto_width=True,       # 欄寬照內容調（見 fit_tree_columns）
        )
        self.source_editor.grid(row=row, column=0, columnspan=3, sticky="nsew")

        row = self._section(
            body, "特殊日規則　（日期用「從最後一天　第 1 天」這種相對寫法，"
                  "換一檔活動也不必重設）")
        self.special_editor = ListEditor(
            body,
            columns=[("event", "依據活動", 110, "w"),
                     ("offset", "第幾天", 90, "center"),
                     ("kind", "類型", 160, "w"),
                     ("value", "數值", 90, "e"),
                     ("note", "說明", 220, "w")],
            specs=self._special_specs,
            to_row=self._special_row,
            make_default=lambda _r: {"day_offset": -1, "event_id": self._first_event_id(),
                                     "type": "stamina_cap_override", "value": 100},
            height=6,
            auto_width=True,       # 欄寬照內容調（見 fit_tree_columns）
        )
        self.special_editor.grid(row=row, column=0, columnspan=3, sticky="nsew")

        row = self._section(
            body, "每檔活動自動套用的規則　（本帳號；每一檔符合類型的活動都會套用，"
                  "某一檔要不同的數字，就在上面特殊日規則加一條，會蓋過這裡）")
        self.default_rule_editor = ListEditor(
            body,
            columns=[("types", "套用類型", 110, "w"),
                     ("offset", "第幾天", 90, "center"),
                     ("kind", "類型", 160, "w"),
                     ("value", "數值", 90, "e"),
                     ("note", "說明", 220, "w")],
            specs=self._default_rule_specs,
            to_row=self._default_rule_row,
            make_default=lambda _r: {"day_offset": -1, "type": "ending_cap_override",
                                     "value": 100,
                                     # 不預設勾類型：讓使用者自己選要套到哪些活動
                                     "event_types": []},
            height=4,
            auto_width=True,       # 欄寬照內容調（見 fit_tree_columns）
        )
        self.default_rule_editor.grid(row=row, column=0, columnspan=3, sticky="nsew")

        row = self._section(
            body, "指定日期打指定次數　（那天那一關一定要打這麼多次，"
                  "當天其他關卡照常安排）")
        self.level_target_editor = ListEditor(
            body,
            columns=[("level", "關卡", 190, "w"),
                     ("date", "日期", 150, "w"),
                     ("count", "次數", 70, "e"),
                     ("mode", "方式", 70, "w")],
            specs=[],                       # 關卡清單會變，在 load() 時重建
            to_row=self._level_target_row,
            make_default=self._default_level_target,
            height=3,
            auto_width=True,       # 欄寬照內容調（見 fit_tree_columns）
        )
        self.level_target_editor.grid(row=row, column=0, columnspan=3, sticky="nsew")

        row = self._section(
            body, "活動優先序　（兩檔重疊時排上面的先打；體力真的不夠時，從最下面那檔開始放寬目標）")
        prio_box, prio_buttons = self._list_with_buttons(body, row)
        self.priority_box = tk.Listbox(prio_box, height=4, exportselection=False)
        self._attach_list(prio_box, self.priority_box)
        ttk.Button(prio_buttons, text="上移", width=8,
                   command=lambda: self._move_priority(-1)).pack(pady=dp(2))
        ttk.Button(prio_buttons, text="下移", width=8,
                   command=lambda: self._move_priority(1)).pack(pady=dp(2))

        row = self._section(
            body, "關卡優先序　（同樣省體力時、以及消化多餘體力時，先打排上面的；"
                  "不會因此多花或多買體力）")
        level_box, level_buttons = self._list_with_buttons(body, row)
        self.level_priority_box = tk.Listbox(level_box, height=5, exportselection=False)
        self._attach_list(level_box, self.level_priority_box)
        adder = ttk.Menubutton(level_buttons, text="加入", width=8)
        # 選單在打開的當下才建：關卡清單會隨活動設定變動，已經加入的也要排除
        self.level_priority_menu = tk.Menu(
            adder, tearoff=False, postcommand=self._fill_level_priority_menu)
        adder["menu"] = self.level_priority_menu
        adder.pack(pady=dp(2))
        ttk.Button(level_buttons, text="移除", width=8,
                   command=self._remove_level_priority).pack(pady=dp(2))
        ttk.Button(level_buttons, text="上移", width=8,
                   command=lambda: self._move_level_priority(-1)).pack(pady=dp(2))
        ttk.Button(level_buttons, text="下移", width=8,
                   command=lambda: self._move_level_priority(1)).pack(pady=dp(2))

        row = self._section(
            body, "指定關卡次數限制　（可限制只在星期幾打；"
                  "填了次數的，多餘體力會優先拿去打）")
        self.daily_level_editor = ListEditor(
            body,
            columns=[("level", "關卡", 190, "w"),
                     ("range", "日期區間", 200, "w"),
                     ("max_count", "限制", 90, "e")],
            specs=[],                       # 關卡清單會變，在 load() 時重建
            to_row=self._level_rule_row,
            make_default=self._default_daily_level,
            validate=self._check_daily_level_unique,
            height=3,
            auto_width=True,       # 欄寬照內容調（見 fit_tree_columns）
        )
        self.daily_level_editor.grid(row=row, column=0, columnspan=3, sticky="nsew")
        # 視窗拉高時多出來的高度給最下面這張表格
        body.rowconfigure(row, weight=1)

        # 各區塊右邊那排按鈕同寬、上下切齊
        self._button_columns = ButtonColumns()
        for frame in (self.source_editor.button_frame,
                      self.special_editor.button_frame,
                      self.default_rule_editor.button_frame,
                      self.level_target_editor.button_frame,
                      prio_buttons, level_buttons,
                      self.daily_level_editor.button_frame):
            self._button_columns.add(frame)

        body.columnconfigure(2, weight=1)

    @staticmethod
    def _list_with_buttons(body, row):
        """清單＋右側按鈕，排法跟 ListEditor 一樣（清單｜捲軸｜按鈕），
        跨滿三欄。這樣各區塊右邊那排按鈕才會在同一條直線上。"""
        box = ttk.Frame(body)
        box.grid(row=row, column=0, columnspan=3, sticky="nsew")
        box.columnconfigure(0, weight=1)
        box.rowconfigure(0, weight=1)
        buttons = ttk.Frame(box)
        buttons.grid(row=0, column=2, sticky="n", padx=(dp(8), 0))
        return box, buttons

    @staticmethod
    def _attach_list(box, listbox):
        listbox.grid(row=0, column=0, sticky="nsew")
        scroll = ttk.Scrollbar(box, orient="vertical", command=listbox.yview)
        listbox.configure(yscrollcommand=scroll.set)
        scroll.grid(row=0, column=1, sticky="ns")

    def _section(self, body, text):
        """分隔線＋標題，回傳這個區塊的清單該放的 grid row。

        區塊順序調整過好幾次，手動改 row 號碼每次都會漏掉一兩個，
        所以改用一個往下長的游標；之後要再調順序只要搬程式碼區塊。
        """
        ttk.Separator(body, orient="horizontal").grid(
            row=self._row, column=0, columnspan=3, sticky="we", pady=dp(12))
        ttk.Label(body, text=text).grid(
            row=self._row + 1, column=0, columnspan=3, sticky="w", pady=(0, dp(6)))
        self._row += 3
        return self._row - 1

    def _first_event_id(self):
        events = storage.real_events(self.app.shared)
        return events[0]["id"] if events else ""

    def _real_event_choices(self):
        """特殊日與活動優先序只看真正的活動。

        「第 N 天」是相對活動起訖日算的，而常駐關卡沒有起訖日，
        拿它當基準算出來的日期沒有意義。
        """
        return [(ev["id"], scheduler.event_label(ev))
                for ev in storage.real_events(self.app.shared)]

    def _event_name(self, event_id):
        """清單那一欄要顯示的活動名稱。

        用 `_event_choices()`（含常駐關卡）而不是 `_real_event_choices()`——
        舊檔裡指到常駐的規則才不會印出裸的 id。體力來源的「不依據活動」也要
        在這裡認得，不然那一欄會印出 `__none__`。
        """
        if event_id == NO_EVENT_ID:
            return NO_EVENT_SHORT
        return dict(self._event_choices()).get(event_id, event_id or "")

    # -- 活動優先序／關卡優先序 --------------------------------------------
    @staticmethod
    def _swap_in(box, ids: list, delta: int) -> list | None:
        """把 Listbox 選中的那一項往上／下挪一格。回傳新順序，挪不動回 None。"""
        selection = box.curselection()
        if not selection:
            return None
        index = selection[0]
        target = index + delta
        if not 0 <= target < len(ids):
            return None
        order = list(ids)
        order[index], order[target] = order[target], order[index]
        return order

    @staticmethod
    def _fill_numbered(box, labels) -> None:
        box.delete(0, "end")
        for position, label in enumerate(labels, start=1):
            box.insert("end", f"{position}. {label}")

    def _move_priority(self, delta):
        selection = self.priority_box.curselection()
        order = self._swap_in(self.priority_box, self._priority_ids, delta)
        if order is None:
            return
        self._priority_ids = order
        self._refresh_priority()
        self.priority_box.selection_set(selection[0] + delta)

    def _refresh_priority(self):
        self._fill_numbered(self.priority_box,
                            [self._event_name(eid) for eid in self._priority_ids])

    def _move_level_priority(self, delta):
        selection = self.level_priority_box.curselection()
        order = self._swap_in(self.level_priority_box, self._level_priority_ids, delta)
        if order is None:
            return
        self._level_priority_ids = order
        self._refresh_level_priority()
        self.level_priority_box.selection_set(selection[0] + delta)

    def _refresh_level_priority(self):
        shared = self.app.shared
        self._fill_numbered(self.level_priority_box,
                            [storage.priority_label(shared, key)
                             for key in self._level_priority_ids])

    def _fill_level_priority_menu(self):
        menu = self.level_priority_menu
        menu.delete(0, "end")
        # 限期關卡以系列列出（忘卻只列一次，自動跟著換檔），已結束的檔次不列
        choices = [(key, label)
                   for key, label in storage.priority_choices(self.app.shared)
                   if key not in self._level_priority_ids]
        if not choices:
            menu.add_command(label="（所有關卡都已加入）", state="disabled")
            return
        for key, label in choices:
            menu.add_command(label=label,
                             command=lambda k=key: self._add_level_priority(k))

    def _add_level_priority(self, key):
        self._level_priority_ids = self._level_priority_ids + [key]
        self._refresh_level_priority()
        self.level_priority_box.selection_clear(0, "end")
        self.level_priority_box.selection_set("end")

    def _remove_level_priority(self):
        selection = self.level_priority_box.curselection()
        if not selection:
            return
        order = list(self._level_priority_ids)
        del order[selection[0]]
        self._level_priority_ids = order
        self._refresh_level_priority()

    # -- 特殊日 -----------------------------------------------------------
    def _special_specs(self, _record):
        return [
            {"key": "event_id", "label": "依據哪一檔活動", "type": "choice",
             "choices": self._real_event_choices() or [("", "（尚未設定活動）")],
             "hint": "「第 N 天」是相對這檔活動的起訖日算的；"
                     "選「當日該活動體力上限」時，上限也是套在這一檔；"
                     "選「當日結束活動體力上限」時只用來決定是哪一天"},
            {"key": "day_offset", "label": "日期", "type": "day_ref"},
            {"key": "type", "label": "類型", "type": "choice", "choices": SPECIAL_TYPES},
            {"key": "value", "label": "數值", "type": "int", "minimum": 0},
        ]

    def _special_row(self, record):
        offset = record.get("day_offset", 0)
        label = f"第 {offset + 1} 天" if offset >= 0 else f"倒數第 {-offset} 天"
        kind = record.get("type")
        return (self._event_name(record.get("event_id")), label,
                SPECIAL_TYPE_LABELS.get(kind, kind), record.get("value", 0),
                SPECIAL_TYPE_NOTES.get(kind, ""))

    # -- 每檔活動自動套用的規則 --------------------------------------------
    def _default_rule_specs(self, _record):
        return [
            {"key": "event_types", "label": "套用到哪些類型的活動", "type": "multi_choice",
             "choices": DEFAULT_RULE_TYPE_CHOICES, "required": True,
             "hint": "可以複選（按住 Ctrl 點）。「第 N 天」照每一檔自己的起訖日算"},
            {"key": "day_offset", "label": "日期", "type": "day_ref"},
            {"key": "type", "label": "類型", "type": "choice", "choices": SPECIAL_TYPES},
            {"key": "value", "label": "數值", "type": "int", "minimum": 0},
        ]

    def _default_rule_row(self, record):
        offset = record.get("day_offset", 0)
        label = f"第 {offset + 1} 天" if offset >= 0 else f"倒數第 {-offset} 天"
        kind = record.get("type")
        return (default_rule_types_text(record), label,
                SPECIAL_TYPE_LABELS.get(kind, kind), record.get("value", 0),
                SPECIAL_TYPE_NOTES.get(kind, ""))

    # -- 指定關卡每日次數 --------------------------------------------------
    def _level_choices(self):
        # 限期關卡帶期數，兩期忘卻才分得出來
        return storage.level_choices(self.app.shared)

    def _level_rule_specs(self):
        choices = self._level_choices()
        key_of = {label: key for key, label in choices}

        def dates_for(position):
            # 換關卡時起訖跟著換成那一關的檔期。拿到的是畫面上的顯示文字，
            # 要先反查回關卡鍵。編輯既有規則時不會觸發（只有改了關卡才會）。
            return lambda values: self._level_rule_dates(
                key_of.get(values.get("level_id"), ""))[position]

        def specs(record):
            # 限期關卡（檢定、忘卻）有難度分組時才多一格「難度」；換關卡要重算
            tier_choices = self._tier_choices(record.get("level_id"),
                                              record.get("tier") or "")
            # 常駐的基本關卡（蜜意時光、經商貿易、探索調查）永遠打得到，起訖可以留白。
            # 提示一律有（只是字不同）：有跟沒有之間切換要整組重建，畫面會動
            permanent = self._is_permanent_level(record.get("level_id"))
            # 只寫在起始日那格，兩格寫一樣的字太囉嗦
            date_hint = {"hint": "起訖留白＝一直有效（常駐的基本關卡永遠打得到）"
                         if permanent else "有勾星期幾時，起訖可以留白＝整個排程期間"}
            fields = [
                {"key": "level_id", "label": "關卡", "type": "choice",
                 "choices": choices or [("", "（尚未設定關卡）")],
                 "rebuild": True},
            ]
            # 「難度」這格一律留著，沒有分組的關卡變灰不能選：換關卡時這格
            # 一下有一下沒有的話，要整組重建，畫面會跳
            fields.append(
                {"key": "tier", "label": "難度", "type": "choice",
                 "choices": tier_choices or [("", "（這一關沒有難度分組）")],
                 "disabled": not tier_choices, "rebuild": True,
                 "hint": ("選了某個難度＝只限制那幾關能在星期幾打，"
                          "其他關照常；要先勾下面的星期幾"
                          if tier_choices else
                          # 跟上面那句一樣排成兩行：行數不同的話高度差一點，
                          # 換關卡時下面的欄位還是會往上下挪
                          "這一關沒有難度分組。\n"
                          "限期關卡（檢定、忘卻）在活動設定填了分組才能選")})
            by_tier = bool(tier_choices) and bool(record.get("tier"))
            fields += [
                {"key": "weekdays", "label": "只在星期幾打", "type": "multi_choice",
                 # 七天一次列完，不用捲才看得到週日
                 "choices": WEEKDAY_CHOICES, "required": by_tier, "height": 7,
                 "hint": ("只有勾的這幾天能打到這個難度的關"
                          if by_tier else
                          "可以複選（按住 Ctrl 點）。留白＝每天都能打；"
                          "勾了的話，期間內其他日子不排這一關")},
                {"key": "from_date", "label": "起始日", "type": "date",
                 "optional": True, **date_hint,
                 "derive_from": ["level_id"], "derive": dates_for(0)},
                {"key": "to_date", "label": "結束日", "type": "date",
                 "optional": True,
                 "derive_from": ["level_id"], "derive": dates_for(1)},
            ]
            if not by_tier:
                # 代幣那兩格只有經商貿易、探索調查才顯示。其他關卡是收起來、不是拿掉：
                # 拿掉的話換關卡要整組重建，畫面會跳（見 RecordDialog._patch_in_place）
                token = self._is_token_level(record.get("level_id"))
                fields.append(
                    {"key": "max_count", "label": "每日最多幾次", "type": "opt_int",
                     "minimum": 1,
                     "hint": "不是「一定要打」。填了的話，多餘體力會優先拿去打這一關；"
                             "有勾星期幾時可以留白＝不限，由排程自己決定打不打。"
                             + ("下面填了代幣的話這格不用填" if token else "")})
                fields += [
                    {"key": "tokens_now", "label": "目前持有代幣", "type": "opt_int",
                     "minimum": 0, "hidden": not token,
                     "hint": "現在手上有幾個（今天記錄過的已經扣掉）。之後每天發的程式會依"
                             "紀錄自動加上，排程每天最多打手上那麼多次。"
                             "留白＝不用代幣算，照上面的每日次數"},
                    {"key": "token_max", "label": "代幣最多存幾個", "type": "opt_int",
                     "minimum": 1, "hint": "留白＝3", "hidden": not token},
                ]
            return fields

        return specs

    def _tier_choices(self, level_id, current="") -> list[tuple[str, str]]:
        """「難度」下拉的選項；那一關不是限期關卡或沒有分組 → []。

        值是關號的字串（"50,55,60"），存檔時直接轉成 stages，不存「第幾組」——
        之後分組改了，舊規則不會默默指到別組。對不到現有分組的舊值也留著。
        """
        event_id, own_id = storage.split_level_key(level_id or "")
        event = storage.find_event(self.app.shared, event_id) if event_id else None
        if event is None or not storage.is_limited(event):
            return []
        level = next((lv for lv in event.get("levels") or []
                      if lv.get("id") == own_id), None)
        tiers = (level or {}).get("tiers") or []
        if not tiers and not current:
            return []
        result = [("", "全部關卡")]
        result += [(",".join(map(str, group)), f"第 {format_stages(group)} 關")
                   for group in tiers]
        result.append(("other", "其他關（沒分到難度的）"))
        if current and current not in dict(result):
            result.append((current, "第 " + format_stages(
                int(x) for x in current.split(",")) + " 關（舊分組）"))
        return result

    def _level_rule_to_json(self, record) -> dict:
        """存檔前檢查：沒勾星期幾的話，起訖與次數都要填。

        選了難度的規則存 `stages`（或 `stages_other`），不存次數。關卡換成
        沒有難度分組的之後，對話框不顯示「難度」，記錄裡殘留的 tier 要丟掉。
        """
        weekdays = sorted({int(x) for x in record.get("weekdays") or []})
        start, end = record.get("from_date") or "", record.get("to_date") or ""
        tier = record.get("tier") or ""
        if tier and not self._tier_choices(record.get("level_id"), tier):
            tier = ""
        if tier:
            if not weekdays:
                raise FieldError("「指定關卡次數限制」選了難度的規則，要勾只在星期幾打")
            if start and end and start > end:
                raise FieldError(
                    f"「指定關卡次數限制」的起始日（{start}）晚於結束日（{end}）")
            out = {"level_id": record["level_id"], "from_date": start,
                   "to_date": end, "max_count": None, "weekdays": weekdays}
            if tier == "other":
                out["stages_other"] = True
            else:
                out["stages"] = [int(x) for x in tier.split(",")]
            return out
        count = record.get("max_count")
        # 代幣那兩格只有代幣關卡看得到；換過關卡的話殘留的數字不算
        held = (record.get("tokens_now")
                if self._is_token_level(record.get("level_id")) else None)
        if not weekdays:
            if (not start or not end) and not self._is_permanent_level(record["level_id"]):
                raise FieldError(
                    "「指定關卡次數限制」沒勾星期幾的規則，起始日和結束日都要填"
                    "（常駐關卡的蜜意時光、經商貿易、探索調查可以留白）")
            if count is None and held is None:
                raise FieldError("「指定關卡次數限制」沒勾星期幾的規則，每日最多幾次要填")
        if start and end and start > end:
            raise FieldError(
                f"「指定關卡次數限制」的起始日（{start}）晚於結束日（{end}）")
        out = {"level_id": record["level_id"], "from_date": start,
               "to_date": end, "max_count": count}
        if weekdays:
            out["weekdays"] = weekdays
        if held is not None:
            # 存成「今天開始時有幾個」，之後每天幾個由紀錄推算（scheduler.token_stock）
            out["max_count"] = None
            cap = record.get("token_max") or scheduler.TOKEN_DEFAULT_MAX
            saved = record.get("_tokens_saved")
            if (isinstance(saved, dict) and held == record.get("_tokens_shown")
                    and record.get("level_id") == record.get("_tokens_level")):
                # 沒改「現在手上有幾個」：原本的起點照留。這一格是載入分頁時算的，
                # 之後又記了打法、或程式開著過了一天，它就舊了——每次存檔都拿它
                # 重設成今天的起點，會把舊數字當成今天的（實測代幣數一直停在同一個數字）。
                out["tokens"] = dict(saved, max=cap)
            else:
                out["tokens"] = scheduler.token_anchor(
                    record["level_id"], held, self.app.log_entries(),
                    date.fromisoformat(self.app._today()), cap)
        return out

    @staticmethod
    def _weekday_span_text(weekdays, start, end) -> str:
        """[5, 6], "2026-10-01", "" → 「每六日（10/01～…）」。"""
        names = dict(WEEKDAY_CHOICES)
        text = "每" + "".join(names[int(x)][1:] for x in sorted(weekdays))
        if start or end:
            text += (f"（{(start or '')[5:].replace('-', '/') or '…'}"
                     f"～{(end or '')[5:].replace('-', '/') or '…'}）")
        return text

    def _level_rule_row(self, record):
        names = dict(storage.level_choices(self.app.shared, include_archived=True))
        weekdays = record.get("weekdays") or []
        if weekdays:
            when = self._weekday_span_text(weekdays, record.get("from_date"),
                                           record.get("to_date"))
        elif not record.get("from_date") and not record.get("to_date"):
            when = "一直有效"
        else:
            when = (f"{record.get('from_date') or '…'} ~ "
                    f"{record.get('to_date') or '…'}")
        tier = record.get("tier") or ""
        if tier == "other":
            when += "・其他關"
        elif tier:
            when += "・第 " + format_stages(int(x) for x in tier.split(",")) + " 關"
        count = record.get("max_count")
        if record.get("tokens_now") is not None and not tier:
            count = (f"代幣 {record['tokens_now']}/"
                     f"{record.get('token_max') or scheduler.TOKEN_DEFAULT_MAX}")
        elif count is not None and not tier:
            count = f"每日 {count} 次"
        return (names.get(record.get("level_id"), record.get("level_id", "")),
                when, "不限" if count is None or tier else count)

    def _event_level(self, level_id):
        """關卡鍵 → (活動, 關卡)；找不到的是 None。"""
        event_id, own_id = storage.split_level_key(level_id or "")
        event = storage.find_event(self.app.shared, event_id) if event_id else None
        level = next((lv for lv in (event or {}).get("levels") or []
                      if lv.get("id") == own_id), None)
        return event, level

    def _is_permanent_level(self, level_id) -> bool:
        """常駐關卡的基本關卡（永遠存在、不能刪）——次數限制不必填起訖日。"""
        event, level = self._event_level(level_id)
        return level is not None and storage.is_locked_standing_level(event, level)

    def _is_token_level(self, level_id) -> bool:
        """經商貿易、探索調查：要用代幣才能打，才有「目前持有代幣」那兩格。"""
        event, level = self._event_level(level_id)
        return level is not None and storage.is_token_level(event, level)

    def _level_rule_dates(self, level_id) -> tuple[str, str]:
        """新增「指定關卡次數限制」時起訖日帶什麼：那一關所屬活動的檔期。

        常駐關卡、找不到活動、活動沒填齊起訖日 → 留白（＝整個排程期間）。
        不能直接呼叫 `_event_bounds(event_id)` 了事：它找不到活動時會退回
        第一檔活動，結果選哪一關都帶到第一檔的檔期。
        """
        event_id, _level = storage.split_level_key(level_id or "")
        event = storage.find_event(self.app.shared, event_id) if event_id else None
        if event is None or storage.is_standing(event):
            return "", ""
        start, end = self._event_bounds(event_id)
        if start is None:
            return "", ""
        return start.isoformat(), end.isoformat()

    def _check_daily_level_unique(self, result, others):
        """同一個關卡只能有一條次數限制（ListEditor 的 validate）。

        限期關卡分了難度的例外：不同難度各一條是正常用法（第 35~45 關週一、
        第 50~60 關週三），只擋同一關同一個難度。
        """
        level_id = result.get("level_id") or ""
        tier = result.get("tier") or ""
        if not level_id:
            return None
        for other in others:
            if (other.get("level_id") or "") == level_id and (other.get("tier") or "") == tier:
                name = dict(storage.level_choices(
                    self.app.shared, include_archived=True)).get(level_id, level_id)
                if tier:
                    return f"「{name}」這個難度已經有一條次數限制了，請直接編輯那一條"
                return f"「{name}」已經有一條次數限制了，請直接編輯那一條"
        return None

    def _default_daily_level(self, _records):
        choices = self._level_choices()
        level_id = choices[0][0] if choices else ""
        start, end = self._level_rule_dates(level_id)
        return {"level_id": level_id, "max_count": None, "weekdays": [],
                "tier": "", "from_date": start, "to_date": end}

    # -- 指定日期打指定次數 ------------------------------------------------
    def _level_target_specs(self):
        """回傳「依記錄算欄位」的函式：選了哪種「哪幾天」，日期那幾格就不一樣。"""
        choices = self._level_choices()

        def specs(record):
            repeat = record.get("repeat") or "once"
            fields = [
                {"key": "level_id", "label": "關卡", "type": "choice",
                 "choices": choices or [("", "（尚未設定關卡）")]},
                {"key": "repeat", "label": "哪幾天", "type": "choice",
                 "choices": LEVEL_TARGET_REPEATS, "rebuild": True},
            ]
            if repeat == "dates":
                fields.append({"key": "dates", "label": "日期", "type": "date_list",
                               "hint": "用頓號或逗號隔開，每個打 8 碼數字，"
                                       f"例如 {example_date()}、{example_date(days=3)}"})
            elif repeat == "weekly":
                fields += [
                    {"key": "weekdays", "label": "星期幾", "type": "multi_choice",
                     "choices": WEEKDAY_CHOICES, "required": True, "height": 7,
                     "hint": "可以複選（按住 Ctrl 點）；那天打不到這一關就自動跳過"},
                    {"key": "from_date", "label": "期間起", "type": "date",
                     "optional": True},
                    {"key": "to_date", "label": "期間訖", "type": "date",
                     "optional": True},
                ]
            else:
                fields.append({"key": "date", "label": "日期", "type": "date"})
            return fields + [
                {"key": "count", "label": "當天打幾次", "type": "int", "minimum": 1,
                 "hint": "每一天的總次數——那天已經記錄打過的也算在裡面"},
                {"key": "mode", "label": "方式", "type": "choice",
                 "choices": LEVEL_TARGET_MODES,
                 "hint": "剛好＝不多不少；至少＝打滿之後還能再多打"},
            ]
        return specs

    @staticmethod
    def _level_target_to_json(record) -> dict:
        """只存用得到的那幾格。單一日期維持舊格式（沒有 repeat 鍵）。"""
        out = {"level_id": record["level_id"]}
        repeat = record.get("repeat") or "once"
        if repeat == "dates":
            out.update(repeat="dates", dates=list(record.get("dates") or []))
        elif repeat == "weekly":
            weekdays = sorted({int(x) for x in record.get("weekdays") or []})
            if not weekdays:
                raise FieldError("「指定日期打指定次數」的每週規則沒有選星期幾")
            start, end = record.get("from_date") or "", record.get("to_date") or ""
            if start and end and start > end:
                raise FieldError(
                    f"「指定日期打指定次數」的每週規則期間起（{start}）晚於期間訖（{end}）")
            out.update(repeat="weekly", weekdays=weekdays,
                       from_date=start, to_date=end)
        else:
            out["date"] = record["date"]
        out.update(count=record["count"], mode=record["mode"])
        return out

    @staticmethod
    def _check_level_target_overlap(targets) -> None:
        """同一關同一天被兩條寫日期的規則（或兩條每週規則）指到就擋下來。

        寫日期的蓋過每週的是刻意的（「每週六 ×3，但這個週六 ×5」），不擋。
        """
        seen = set()
        weekly = []
        for r in targets:
            repeat = r.get("repeat") or "once"
            if repeat == "weekly":
                for other in weekly:
                    if (other["level_id"] == r["level_id"]
                            and set(other["weekdays"]) & set(r["weekdays"])
                            and (r["from_date"] or "0") <= (other["to_date"] or "9")
                            and (other["from_date"] or "0") <= (r["to_date"] or "9")):
                        raise FieldError(
                            "「指定日期打指定次數」裡同一關有兩條每週規則的星期幾"
                            "與期間重疊了，請合併成一條")
                weekly.append(r)
                continue
            for day in (r["dates"] if repeat == "dates" else [r["date"]]):
                if (r["level_id"], day) in seen:
                    raise FieldError(
                        f"「指定日期打指定次數」裡 {day} 的同一關填了不只一條，"
                        "請留一條就好")
                seen.add((r["level_id"], day))

    @staticmethod
    def _level_target_when(record) -> str:
        repeat = record.get("repeat") or "once"
        if repeat == "dates":
            dates = record.get("dates") or []
            return "、".join(d[5:].replace("-", "/") for d in dates)
        if repeat == "weekly":
            return GlobalTab._weekday_span_text(
                record.get("weekdays") or [], record.get("from_date"),
                record.get("to_date"))
        return record.get("date", "")

    def _level_target_row(self, record):
        names = dict(storage.level_choices(self.app.shared, include_archived=True))
        return (names.get(record.get("level_id"), record.get("level_id", "")),
                self._level_target_when(record),
                record.get("count", 0),
                dict(LEVEL_TARGET_MODES).get(record.get("mode"), "剛好"))

    def _default_level_target(self, _records):
        choices = self._level_choices()
        reset = scheduler.parse_clock(
            (self.app.shared or {}).get("daily_reset_time"), "05:00")
        today = scheduler.task_day_of(datetime.now(), reset).isoformat()
        # 三種「哪幾天」的欄位都先帶好，切換時才不會是空的
        return {"level_id": choices[0][0] if choices else "",
                "repeat": "once", "date": today, "dates": [today],
                "weekdays": [], "from_date": "", "to_date": "",
                "count": 1, "mode": "exact"}

    # -- 體力來源 ----------------------------------------------------------
    def _default_source(self, preset_key) -> dict:
        """「新增」選了一種來源時帶進對話框的初值。

        月卡預設「不依據活動」＋今天起算 30 天：月卡是真實世界的 30 天，跟活動
        檔期無關；綁在活動上的話，活動一結束月卡就不發體力了。
        積分兌換同理：它是真實世界的某一天，預設就是今天、不依據活動。綁在活動上
        存的是偏移量，今天早於活動起始日時會變成負數，而負的偏移量在這裡的意思是
        「從最後一天倒數」，日期會整個跑掉。
        其餘來源（每日／每週任務、簽到）本來就跟著活動走，維持原樣。
        """
        preset = {k: (label, kind, defaults)
                  for k, label, kind, defaults in STAMINA_SOURCE_PRESETS}[preset_key]
        _label, kind, defaults = preset
        if preset_key == "gift":
            # 積分兌換：依據哪一檔活動只用來算兌換期限（活動結束後 7 天），
            # 日期是領取日（真實日期），預設留白＝當成最後一天才領
            today = date.today()
            record = self._source_record(preset_key, kind, defaults,
                                         self._gift_default_event(), today, today)
            record.pop("day_date", None)
            return record
        if preset_key not in ABSOLUTE_DATE_PRESETS:
            event_id = self._first_event_id()
            start, end = self._event_bounds(event_id)
            if start is not None:
                return self._source_record(preset_key, kind, defaults,
                                           event_id, start, end)
            # 連一檔有起訖日的真活動都沒有：綁上去也算不出日期，一樣退成
            # 「不依據活動」，使用者至少填得完、存得了檔。
        today = date.today()
        return self._source_record(preset_key, kind, defaults, NO_EVENT_ID,
                                   today,
                                   today + timedelta(days=MONTHLY_CARD_DAYS - 1))

    def _gift_default_event(self):
        """新增積分兌換時預設依據哪一檔活動：兌換期限還沒過、最早結束的那檔
        （通常就是剛結束或快結束、正要拿積分去換的那檔）；都過了就不依據活動。"""
        today = datetime.strptime(self.app._today(), "%Y-%m-%d").date()
        best = None
        for event in storage.real_events(self.app.shared):
            _start, end = self._event_bounds(event["id"])
            if end is None or scheduler.gift_deadline(end) < today:
                continue
            if best is None or end < best[0]:
                best = (end, event["id"])
        return best[1] if best else NO_EVENT_ID

    def _gift_deadline(self, event_id):
        """這一筆積分兌換最晚哪天要換；不依據活動／活動沒結束日回 None。"""
        if not event_id or event_id == NO_EVENT_ID:
            return None
        if storage.find_event(self.app.shared, event_id) is None:
            return None       # _event_bounds 找不到會退到第一檔，不能用它
        _start, end = self._event_bounds(event_id)
        return scheduler.gift_deadline(end) if end else None

    @staticmethod
    def _source_record(preset_key, kind, defaults, event_id, start, end) -> dict:
        # `day_date`（積分兌換那種 once 型）也一起帶——對話框依 kind 只顯示
        # 用得到的那幾格，多帶的欄位不會露出來，但切換 kind 時就不會是空的。
        return {"preset": preset_key, "kind": kind, "weekday": 6,
                "event_id": event_id,
                "month_days": list(DEFAULT_MONTH_DAYS),
                "from_date": start.isoformat(), "to_date": end.isoformat(),
                "day_date": start.isoformat(), **defaults}

    def _source_specs(self, record) -> list[dict]:
        kind = record.get("kind") or "daily"
        note = {"key": "note", "label": "說明", "type": "opt_str",
                "hint": "這筆體力是哪裡來的（例如「維修補償」），報表會用這個稱呼它；可留白"}
        if kind == "mail":
            # 信箱永遠是真實日期，不必選依據哪一檔活動
            return [note,
                    {"key": "day_date", "label": "收到日", "type": "date",
                     "hint": f"收到那天起 {scheduler.MAIL_HOLD_DAYS} 天內要領，"
                             "整封一次領；排程會算哪天領、領出來哪天到期"},
                    {"key": "claimed", "label": "已領取", "type": "bool",
                     "hint": "領出來之後勾這格，剩多少照計算頁的「包包實際還剩」填"},
                    # 「清除已失效」靠它算這封信領出來的體力哪天過期；
                    # 剛勾已領取又留白＝記成今天（見 _source_to_json）
                    {"key": "claimed_date", "label": "領取日（可留白）",
                     "type": "date", "optional": True},
                    ] + item_specs("")
        if record.get("preset") == "gift":
            deadline = self._gift_deadline(record.get("event_id"))
            last = ""
            if deadline:
                weekday = "一二三四五六日"[deadline.weekday()]
                last = f"（這一筆是 {deadline:%m/%d} 週{weekday}中午 12 點前）"
            return [note,
                    {"key": "event_id", "label": "哪一檔活動的積分", "type": "choice",
                     "rebuild": True,      # 換活動時提示裡的最後一天跟著更新
                     "choices": ([(NO_EVENT_ID, NO_EVENT_LABEL)]
                                 + self._real_event_choices()),
                     "hint": f"最晚活動結束後 {scheduler.REWARD_CLAIM_DAYS} 天"
                             f"（週四中午 12 點前）要換{last}"},
                    {"key": "claimed", "label": "已領取", "type": "bool",
                     "hint": "換出來之後勾這格，剩多少照計算頁的「包包實際還剩」填"},
                    {"key": "claimed_date", "label": "領取日（可留白）",
                     "type": "date", "optional": True,
                     "hint": "效期從這天算（隔週的星期日到期）。留白：勾了已領取"
                             "＝記成今天；沒勾＝當成最後一天才換。"
                             "選「不依據活動」的話要填"},
                    ] + item_specs("")
        fields = [note,
                  {"key": "event_id", "label": "依據哪一檔活動", "type": "choice",
                   # 常駐關卡不在選項裡——它沒有起訖日，拿它當偏移量的基準算不出
                   # 日期（跟「特殊日」同一個理由）。第一個選項恆存在，所以也
                   # 不必再留「（尚未設定活動）」那種假選項。
                   "choices": ([(NO_EVENT_ID, NO_EVENT_LABEL)]
                               + self._real_event_choices()),
                   "hint": "依據活動＝日期存成相對那檔活動起始日的偏移量，換一檔"
                           "活動整組跟著移動（每日／每週任務、簽到適合這種）；"
                           "不依據活動＝存你填的實際日期，跟活動檔期無關"
                           "（月卡是真實世界的 30 天，適合這種）"}]
        if kind == "once":
            fields.append({"key": "day_date", "label": "發放日", "type": "date"})
            prefix = ""
        else:
            fields += [{"key": "from_date", "label": "期間起", "type": "date"},
                       {"key": "to_date", "label": "期間訖", "type": "date"}]
            # 一律「每次」：多久發一次已經由來源種類和期間交代了，寫「每天」
            # 在每日任務這類來源讀起來像「一天發 100 點」，跟「每次」混用也不一致
            prefix = "每次 "
            if kind == "weekly":
                fields.append({"key": "weekday", "label": "星期幾",
                               "type": "choice", "choices": WEEKDAY_CHOICES,
                               "hint": "同一週內哪天拿到，過期日都一樣；"
                                       "記成週日最保守"})
            if kind == "monthly":
                fields.append({"key": "month_days", "label": "每月幾號",
                               "type": "int_list", "minimum": 1, "maximum": 31,
                               "hint": "用頓號或逗號隔開，例如 5、11、17、23"})
        return fields + item_specs(prefix)

    def _source_when(self, record) -> str:
        kind = record.get("kind") or "daily"
        if record.get("preset") == "gift":
            text = (record.get("claimed_date") or "")[5:].replace("-", "/")
            if record.get("claimed"):
                return f"已領取 {text}".rstrip()
            deadline = self._gift_deadline(record.get("event_id"))
            last = f"（{deadline:%m/%d} 中午前要換）" if deadline else ""
            if text:
                return f"{text} 領取{last}"
            return f"{deadline:%m/%d} 中午前領取（最後一天）" if deadline else ""
        if kind == "once":
            return record.get("day_date", "")
        if kind == "mail":
            text = record.get("day_date", "")
            try:
                received = datetime.strptime(text, "%Y-%m-%d").date()
            except ValueError:
                return text
            deadline = received + timedelta(days=scheduler.MAIL_HOLD_DAYS)
            claimed = ""
            if record.get("claimed"):
                text = record.get("claimed_date") or ""
                claimed = f"　已領取 {text[5:].replace('-', '/')}".rstrip()
            return f"{received:%m/%d} 收到（{deadline:%m/%d} 前要領）" + claimed
        span = f"{record.get('from_date', '')} ~ {record.get('to_date', '')}"
        if kind == "weekly":
            weekday = dict(WEEKDAY_CHOICES).get(int(record.get("weekday", 6)), "")
            return f"{span}（{weekday}）"
        if kind == "monthly":
            days = "、".join(str(int(x)) for x in (record.get("month_days") or []))
            return f"{span}（每月 {days} 號）"
        return span

    def _source_days(self, record) -> int:
        """這一筆總共會發幾次（清單的「合計」欄要用）。

        順序是**先換算成存檔結構、再看它要不要基準**。反過來不行：
        `NO_EVENT_ID` 不是有效的活動 id，`_event_bounds` 找不到會退到第一檔真
        活動，絕對日期的來源就會被誤判成「有基準」。
        """
        if (record.get("kind") or "daily") == "mail" or record.get("preset") == "gift":
            return 1          # 一封信／一次兌換，整筆一次領
        try:
            source = self._source_to_json(record)
        except (FieldError, ValueError):
            return 0          # 日期還沒填好／那檔活動沒起訖日，算不出來
        if scheduler.source_is_absolute(source):
            # 絕對日期鍵優先，基準給哪一天結果都一樣；給今天只是為了可重現。
            return len(scheduler.expand_stamina_sources([source], date.today()))
        start, _end = self._event_bounds(source.get("event_id")
                                         or self._first_event_id())
        if start is None:
            return 0
        return len(scheduler.expand_stamina_sources([source], start))

    def _source_row(self, record):
        each = items_total(record)
        times = self._source_days(record)
        mail = (record.get("kind") or "daily") == "mail"
        return (SOURCE_PRESET_LABELS.get(record.get("preset"), "自訂"),
                (record.get("note") or "").strip(),
                NO_EVENT_SHORT if mail else self._event_name(record.get("event_id")),
                self._source_when(record),
                item_summary(record),
                f"{SOURCE_KIND_LABELS.get(record.get('kind'), '')} {each}",
                each * times)

    def _source_to_json(self, record) -> dict:
        """編輯器的一筆 → 存檔用的結構。

        依據某一檔活動的，日期換算成相對那檔活動起始日的偏移量；「不依據活動」
        的直接寫絕對日期鍵，並把 `event_id` 寫成 null。讀回來是靠絕對日期鍵在
        不在判定的（見 `_source_from_json`），`event_id` 純粹是給人看的。

        日期字串的格式已經由 RecordDialog 的 `date` 欄驗過，這裡不必再驗一次。
        """
        kind = record.get("kind") or "daily"
        note = (record.get("note") or "").strip()
        if kind == "mail":
            # 信箱一律是真實日期（收到日），不依據活動
            claimed = bool(record.get("claimed"))
            out = {"preset": record.get("preset", "mail"), "kind": kind,
                   "event_id": None, "day_date": record["day_date"],
                   "claimed": claimed,
                   "amount": items_total(record),
                   "items": items_from_record(record)}
            if note:
                out["note"] = note
            # 領取日：這次才勾已領取、又沒填日期的，記成今天。載入時就已經是
            # 已領取的舊資料（`_was_claimed`）不補——補今天會比實際晚，
            # 「清除已失效」就會晚刪；留白的話它改用領取期限保守判斷。
            claimed_date = record.get("claimed_date") or ""
            if claimed and not claimed_date and not record.get("_was_claimed"):
                claimed_date = self.app._today()
            if claimed and claimed_date:
                out["claimed_date"] = claimed_date
            return out
        if record.get("preset") == "gift":
            # 積分兌換：event_id 只用來算兌換期限；日期一律是領取日（真實日期）
            event_id = record.get("event_id")
            event_id = None if not event_id or event_id == NO_EVENT_ID else event_id
            claimed = bool(record.get("claimed"))
            out = {"preset": "gift", "kind": "once", "event_id": event_id,
                   "claimed": claimed,
                   "amount": items_total(record),
                   "items": items_from_record(record)}
            if note:
                out["note"] = note
            claimed_date = record.get("claimed_date") or ""
            if claimed and not claimed_date and not record.get("_was_claimed"):
                claimed_date = self.app._today()
            if claimed_date:
                out["claimed_date"] = claimed_date
            elif event_id is None:
                which = f"「{note}」" if note else ""
                raise FieldError(
                    f"積分兌換{which}沒有選是哪一檔活動的積分，"
                    "算不出最晚哪天要換——請選活動，或填領取日")
            return out
        absolute = record.get("event_id") == NO_EVENT_ID
        event_id = None if absolute else (record.get("event_id")
                                          or self._first_event_id())
        out = {"preset": record.get("preset", "custom"), "kind": kind,
               "event_id": event_id,
               "amount": items_total(record),
               "items": items_from_record(record)}
        if note:
            out["note"] = note
        if kind == "once":
            if absolute:
                out["day_date"] = record["day_date"]
            else:
                out["day_offset"] = self._date_to_offset(record["day_date"],
                                                         event_id)
        else:
            if absolute:
                out["from_date"] = record["from_date"]
                out["to_date"] = record["to_date"]
            else:
                out["from_offset"] = self._date_to_offset(record["from_date"],
                                                         event_id)
                out["to_offset"] = self._date_to_offset(record["to_date"],
                                                       event_id)
            if kind == "weekly":
                out["weekday"] = int(record.get("weekday", 6))
            if kind == "monthly":
                out["month_days"] = [int(x) for x in
                                     (record.get("month_days") or [])]
        return out

    def _source_from_json(self, source) -> dict:
        """存檔的一筆 → 編輯器用的結構（偏移量換算回日期）。

        「不依據活動」一律靠絕對日期鍵判定（見 scheduler.source_is_absolute）。
        """
        absolute = scheduler.source_is_absolute(source)
        event_id = (NO_EVENT_ID if absolute
                    else (source.get("event_id") or self._first_event_id()))
        record = {"preset": source.get("preset", "custom"),
                  "kind": source.get("kind") or "daily",
                  "event_id": event_id,
                  "weekday": int(source.get("weekday", 6)),
                  "month_days": [int(x) for x in (source.get("month_days")
                                                  or DEFAULT_MONTH_DAYS)],
                  "note": source.get("note") or "",
                  **record_from_items(source.get("items"), source.get("amount"))}
        if record["preset"] == "gift" and record["kind"] == "once":
            # 積分兌換：event_id 是哪一檔活動的積分（算兌換期限用）
            gift_event = source.get("event_id")
            if not gift_event or storage.find_event(self.app.shared, gift_event) is None:
                gift_event = NO_EVENT_ID
            claimed_date = source.get("claimed_date") or ""
            claimed = bool(source.get("claimed"))
            record.update(event_id=gift_event, claimed=claimed,
                          _was_claimed=claimed, claimed_date=claimed_date)
        elif record["kind"] == "mail":
            record["event_id"] = NO_EVENT_ID
            record["day_date"] = source.get("day_date") or ""
            record["claimed"] = bool(source.get("claimed"))
            record["_was_claimed"] = record["claimed"]
            record["claimed_date"] = source.get("claimed_date") or ""
        elif record["kind"] == "once":
            record["day_date"] = (source.get("day_date") or "" if absolute
                                  else self._offset_to_date(
                                      source.get("day_offset"), event_id))
        elif absolute:
            record["from_date"] = source.get("from_date") or ""
            record["to_date"] = source.get("to_date") or ""
        else:
            record["from_date"] = self._offset_to_date(source.get("from_offset"),
                                                       event_id)
            record["to_date"] = self._offset_to_date(source.get("to_offset"),
                                                     event_id)
        return record

    def _stale_reason(self, record, today):
        """清單的一筆已經失效了嗎（見 scheduler.stale_source_reason）。"""
        try:
            source = self._source_to_json(record)
        except (FieldError, ValueError, KeyError):
            return None       # 日期沒填好／依據的活動沒起訖日：不替使用者決定
        if source.get("preset") == "gift":
            deadline = self._gift_deadline(source.get("event_id"))
            if deadline is not None:
                source["claim_deadline"] = deadline
            return scheduler.stale_source_reason(source, None, today)
        base = None
        if not scheduler.source_is_absolute(source) and source.get("kind") != "mail":
            base, _end = self._event_bounds(source.get("event_id"))
            if base is None:
                return None
        return scheduler.stale_source_reason(source, base, today)

    def _clear_stale_sources(self):
        """「清除已失效」：列出體力全部用不到了的來源，確認後從清單拿掉。

        跟「刪除」一樣只改畫面上的清單，按「儲存」才寫檔——反悔就不要存。
        """
        today = datetime.strptime(self.app._today(), "%Y-%m-%d").date()
        records = self.source_editor.records
        stale = [(i, reason) for i, record in enumerate(records)
                 if (reason := self._stale_reason(record, today))]
        if not stale:
            messagebox.showinfo("清除已失效", "沒有已失效的體力來源。", parent=self)
            return
        lines = []
        for index, reason in stale[:30]:
            row = self._source_row(records[index])
            name = row[0] + (f"「{row[1]}」" if row[1] else "")
            lines.append(f"・{name}　{row[3]}　→ {reason}")
        if len(stale) > 30:
            lines.append(f"……還有 {len(stale) - 30} 筆")
        if not messagebox.askyesno(
                "清除已失效",
                f"這 {len(stale)} 筆的體力都已經過期或過了領取期限，"
                "排程也不會再用到：\n\n" + "\n".join(lines)
                + "\n\n要從清單拿掉嗎？（按「儲存」之後才會寫進存檔）",
                parent=self):
            return
        drop = {index for index, _reason in stale}
        self.source_editor.records = [r for i, r in enumerate(records)
                                      if i not in drop]
        self.source_editor.refresh()
        self.app.set_status(f"已從體力來源清單拿掉 {len(stale)} 筆已失效的，記得儲存")

    # -- 載入／儲存 -------------------------------------------------------
    def load(self):
        shared, profile = self.app.shared, self.app.profile
        prefs = shared.get("schedule_prefs") or {}
        self.light_weekdays_var.set(prefs.get("light_weekdays") is not False)
        self.simplify_days_var.set(prefs.get("simplify_days") is not False)
        self.expire_late_var.set(prefs.get("expire_late") is not False)

        real_ids = {ev["id"] for ev in storage.real_events(shared)}
        order = [eid for eid in (profile.get("event_priority") or [])
                 if eid in real_ids]
        order += [ev["id"] for ev in storage.real_events(shared)
                  if ev["id"] not in order]
        self._priority_ids = order
        self._refresh_priority()

        # 關卡優先序：已經不存在的關卡（刪掉了）直接拿掉；停用的留著，
        # 那是這次不算、下次可能又要算，順序不該跟著丟。
        # 限期關卡一律換成系列鍵（舊設定存的是某一檔的鍵），系列沒有檔次存在
        # 時也留著——下一檔可能只是還沒建。
        level_keys = {key for key, _label in storage.level_choices(
            shared, include_archived=True)}
        converted = [storage.priority_key_of(shared, key)
                     for key in profile.get("level_priority") or []]
        self._level_priority_ids = [
            key for key in dict.fromkeys(converted)
            if key in level_keys or scheduler.split_limited_series_key(key)]
        self._refresh_level_priority()

        # 存的就是絕對日期，畫面填的也是日期，兩邊同一件事，不必換算。
        # 代幣顯示「現在手上有幾個」——依紀錄從存檔那天推算到今天。
        entries = self.app.log_entries()
        today = date.fromisoformat(self.app._today())
        self.daily_level_editor.set_specs(self._level_rule_specs())
        self.daily_level_editor.set_records([
            {"level_id": r.get("level_id", ""),
             "tokens_now": scheduler.tokens_held(r, entries, today),
             # 存檔時沒改這一格就沿用原本的起點（見 _daily_level_rule 的代幣那段）
             "_tokens_saved": r.get("tokens"),
             "_tokens_shown": scheduler.tokens_held(r, entries, today),
             "_tokens_level": r.get("level_id", ""),
             "token_max": (scheduler.token_spec(r) or {}).get("max"),
             "weekdays": [int(x) for x in r.get("weekdays") or []],
             "tier": ("other" if r.get("stages_other")
                      else ",".join(str(int(x)) for x in sorted(r["stages"]))
                      if r.get("stages") else ""),
             "from_date": r.get("from_date") or "",
             "to_date": r.get("to_date") or "",
             "max_count": r.get("max_count", r.get("min_count", 1))}
            for r in profile.get("daily_level_rules") or []
        ])

        self.level_target_editor.set_specs(self._level_target_specs())
        # 舊檔沒有 repeat 鍵＝單一日期
        self.level_target_editor.set_records([
            {"level_id": r.get("level_id", ""),
             "repeat": r.get("repeat") or "once",
             "date": r.get("date") or "",
             "dates": list(r.get("dates") or []),
             "weekdays": [int(x) for x in r.get("weekdays") or []],
             "from_date": r.get("from_date") or "",
             "to_date": r.get("to_date") or "",
             "count": r.get("count", 1),
             "mode": "min" if r.get("mode") == "min" else "exact"}
            for r in profile.get("daily_level_targets") or []
        ])

        self.special_editor.set_records([
            {**special_from_json(entry),
             "event_id": entry.get("event_id") or self._first_event_id()}
            for entry in profile.get("special_days") or []])
        self.default_rule_editor.set_records([
            {**special_from_json(rule),
             "event_types": list(rule.get("event_types")
                                 if rule.get("event_types") is not None
                                 else scheduler.DEFAULT_RULE_EVENT_TYPES)}
            for rule in profile.get("event_default_rules") or []])

        # 體力來源：存的是總點數，畫面上填的是「幾個 100/30/10」——載入時拆回數量。
        self.source_editor.set_records([self._source_from_json(x)
                                        for x in profile.get("stamina_sources") or []])

    def collect(self) -> bool:
        try:
            # 指定關卡的日期區間存絕對日期，跟畫面填的是同一件事，不必換算。
            daily_level = [self._level_rule_to_json(r)
                           for r in self.daily_level_editor.get_records()]
            level_targets = [self._level_target_to_json(r)
                             for r in self.level_target_editor.get_records()]
            self._check_level_target_overlap(level_targets)
            # 到期日不存檔——它由發放日推導（下一週的星期日），存下來只會有機會對不上。
            #
            # 一律建起 sources，不能因為「算不出活動起始日」就整份跳過——那會讓
            # 體力來源不寫檔也不報錯（靜默資料遺失）。真的有「依據某活動、但那
            # 活動沒填起訖日」的列時，`_source_to_json` 自己會丟 FieldError，
            # 下面的 except 會把話講出來。
            sources = [self._source_to_json(r)
                       for r in self.source_editor.get_records()]
            # 剛補上的領取日寫回清單：存檔不會重載這一頁，不寫回的話
            # 隔天再存一次，領取日會被改成那天
            for record, source in zip(self.source_editor.records, sources):
                if source.get("claimed_date"):
                    record["claimed_date"] = source["claimed_date"]
                    record["_was_claimed"] = True
        except (FieldError, ValueError) as exc:
            messagebox.showerror("輸入有誤", str(exc), parent=self)
            return False

        shared, profile = self.app.shared, self.app.profile
        shared["schedule_prefs"] = {
            "light_weekdays": bool(self.light_weekdays_var.get()),
            "simplify_days": bool(self.simplify_days_var.get()),
            "expire_late": bool(self.expire_late_var.get()),
        }
        profile["event_priority"] = list(self._priority_ids)
        profile["level_priority"] = list(self._level_priority_ids)
        if daily_level is not None:
            profile["daily_level_rules"] = daily_level
        profile["daily_level_targets"] = level_targets
        profile["stamina_sources"] = sources
        profile["special_days"] = [
            {"day_offset": r["day_offset"], "event_id": r.get("event_id"),
             "type": r["type"], "value": r["value"]}
            for r in self.special_editor.get_records()
        ]
        profile["event_default_rules"] = [
            {**special_to_json(r), "event_types": list(r.get("event_types") or [])}
            for r in self.default_rule_editor.get_records()
        ]
        return True


class RoutineTab(ttk.Frame):
    """任務進度：這個帳號對每一條任務（固定任務＋活動任務）的進度與開關。

    任務清單本身所有帳號共用，在「設定 → 任務清單」維護。
    """

    def __init__(self, master, app):
        super().__init__(master)
        # 視窗縮小時整頁可以兩個方向捲（見 ScrollableFrame）
        self.scroller = ScrollableFrame(self, fill_height=True)
        self.scroller.pack(fill="both", expand=True)
        page = self.scroller.inner
        page.configure(padding=dp(16))
        self.app = app

        lead = ttk.Label(page, text="這個帳號自己的：要不要做、目標改多少、開始記錄前已經累積多少；"
                                    "選一列按「編輯」或直接雙擊。"
                                    "還沒完成的任務整列灰綠色；做完但體力獎勵還沒領的淡橘色。"
                                    "每日／每週／每月任務只看目前這一期",
                         foreground="#b45309")
        lead.grid(row=0, column=0, sticky="w")
        where = ttk.Label(page, text="固定任務的清單所有帳號共用，在「設定 → 任務清單」新增或修改；"
                                     "活動任務在「活動設定」",
                          foreground="#666666")
        where.grid(row=1, column=0, sticky="w", pady=(dp(2), dp(10)))
        self.scroller.wrap_label(lead)
        self.scroller.wrap_label(where)
        # 這個帳號不做的任務平常收起來；要改回來時勾這格叫出來
        self.show_off_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(page, text="顯示這個帳號不做的任務",
                        variable=self.show_off_var,
                        command=lambda: self.state_editor.refresh()).grid(
            row=2, column=0, sticky="w", pady=(0, dp(6)))
        self.state_editor = ListEditor(
            page,
            columns=[("task", "任務", 240, "w"),
                     ("baseline", "起始值", 80, "e"),
                     # 目標不另開一欄：進度欄已經是「單位 已完成 / 目標」
                     ("progress", "進度", 230, "w"),
                     ("rewards", "獎勵", 160, "w"),
                     ("mode", "獎勵怎麼領", 90, "center"),
                     ("claimed", "獎勵已領", 70, "center")],
            specs=self._state_specs,
            to_row=self._state_row,
            fixed_rows=True,
            heading_of=lambda r: r.get("_label", ""),
            row_tags=self._state_tags,
            visible=lambda r: self.show_off_var.get() or r.get("enabled", True),
            # 欄寬照內容調：活動名稱、進度文字長短差很多，固定寬度不是切掉就是空一大塊
            auto_width=True,
            # 最少這麼高；視窗大的時候會再撐高（fill_height）
            height=12,
        )
        # 還沒完成的整列灰綠底，一眼看出這期還有哪些沒做；
        # 做完但體力獎勵還要自己去領的淡橘底
        self.state_editor.tree.tag_configure("pending", background="#e3ede6")
        self.state_editor.tree.tag_configure("unclaimed", background="#fde2c8")
        self.state_editor.grid(row=3, column=0, sticky="nsew")
        page.rowconfigure(3, weight=1)
        page.columnconfigure(0, weight=1)

    OFF_HINT = "取消後這一列會收起來，勾上方「顯示這個帳號不做的任務」才看得到"

    def _state_specs(self, record) -> list[dict]:
        if record.get("_manual"):
            # 手動勾選的任務沒有目標數字（排程只看期限與「沒做到」的標記），
            # 列出那兩格只會讓人以為存檔裡那個 0／1 有意義
            return [{"key": "enabled", "label": "這個帳號要做", "type": "bool",
                     "default": True,
                     "hint": "手動勾選的任務沒有目標數字，"
                             "到「每日紀錄」勾完成／沒做到。" + self.OFF_HINT}]
        return [
            {"key": "enabled", "label": "這個帳號要做", "type": "bool",
             "default": True, "hint": self.OFF_HINT},
            {"key": "amount_override", "label": "目標（本帳號）",
             "type": "opt_int", "minimum": 0,
             "hint": f"留空＝用任務本身的數字（{record.get('_amount', 0)}）"},
        ] + ([{"key": "baseline", "label": "起始值", "type": "int", "minimum": 0,
               "hint": "開始用這個工具之前就已經完成的量（只算指定的那幾關）"}]
             if (record.get("_progress") or {}).get("uses_baseline") else []) + ([{"key": "reward_mode", "label": "體力獎勵怎麼領", "type": "choice",
               "choices": REWARD_MODE_CHOICES,
               "hint": "手動領取＝達標後放著，排程決定哪一週去領（最晚活動結束後 "
                       f"{scheduler.REWARD_CLAIM_DAYS} 天）；達標自動領取＝一達標就進包包，"
                       "效期從達標那週算"},
              {"key": "reward_claimed", "label": "體力獎勵已領取", "type": "bool",
               "hint": "達標後領出來了就勾這格，排程就不再算這筆；"
                       "包包裡剩多少照計算頁的「包包實際還剩」填"}]
             if record.get("_claimable") else [])

    @staticmethod
    def _progress_of(record) -> tuple[str, bool | None]:
        """(進度欄的字, 完成與否)。完成與否是 None＝不適用（停用、不在期間內）。

        數字類的拿記錄**當下**的目標與起始值比，編輯完一重畫就跟著變。
        """
        if not record.get("enabled", True):
            return "不做", None
        info = record.get("_progress") or {}
        unit = storage.TASK_METRIC_LABELS.get(record.get("_metric"), "")
        state = info.get("state")
        period = info.get("period", "")
        kind = info.get("kind")
        if kind == "count":
            override = record.get("amount_override")
            target = (int(record.get("_amount") or 0) if override in (None, "")
                      else int(override))
            done = int(info.get("done") or 0)
            if info.get("uses_baseline"):
                done += int(record.get("baseline") or 0)
            met = done >= target
        else:
            met = bool(info.get("met"))
        once = info.get("once")
        if state == "not_started":
            # 沒有目標欄了，還沒開始的把目標寫出來，才知道之後要做多少
            if kind != "count":
                return "未開始", None
            return f"未開始（目標 {target}{' ' + unit if unit else ''}）", None
        if state == "ended":
            # 會重置的任務期間過了就沒有「這一期」可看；
            # 活動任務照樣講達標沒有（沒達標就是錯過了）
            if not once:
                return "已結束", None
            if not met:
                return (f"已結束，{unit} {done} / {target}" if kind == "count"
                        else "已結束，沒做到"), None
        # 活動任務整檔只有一期，標期限；會重置的標是哪一期
        prefix = "" if once else period
        # 只有比活動早截止的才標期限（到活動結束的不必講）
        suffix = f"（{info['deadline']} 前）" if once and info.get("deadline") else ""
        if kind == "assumed" and info.get("assumed_on"):
            due = info["assumed_on"]
            return f"{period}{WEEKDAY_CHOICES[due.weekday()][1]}預設完成（還沒到）", None
        if met:
            label = {"ticked": "已勾", "assumed": "預設完成"}.get(kind, "已完成")
            return f"✓ {label}" + ("" if once else f"（{period}）"), True
        if kind == "ticked":
            return f"{prefix}還沒勾{suffix}", False
        if kind == "assumed":
            return f"{prefix}標記沒做到", False
        return f"{prefix} {unit} {done} / {target}{suffix}".strip(), False

    def _state_tags(self, record):
        if not record.get("enabled", True):
            return ("disabled",)
        met = self._progress_of(record)[1]
        if met is False:
            return ("pending",)
        # 達標了、但體力獎勵要自己去領而且還沒領（自動領取的一達標就進包包）
        if (met and record.get("_claimable") and record.get("reward_mode") != "auto"
                and not record.get("reward_claimed")):
            return ("unclaimed",)
        return ()

    def _state_row(self, record):
        # 起始值只有「活動任務、指定了關卡」用得到；其他的看活動設定的起始值
        # （預設範圍）或根本沒有起始值（每日／每週這種會重置的），寫「—」
        uses = (record.get("_progress") or {}).get("uses_baseline")
        return (record.get("_label", ""),
                record.get("baseline", 0) if uses else "—",
                self._progress_of(record)[0],
                record.get("_rewards", ""),
                dict(REWARD_MODE_CHOICES).get(record.get("reward_mode"), "")
                if record.get("_claimable") else "",
                ("是" if record.get("reward_claimed") else "否")
                if record.get("_claimable") else "")

    def load(self):
        self._load_states()

    def _task_progress(self) -> dict:
        try:
            return scheduler.task_progress(self.app.shared, self.app.profile,
                                           self.app.log_entries(), datetime.now())
        except Exception:       # 進度只是顯示用，算不出來也不該擋住這一頁
            return {}

    def refresh_progress(self):
        """每日紀錄改了之後只重算進度欄，不洗掉表格裡還沒存的編輯。"""
        progress = self._task_progress()
        records = self.state_editor.get_records()
        for record in records:
            record["_progress"] = progress.get(record.get("_key")) or {}
        self.state_editor.set_records(records)

    @staticmethod
    def _reward_still_open(task, owner, state, stamina_of, today) -> bool:
        """活動任務的體力獎勵還沒勾已領、也還在領取期限（結束後 REWARD_CLAIM_DAYS 天）內。"""
        if (task.get("cycle") != "event" or task.get("metric") == "manual"
                or state.get("reward_claimed") or state.get("reward_auto")):
            return False
        if not any(stamina_of.get(r.get("item"), 0) * int(r.get("qty") or 0) > 0
                   for r in task.get("rewards") or []):
            return False
        try:
            end = date.fromisoformat(owner.get("end_date") or "")
        except ValueError:
            return False
        return today <= end + timedelta(days=scheduler.REWARD_CLAIM_DAYS)

    def _load_states(self):
        states = self.app.profile.get("task_state") or {}
        progress = self._task_progress()
        stamina_of = scheduler.item_stamina_table(self.app.shared)
        items = self.app.shared.get("items") or []
        records = []
        today = date.today()
        for task, owner, key in scheduler.iter_tasks(self.app.shared):
            state = states.get(key) or {}
            if owner is not None and storage.is_archived(owner):
                # 已封存的活動，任務也跟著收起來——除非還有體力獎勵沒領、
                # 又還在領取期限內：不然封存之後就沒地方勾「已領取」了
                if not self._reward_still_open(task, owner, state, stamina_of, today):
                    continue
            where = f"{owner.get('name') or owner['id']}／" if owner else "固定／"
            records.append({
                "_key": key,
                "_label": where + (task.get("name") or key),
                "_amount": int(task.get("amount") or 0),
                "_metric": task.get("metric"),
                "_manual": task.get("metric") == "manual",
                # 達標會拿到什麼——決定要不要做、要不要改目標時得看得到
                "_rewards": reward_summary(
                    record_from_rewards(task.get("rewards"), items), items),
                "enabled": state.get("enabled", True) is not False,
                "amount_override": state.get("amount_override"),
                "baseline": int(state.get("baseline") or 0),
                # 活動任務的體力獎勵要自己去領（見 scheduler.REWARD_CLAIM_DAYS）
                "_claimable": (owner is not None and task.get("cycle") == "event"
                               and task.get("metric") != "manual"
                               and any(stamina_of.get(r.get("item"), 0)
                                       * int(r.get("qty") or 0) > 0
                                       for r in task.get("rewards") or [])),
                "reward_mode": "auto" if state.get("reward_auto") else "manual",
                "reward_claimed": bool(state.get("reward_claimed")),
                # 目前這一期做到哪裡（scheduler.task_progress）
                "_progress": progress.get(key) or {},
            })
        self.state_editor.set_records(records)

    def collect(self) -> bool:
        self.app.profile.setdefault("task_state", {})
        for record in self.state_editor.get_records():
            key = record.get("_key")
            if not key:
                continue
            state = storage.task_state(self.app.profile, key)
            state["enabled"] = bool(record.get("enabled", True))
            override = record.get("amount_override")
            state["amount_override"] = None if override in (None, "") else int(override)
            state["baseline"] = int(record.get("baseline") or 0)
            if record.get("_claimable"):
                state["reward_claimed"] = bool(record.get("reward_claimed"))
                state["reward_auto"] = record.get("reward_mode") == "auto"
        return True


class CalcTab(ttk.Frame):
    """計算結果：輸入當下體力與查詢時間，跑 ILP 求最省排程。"""

    def __init__(self, master, app):
        super().__init__(master)
        # 視窗縮小時整頁可以兩個方向捲（見 ScrollableFrame）
        self.scroller = ScrollableFrame(self, fill_height=True)
        self.scroller.pack(fill="both", expand=True)
        page = self.scroller.inner
        page.configure(padding=dp(16))
        self.app = app
        self.stamina_var = tk.StringVar()
        self.time_var = tk.StringVar()
        self.until_var = tk.StringVar()

        bar = ttk.Frame(page)
        bar.grid(row=0, column=0, sticky="we")
        ttk.Label(bar, text="目前體力").pack(side="left")
        ttk.Entry(bar, textvariable=self.stamina_var, width=8).pack(side="left", padx=(dp(6), dp(16)))
        ttk.Label(bar, text="查詢時間").pack(side="left")
        ttk.Entry(bar, textvariable=self.time_var, width=18).pack(side="left", padx=(dp(6), dp(4)))
        ttk.Button(bar, text="現在", command=self.reset_time).pack(side="left", padx=(0, dp(16)))
        # 活動空窗期（所有活動都結束了、只剩常駐關卡）沒有結束日可以當排程終點，
        # 這時要靠這一格。平常留白就好。
        # 跟上面分成兩排：擠在同一排的話，視窗縮到最小時這格要捲過去才看得到
        until = ttk.Frame(page)
        until.grid(row=1, column=0, sticky="w", pady=(dp(8), 0))
        ttk.Label(until, text="排到").pack(side="left")
        ttk.Entry(until, textvariable=self.until_var, width=12).pack(side="left", padx=(dp(6), dp(4)))
        self.until_hint = ttk.Label(until, text="留白＝排到最後一檔活動結束",
                                    foreground="#666666")
        self.until_hint.pack(side="left", padx=(0, dp(16)))
        # 代幣關卡（經商貿易、探索調查）：現在手上有幾個。預設是依每日紀錄推算的
        # 數字，跟遊戲裡對不上就改——開始計算時會以填的數字為新的起點。
        # 自己一排，放在「手上的限時體力道具」上面
        self._tokens = ttk.Frame(page)
        self._tokens.grid(row=2, column=0, sticky="w", pady=(dp(8), 0))
        self._token_rows: list[dict] = []
        self._token_key = None

        # 排程預設「發過而且還沒過期的限時體力一點都沒用過」。打過幾天之後那多半是
        # 高估的，所以計算前讓使用者依到期日逐一校正——包包裡看得到每批的到期日，
        # 照抄就好，程式不必去猜哪一批先用掉。
        # 要比下面的按鈕列先建立：Tab 鍵照建立順序跳，晚建的話會從「排到」
        # 直接跳到「開始計算」，最後才回頭填這幾格
        self._held = ttk.LabelFrame(page, text="手上的限時體力道具", padding=(dp(10), dp(6)))
        self._held.grid(row=3, column=0, sticky="w", pady=(dp(8), 0))
        self._held_rows: list[dict] = []
        self._held_expiries: tuple = ()

        # 動作按鈕自己一排，放在所有輸入（含手上的限時體力）之後
        actions = ttk.Frame(page)
        actions.grid(row=4, column=0, sticky="w", pady=(dp(10), 0))
        self.run_button = ttk.Button(actions, text="開始計算", command=self.run)
        self.run_button.pack(side="left")
        self._solving = False
        # 算完先停在「尚未存入」：可以先對調日期，確認了才寫進每日紀錄。
        self._pending = None            # 還沒存入的計算結果
        self._pending_inputs = None     # 那次計算的 (體力, 查詢時間, 限時體力, 排到)
        self.save_button = ttk.Button(actions, text="存入計畫", command=self.save_pending)
        self.save_button.pack(side="left", padx=(dp(16), 0))
        self.swap_button = ttk.Button(actions, text="對調日期…", command=self.swap_days)
        self.swap_button.pack(side="left", padx=(dp(4), 0))
        self.discard_button = ttk.Button(actions, text="放棄", command=self.discard_pending)
        self.discard_button.pack(side="left", padx=(dp(4), 0))
        self._sync_pending_buttons()
        # 打法歸納與提醒平常不用看，不放在報告裡，按這顆才另開視窗
        self._extras_text = ""
        self.extras_button = ttk.Button(actions, text="打法歸納與提醒…",
                                        command=self.show_extras, state="disabled")
        self.extras_button.pack(side="left", padx=(dp(16), 0))

        self.time_var.trace_add("write", lambda *_a: (self._refresh_held(),
                                                       self._refresh_tokens()))

        volatile = ttk.Label(page, text="體力每 5 分鐘就在變動，上面這些欄位每次計算都要重新確認，"
                                        "不會存檔；換帳號或換活動會自動清空",
                             foreground="#666666")
        volatile.grid(row=5, column=0, sticky="w", pady=(dp(6), dp(10)))
        self.scroller.wrap_label(volatile)

        # 每日明細是寬表格，垂直與水平捲軸都需要
        wrap = ttk.Frame(page)
        wrap.grid(row=6, column=0, sticky="nsew")
        wrap.rowconfigure(0, weight=1)
        wrap.columnconfigure(0, weight=1)

        # 報告是用空白排版的表格，字型必須「中文剛好等於兩個半形字」才對得齊。
        # Consolas 的比值是 1.86，中英混排會歪掉；TkFixedFont 在這台是 7/14=2.00。
        # width／height 只是最小值，視窗大的時候會撐滿；設小一點，
        # 視窗縮小時才是表格自己捲，而不是整頁冒出捲軸
        self.output = tk.Text(wrap, wrap="none", width=40, height=12,
                              font=report_font())
        self.output.grid(row=0, column=0, sticky="nsew")
        vbar = ttk.Scrollbar(wrap, orient="vertical", command=self.output.yview)
        vbar.grid(row=0, column=1, sticky="ns")
        hbar = ttk.Scrollbar(wrap, orient="horizontal", command=self.output.xview)
        hbar.grid(row=1, column=0, sticky="we")
        self.output.configure(yscrollcommand=vbar.set, xscrollcommand=hbar.set,
                              state="disabled")

        page.rowconfigure(6, weight=1)
        page.columnconfigure(0, weight=1)
        self._loaded_key = None

    def reset_time(self):
        self.time_var.set(datetime.now().strftime("%Y-%m-%d %H:%M"))

    def load(self):
        if not self.time_var.get():
            self.reset_time()
        # 換帳號或換活動時，上一個帳號填的體力與道具數量全部作廢——
        # 留著比空白危險，因為那看起來像是已經確認過的數字。
        # 活動的名稱或起訖日一改就視為「換了一檔活動」，上一檔填的數字全部作廢
        # 只看 id 與起訖日——改個名字不該把使用者已經填好的體力與道具數量清掉。
        key = (self.app.profile_id,
               repr([(ev.get("id"), ev.get("start_date"), ev.get("end_date"))
                     for ev in storage.events_of(self.app.shared)]))
        if key != self._loaded_key:
            self._loaded_key = key
            self.stamina_var.set("")
            self._held_expiries = ()
            self._token_key = None
            # 還沒存入的結果也是上一個帳號／上一檔活動的，一併作廢
            self._pending = self._pending_inputs = None
            self._sync_pending_buttons()
        self._refresh_held()
        self._refresh_tokens()
        # 有還沒存入的結果時畫面留著它，不要被上次存的報表蓋掉
        if not self._solving and self._pending is None:
            self.show_stored_report()

    # -- 手上的限時體力 ---------------------------------------------------
    def _today(self):
        """排程的第一天——跟 compute_plan 算的是同一個（重置時刻前算前一天）。"""
        reset = scheduler.parse_clock(self.app.shared.get("daily_reset_time"),
                                      "05:00")
        try:
            moment = datetime.strptime(self.time_var.get().strip(), "%Y-%m-%d %H:%M")
        except ValueError:
            moment = datetime.now()
        return scheduler.task_day_of(moment, reset)

    def _token_estimates(self) -> list[tuple]:
        """[(規則的關卡鍵, 顯示名稱, 推算現在有幾個, 上限)]，只列代幣規則。"""
        try:
            entries = self.app.log_entries()
            names = dict(storage.level_choices(self.app.shared, include_archived=True))
            today = self._today()
            out = []
            for rule in self.app.profile.get("daily_level_rules") or []:
                spec = scheduler.token_spec(rule)
                if spec is None:
                    continue
                key = rule.get("level_id") or ""
                name = names.get(key, key).split("·")[-1]
                out.append((key, name, scheduler.tokens_held(rule, entries, today),
                            spec["max"]))
            return out
        except Exception:      # 設定還沒填完整時不要害整個分頁開不起來
            return []

    def _refresh_tokens(self):
        """推算值變了才重填；使用者已經改過的那格不動（除非換帳號／換日子）。"""
        estimates = self._token_estimates()
        key = (self._today(), tuple(k for k, *_ in estimates))
        if key == self._token_key:
            for row, (_k, _n, held, _cap) in zip(self._token_rows, estimates):
                if row["var"].get().strip() == str(row["estimate"]):
                    row["var"].set(str(held))
                row["estimate"] = held
                self._token_hint(row)
            return
        self._token_key = key
        for child in self._tokens.winfo_children():
            child.destroy()
        self._token_rows = []
        if not estimates:
            self._tokens.grid_remove()
            return
        self._tokens.grid()
        ttk.Label(self._tokens, text="代幣").pack(side="left")
        for level_id, name, held, cap in estimates:
            var = tk.StringVar(value=str(held))
            row = {"level_id": level_id, "name": name, "estimate": held,
                   "max": cap, "var": var}
            ttk.Label(self._tokens, text=name).pack(side="left", padx=(dp(10), dp(4)))
            ttk.Entry(self._tokens, textvariable=var, width=3,
                      justify="center").pack(side="left")
            row["hint"] = ttk.Label(self._tokens, foreground="#666666")
            row["hint"].pack(side="left", padx=(dp(4), 0))
            var.trace_add("write", lambda *_a, r=row: self._token_hint(r))
            self._token_rows.append(row)
            self._token_hint(row)
        ttk.Label(self._tokens, text="（依每日紀錄推算，請對照遊戲確認）",
                  foreground="#666666").pack(side="left", padx=(dp(10), 0))

    @staticmethod
    def _token_hint(row):
        text = row["var"].get().strip()
        if text == str(row["estimate"]):
            row["hint"].config(text=f"/{row['max']}", foreground="#666666")
        else:
            row["hint"].config(text=f"推算 {row['estimate']}，開始計算時更新",
                               foreground="#b45f06")

    def token_values(self) -> dict:
        """{關卡鍵: 填的數量}，只放跟推算不同的（＝要更新起點的）。"""
        out = {}
        for row in self._token_rows:
            text = row["var"].get().strip()
            if text == str(row["estimate"]):
                continue
            label = f"{row['name']}代幣"
            value = parse_int(text, label, 0)
            if value > row["max"]:
                raise FieldError(f"「{label}」最多存 {row['max']} 個，填了 {value}")
            out[row["level_id"]] = value
        return out

    def _apply_tokens(self, values: dict) -> None:
        """把填的代幣數量存成新的起點（今天開始時有幾個），規則頁跟著重載。"""
        if not values:
            return
        entries = self.app.log_entries()
        today = self._today()
        for rule in self.app.profile.get("daily_level_rules") or []:
            key = rule.get("level_id")
            spec = scheduler.token_spec(rule)
            if key in values and spec is not None:
                rule["tokens"] = scheduler.token_anchor(
                    key, values[key], entries, today, spec["max"], spec["per_day"])
        storage.save_profile(self.app.profile_id, self.app.profile)
        for tab, _label in self.app.tabs:
            if isinstance(tab, GlobalTab):
                tab.load()     # 規則頁拿新的起點重算顯示，下次存檔才不會蓋回去
        self._token_key = None
        self._refresh_tokens()
        names = {row["level_id"]: row["name"] for row in self._token_rows}
        self.app.set_status("代幣已更新：" + "、".join(
            f"{names.get(k, k)} {v} 個" for k, v in values.items()))

    def _held_pools(self) -> list[tuple]:
        """這次計算會用到哪幾個到期日的限時體力（今天以前發放、還沒過期的）。"""
        try:
            entries = self.app.log_entries()
            return scheduler.held_pools(self.app.shared, self.app.profile,
                                        self._today(),
                                        storage.missed_by_task(entries),
                                        storage.done_by_task(entries))
        except Exception:      # 設定還沒填完整時不要害整個分頁開不起來
            return []

    def _refresh_held(self):
        """到期日集合變了才重建，不然使用者填到一半切個分頁就被洗掉。"""
        pools = self._held_pools()
        expiries = tuple(expire for expire, _amount in pools)
        if expiries == self._held_expiries:
            for row, (_expire, amount) in zip(self._held_rows, pools):
                row["hint"].config(text=f"留白＝沿用推算 {amount}")
                row["estimate"] = amount
            return
        self._held_expiries = expiries
        for child in self._held.winfo_children():
            child.destroy()
        self._held_rows = []
        if not pools:
            self._held.grid_remove()
            return
        self._held.grid()
        for index, denom in enumerate(STAMINA_ITEMS):
            ttk.Label(self._held, text=f"{denom}×", foreground="#666666").grid(
                row=0, column=index + 1, padx=(dp(6), 0))
        first_day = self._today()
        for line, (expire, amount) in enumerate(pools, start=1):
            # 今天就到期的那一池最要命——沒用掉就是蒸發，排程會拼命想燒掉它
            soon = "（今晚到期）" if expire == first_day else ""
            row = {"expire": expire, "estimate": amount, "vars": {}}
            ttk.Label(self._held, text=f"到期 {expire:%m/%d}{soon}").grid(
                row=line, column=0, sticky="w", padx=(0, dp(6)), pady=dp(2))
            for index, key in enumerate(ITEM_KEYS):
                var = tk.StringVar()
                ttk.Entry(self._held, textvariable=var, width=5,
                          justify="center").grid(row=line, column=index + 1,
                                                 padx=(dp(6), 0), pady=dp(2))
                row["vars"][key] = var
            hint = ttk.Label(self._held, text=f"留白＝沿用推算 {amount}",
                             foreground="#666666")
            hint.grid(row=line, column=len(ITEM_KEYS) + 1, sticky="w", padx=(dp(12), 0))
            row["hint"] = hint
            ttk.Button(self._held, text="已用完", width=7,
                       command=lambda r=row: self._held_zero(r)).grid(
                row=line, column=len(ITEM_KEYS) + 2, padx=(dp(10), 0))
            self._held_rows.append(row)

    @staticmethod
    def _held_zero(row):
        """「這批用完了」——填 0 跟留白意義不同，給個按鈕就不必去想規則。"""
        for var in row["vars"].values():
            var.set("0")

    def held_values(self) -> dict:
        """{到期日: 手上還有幾點}。整列留白的不放進去（＝沿用推算）。"""
        out = {}
        for row in self._held_rows:
            raw = {key: var.get().strip() for key, var in row["vars"].items()}
            if not any(raw.values()):
                continue
            counts = {}
            for denom, key in zip(STAMINA_ITEMS, ITEM_KEYS):
                text = raw.get(key) or ""
                if text:
                    counts[key] = parse_int(
                        text, f"到期 {row['expire']:%m/%d} 的 {denom} 點道具", 0)
            out[row["expire"]] = items_total(counts)
        return out

    def show_stored_report(self):
        """顯示上次存下來的分析結果，免得為了看結論又重跑一次求解。"""
        plan = self.app.stored_plan() or {}
        report = plan.get("report")
        if not report:
            self._set_extras("")
            self._write("還沒算過排程。\n\n"
                        "填好上方的「目前體力」與「查詢時間」後按「開始計算」。")
            return
        self._set_extras(plan.get("extras") or "")
        when = (plan.get("computed_at") or "")[:16].replace("T", " ")
        stale = self.app.plan_stale_note()
        self._write((f"{stale}\n\n" if stale else "") + f"（以下是 {when} 算出的結果；條件有改動的話請重新計算）\n\n"
                    + report)

    def collect(self) -> bool:
        return True

    def _set_extras(self, text: str):
        self._extras_text = text or ""
        self.extras_button.config(state="normal" if self._extras_text else "disabled")

    def show_extras(self):
        if self._extras_text:
            CopyTextDialog(self, "打法歸納與提醒", self._extras_text)

    def _write(self, text: str):
        self.output.configure(state="normal")
        self.output.delete("1.0", "end")
        self.output.insert("1.0", text)
        self.output.configure(state="disabled")

    def run(self):
        if self._solving:
            return
        if not self.app.collect_all():
            return
        # 啟動時修過一次還不夠：開著的期間改了關卡積分，目前積分就又跟紀錄脫節了。
        # 放在 save_all 前面，修正後的值才會一併存檔。沒有分頁的 collect() 會寫
        # 這幾個欄位，所以 save_all 裡再 collect 一次也不會蓋回去。
        if self.app.sync_derived_from_log():
            self.app.refresh_derived_fields()
        if not self.app.save_all(silent=True):
            return
        if self.app.last_shared_sync == "reloaded":
            # 不要拿使用者還沒看過的新設定直接算
            messagebox.showinfo(
                "共用設定已更新",
                "共用設定剛被其他視窗更新，已重新載入。\n請確認內容後再按一次。",
                parent=self)
            return
        # 還沒有每日紀錄：活動可能已經進行一段時間，先把遊戲裡現在的進度補上
        if (self.app.needs_start_progress()
                and not StartProgressDialog(self.app, from_compute=True).proceed):
            return

        try:
            stamina = parse_int(self.stamina_var.get(), "目前體力", 0)
        except FieldError as exc:
            messagebox.showerror("輸入有誤", str(exc), parent=self)
            return
        try:
            query_dt = datetime.strptime(self.time_var.get().strip(), "%Y-%m-%d %H:%M")
        except ValueError:
            messagebox.showerror("輸入有誤",
                                 "「查詢時間」格式需為 YYYY-MM-DD HH:MM", parent=self)
            return
        until_text = self.until_var.get().strip()
        try:
            plan_until = (datetime.strptime(until_text, "%Y-%m-%d").date()
                          if until_text else None)
        except ValueError:
            messagebox.showerror("輸入有誤",
                                 "「排到」格式需為 YYYY-MM-DD"
                                 f"（例如 {example_date('%Y-%m-%d', days=7)}）",
                                 parent=self)
            return
        try:
            held = self.held_values()
            tokens = self.token_values()
        except FieldError as exc:
            messagebox.showerror("輸入有誤", str(exc), parent=self)
            return
        self._apply_tokens(tokens)
        missing = scheduler.events_missing_bonus(self.app.shared, self.app.profile, query_dt)
        if missing:
            messagebox.showerror(
                "活動加成還沒填",
                f"「{self.app.profile.get('profile_name') or self.app.profile_id}」"
                "這幾檔當期活動的活動加成是 0 或空白：\n"
                + "\n".join(f"　{name}" for name in missing)
                + "\n\n當期活動一定有加成，漏填會把每關積分算成基礎分、多排很多體力。"
                "\n請到「活動設定」選那一檔填好「活動加成」再計算。"
                "\n（這檔真的不吃加成的話，取消勾選「這檔活動套用活動加成」）",
                parent=self)
            return
        missing = scheduler.events_missing_points_cap(self.app.shared, query_dt)
        if missing:
            messagebox.showerror(
                "積分上限還沒填",
                "這幾檔當期／復刻活動的「積分上限」是空白：\n"
                + "\n".join(f"　{name}" for name in missing)
                + "\n\n沒填的話排程以為分數拿不滿，會為了多拿分一直排計分關卡。"
                "\n請到「活動設定」選那一檔填好「積分上限」再計算。",
                parent=self)
            return

        # 重新按「開始計算」＝從頭算，先前對調的日期不帶過來
        self._start_solve((stamina, query_dt, held, plan_until), None)

    def _start_solve(self, inputs, pinned):
        """inputs 是 (體力, 查詢時間, 限時體力, 排到)；pinned 是手動鎖定的日子。"""
        stamina, query_dt, held, plan_until = inputs
        # 求解可能要花上幾十秒。放在背景執行緒跑，否則視窗會整個凍住，
        # 看起來就像當掉了。傳入深拷貝，免得使用者在計算途中改欄位影響結果。
        self._solving = True
        self._sync_pending_buttons()
        # 計算中這顆按鈕就是「停止計算」；下面的報告區保持原本的內容，
        # 進度寫在狀態列（見 _poll）
        self.run_button.config(state="normal", text="停止計算", command=self.stop)
        self.app.set_status(self._progress_text(0, ""))
        # key：這次是替哪個帳號／哪幾檔活動算的。算完時對不上就不能收
        holder: dict = {"inputs": inputs, "pinned": pinned,
                        "key": self._loaded_key, "cancel": threading.Event()}
        self._holder = holder
        thread = threading.Thread(
            target=self._solve_worker,
            args=(copy.deepcopy(self.app.shared), copy.deepcopy(self.app.profile),
                  stamina, query_dt, self.app.log_entries(), held, plan_until,
                  pinned, holder),
            daemon=True)
        self._started_at = time.monotonic()
        thread.start()
        self._poll(thread, holder)

    @staticmethod
    def _solve_worker(shared, profile, stamina, query_dt, entries, held,
                      plan_until, pinned, holder):
        """在背景執行緒裡求解；例外一律收進 holder，不讓執行緒直接爆掉。"""
        cancel = holder["cancel"]

        def progress(text):
            # 每個求解階段開始時都會叫到這裡：按了「停止計算」就在這裡收工
            if cancel.is_set():
                raise _SolveCancelled()
            # 只寫進 holder，畫面由 _poll 在主執行緒讀出來顯示
            holder["stage"] = text

        try:
            holder["result"] = scheduler.compute_plan(
                shared, profile, stamina, query_dt, log_entries=entries,
                held_by_expiry=held or None, plan_until=plan_until,
                pinned=pinned or None, progress=progress)
        except _SolveCancelled:
            pass
        except scheduler.PlanError as exc:
            holder["error"] = f"無法計算：\n\n{exc}"
        except Exception:  # pragma: no cover - 意外錯誤也要看得到原因
            if not cancel.is_set():     # 停止時砍掉求解器會讓 PuLP 丟錯，那不算錯誤
                holder["error"] = "計算時發生未預期的錯誤：\n\n" + traceback.format_exc()

    @staticmethod
    def _progress_text(elapsed: float, stage) -> str:
        """計算中的狀態列：第一行固定是可以中斷的提示，第二行才是會變的進度。

        寫成一行、放不下才折的話，進度字數一變就會在一行和兩行之間跳來跳去。
        """
        # 階段名稱可能帶換行（「放寬目標重算：\n第二階段」），進度只佔一行
        stage = " ".join((stage or "準備中").split())
        return (f"計算中…（可以按「停止計算」中止）\n"
                f"已經過 {elapsed:.0f} 秒　目前：{stage}")

    def stop(self):
        """停止計算：這次的結果不收，並結束正在跑的求解器。"""
        holder = getattr(self, "_holder", None)
        if not self._solving or holder is None or holder["cancel"].is_set():
            return
        holder["cancel"].set()
        # 背景執行緒真的結束之前不能再按：求解器的暫存檔名是固定的，
        # 新舊兩次同時跑會互相蓋掉（見 scheduler._remove_solver_files）
        self.run_button.config(state="disabled", text="停止中…")
        self.app.set_status("正在停止計算…")
        kill_solver_processes()

    # -- 還沒存入的結果 ---------------------------------------------------
    PENDING_NOTE = ("（這份結果還沒存入——按上方「存入計畫」才會更新每日紀錄與今日待辦；"
                    "想把某兩天的打法互換，按「對調日期…」）\n\n")

    def _sync_pending_buttons(self):
        state = ("normal" if self._pending is not None and not self._solving
                 else "disabled")
        for button in (self.save_button, self.swap_button, self.discard_button):
            button.config(state=state)

    def _show_pending(self):
        self._set_extras(scheduler.format_extras(self._pending))
        self._write(self.PENDING_NOTE + scheduler.format_result(self._pending))

    def save_pending(self):
        """把預覽中的結果存下來，「每日紀錄」才看得到每天該打什麼。"""
        if self._pending is None:
            return
        result = self._pending
        self._pending = self._pending_inputs = None
        self._sync_pending_buttons()
        self.app.last_plan = result
        self.app.save_plan(result)
        self._set_extras(scheduler.format_extras(result))
        self._write(scheduler.format_result(result))
        self.app.set_status("計畫已存入每日紀錄")

    def discard_pending(self):
        if self._pending is None:
            return
        self._pending = self._pending_inputs = None
        self._sync_pending_buttons()
        self.show_stored_report()
        self.app.set_status("已放棄這次的計算結果")

    def swap_days(self):
        """對調日期：選好之後把那幾天鎖住，其餘日子重新求解。"""
        if self._pending is None or self._solving:
            return
        dialog = SwapDaysDialog(self, self._pending)
        if dialog.result is None:
            return
        self._start_solve(self._pending_inputs, dialog.result)

    def _poll(self, thread, holder):
        if thread.is_alive():
            if not holder["cancel"].is_set():
                elapsed = time.monotonic() - self._started_at
                self.app.set_status(self._progress_text(elapsed, holder.get("stage")))
            self.after(200, lambda: self._poll(thread, holder))
            return

        self._solving = False
        self.run_button.config(state="normal", text="開始計算", command=self.run)
        if holder["cancel"].is_set():
            # 報告區本來就沒被蓋掉；停止前有預覽的話，它跟三顆按鈕都還在
            self._sync_pending_buttons()
            self.app.set_status("已停止計算")
            return
        if holder["key"] != self._loaded_key:
            # 計算途中換了帳號（或活動的起訖日）：這份結果是替上一個帳號算的，
            # 收下來的話「存入計畫」會把它寫進現在這個帳號的紀錄。
            self._pending = self._pending_inputs = None
            self._sync_pending_buttons()
            self.show_stored_report()
            self.app.set_status("計算途中換了帳號或活動，那次的結果已丟棄，請重新計算")
            return
        if "error" in holder:
            if holder["pinned"] and self._pending is not None:
                # 對調之後算不出來：原本那份結果還在，別把畫面洗成錯誤訊息
                self._show_pending()
                self._sync_pending_buttons()
                self.app.set_status("對調後算不出來，保留調整前的結果")
                messagebox.showerror("對調後算不出來", holder["error"], parent=self)
                return
            self._pending = self._pending_inputs = None
            self._sync_pending_buttons()
            self._set_extras("")
            self._write(holder["error"])
            self.app.set_status("計算失敗")
            self._announce_done("計算失敗", "這次沒有算出排程，原因寫在「計算結果」頁。",
                                icon="warning")
            return
        elapsed = time.monotonic() - self._started_at
        # 先不存：停在預覽，讓使用者有機會對調日期（見 save_pending）
        self._pending = holder["result"]
        self._pending_inputs = holder["inputs"]
        self._sync_pending_buttons()
        self._show_pending()
        self.app.set_status(f"計算完成（耗時 {elapsed:.1f} 秒），尚未存入")
        self._announce_done("計算完成", f"排程算好了（耗時 {elapsed:.0f} 秒）。\n\n"
                                        "結果還沒存入：看過沒問題，請按「存入計畫」。")

    def _announce_done(self, title: str, message: str, icon: str = "info",
                       _waiting: bool = False) -> None:
        """算完跳一個訊息框，免得使用者不知道跑完了。

        計算期間可以自由切去別的分頁；算完不會自動跳頁，而是問要不要切過來看，
        使用者正在看的那一頁不會被打斷。視窗不在最前面時工作列會閃。
        正開著別的對話框（例如在編輯紀錄）時先等它關掉，不然會搶走它的控制權。
        """
        try:
            busy = self.grab_current() is not None
        except (KeyError, tk.TclError):
            busy = False        # 正在關的對話框，Tk 找不到它的元件
        if busy:
            self.after(500, lambda: self._announce_done(title, message, icon,
                                                        _waiting))
            return
        # 主視窗縮在工作列時，它的座標在螢幕外很遠（Windows 放在 -32000），照它置中
        # 會被夾到螢幕左上角。先閃工作列，等使用者把主視窗叫回來才跳訊息框
        try:
            minimized = self.winfo_toplevel().state() == "iconic"
        except tk.TclError:
            minimized = False
        if minimized:
            if not _waiting:
                flash_if_inactive(self)
            self.after(500, lambda: self._announce_done(title, message, icon,
                                                        _waiting=True))
            return
        if not _waiting:
            flash_if_inactive(self)
        if self.app.notebook.select() == str(self):
            if icon == "warning":
                messagebox.showwarning(title, message, parent=self)
            else:
                messagebox.showinfo(title, message, parent=self)
            return
        if messagebox.askyesno(title, message + "\n\n要切到「計算結果」頁看嗎？",
                               icon=icon, parent=self):
            self.app.notebook.select(self)


class SharedSettingsDialog(tk.Toplevel):
    """「設定」選單開出來的共用設定視窗的底子。

    開窗時從 app.shared 讀值，按「確定」才寫回並存檔；按取消或 Esc 什麼都不動。
    子類別實作 _build(body)、_load()、_apply() -> bool（回 False＝輸入有誤、不關窗）。
    """

    def __init__(self, app, title: str):
        super().__init__(app)
        hide_until_centered(self)
        self.app = app
        self.title(title)

        outer = ttk.Frame(self, padding=dp(12))
        outer.pack(fill="both", expand=True)
        # 按鈕先排在最底下、放在捲動區外面：對話框拉得再小都按得到
        buttons = ttk.Frame(outer)
        buttons.pack(side="bottom", anchor="e", pady=(dp(14), 0))
        ttk.Button(buttons, text="確定", command=self._on_ok).pack(
            side="left", padx=(0, dp(6)))
        ttk.Button(buttons, text="取消", command=self.destroy).pack(side="left")
        self.scroller = ScrollableFrame(outer, fill_height=True)
        self.scroller.pack(fill="both", expand=True)
        body = self.scroller.inner
        body.columnconfigure(0, weight=1)

        self._build(body)
        self._load()
        self.scroller.wrap_long_labels()
        self.scroller.request_natural_size(max_height=px(560))

        self.bind("<Escape>", lambda _e: self.destroy())
        self.transient(app)
        center_on(self, app)
        run_modal(self)

    def _build(self, body):
        raise NotImplementedError

    def _load(self):
        raise NotImplementedError

    def _apply(self) -> bool:
        raise NotImplementedError

    def _on_ok(self):
        if not self._apply():
            return
        title = self.title()        # 關窗後就讀不到了
        self.destroy()
        self.app.save_all(silent=True)
        self.app.set_status(f"已更新「{title}」（{datetime.now():%H:%M:%S}）")


class ClocksDialog(SharedSettingsDialog):
    """重置與回復：只有上線時段能改，回復速率與重置時刻是程式寫死的（storage.fixed_clocks）。"""

    def __init__(self, app):
        self.act_start_var = tk.StringVar()
        self.act_end_var = tk.StringVar()
        super().__init__(app, "重置與回復")

    def _build(self, box):
        ttk.Label(box, text="所有帳號共用").grid(row=0, column=0, sticky="w",
                                                pady=(0, dp(8)))
        clocks = ttk.Frame(box)
        clocks.grid(row=1, column=0, sticky="w")
        for label, var in (("上線時段　自", self.act_start_var),
                           ("至", self.act_end_var)):
            ttk.Label(clocks, text=label).pack(side="left", padx=(0, dp(6)))
            ttk.Entry(clocks, textvariable=var, width=8).pack(side="left", padx=(0, dp(16)))
        ttk.Label(box, text="格式 HH:MM。上線時段以外只累積自然回復、不打關卡",
                  foreground="#666666").grid(row=2, column=0, sticky="w", pady=(dp(6), 0))

        rate = storage.RECOVERY_RATE_PER_5MIN
        reset = storage.DAILY_RESET_TIME
        weekday = dict(WEEKDAY_CHOICES)[storage.WEEKLY_RESET_WEEKDAY]
        ttk.Label(box, text=(
            f"自然回復：每 5 分鐘 {rate} 點（一天 {rate * scheduler.TICKS_PER_DAY} 點）\n"
            f"每日任務、公會任務：每天 {reset} 重置\n"
            f"每週任務：每{weekday} {reset} 重置\n"
            f"每月任務：每月 {storage.MONTHLY_RESET_DAY} 號 {reset} 重置"),
            justify="left").grid(row=3, column=0, sticky="w", pady=(dp(14), 0))
        ttk.Label(box, text="以上是遊戲固定的規則，不能修改",
                  foreground="#666666").grid(row=4, column=0, sticky="w", pady=(dp(6), 0))

    def _load(self):
        window = self.app.shared.get("active_window") or {}
        self.act_start_var.set(window.get("start") or "06:00")
        self.act_end_var.set(window.get("end") or "21:30")

    def _apply(self) -> bool:
        clocks = {}
        for key, var, label in (("start", self.act_start_var, "上線時段開始"),
                                ("end", self.act_end_var, "上線時段結束")):
            text = var.get().strip()
            try:
                datetime.strptime(text, "%H:%M")
            except ValueError:
                messagebox.showerror(
                    "輸入有誤", f"「{label}」格式需為 HH:MM（例如 06:00）：{text}", parent=self)
                return False
            clocks[key] = text
        self.app.shared["active_window"] = {"start": clocks["start"], "end": clocks["end"]}
        return True


class RoutineTasksDialog(EventDateMixin, TaskEditorMixin, SharedSettingsDialog):
    """任務清單：每日／每週／每月／公會的固定任務，所有帳號共用。"""

    def __init__(self, app):
        super().__init__(app, "任務清單")

    def _build(self, box):
        box.rowconfigure(1, weight=1)
        ttk.Label(box, text="跟哪一檔活動無關，所有帳號共用同一份清單；"
                            "各帳號可以在「任務進度」調整數字或停用。"
                            "獎勵裡的體力會自動變成排程可用的體力來源；"
                            "上移／下移只排順序，不會改變要打什麼",
                  foreground="#666666").grid(row=0, column=0, sticky="w", pady=(0, dp(6)))
        self.task_editor = self._task_editor(box, height=12)
        self.task_editor.grid(row=1, column=0, sticky="nsew")

    def _default_task(self, records):
        return {"id": storage.next_task_id(records, "r"),
                "name": "新任務", "cycle": "daily", "metric": "clears",
                "amount": 10, "deadline_offset": -1, "enforce": True,
                "assume_done": False, "scope": [], "reward_weekday": 6,
                "reward_days": list(DEFAULT_MONTH_DAYS)}

    def _load(self):
        self.task_editor.set_specs(self._task_specs)
        self.task_editor.set_records([
            self._task_from_json(task)
            for task in self.app.shared.get("routine_tasks") or []])

    def _apply(self) -> bool:
        try:
            tasks = [self._task_to_json(r) for r in self.task_editor.get_records()]
        except (FieldError, ValueError) as exc:
            messagebox.showerror("輸入有誤", str(exc), parent=self)
            return False
        # 「任務進度」一個任務一列：先把那張表還沒存的編輯收回帳號，再換清單、重建
        routine = [tab for tab, _label in self.app.tabs if isinstance(tab, RoutineTab)]
        for tab in routine:
            tab.collect()
        self.app.shared["routine_tasks"] = tasks
        for tab in routine:
            tab._load_states()
        return True


class ItemsDialog(SharedSettingsDialog):
    """獎勵道具：任務獎勵可以選的道具，填了體力值的會被當成體力來源。"""

    def __init__(self, app):
        super().__init__(app, "獎勵道具")

    def _build(self, box):
        ttk.Label(box, text="「體力值」填了幾點，這個道具才會被當成體力來源",
                  foreground="#666666").grid(row=0, column=0, sticky="w", pady=(0, dp(6)))
        self.item_editor = ListEditor(
            box,
            columns=[("name", "道具名稱", 160, "w"),
                     ("stamina", "體力值", 80, "e")],
            specs=[
                {"key": "name", "label": "道具名稱", "type": "str"},
                {"key": "stamina", "label": "體力值", "type": "int", "minimum": 0,
                 "hint": "一個這種道具值幾點體力；不是體力的填 0"},
            ],
            to_row=lambda r: (r.get("name", ""), r.get("stamina", 0)),
            make_default=lambda records: {
                "id": storage.next_item_id(records), "name": "新道具",
                "stamina": 0},
            height=8,
            auto_width=True,
        )
        # 表格跟著視窗拉寬（多出來的寬度給道具名稱），按鈕靠右
        self.item_editor.grid(row=1, column=0, sticky="nsew")
        self.item_editor.tree.column("name", stretch=True)
        box.rowconfigure(1, weight=1)

    def _load(self):
        self.item_editor.set_records(self.app.shared.get("items") or [])

    def _apply(self) -> bool:
        self.app.shared["items"] = [
            {"id": r.get("id") or storage.next_item_id([]),
             "name": r.get("name", ""),
             "stamina": int(r.get("stamina") or 0)}
            for r in self.item_editor.get_records()]
        # 道具清單一改，用到獎勵欄位的任務編輯器（活動設定）都要重建欄位
        for tab, _label in self.app.tabs:
            editor = getattr(tab, "task_editor", None)
            if editor is not None and hasattr(tab, "_task_specs"):
                editor.set_specs(tab._task_specs)
                editor.refresh()
        return True


class TypeDefaultsDialog(SharedSettingsDialog):
    """活動類型預設：當期、復刻的預設關卡結構與活動任務（所有帳號共用）。

    「新增活動」「套用類型預設」「第一次執行」建出來的當期／復刻都照這張表
    （storage.type_defaults）。上面切換要改哪個類型，兩個類型改完一起按確定。
    """

    TYPES = [(key, storage.EVENT_TYPE_LABELS[key]) for key in storage.TEMPLATE_TYPES]

    def __init__(self, app):
        super().__init__(app, "活動類型預設")

    # -- 版面 --------------------------------------------------------------
    def _build(self, box):
        top = ttk.Frame(box)
        top.grid(row=0, column=0, sticky="we")
        ttk.Label(top, text="類型").pack(side="left", padx=(0, dp(6)))
        self.type_box = ttk.Combobox(top, state="readonly", width=10,
                                     values=[label for _k, label in self.TYPES])
        self.type_box.pack(side="left")
        self.type_box.bind("<<ComboboxSelected>>", self._on_type_selected)
        ttk.Button(top, text="還原成內建預設", command=self._restore_builtin).pack(
            side="left", padx=(dp(12), 0))
        ttk.Label(box, text="「新增活動」「套用類型預設」建出來的活動，關卡與任務都從這裡來。"
                            "已經建好的活動不會跟著改。",
                  foreground="#666666").grid(row=1, column=0, sticky="w", pady=(dp(4), dp(8)))

        opts = ttk.Frame(box)
        opts.grid(row=2, column=0, sticky="w", pady=(0, dp(8)))
        self.bonus_var = tk.BooleanVar()
        ttk.Checkbutton(opts, text="套用活動加成", variable=self.bonus_var).pack(side="left")
        ttk.Label(opts, text="積分上限").pack(side="left", padx=(dp(20), dp(6)))
        self.cap_var = tk.StringVar()
        ttk.Entry(opts, textvariable=self.cap_var, width=8).pack(side="left")
        ttk.Label(opts, text="留白＝不帶（套用到既有活動時，那檔已經有值就不蓋）",
                  foreground="#666666").pack(side="left", padx=(dp(8), 0))

        ttk.Label(box, text="關卡結構").grid(row=3, column=0, sticky="w")
        self.level_editor = ListEditor(
            box,
            columns=[("name", "關卡名稱", 120, "w"),
                     ("cost", "體力", 50, "e"),
                     ("enemies", "敵人", 50, "e"),
                     ("kind", "類型", 70, "center"),
                     ("base", "基礎積分", 70, "e"),
                     ("rule", "開放／次數", 180, "w")],
            specs=self._level_specs,
            to_row=self._level_row,
            make_default=lambda records: {
                "name": default_level_name(records), "stamina_cost": 10, "enemies": 0,
                "drops": 0, "kind": "scoring", "base_points": None,
                "unlock_first": True, "open_day": None, "max_total": None,
                "must_finish": False, "same_day": False},
            reorderable=True, height=7, auto_width=True, validate=check_level_name)
        self.level_editor.grid(row=4, column=0, sticky="nsew", pady=(dp(2), dp(10)))

        ttk.Label(box, text="活動任務").grid(row=5, column=0, sticky="w")
        self.task_editor = ListEditor(
            box,
            columns=[("name", "任務名稱", 120, "w"),
                     ("metric", "條件", 80, "w"),
                     ("amount", "數量", 70, "e"),
                     ("deadline", "期限", 80, "w"),
                     ("rewards", "獎勵", 140, "w")],
            specs=self._task_specs,
            to_row=self._task_row,
            make_default=lambda records: {
                "name": storage.EVENT_TASK_NAME, "metric": "points", "amount": 0,
                "deadline_offset": -1, "enforce": True, "assume_done": False,
                **record_from_rewards([], self._items())},
            reorderable=True, height=8, auto_width=True)
        self.task_editor.grid(row=6, column=0, sticky="nsew", pady=(dp(2), 0))
        box.rowconfigure(4, weight=1)
        box.rowconfigure(6, weight=1)

    def _items(self):
        return self.app.shared.get("items") or []

    # -- 關卡 --------------------------------------------------------------
    def _level_specs(self, record):
        specs = [
            {"key": "name", "label": "關卡名稱", "type": "str"},
            {"key": "stamina_cost", "label": "消耗體力", "type": "int", "minimum": 1,
             "hint": "套用到既有活動時，計分關卡照這個數字對上那檔的關卡"},
            {"key": "enemies", "label": "敵人人數", "type": "int", "minimum": 0},
            {"key": "drops", "label": "取得道具", "type": "int", "minimum": 0},
            {"key": "kind", "label": "類型", "type": "choice", "choices": LEVEL_KIND_CHOICES,
             "rebuild": True,
             "hint": "不計分的關卡（活動BOSS）套用到既有活動時，那檔沒有同名的才補上"},
        ]
        if record.get("kind", "scoring") == "scoring":
            specs.append({"key": "base_points", "label": "基礎積分", "type": "opt_int",
                          "minimum": 0, "hint": "沒有活動加成的原始積分；留白＝積分自己填"})
        specs += [
            {"key": "unlock_first", "label": "開場先打一次", "type": "bool",
             "hint": "解鎖鏈：照消耗體力由小到大各先打一次"},
            {"key": "open_day", "label": "第幾天開放", "type": "opt_int", "minimum": 1,
             "hint": "1＝活動起始日當天，8＝起始日後第 7 天；留白＝整檔活動都能打"},
            {"key": "max_total", "label": "總共最多幾次", "type": "opt_int", "minimum": 1,
             "hint": "整檔活動的總次數；留白＝沒有上限"},
            {"key": "must_finish", "label": "一定要打滿", "type": "bool"},
            {"key": "same_day", "label": "同一天打完", "type": "bool"},
        ]
        return specs

    @staticmethod
    def _level_row(record):
        level = dict(record, available_from=TypeDefaultsDialog._offset_of(record))
        rule = level_summary(level).split("、", 2)[2:]       # 拿掉「N 體、類型」
        base = record.get("base_points")
        return (record.get("name", ""), record.get("stamina_cost", 0),
                record.get("enemies", 0), LEVEL_KIND_LABELS.get(level_kind_of(record), ""),
                "—" if not level_is_scoring(record) else ("-" if base is None else base),
                rule[0] if rule else "全期")

    @staticmethod
    def _offset_of(record):
        day = record.get("open_day")
        return None if day in (None, "") else int(day) - 1

    # -- 任務 --------------------------------------------------------------
    def _task_specs(self, record):
        manual = record.get("metric") == "manual"
        specs = [
            {"key": "name", "label": "任務名稱", "type": "str"},
            {"key": "metric", "label": "達成條件", "type": "choice",
             "choices": storage.TASK_METRICS, "rebuild": True},
        ]
        if not manual:
            specs.append({"key": "amount", "label": "需要數量", "type": "int", "minimum": 0})
        specs.append({"key": "deadline_offset", "label": "期限", "type": "day_ref"})
        if not manual:
            specs.append({"key": "enforce", "label": "算進排程計算", "type": "bool",
                          "default": True})
        specs.append({"key": "assume_done", "label": "預設完成", "type": "bool",
                      "default": manual})
        return specs + reward_specs(self._items())

    def _task_row(self, record):
        manual = record.get("metric") == "manual"
        offset = int(record.get("deadline_offset", -1))
        deadline = ("最後一天" if offset == -1 else
                    f"倒數第 {-offset} 天" if offset < 0 else f"第 {offset + 1} 天")
        return (record.get("name", ""),
                storage.TASK_METRIC_LABELS.get(record.get("metric"), ""),
                "—" if manual else record.get("amount", 0), deadline,
                reward_summary(record, self._items()))

    # -- 載入／切換／存 ------------------------------------------------------
    def _to_records(self, template):
        items = self._items()
        levels = [dict(level, kind=level_kind_of(level),
                       open_day=(None if level.get("available_from") is None
                                 else int(level["available_from"]) + 1))
                  for level in template["levels"]]
        tasks = [dict(task, **record_from_rewards(task.get("rewards"), items))
                 for task in template["tasks"]]
        return {"bonus_applies": template["bonus_applies"],
                "points_cap": template["points_cap"], "levels": levels, "tasks": tasks}

    def _load(self):
        self._data = {key: self._to_records(template)
                      for key, template in storage.type_defaults(self.app.shared).items()}
        self._type = self.TYPES[0][0]
        self.type_box.current(0)
        self._show(self._type)

    def _show(self, key):
        data = self._data[key]
        self.bonus_var.set(bool(data["bonus_applies"]))
        self.cap_var.set("" if data["points_cap"] is None else str(data["points_cap"]))
        self.level_editor.set_records(data["levels"])
        self.task_editor.set_records(data["tasks"])

    def _stash(self) -> bool:
        """畫面上這個類型的內容收回 self._data；積分上限填錯就回 False。"""
        try:
            cap = parse_opt_int(self.cap_var.get(), "積分上限", 0)
        except FieldError as exc:
            messagebox.showerror("輸入有誤", str(exc), parent=self)
            return False
        self._data[self._type] = {
            "bonus_applies": bool(self.bonus_var.get()), "points_cap": cap,
            "levels": self.level_editor.get_records(),
            "tasks": self.task_editor.get_records()}
        return True

    def _on_type_selected(self, _event=None):
        key = self.TYPES[self.type_box.current()][0]
        if key == self._type:
            return
        if not self._stash():
            self.type_box.current([k for k, _l in self.TYPES].index(self._type))
            return
        self._type = key
        self._show(key)

    def _restore_builtin(self):
        label = dict(self.TYPES)[self._type]
        if not messagebox.askyesno(
                "還原成內建預設",
                f"要把「{label}」的預設關卡、任務、加成與積分上限換回程式內建的嗎？\n"
                "（按確定之前都還可以取消）", parent=self):
            return
        self._data[self._type] = self._to_records(storage.builtin_type_defaults()[self._type])
        self._show(self._type)

    def _template_of(self, data) -> dict:
        items = self._items()
        levels = []
        for record in data["levels"]:
            scoring, counts = LEVEL_KIND_FLAGS[level_kind_of(record)]
            levels.append({
                "name": record.get("name", ""),
                "stamina_cost": int(record.get("stamina_cost") or 0),
                "enemies": int(record.get("enemies") or 0),
                "drops": int(record.get("drops") or 0),
                "scoring": scoring, "counts_clears": counts,
                "base_points": record.get("base_points") if scoring else None,
                "unlock_first": bool(record.get("unlock_first")),
                "available_from": self._offset_of(record),
                "max_total": record.get("max_total"),
                "must_finish": bool(record.get("must_finish")),
                "same_day": bool(record.get("same_day")),
                "group": None})
        tasks = []
        for record in data["tasks"]:
            metric = record.get("metric", "manual")
            tasks.append({
                "name": record.get("name", ""), "cycle": "event", "metric": metric,
                "amount": int(record.get("amount") or 0),
                "deadline_offset": int(record.get("deadline_offset", -1)),
                "enforce": bool(record.get("enforce", True)) and metric != "manual",
                "assume_done": bool(record.get("assume_done")),
                "rewards": rewards_from_record(record, items)})
        return storage.normalise_type_default({
            "bonus_applies": data["bonus_applies"], "points_cap": data["points_cap"],
            "levels": levels, "tasks": tasks})

    def _apply(self) -> bool:
        if not self._stash():
            return False
        self.app.shared["type_defaults"] = {
            key: self._template_of(data) for key, data in self._data.items()}
        return True


class PlayListDialog(tk.Toplevel):
    """一天之內的分筆紀錄：每一筆的時刻與打法，可新增／編輯／刪除。

    內部把一筆攤平成 `{TIME_KEY: "HH:MM", 關卡鍵: 次數, ...}`，ListEditor 的
    欄位規格才表達得出來；按確定時再折回 `{at, counts}`。
    """

    def __init__(self, parent, tab, date_str: str, plays: list):
        super().__init__(parent)
        hide_until_centered(self)
        self.title(f"{date_str} 分筆紀錄")
        self.result = None
        self._tab = tab
        self._date = date_str
        # 那天任何一筆記過的關卡都要留著，否則舊檔的數字編輯後會被弄丟
        self._keep = storage.counts_of_plays(plays)

        outer = ttk.Frame(self, padding=dp(12))
        outer.pack(fill="both", expand=True)
        # 按鈕先排在最底下、放在捲動區外面：對話框拉得再小都按得到
        buttons = ttk.Frame(outer)
        buttons.pack(side="bottom", anchor="e", pady=(dp(14), 0))
        ttk.Button(buttons, text="確定", command=self._on_ok).pack(
            side="left", padx=(0, dp(6)))
        ttk.Button(buttons, text="取消", command=self.destroy).pack(side="left")
        scroller = ScrollableFrame(outer, fill_height=True)
        scroller.pack(fill="both", expand=True)
        body = scroller.inner
        body.columnconfigure(0, weight=1)
        body.rowconfigure(1, weight=1)
        hint = ttk.Label(body, text="時刻決定「打的當下哪幾檔活動開著」。"
                                    "留白＝不知道什麼時候打的，排程會退回用整天估。",
                         foreground="#666666")
        hint.grid(row=0, column=0, sticky="w", pady=(0, dp(8)))
        scroller.wrap_label(hint)

        self.editor = ListEditor(
            body,
            columns=[("at", "時間", 70, "center"),
                     ("what", "打法", 320, "w"),
                     ("clears", "關數", 55, "e"),
                     ("stamina", "耗體", 65, "e")],
            specs=self._specs(),
            to_row=self._row,
            make_default=lambda _records: {
                TIME_KEY: datetime.now().strftime("%H:%M")},
            reorderable=False,
            height=10,
        )
        self.editor.grid(row=1, column=0, sticky="nsew")
        self.editor.set_records([self._flatten(play) for play in plays])
        scroller.request_natural_size()

        self.bind("<Escape>", lambda _e: self.destroy())
        self.transient(parent)
        center_on(self, parent)
        run_modal(self)

    # -- 一筆 <-> 攤平 ----------------------------------------------------
    def _specs(self):
        specs = [{"key": TIME_KEY, "label": "時間", "type": "time",
                  "hint": "HH:MM（例如 15:00）"}]
        specs += [{"key": level["key"],
                   "label": self._tab._level_label(level),
                   "type": "int", "minimum": 0, "default": 0}
                  for level in self._tab._levels_on(self._date, self._keep)]
        return specs

    def _flatten(self, play: dict) -> dict:
        record = {TIME_KEY: self._tab._clock_of(play.get("at"))}
        record.update(play.get("counts") or {})
        return record

    @staticmethod
    def _counts_of(record: dict) -> dict:
        return {key: int(value) for key, value in record.items()
                if key != TIME_KEY and int(value or 0) > 0}

    def _row(self, record):
        counts = self._counts_of(record)
        text, clears, stamina, _points = self._tab._describe(counts)
        return (record.get(TIME_KEY) or "—", text or "（沒打）", clears, stamina)

    def _on_ok(self):
        plays = []
        for record in self.editor.get_records():
            counts = self._counts_of(record)
            if not counts:
                continue        # 沒打什麼的那一筆直接丟掉
            at = self._tab._moment_iso(self._date, record[TIME_KEY])
            plays.append({"at": at, "counts": counts})
        self.result = plays
        self.destroy()


class ClaimReminderDialog(tk.Toplevel):
    """今天該領的信箱／任務獎勵體力（依存入的計畫）。勾了按確定＝已領取。

    `result` 是勾選的那幾筆的 ref 清單；按「稍後」或關掉是 None。
    """

    def __init__(self, parent, claims: list[dict]):
        super().__init__(parent)
        hide_until_centered(self)
        self.title("今天要領的體力")
        self.result = None
        outer = ttk.Frame(self, padding=dp(14))
        outer.pack(fill="both", expand=True)
        # 按鈕放在捲動區外面：對話框拉得再小都按得到
        buttons = ttk.Frame(outer)
        buttons.pack(side="bottom", anchor="e", pady=(dp(12), 0))
        ttk.Button(buttons, text="確定", command=self._ok).pack(side="left", padx=dp(4))
        ttk.Button(buttons, text="稍後", command=self.destroy).pack(side="left")
        scroller = ScrollableFrame(outer, fill_height=True)
        scroller.pack(fill="both", expand=True)
        body = scroller.inner
        hint = ttk.Label(body, text="照存入的計畫，這幾筆今天（或更早）該領了。"
                                    "領好的勾起來按「確定」，就會記成已領取：")
        hint.pack(anchor="w", pady=(0, dp(8)))
        scroller.wrap_label(hint)
        self._vars = []
        for claim in claims:
            var = tk.BooleanVar(value=False)
            self._vars.append((var, claim))
            check = ttk.Checkbutton(body, variable=var, text=self._describe(claim))
            check.pack(anchor="w", pady=dp(2))
            scroller.wrap_label(check)
        scroller.request_natural_size(max_height=self.winfo_screenheight() - dp(200))
        self.bind("<Escape>", lambda _e: self.destroy())
        self.transient(parent)
        center_on(self, parent)
        run_modal(self)

    @staticmethod
    def _describe(claim) -> str:
        def md(text):
            return f"{text[5:7]}/{text[8:10]}" if text else "?"
        expire = f"，{md(claim.get('expire'))} 到期" if claim.get("expire") else ""
        return (f"{claim['label']} {claim['amount']} 點　建議 {md(claim['claim_day'])} 領"
                f"{expire}（最晚 {md(claim.get('deadline'))} 要領）")

    def _ok(self):
        self.result = [claim["ref"] for var, claim in self._vars if var.get()]
        self.destroy()


class TargetAnalysisDialog(tk.Toplevel):
    """活動目標分析的結果視窗（純文字報表，唯讀）。"""

    def __init__(self, parent, text: str):
        super().__init__(parent)
        hide_until_centered(self)
        self.title("活動目標分析")
        outer = ttk.Frame(self, padding=dp(12))
        outer.pack(fill="both", expand=True)
        # 文字會自動折行，對話框拉小時讓文字框跟著變窄就好，不需要橫向捲軸。
        # 捲軸要先排：pack 空間不夠時先犧牲後排的，後排的捲軸會被擠掉
        box = tk.Text(outer, width=78, height=26, font=report_font())
        bar = ttk.Scrollbar(outer, orient="vertical", command=box.yview)
        bar.pack(side="right", fill="y")
        box.pack(side="left", fill="both", expand=True)
        box.configure(yscrollcommand=bar.set)
        fill_wrapped_text(box, text)
        box.configure(state="disabled")
        self.bind("<Escape>", lambda _e: self.destroy())
        self.transient(parent)
        center_on(self, parent)
        run_modal(self)


class CopyTextDialog(tk.Toplevel):
    """顯示一段純文字讓人複製（可以反白，也可以按「複製全部」）。"""

    def __init__(self, parent, title: str, text: str):
        super().__init__(parent)
        hide_until_centered(self)
        self.title(title)
        self._text = text
        outer = ttk.Frame(self, padding=dp(12))
        outer.pack(fill="both", expand=True)
        buttons = ttk.Frame(outer)
        buttons.pack(side="bottom", fill="x", pady=(dp(8), 0))
        self.status = ttk.Label(buttons, text="", foreground="#0a5")
        self.status.pack(side="left")
        ttk.Button(buttons, text="關閉", command=self.destroy).pack(side="right")
        ttk.Button(buttons, text="複製全部", command=self._copy).pack(
            side="right", padx=(0, dp(6)))
        lines = text.splitlines() or [""]
        box = tk.Text(outer, font=report_font(),
                      width=max(40, min(80, max(scheduler.text_width(l) for l in lines) + 2)),
                      height=max(6, min(30, len(lines) + 1)))
        bar = ttk.Scrollbar(outer, orient="vertical", command=box.yview)
        bar.pack(side="right", fill="y")
        box.pack(side="left", fill="both", expand=True)
        box.configure(yscrollcommand=bar.set)
        fill_wrapped_text(box, text)
        # 唯讀但仍可反白複製：disabled 在 Windows 上也能選取與 Ctrl+C
        box.configure(state="disabled")
        self.bind("<Escape>", lambda _e: self.destroy())
        self.transient(parent)
        center_on(self, parent)
        run_modal(self)

    def _copy(self):
        self.clipboard_clear()
        self.clipboard_append(self._text)
        self.status.config(text="已複製 ✓")


class SwapDaysDialog(tk.Toplevel):
    """對調日期：把求解器排的打法以「天」為單位互換。

    這裡只決定「哪幾天要照什麼打」，不自己算體力——按「套用並重算」之後，
    被動過的日子交給 `compute_plan(pinned=...)` 鎖住，其餘日子重新求解。
    `result` 是 `{日期: {關卡鍵: 次數}}`；沒有任何變動或按取消時是 None。
    """

    def __init__(self, parent, plan: dict):
        super().__init__(parent)
        hide_until_centered(self)
        self.title("對調日期")
        self.result = None
        self._levels = plan["levels"]
        self._days = [row["date"] for row in plan["schedule"]]
        self._playable = plan["playable"]
        self._done_label = plan["done_today"]["label"]
        # 開啟時的打法；之前已經鎖定的日子（上一次對調的結果）要一路帶著
        self._opening = [list(row["counts"]) for row in plan["schedule"]]
        self._was_pinned = {d for d, row in enumerate(plan["schedule"])
                            if row.get("pinned")}
        self._counts = [list(counts) for counts in self._opening]
        self._touched = set(self._was_pinned)

        outer = ttk.Frame(self, padding=dp(12))
        outer.pack(fill="both", expand=True)
        # 對調按鈕跟「套用並重算／取消」同一排、放在捲動區外面：
        # 對話框拉得再小（或 100% 縮放時表格撐滿）都按得到
        bar = ttk.Frame(outer)
        bar.pack(side="bottom", fill="x", pady=(dp(14), 0))
        actions = ttk.Frame(bar)
        actions.pack(side="left")
        ttk.Button(actions, text="與前一天對調",
                   command=lambda: self._swap_neighbor(-1)).pack(side="left")
        ttk.Button(actions, text="與隔天對調",
                   command=lambda: self._swap_neighbor(1)).pack(side="left", padx=dp(4))
        ttk.Button(actions, text="對調選取的兩天",
                   command=self._swap_selected).pack(side="left")
        ttk.Button(actions, text="取消所有調整",
                   command=self._reset).pack(side="left", padx=(dp(16), 0))
        buttons = ttk.Frame(bar)
        buttons.pack(side="right", padx=(dp(16), 0))
        ttk.Button(buttons, text="套用並重算", command=self._on_ok).pack(
            side="left", padx=(0, dp(6)))
        ttk.Button(buttons, text="取消", command=self.destroy).pack(side="left")
        scroller = ScrollableFrame(outer, fill_height=True)
        scroller.pack(fill="both", expand=True)
        body = scroller.inner
        hint = ttk.Label(body, text="選一天按「與前一天／隔天對調」，或按住 Ctrl 選兩天按"
                                    "「對調選取的兩天」。整天的打法會互換。\n"
                                    "按「套用並重算」後，動過的日子照你的安排鎖住，"
                                    "其餘日子重新計算（體力不夠會反映在「需額外補充」）。",
                         foreground="#666666")
        hint.pack(anchor="w", pady=(0, dp(8)))
        scroller.wrap_label(hint)

        wrap = ttk.Frame(body)
        wrap.pack(fill="both", expand=True)
        columns = [("date", "日期", 110, "w"), ("plan", "打法", 460, "w"),
                   ("clears", "關數", 55, "e"), ("stamina", "耗體", 65, "e"),
                   ("state", "狀態", 80, "center")]
        self.tree = ttk.Treeview(wrap, columns=[c[0] for c in columns],
                                 show="headings", selectmode="extended",
                                 height=min(16, max(6, len(self._days))))
        for key, title, width, anchor in columns:
            self.tree.heading(key, text=title)
            self.tree.column(key, width=px(width), anchor=anchor,
                             stretch=(key == "plan"))
        self.tree.tag_configure("touched", background="#fff3cd")
        self.tree.pack(side="left", fill="both", expand=True)
        vbar = ttk.Scrollbar(wrap, orient="vertical", command=self.tree.yview)
        vbar.pack(side="left", fill="y")
        self.tree.configure(yscrollcommand=vbar.set)

        self._refresh()
        scroller.request_natural_size()
        self.bind("<Escape>", lambda _e: self.destroy())
        self.transient(parent)
        center_on(self, parent)
        run_modal(self)

    def _text(self, counts) -> str:
        return "、".join(f"{self._levels[i]['label']}×{c}"
                         for i, c in enumerate(counts) if c) or "（不打）"

    def _refresh(self, select=()):
        self.tree.delete(*self.tree.get_children())
        for d, day in enumerate(self._days):
            counts = self._counts[d]
            label = scheduler.format_day(day)
            # 首日列的是「從現在起還要打的」，跟計算結果的每日明細同一個基準
            if d == 0 and self._done_label:
                label += "（還要打的）"
            touched = d in self._touched
            self.tree.insert(
                "", "end", iid=str(d),
                values=(label, self._text(counts), sum(counts),
                        sum(self._levels[i]["stamina_cost"] * c
                            for i, c in enumerate(counts)),
                        "已調整" if touched else ""),
                tags=("touched",) if touched else ())
        picked = [str(d) for d in select]
        if picked:
            self.tree.selection_set(picked)
            self.tree.see(picked[0])

    def _selected(self) -> list[int]:
        return sorted(int(iid) for iid in self.tree.selection())

    def _swap_neighbor(self, step: int):
        picked = self._selected()
        if len(picked) != 1:
            messagebox.showinfo("對調日期", "請先選一天。", parent=self)
            return
        other = picked[0] + step
        if not 0 <= other < len(self._days):
            messagebox.showinfo(
                "對調日期",
                "排程範圍內沒有" + ("前一天" if step < 0 else "隔天") + "可以對調。",
                parent=self)
            return
        self._swap(picked[0], other, keep=other)

    def _swap_selected(self):
        picked = self._selected()
        if len(picked) != 2:
            messagebox.showinfo("對調日期", "請選兩天（按住 Ctrl 點第二天）。",
                                parent=self)
            return
        self._swap(picked[0], picked[1], keep=picked[0])

    def _swap(self, a: int, b: int, keep: int):
        # 搬過去的那天打不到的關卡（活動沒開、關卡還沒開放）先擋，不必等求解
        problems = []
        for src, dst in ((a, b), (b, a)):
            blocked = [self._levels[i]["label"]
                       for i, c in enumerate(self._counts[src])
                       if c and not self._playable[dst][i]]
            if blocked:
                problems.append(f"{scheduler.format_day(self._days[dst])} 打不到："
                                + "、".join(blocked))
        if problems:
            messagebox.showerror(
                "不能對調",
                "\n".join(problems)
                + "\n\n（那天活動還沒開始／已經結束、關卡還沒開放，"
                  "或已經過了上線時段）", parent=self)
            return
        self._counts[a], self._counts[b] = self._counts[b], self._counts[a]
        for d in (a, b):
            # 換回原樣、之前也沒鎖過的日子就不算動過，交回給求解器
            if (self._counts[d] == self._opening[d]
                    and d not in self._was_pinned):
                self._touched.discard(d)
            else:
                self._touched.add(d)
        self._refresh(select=(keep,))

    def _reset(self):
        """連之前鎖定的一起放掉：套用後整份排程交回給求解器重排。"""
        self._counts = [list(counts) for counts in self._opening]
        self._touched = set()
        self._refresh()

    def _on_ok(self):
        if self._touched == self._was_pinned and self._counts == self._opening:
            self.destroy()      # 什麼都沒變，不必重算
            return
        self.result = {
            self._days[d]: {self._levels[i]["key"]: c
                            for i, c in enumerate(self._counts[d]) if c}
            for d in sorted(self._touched)}
        self.destroy()


class LogTab(ttk.Frame):
    """每日紀錄：一天一列，左邊是計畫、右邊是實際打了什麼。

    多活動並行之後這是**單一時間軸**：同一天會同時記到好幾檔活動的關卡，
    關卡用「活動·關卡」指稱。實際紀錄的累計會自動寫回各活動的目前積分、
    已打關卡數與全域的已消耗體力。
    """

    def __init__(self, master, app):
        super().__init__(master)
        # 視窗縮小時整頁可以兩個方向捲（見 ScrollableFrame）
        self.scroller = ScrollableFrame(self, fill_height=True)
        self.scroller.pack(fill="both", expand=True)
        page = self.scroller.inner
        page.configure(padding=dp(16))
        self.app = app
        self._entries: dict[str, dict] = {}     # 日期 -> 實際打法（分筆的加總）
        self._plays: dict[str, list] = {}       # 日期 -> 分筆紀錄 [{at, counts}]
        self._tasks_done: dict[str, list] = {}    # 日期 -> 做到了（要主動勾的）
        self._tasks_missed: dict[str, list] = {}  # 日期 -> 沒做到（預設完成的）
        self._plan_days: dict[str, dict] = {}   # 日期 -> 計畫打法
        self._loading = False

        self.header = ttk.Label(page, text="", foreground="#b45309")
        self.header.grid(row=0, column=0, sticky="w", pady=(0, dp(8)))

        baseline = ttk.Label(page, text="開始記錄之前就已經累積的量（起始值）：起始積分／起始關卡數"
                                        "在「活動設定」；"
                                        "下面的實際紀錄會加在起始值上面",
                             foreground="#666666")
        baseline.grid(row=2, column=0, sticky="w", pady=(0, dp(12)))
        self.scroller.wrap_label(self.header)
        self.scroller.wrap_label(baseline)

        table = ttk.Frame(page)
        table.grid(row=3, column=0, sticky="nsew")
        table.rowconfigure(0, weight=1)
        table.columnconfigure(0, weight=1)

        columns = [("date", "日期", 110, "w"),
                   ("plan", "計畫打法", 250, "w"),
                   ("actual", "實際打法", 250, "w"),
                   ("clears", "關數", 55, "e"),
                   ("stamina", "耗體", 65, "e"),
                   ("points", "積分", 75, "e"),
                   ("tasks", "任務", 80, "center")]
        self.tree = ttk.Treeview(table, columns=[c[0] for c in columns],
                                 show="headings", height=14)
        for key, heading, width, anchor in columns:
            self.tree.heading(key, text=heading)
            self.tree.column(key, width=px(width), anchor=anchor, stretch=False)
        self.tree.grid(row=0, column=0, sticky="nsew")
        self.tree.bind("<Double-1>", lambda _e: self.edit_selected())
        # 已記錄的日子上色，一眼看得出哪幾天還沒填
        self.tree.tag_configure("logged", foreground="#0a5")
        self.tree.tag_configure("today", background="#fff4d6")

        vbar = ttk.Scrollbar(table, orient="vertical", command=self.tree.yview)
        vbar.grid(row=0, column=1, sticky="ns")
        # 欄位加總比視窗寬（尤其打法欄位可能很長），水平捲軸不能少
        hbar = ttk.Scrollbar(table, orient="horizontal", command=self.tree.xview)
        hbar.grid(row=1, column=0, sticky="we")
        self.tree.configure(yscrollcommand=vbar.set, xscrollcommand=hbar.set)

        buttons = ttk.Frame(table)
        buttons.grid(row=0, column=2, sticky="n", padx=(dp(8), 0))

        # 按用途分三組，各有一行灰字標題：記錄打法／任務／查看。
        # 任務狀態跟打法是兩回事（清除打法也不會動到它），不跟打法按鈕混在一起
        def group(title, first=False):
            ttk.Label(buttons, text=title, foreground="#666666").pack(
                anchor="w", pady=(0 if first else dp(12), dp(1)))

        def button(text, command):
            ttk.Button(buttons, text=text, width=13, command=command).pack(pady=dp(2))

        group("記錄打法", first=True)
        button("編輯實際", self.edit_selected)
        button("分筆紀錄", self.edit_plays)
        button("照計畫記錄", self.accept_plan)
        button("清除打法", self.clear_selected)
        group("任務")
        button("任務狀態", self.edit_tasks)
        group("查看")
        button("剩餘打法", self.show_remaining)
        button("跳到今天", self.goto_today)
        # 進行中的任務用不到的舊日子平常收起來；要看或補記時勾這格（見 _all_days）
        self.show_empty_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(buttons, text="顯示更早的紀錄",
                        variable=self.show_empty_var,
                        command=self._refresh_tree).pack(anchor="w", pady=(dp(4), dp(2)))

        # 今天還要打的（跟「目前狀態」的今日待辦同一份），邊記錄邊看剩多少
        self.remaining = ttk.Label(page, text="", justify="left")
        self.remaining.grid(row=4, column=0, sticky="w", pady=(dp(10), 0))
        self.scroller.wrap_label(self.remaining)

        self.summary = ttk.Label(page, text="", foreground="#0a5", justify="left")
        self.summary.grid(row=5, column=0, sticky="w", pady=(dp(6), 0))
        self.scroller.wrap_label(self.summary)
        # 表格自己有橫向捲軸；只留「表格最窄 ~250px＋右邊整排按鈕」的寬度
        loosen_width(table, 420)

        page.rowconfigure(3, weight=1)
        page.columnconfigure(0, weight=1)

    # -- 工具 ------------------------------------------------------------
    def _all_days(self) -> list[str]:
        """表格要列出的日子。

        * 真正的活動（`storage.real_events`）涵蓋的每一天。限期關卡、常駐關卡、
          已封存的不撐日子——跟排程算期間的規則一樣；限期關卡動輒兩三個月，
          照算會從好幾個月前一路列到明年。
        * 一定補上：有紀錄或勾過任務的日子、今天、存入計畫裡有的日子
          （活動空窗期只剩限期關卡時，今天那一列才不會不見）。
        * 沒勾「顯示更早的紀錄」時，只列還在進行的任務會量到的日子
          （見 _earliest_needed）：從那天到今天每天都列，沒記錄的也列
          （這段漏記會影響任務進度）；更早的就算有紀錄也收起來。
        * 勾了的話全部列出，今天以前的日子連限期關卡的期間也列——要補記
          活動開始前打的限期關卡，才有那一列可以填。未來的日子不受影響。
        """
        today = self._task_today()
        show_empty = self.show_empty_var.get()
        earliest = None if show_empty else self._earliest_needed()

        def span(event):
            try:
                start = datetime.strptime(event["start_date"], "%Y-%m-%d").date()
                end = datetime.strptime(event["end_date"], "%Y-%m-%d").date()
            except (KeyError, TypeError, ValueError):
                return set()
            return {(start + timedelta(days=n)).isoformat()
                    for n in range((end - start).days + 1)}

        days = set()
        for event in storage.real_events(self.app.shared):
            days |= span(event)
        if show_empty:
            for event in storage.limited_events(self.app.shared):
                days |= {d for d in span(event) if d < today}
        has_data = (set(self._entries) | set(self._tasks_done)
                    | set(self._tasks_missed) | set(self._plan_days))
        days |= has_data | {today}
        if earliest is not None:
            first = date.fromisoformat(earliest)
            last = date.fromisoformat(today)
            days |= {(first + timedelta(days=n)).isoformat()
                     for n in range(max(0, (last - first).days) + 1)}
            days = {d for d in days if d >= earliest}
        elif not show_empty:
            # 算不出任務起點時退回舊規則：今天以前只列有資料的日子
            days = {d for d in days if d >= today or d in has_data}
        return sorted(days)

    def _earliest_needed(self) -> str | None:
        """還在進行的任務最早會量到哪一天（ISO 字串）。

        每日／每週／每月任務量目前這一期、活動任務量活動開始以來
        （scheduler.task_progress 的 `since`）。這個帳號不做的、已經過期的、
        活動已封存的任務都不算。沒有任何進行中的任務就是今天；
        算不出來回 None（呼叫端退回不裁的規則，免得整張表消失）。
        """
        today = self._task_today()
        try:
            progress = scheduler.task_progress(
                self.app.shared, self.app.profile, self.app.log_entries(),
                datetime.now())
        except Exception:
            return None
        states = self.app.profile.get("task_state") or {}
        starts = [info["since"] for key, info in progress.items()
                  if info.get("since") and info.get("state") == "active"
                  and not info.get("archived")
                  and (states.get(key) or {}).get("enabled") is not False]
        return min([s.isoformat() for s in starts] + [today])

    def _levels(self):
        return storage.all_levels(self.app.shared)

    def _levels_on(self, date_str: str, keep=None) -> list[dict]:
        """那一個任務日開著的活動的關卡——填實際打法時只列這些。

        限期關卡接下一期後新舊兩檔同名，全部列出會有兩組一樣的「忘卻·xxx」。
        用日期比而不是看現在：補記過去某天時，當天開著的舊檔仍要能填。
        換期當天新舊兩期都在（中午結束、下午開始），靠標籤上的期數區分。
        `keep` 是那天已經記過的次數，有數字的關卡不管活動開沒開都留著。
        """
        keep = keep or {}
        open_ids = set()
        for event in storage.events_of(self.app.shared):
            start, end = event.get("start_date"), event.get("end_date")
            if (not start or start <= date_str) and (not end or date_str <= end):
                open_ids.add(event.get("id"))
        return [level for level in self._levels()
                if level["event_id"] in open_ids or int(keep.get(level["key"]) or 0)]

    def _level_label(self, level: dict) -> str:
        """「活動·關卡」；限期關卡帶期數，兩期忘卻才分得出來。只有一檔活動就只寫關卡。"""
        if len(storage.events_of(self.app.shared)) <= 1:
            return level["name"]
        event = storage.find_event(self.app.shared, level["event_id"])
        name = storage.event_choice_label(event) if event else level["event_name"]
        return scheduler.level_label(name, level.get("series_name"), level["name"])

    # -- 任務日與時刻 ----------------------------------------------------
    def _reset_clock(self):
        return scheduler.parse_clock(
            (self.app.shared or {}).get("daily_reset_time"), "05:00")

    def _task_today(self) -> str:
        """現在算哪一個「任務日」。凌晨 2 點要記在前一天那一列。"""
        return scheduler.task_day_of(datetime.now(),
                                     self._reset_clock()).isoformat()

    def _moment_iso(self, date_str: str, clock: str) -> str:
        """HH:MM ＋ 任務日 → 實際時刻。

        時刻一律**以所編輯的那一個任務日解讀**：重置時刻以後是當天，
        之前的是隔天凌晨。所以在 09/13 那一列填 02:00，存下來是
        2026-09-14T02:00——仍然屬於 09/13 這個任務日，不必另外搬資料。
        """
        reset = self._reset_clock()
        day = datetime.strptime(date_str, "%Y-%m-%d").date()
        moment = datetime.strptime(clock, "%H:%M").time()
        if moment < reset:
            day = day + timedelta(days=1)
        return datetime.combine(day, moment).strftime(storage.PLAY_TIME_FORMAT)

    @staticmethod
    def _clock_of(at) -> str:
        """分筆紀錄的時刻 → HH:MM；讀不出來的回空字串。"""
        if not at:
            return ""
        try:
            return datetime.strptime(
                str(at), storage.PLAY_TIME_FORMAT).strftime("%H:%M")
        except ValueError:
            return ""

    def _plays_for(self, date_str: str) -> list[dict]:
        """那一天的分筆紀錄（複本，可以直接改）。"""
        return [{"at": play.get("at"), "counts": dict(play.get("counts") or {})}
                for play in self._plays.get(date_str) or []]

    def _set_plays(self, date_str: str, plays: list) -> None:
        plays = storage.clean_plays(plays)
        if plays:
            self._plays[date_str] = plays
        else:
            self._plays.pop(date_str, None)
        self._entries[date_str] = storage.counts_of_plays(plays)

    def _describe(self, counts: dict) -> tuple[str, int, int, int]:
        """把 {關卡鍵: 次數} 轉成 (顯示文字, 關數, 耗體, 積分)。"""
        points_of = storage.points_map(self.app.shared, self.app.profile)
        parts, clears, stamina, points = [], 0, 0, 0
        for level in self._levels():
            count = int((counts or {}).get(level["key"]) or 0)
            if count:
                parts.append(f"{self._level_label(level)}×{count}")
                clears += count
                stamina += level["stamina_cost"] * count
                if level.get("scoring"):
                    points += int(points_of.get(level["key"]) or 0) * count
        return "、".join(parts), clears, stamina, points

    def _level_specs(self, date_str: str, keep=None) -> list[dict]:
        """實際打法的欄位：一關一列，計畫（唯讀）／前次／這次。

        只列那天開著的活動（見 `_levels_on`）。
        計畫值只是參考，讓人不必切回表格對照；沒算過的日子顯示 -。
        """
        plan = self._plan_days.get(date_str) or {}
        return [{"key": level["key"],
                 "label": self._level_label(level),
                 "type": "pair_int", "minimum": 0,
                 "note": str(plan.get(level["key"]) or 0) if plan else "-"}
                for level in self._levels_on(date_str, keep)]

    def _manual_tasks(self):
        """要逐日記錄的任務，分成兩種：

        * 預設完成（`assume_done`）—— 當作每次都會做到，只記「沒做到」的日子
        * 其餘手動勾選類 —— 要主動勾「做到了」
        * 出現時間不固定（`grant_on_done`，一定也是預設完成）—— 一列下拉：
          做到那天選「今天做到了」（那週的獎勵改算在那天），真的沒做到選「這週沒做到」

        回傳 [(任務鍵, 顯示名稱, 是否預設完成, 是否出現時間不固定)]。
        """
        rows = []
        for task, owner, key in scheduler.iter_tasks(self.app.shared):
            if owner is not None and storage.is_archived(owner):
                continue      # 已封存的活動，任務也跟著收起來
            if task.get("metric") != "manual" and not task.get("assume_done"):
                continue
            state = (self.app.profile.get("task_state") or {}).get(key) or {}
            if state.get("enabled") is False:
                continue
            where = f"{owner.get('name') or owner['id']}／" if owner else ""
            rows.append((key, where + (task.get("name") or key),
                         bool(task.get("assume_done")),
                         bool(task.get("grant_on_done"))
                         and task.get("cycle") == "weekly"))
        return rows

    # -- 顯示 ------------------------------------------------------------
    def _refresh_tree(self):
        selected = self.tree.selection()
        self.tree.delete(*self.tree.get_children())
        # 用任務日而不是日曆日：凌晨 2 點開程式時，該反白的是前一天那一列
        today = self._task_today()
        tasks = self._manual_tasks()
        need_tick = [t for t in tasks if not t[2]]
        for date_str in self._all_days():
            plan_text, *_ = self._describe(self._plan_days.get(date_str))
            actual = self._entries.get(date_str)
            if actual is None:
                actual_text, clears, stamina, points = "（未記錄）", "", "", ""
                tags = ()
            else:
                actual_text, clears, stamina, points = self._describe(actual)
                actual_text = actual_text or "（沒打）"
                # 分成好幾筆的才標——一筆的話「1 筆」只是噪音
                count = len(self._plays.get(date_str) or ())
                if count > 1:
                    actual_text = f"{actual_text}　（{count} 筆）"
                tags = ("logged",)
            # 預設完成的只顯示「沒做到幾條」（正常是 0，不必每天去看）；
            # 要主動勾的才顯示 N/M。
            missed = len(self._tasks_missed.get(date_str) or [])
            need_keys = {t[0] for t in need_tick}
            done = len(set(self._tasks_done.get(date_str) or []) & need_keys)
            bought = [t[1] for t in tasks
                      if t[3] and t[0] in (self._tasks_done.get(date_str) or [])]
            if missed:
                task_text = f"沒做到 {missed}"
            elif need_tick:
                task_text = f"{done}/{len(need_tick)}"
            elif tasks:
                task_text = "✓"
            else:
                task_text = "—"
            if bought:
                task_text += "　做到了 " + "、".join(bought)
            if date_str == today:
                tags = tags + ("today",)
            if not plan_text:
                # 計畫裡有這一天、只是排的是不打，跟「沒算過」分開寫
                if date_str not in self._plan_days:
                    plan_text = "（尚未計算）"
                else:
                    plan_text = "（今天不排）" if date_str == today else "（不打）"
            self.tree.insert("", "end", iid=date_str, tags=tags,
                             values=(date_str, plan_text,
                                     actual_text, clears, stamina, points,
                                     task_text))
        for iid in selected:
            if self.tree.exists(iid):
                self.tree.selection_set(iid)

    def goto_today(self):
        today = self._task_today()
        if self.tree.exists(today):
            self.tree.selection_set(today)
            self.tree.see(today)

    # -- 操作 ------------------------------------------------------------
    def _selected_date(self) -> str | None:
        selection = self.tree.selection()
        return selection[0] if selection else None

    def remaining_text(self, date_str: str) -> str:
        """選取那天還要打什麼（存入計畫減掉已記錄的），純文字，給人複製到別的裝置。"""
        plan = self._plan_days.get(date_str)
        done = self._entries.get(date_str) or {}
        weekday = "一二三四五六日"[date.fromisoformat(date_str).weekday()]
        account = self.app.profile.get("profile_name") or self.app.profile_id
        lines = [f"剩餘打法　{date_str}（{weekday}）　帳號：{account}"]
        if not plan:
            lines.append("這天沒有存入的計畫（到「計算結果」算好並存入計畫才會有）")
            return "\n".join(lines)
        remain, clears, stamina = [], 0, 0
        each = []       # 逐次清單：打一次刪一行
        for level in self._levels():
            planned = int(plan.get(level["key"]) or 0)
            if planned <= 0:
                continue
            got = int(done.get(level["key"]) or 0)
            left = planned - got
            if left <= 0:
                continue
            remain.append(f"　{self._level_label(level)} ×{left}"
                          f"（計畫 {planned}，已打 {got}）")
            each += [self._level_label(level)] * left
            clears += left
            stamina += level["stamina_cost"] * left
        if remain:
            lines.append("還要打：")
            lines += remain
            lines.append(f"合計還要 {clears} 關、耗體 {stamina}")
            lines.append("")
            lines += each
        else:
            lines.append("計畫的關卡都打完了 ✓")
        stale = self.app.plan_stale_note()
        if stale:
            lines.append(stale)
        return "\n".join(lines)

    def show_remaining(self):
        date_str = self._selected_date()
        if not date_str:
            messagebox.showinfo("剩餘打法", "請先在表格選一天。", parent=self)
            return
        CopyTextDialog(self.winfo_toplevel(), f"{date_str} 剩餘打法",
                       self.remaining_text(date_str))

    def edit_selected(self):
        date_str = self._selected_date()
        if not date_str:
            return
        # 「前次」是既有分筆的加總（唯讀——要改既有的量請走「分筆紀錄」），
        # 「這次」一律從 0 開始，按確定時存成**一筆**帶時刻的新紀錄。
        # 計畫的數字只放在旁邊當唯讀參考，不會被當成實際成績存下去；
        # 真的照計畫打完的話，用旁邊的「照計畫記錄」按鈕一鍵帶入。
        plays = self._plays_for(date_str)
        recorded = storage.counts_of_plays(plays)
        specs = [{"key": TIME_KEY, "label": "時間", "type": "time",
                  "above_headers": True,
                  "hint": "這一筆是幾點打的，預設是現在。只有活動開始或結束"
                          "當天才要填準：例如中午換活動，早上打的要填早上，"
                          "才不會算進下午新活動的任務。其他日子不用管"}]
        level_specs = self._level_specs(date_str, recorded)
        specs += [dict(spec, locked_prev=True) for spec in level_specs]
        initial = {TIME_KEY: datetime.now().strftime("%H:%M")}
        initial.update({spec["key"]: recorded.get(spec["key"], 0)
                        for spec in level_specs})

        def summary(values):
            counts = {k: RecordDialog._int_or_zero(v)
                      for k, v in values.items() if k != TIME_KEY}
            _text, clears, stamina, points = self._describe(counts)
            return f"合計 {clears} 關、耗體 {stamina}、積分 {points}"

        dialog = RecordDialog(self.winfo_toplevel(),
                              f"{date_str} 實際打法",
                              specs, initial,
                              total_of=summary,
                              headers=("計畫", "前次", "這次"),
                              width=MIN_WIDTH)
        if dialog.result is None:
            return
        added = {key: count for key, count in dialog.added.items() if count > 0}
        if not added:
            return          # 「這次」全是 0，不要留下一筆空白的分筆紀錄
        plays.append({"at": self._moment_iso(date_str, dialog.result[TIME_KEY]),
                      "counts": added})
        self._set_plays(date_str, plays)
        self._persist()

    def edit_plays(self):
        """那一天的每一筆：時刻、打了什麼，可以改也可以刪。"""
        date_str = self._selected_date()
        if not date_str:
            return
        plays = self._plays_for(date_str)
        if not plays:
            messagebox.showinfo(
                "還沒有紀錄",
                f"{date_str} 還沒記錄任何打法，請先用「編輯實際」記一筆。",
                parent=self)
            return
        dialog = PlayListDialog(self.winfo_toplevel(), self, date_str, plays)
        if dialog.result is None:
            return
        self._set_plays(date_str, dialog.result)
        self._persist()

    def edit_tasks(self):
        """任務狀態：預設完成的勾「沒做到」，其餘勾「做到了」。

        兩種語意相反的東西放同一個對話框，所以標籤要各自講清楚是哪一種——
        只靠上面一行說明的話，勾錯的後果是體力算反。
        """
        date_str = self._selected_date()
        if not date_str:
            return
        tasks = self._manual_tasks()
        if not tasks:
            messagebox.showinfo(
                "沒有要記錄的任務",
                "目前沒有需要逐日記錄的任務。\n\n"
                "登入、簽到這種程式看不出來的任務，可以在「設定 → 任務清單」\n"
                "把達成條件設成「手動勾選」。如果那是你每次都會做到的，\n"
                "再把「預設完成」勾起來——之後就不必每天來勾，\n"
                "只有真的沒做到時才回來標記那一天。",
                parent=self)
            return
        missed = set(self._tasks_missed.get(date_str) or [])
        done = set(self._tasks_done.get(date_str) or [])
        specs, initial = [], {}
        for key, label, assume, on_done in tasks:
            if on_done:
                # 出現時間不固定：一列下拉，「做到了」跟「沒做到」不會同時勾到。
                # 做到了存進 tasks_done（那週的獎勵改算在這天）、沒做到存進 tasks_missed
                specs.append({"key": key, "type": "choice", "label": label,
                              "choices": [("", "未標記"), ("done", "今天做到了"),
                                          ("missed", "這週沒做到")]})
                initial[key] = ("missed" if key in missed
                                else "done" if key in done else "")
                continue
            specs.append({"key": key, "type": "bool", "default": False,
                          "label": (f"[沒做到] {label}" if assume
                                    else f"[做到了] {label}")})
            initial[key] = key in (missed if assume else done)
        # 沒有提示可以攤開；拉寬時讓任務名稱那欄變寬，勾選框、下拉選單不動
        dialog = RecordDialog(self.winfo_toplevel(), f"{date_str} 任務狀態",
                              specs, initial, stretch=0)
        if dialog.result is None:
            return
        new_missed, new_done = set(), set()
        for key, _label, assume, on_done in tasks:
            value = dialog.result.get(key)
            if on_done:
                if value == "missed":
                    new_missed.add(key)
                elif value == "done":
                    new_done.add(key)
            elif value:
                (new_missed if assume else new_done).add(key)
        self._tasks_missed[date_str] = sorted(new_missed)
        self._tasks_done[date_str] = sorted(new_done)
        self._persist()

    def accept_plan(self):
        date_str = self._selected_date()
        if not date_str:
            return
        plan = self._plan_days.get(date_str)
        if not plan:
            if date_str in self._plan_days:
                # 有算過，只是那天排的是不打（例如計算時已經過了上線時段、
                # 今天也沒有要補的任務）——這時叫人「先去算」是錯的
                messagebox.showinfo(
                    "這天不打", f"{date_str} 的計畫沒有排任何關卡"
                                "（例如計算時已經過了上線時段，今天也沒有要補的任務），"
                                "不用照計畫記錄。", parent=self)
            else:
                messagebox.showinfo(
                    "沒有計畫", f"{date_str} 沒有排程資料。\n"
                                "請先到「計算結果」分頁算一次排程。", parent=self)
            return
        # 計畫本身沒有時刻，一律存成一筆、時刻預設帶入現在；要拆成早晚兩筆
        # 或改時刻，到「分筆紀錄」裡調。
        self._set_plays(date_str, [{
            "at": self._moment_iso(date_str, datetime.now().strftime("%H:%M")),
            "counts": dict(plan)}])
        self._persist()

    def clear_selected(self):
        """只清那天的打法（實際打法＋分筆紀錄），任務狀態留著。

        任務的「沒做到」標記漏掉的話體力會算成有做到，不能跟著打法一起被
        順手清掉；要改任務就到「任務狀態」取消勾選。清掉前一定先問。
        """
        date_str = self._selected_date()
        if not date_str:
            return
        counts = self._entries.get(date_str) or {}
        plays = self._plays.get(date_str) or []
        if not any(int(v or 0) > 0 for v in counts.values()) and not plays:
            messagebox.showinfo("沒有打法", f"{date_str} 沒有記錄打法，不用清除。",
                                parent=self)
            return
        text = self._describe(counts)[0]
        detail = f"（分筆紀錄 {len(plays)} 筆）" if plays else ""
        if not messagebox.askyesno(
                "清除打法",
                f"要清除 {date_str} 的打法嗎？\n\n{text}{detail}\n\n"
                "清除後無法復原。任務狀態不會清掉，要改請用「任務狀態」。",
                icon="warning", default="no", parent=self):
            return
        self._entries.pop(date_str, None)
        self._plays.pop(date_str, None)
        self._persist()

    # -- 載入/儲存 -------------------------------------------------------
    def load(self):
        self._loading = True
        try:
            log = storage.load_log(self.app.profile_id)
            self._entries = {e["date"]: dict(e.get("counts") or {})
                             for e in log.get("entries") or [] if e.get("date")}
            self._plays = {e["date"]: list(e.get("plays") or [])
                           for e in log.get("entries") or []
                           if e.get("date") and e.get("plays")}
            self._tasks_done = {e["date"]: list(e.get("tasks_done") or [])
                                for e in log.get("entries") or [] if e.get("date")}
            self._tasks_missed = {e["date"]: list(e.get("tasks_missed") or [])
                                  for e in log.get("entries") or [] if e.get("date")}
            # 計算後新增／刪除活動或改日期，舊計畫照樣顯示，標題列會提醒重算
            plan = self.app.stored_plan() or {}
            self._plan_days = dict(plan.get("days") or {})
            computed_at = plan.get("computed_at")
            plan_note = (f"計畫來自 {computed_at[:16].replace('T', ' ')} 的計算"
                         if computed_at else "尚未計算排程")
            names = "、".join(scheduler.event_label(ev)
                             for ev in storage.visible_events(self.app.shared))
            text = f"進行中的活動：{names}\n{plan_note}"
            stale = self.app.plan_stale_note()
            if stale:
                text = f"{text}\n{stale}"
            self.header.config(text=text)
            self._refresh_tree()
            self._refresh_summary()
            self.goto_today()
        finally:
            self._loading = False

    def collect(self) -> bool:
        return True

    def _entry_list(self) -> list[dict]:
        days = sorted(set(self._entries) | set(self._tasks_done)
                      | set(self._tasks_missed))
        rows = []
        for date_str in days:
            counts = {k: int(v) for k, v in (self._entries.get(date_str) or {}).items()
                      if int(v or 0) > 0}
            done = list(self._tasks_done.get(date_str) or [])
            missed = list(self._tasks_missed.get(date_str) or [])
            plays = storage.clean_plays(self._plays.get(date_str))
            counts = storage.counts_of_plays(plays)       # 總量一律由分筆加總
            if counts or done or missed:
                rows.append({"date": date_str, "counts": counts, "plays": plays,
                             "tasks_done": done, "tasks_missed": missed})
        return rows

    def _persist(self):
        """把紀錄寫進檔案，並把累計結果同步回帳號。

        起始值不在這一頁改（見 App.set_log_baselines），這裡只寫紀錄本身。
        """
        log = storage.load_log(self.app.profile_id)
        for event in storage.events_of(self.app.shared):
            storage.ensure_log_event(log, event, self.app.profile)
        log["entries"] = self._entry_list()
        storage.save_log(self.app.profile_id, log)
        self._refresh_tree()
        # 目前積分/已打關卡數已經變了，讓顯示它們的分頁跟著更新
        self.app.apply_log(log)

    def _refresh_summary(self):
        """各活動的進度，每檔只列它用得到的數字；什麼都沒有的那檔不列。

        * 常駐關卡：沒有積分、任務與上限，不列
        * 限期關卡：每一關已打幾次／這一檔的上限
        * 活動：有計分關卡或積分任務才列積分；有關卡次數任務才列已打幾關；
          有累計耗體任務列累計耗體；有每日耗體任務列今天花了多少
        """
        text, left = self.app.remaining_today(datetime.now())
        self.remaining.config(text=f"今天（{self._task_today()}）{text}",
                              foreground="#b45309" if left else "#0a5")

        table = storage.level_table(self.app.shared)
        lines = []
        for event in storage.visible_events(self.app.shared):
            if storage.is_standing(event):
                continue
            data = storage.profile_event(self.app.profile, event["id"])
            if storage.is_limited(event):
                parts = self._limited_parts(event, data)
            else:
                parts = []
                if (any(lv.get("scoring") for lv in event.get("levels") or [])
                        or self._tasks_of(event, "points")):
                    parts.append(f"積分 {data.get('current_points') or 0}")
                if self._tasks_of(event, "clears"):
                    parts.append(f"已打 {data.get('current_clears') or 0} 關")
                if self._tasks_of(event, "stamina"):
                    parts.append(f"累計耗體 {self._event_stamina(event, table)}"
                                 "（活動開始後）")
                daily = self._tasks_of(event, "stamina", cycle="daily")
                if daily:
                    goal = max(self._task_goal(event, task) for task in daily)
                    today = self._event_stamina(event, table, day=self._task_today())
                    parts.append(f"今日耗體 {today} / {goal}")
            if parts:
                lines.append(f"　{scheduler.event_label(event)}：" + "、".join(parts))
        self.summary.config(text="\n".join(lines))

    def _limited_parts(self, event, data) -> list[str]:
        """限期關卡：每一關這一檔已打幾次，有上限就一起列（本帳號的上限優先）。

        本帳號取消「計算」的關不列（見 limited_progress）。
        """
        parts = []
        for level, done, cap in limited_progress(event, data, self._entries.values()):
            name = level.get("name") or level["id"]
            parts.append(f"{name} {done} / {cap} 次" if cap is not None
                         else f"{name} 已打 {done} 次")
        return parts

    def _tasks_of(self, event, metric, cycle="event") -> list[dict]:
        """這檔這一類的任務（本帳號在任務進度停用的不算）。"""
        states = self.app.profile.get("task_state") or {}
        return [task for task in event.get("tasks") or []
                if task.get("metric") == metric
                and (task.get("cycle") or "event") == cycle
                and (states.get(f"{event['id']}/{task.get('id')}") or {}).get("enabled")
                is not False]

    def _task_goal(self, event, task) -> int:
        """任務目標：本帳號在任務進度改過就用改過的數字。"""
        state = (self.app.profile.get("task_state") or {}).get(
            f"{event['id']}/{task.get('id')}") or {}
        override = state.get("amount_override")
        return int(task.get("amount") or 0) if override is None else int(override)

    def _event_stamina(self, event, table, day=None) -> int:
        """這檔活動開著的時候打掉的體力（跨活動所有關卡一起算）。

        跟排程算「累計消耗體力」任務的方式一樣（scheduler 的 live_filter）：
        看每一筆打的那一刻這檔開沒開。
        不含任務自己的起始值——那是各條任務分開填的。
        `day`（任務日字串）有給就只算那一天。
        """
        try:
            start_dt, end_dt = scheduler.event_bounds(event)
        except scheduler.PlanError:
            return 0
        total = 0
        for date_str, plays in self._plays.items():
            if day is not None and date_str != day:
                continue
            for play in plays:
                moment = datetime.strptime(play["at"], storage.PLAY_TIME_FORMAT)
                if not start_dt <= moment < end_dt:
                    continue
                for key, count in (play.get("counts") or {}).items():
                    total += (int((table.get(key) or {}).get("stamina_cost") or 0)
                              * int(count or 0))
        return total


class StartProgressDialog(tk.Toplevel):
    """補登開始前的進度：活動進行到一半才開始用時，把遊戲裡已經有的進度補上。

    這些數字通常只在第一次計算前要填一次，所以不常駐在各分頁，集中在這裡：
    活動的起始值（積分、關卡數、耗體、敵人、道具）、有次數限制的關卡已打幾次、
    限期關卡這期已打幾次、固定任務這一期已完成多少、活動任務的獎勵已經領過。
    只列這個帳號現在用得到的項目（進行中的活動、算得出來的任務）。

    from_compute：從「開始計算」跳出來的。按鈕是「存檔並開始計算」／「不補登，直接計算」
    ／「取消」。`proceed` 告訴呼叫端要不要接著算：前兩個會算，而且這個帳號之後不再自動跳；
    取消（含 Esc、關窗）什麼都不存也不算，下次按計算還會再跳。
    從「設定」選單打開的（from_compute=False）最上面可以選要補哪個帳號；
    從計算跳出來的只補正在算的這個帳號。
    """

    def __init__(self, app, from_compute: bool = False):
        super().__init__(app)
        hide_until_centered(self)
        self.app = app
        self.proceed = False
        self.title("補登開始前的進度")
        # 正在補的帳號。預設是目前選中的；選單打開的可以換（見 _on_account_selected）
        self.profile_id = app.profile_id
        self.profile = app.profile

        outer = ttk.Frame(self, padding=dp(12))
        outer.pack(fill="both", expand=True)
        if not from_compute:
            # 放在捲動區外面：內容再長，帳號選單都在最上面
            bar = ttk.Frame(outer)
            bar.pack(side="top", fill="x", pady=(0, dp(8)))
            ttk.Label(bar, text="帳號").pack(side="left", padx=(0, dp(6)))
            self._accounts = storage.list_profiles()
            self.account_box = ttk.Combobox(
                bar, state="readonly", width=16,
                values=[name for _pid, name in self._accounts])
            self.account_box.current(next(
                (i for i, (pid, _n) in enumerate(self._accounts)
                 if pid == self.profile_id), 0))
            self.account_box.pack(side="left")
            self.account_box.bind("<<ComboboxSelected>>", self._on_account_selected)
            ttk.Label(bar, text="每個帳號各自填、各自存", foreground="#666666").pack(
                side="left", padx=(dp(10), 0))
        buttons = ttk.Frame(outer)
        buttons.pack(side="bottom", anchor="e", pady=(dp(14), 0))
        ttk.Button(buttons, text="存檔並開始計算" if from_compute else "確定",
                   command=self._on_ok).pack(side="left", padx=(0, dp(6)))
        if from_compute:
            ttk.Button(buttons, text="不補登，直接計算",
                       command=self._on_skip).pack(side="left", padx=(0, dp(6)))
        ttk.Button(buttons, text="取消", command=self._on_cancel).pack(side="left")
        self._from_compute = from_compute
        self.scroller = ScrollableFrame(outer, fill_height=True)
        self.scroller.pack(fill="both", expand=True)
        self.scroller.inner.columnconfigure(2, weight=1)

        self._bold = tkfont.Font(font="TkDefaultFont")
        self._bold.configure(weight="bold")
        self._render()
        self.scroller.request_natural_size(max_height=px(560))

        # Esc／關窗＝取消：不存、不算，下次按計算還會再跳
        self.bind("<Escape>", lambda _e: self._on_cancel())
        self.protocol("WM_DELETE_WINDOW", self._on_cancel)
        self.transient(app)
        center_on(self, app)
        run_modal(self)

    # -- 版面 --------------------------------------------------------------
    def _render(self):
        """依目前選的帳號（重新）排出所有欄位。換帳號時整個重建。"""
        body = self.scroller.inner
        for child in body.winfo_children():
            child.destroy()
        self._event_vars: dict = {}      # event_id -> {種類: StringVar}
        self._level_vars: dict = {}      # event_id -> {level_id: StringVar／BooleanVar}
        self._period_vars: dict = {}     # 任務鍵 -> (StringVar, 這一期的第一天)
        self._claimed_vars: dict = {}    # 任務鍵 -> BooleanVar
        self._labels: dict = {}          # 變數 id -> 錯誤訊息用的名稱
        self._row = 0
        lead = ttk.Label(
            body, text=("還沒有每日紀錄。活動如果已經進行一段時間，先把遊戲裡現在的進度"
                        "補上，排程才不會要你重打已經做完的部分。沒有的填 0 或留空。"
                        "之後要改，到「設定 → 補登開始前的進度」。")
            if self._from_compute else
            "開始用這個程式之前，遊戲裡已經有的進度。沒有的填 0 或留空。",
            foreground="#666666")
        lead.grid(row=self._next_row(), column=0, columnspan=3, sticky="w",
                  pady=(0, dp(8)))
        self.scroller.wrap_label(lead)
        if not self._from_compute and storage.has_entries(storage.load_log(self.profile_id)):
            # 已經在記錄了：之後的進度從每日紀錄算，這裡再填一次「開始前」的量會重複算。
            # 只提醒、不擋——記錯要修正，或真的漏了開始前那段時還是得來這裡
            warn = ttk.Label(
                body, foreground="#b45309",
                text=f"⚠「{self._account_name()}」已經有每日紀錄了，通常不需要用這個功能。"
                     "開始記錄之後的進度都從每日紀錄算；這裡填的是「開始用之前」就有的量，"
                     "把已經記在每日紀錄裡的部分再填進來會重複計算。"
                     "只有開始記錄前那段真的漏填時才需要改。")
            warn.grid(row=self._next_row(), column=0, columnspan=3, sticky="w",
                      pady=(0, dp(8)))
            self.scroller.wrap_label(warn)
        if not self._build(body):
            ttk.Label(body, text="現在沒有進行中的活動或要補的任務，不用填。").grid(
                row=self._next_row(), column=0, columnspan=3, sticky="w")
        self.scroller.wrap_long_labels()
        self._snapshot = self._values()

    def _values(self) -> tuple:
        """畫面上所有欄位目前的值，用來判斷換帳號前有沒有改過。"""
        out = []
        for kinds in self._event_vars.values():
            out += [var.get() for var in kinds.values()]
        for levels in self._level_vars.values():
            out += [var.get() for var in levels.values()]
        out += [var.get() for var, _w in self._period_vars.values()]
        out += [var.get() for var in self._claimed_vars.values()]
        return tuple(out)

    def _on_account_selected(self, _event=None):
        pid = self._accounts[self.account_box.current()][0]
        if pid == self.profile_id:
            return
        if self._values() != self._snapshot:
            answer = messagebox.askyesnocancel(
                "換帳號", f"「{self._account_name()}」改過的數字要先存起來嗎？",
                parent=self)
            if answer is None or (answer and not self._apply()):
                # 取消（或存檔失敗）：選單退回原本的帳號
                self.account_box.current(next(
                    i for i, (p, _n) in enumerate(self._accounts) if p == self.profile_id))
                return
        self.profile_id = pid
        if pid == self.app.profile_id:
            self.profile = self.app.profile
        else:
            self.profile = storage.load_profile(pid)
            storage.sync_levels(self.profile, self.app.shared)
        self._render()

    def _account_name(self) -> str:
        return dict(storage.list_profiles()).get(self.profile_id, self.profile_id)

    def _next_row(self) -> int:
        self._row += 1
        return self._row

    def _heading(self, body, text):
        ttk.Label(body, text=text, font=self._bold).grid(
            row=self._next_row(), column=0, columnspan=3, sticky="w", pady=(dp(10), dp(4)))

    def _number_row(self, body, label, value, hint="", name=None):
        row = self._next_row()
        ttk.Label(body, text=label).grid(row=row, column=0, sticky="w",
                                         padx=(dp(12), dp(10)), pady=dp(3))
        var = tk.StringVar(value="" if not value else str(value))
        ttk.Entry(body, textvariable=var, width=8, justify="right").grid(
            row=row, column=1, sticky="w")
        if hint:
            ttk.Label(body, text=hint, foreground="#666666").grid(
                row=row, column=2, sticky="w", padx=(dp(10), 0))
        self._labels[str(var)] = name or label
        return var

    @staticmethod
    def _running(event, now) -> bool:
        try:
            start, end = scheduler.event_bounds(event)
        except scheduler.PlanError:
            return False
        return start <= now < end

    def _build(self, body) -> bool:
        shared, profile = self.app.shared, self.profile
        now = datetime.now()
        log = storage.load_log(self.profile_id)
        sections = log.get("events") or {}
        stamina_of = scheduler.item_stamina_table(shared)
        states = profile.get("task_state") or {}
        built = False

        events = [ev for ev in storage.visible_events(shared)
                  if not storage.is_standing(ev) and self._running(ev, now)]
        for event in events:
            event_id = event["id"]
            data = storage.profile_event(profile, event_id)
            section = sections.get(event_id)
            enabled = data.get("level_enabled") or {}
            limited = storage.is_limited(event)

            def start_value(kind, _section=section, _data=data):
                if _section is not None:
                    return int(_section.get(f"baseline_{kind}") or 0)
                # 還沒有紀錄區段：第一次記錄時會把目前值快照成起始值
                if kind in ("points", "clears"):
                    return int(_data.get(f"current_{kind}") or 0)
                return 0

            # 活動預設範圍的任務用得到哪幾種起始值
            metrics = {t.get("metric") for t in event.get("tasks") or []
                       if t.get("cycle") == "event" and not t.get("scope")}
            kinds = []
            if not limited:
                if event.get("type") not in storage.NO_POINTS_TYPES:
                    kinds.append(("points", "積分", "遊戲裡這檔活動目前的積分"))
                if "clears" in metrics:
                    kinds.append(("clears", "已打關卡數", ""))
                if "stamina" in metrics:
                    kinds.append(("stamina", "已消耗體力", "活動任務「累計消耗體力」的目前進度"))
                if "enemies" in metrics:
                    kinds.append(("enemies", "已擊殺敵人", ""))
                if "drops" in metrics:
                    kinds.append(("drops", "已取得道具", ""))
            # 有次數限制的關卡：總共最多幾次（BOSS）、開場先打一次（解鎖鏈）；
            # 限期關卡每一關都有這期的上限
            levels = [lv for lv in event.get("levels") or []
                      if enabled.get(lv["id"], True) is not False
                      and (limited or lv.get("max_total") or lv.get("unlock_first"))]
            if not kinds and not levels:
                continue
            built = True
            self._heading(body, scheduler.event_label(event)
                          + ("（限期關卡，這一期）" if limited else ""))
            self._event_vars[event_id] = {
                kind: self._number_row(body, label, start_value(kind), hint,
                                       f"{scheduler.event_label(event)}的{label}")
                for kind, label, hint in kinds}
            prior = (section or {}).get("baseline_levels") or {}
            level_vars = self._level_vars[event_id] = {}
            for lv in levels:
                name = lv.get("name") or lv["id"]
                if not limited and not lv.get("max_total"):
                    # 只有「開場先打一次」：重點只是打過沒有，勾一下就好
                    var = tk.BooleanVar(value=int(prior.get(lv["id"]) or 0) > 0)
                    ttk.Checkbutton(body, variable=var,
                                    text=f"{name} 已經打過（解鎖鏈：打過之後才開下一關）").grid(
                        row=self._next_row(), column=0, columnspan=3, sticky="w",
                        padx=(dp(12), 0), pady=dp(2))
                    level_vars[lv["id"]] = var
                    continue
                if limited:
                    hint = "這期已經打了幾次"
                else:
                    hint = f"整檔最多 {lv['max_total']} 次" + (
                        "、一定要打滿" if lv.get("must_finish") else "")
                level_vars[lv["id"]] = self._number_row(
                    body, f"{name} 已打", prior.get(lv["id"]),
                    hint, f"{scheduler.event_label(event)}·{name}的已打次數")

        # 固定任務（與活動裡會重置的任務）這一期已完成多少
        progress = scheduler.task_progress(shared, profile, log.get("entries") or [], now)
        period_rows = []
        claim_rows = []
        for task, owner, key in scheduler.iter_tasks(shared):
            state = states.get(key) or {}
            if state.get("enabled") is False or task.get("metric") == "manual":
                continue
            if owner is not None and (storage.is_archived(owner)
                                      or not self._running(owner, now)):
                continue
            info = progress.get(key) or {}
            where = f"{scheduler.event_label(owner)}·" if owner else ""
            if task.get("cycle") != "event":
                if info.get("state") != "active" or not info.get("window_from"):
                    continue
                period_rows.append((task, key, where, info))
            elif any(stamina_of.get(r.get("item"), 0) * int(r.get("qty") or 0) > 0
                     for r in task.get("rewards") or []):
                claim_rows.append((task, key, where, state))

        if period_rows:
            built = True
            self._heading(body, "固定任務：這一期已經做了多少")
            for task, key, where, info in period_rows:
                win_from = info["window_from"]
                state = states.get(key) or {}
                period = state.get("period_done") or {}
                value = period.get("amount") if period.get("from") == win_from else 0
                unit = storage.TASK_METRIC_LABELS.get(task.get("metric"), "")
                start = date.fromisoformat(win_from)
                label = scheduler.PERIOD_NAMES.get(task.get("cycle"), "本期")
                hint = (f"{label}（{start:%m/%d} 起）{unit}，目標 {task.get('amount', 0)}；"
                        "只算這一期，下次重置後就不再加")
                self._period_vars[key] = (
                    self._number_row(body, where + (task.get("name") or key), value, hint),
                    win_from)

        if claim_rows:
            built = True
            self._heading(body, "活動任務：體力獎勵已經領過了")
            ttk.Label(body, text="已經達標、也把體力領出來的勾起來，排程才不會再算一次",
                      foreground="#666666").grid(row=self._next_row(), column=0,
                                                 columnspan=3, sticky="w",
                                                 padx=(dp(12), 0))
            for task, key, where, state in claim_rows:
                var = tk.BooleanVar(value=bool(state.get("reward_claimed")))
                # 同名任務（好幾條都叫「活動任務」）靠條件與目標分辨
                goal = (f"{storage.TASK_METRIC_LABELS.get(task.get('metric'), '')} "
                        f"{task.get('amount', 0)}")
                check = ttk.Checkbutton(
                    body, variable=var,
                    text=f"{where}{task.get('name') or key}（{goal}）")
                check.grid(row=self._next_row(), column=0, columnspan=3, sticky="w",
                           padx=(dp(12), 0), pady=dp(2))
                self._claimed_vars[key] = var
        return built

    # -- 存檔 --------------------------------------------------------------
    def _read(self, var, minimum=0) -> int:
        text = var.get().strip()
        if not text:
            return 0
        return parse_int(text, self._labels.get(str(var), "數字"), minimum)

    def _apply(self) -> bool:
        try:
            events = {}
            for event_id, kinds in self._event_vars.items():
                events[event_id] = {
                    kind: self._read(var, None if kind == "points" else 0)
                    for kind, var in kinds.items()}
            for event_id, levels in self._level_vars.items():
                events.setdefault(event_id, {})["levels"] = {
                    level_id: (int(var.get()) if isinstance(var, tk.BooleanVar)
                               else self._read(var))
                    for level_id, var in levels.items()}
            periods = {key: (self._read(var), win_from)
                       for key, (var, win_from) in self._period_vars.items()}
        except FieldError as exc:
            messagebox.showerror("輸入有誤", str(exc), parent=self)
            return False
        profile = self.profile
        for key, (amount, win_from) in periods.items():
            state = storage.task_state(profile, key)
            if amount > 0:
                state["period_done"] = {"from": win_from, "amount": amount}
            else:
                state.pop("period_done", None)
        for key, var in self._claimed_vars.items():
            storage.task_state(profile, key)["reward_claimed"] = bool(var.get())
        profile["start_progress_done"] = True
        if self.profile_id == self.app.profile_id:
            # 目前這個帳號：set_log_baselines 會存紀錄檔、重算目前值並存帳號設定，
            # 各分頁再照新的值重畫
            if events:
                self.app.set_log_baselines(events=events)
            else:
                storage.save_profile(self.profile_id, profile)
            self.app.reload_tabs()
        else:
            # 別的帳號：畫面上沒開著它，直接寫它自己的紀錄檔與設定檔
            log = storage.load_log(self.profile_id)
            for event in storage.events_of(self.app.shared):
                section = storage.ensure_log_event(log, event, profile)
                storage.set_event_baselines(section, events.get(event["id"]))
            storage.save_log(self.profile_id, log)
            storage.apply_log_to_profile(profile, log, self.app.shared)
            storage.save_profile(self.profile_id, profile)
        self._snapshot = self._values()
        return True

    def _on_ok(self):
        if not self._apply():
            return
        self.proceed = True
        name = self._account_name()
        self.destroy()
        self.app.set_status(
            f"已更新「{name}」的開始前進度（{datetime.now():%H:%M:%S}）")

    def _on_cancel(self):
        """取消：不存、不算。"""
        self.proceed = False
        self.destroy()

    def _on_skip(self):
        """從計算跳出來時按「不補登，直接計算」：照樣算，之後這個帳號不再自動跳。"""
        self.profile["start_progress_done"] = True
        storage.save_profile(self.profile_id, self.profile)
        self.proceed = True
        self.destroy()


# --------------------------------------------------------------------------
# 主視窗
# --------------------------------------------------------------------------

class App(tk.Tk):
    def __init__(self):
        super().__init__()
        init_dpi(self)
        # 版本號只放在「說明 → 關於…」，標題列不放
        self.title("體力分配計算機")
        self.minsize(px(MIN_WIDTH), px(MIN_HEIGHT))
        # 縮放要在建任何元件之前套上，表格欄寬等才會用對的比例建出來
        self._zoom_job = None
        self._zooming = False
        self._apply_zoom(storage.get_ui_zoom(), save=False)
        # 最小尺寸要等縮放套上才算得出來，所以大小位置放在縮放後面決定
        self._place_main_window()
        # 所有 tk.Menu（選單列展開的項目、下拉按鈕、右鍵選單）都用會縮放的字型；
        # 選單列本身在 _build_menubar 改回 TkMenuFont
        self.option_add("*Menu.font", menu_font())
        # 兩行字的按鈕：ttk 按鈕的多行文字預設靠左，另外給一個置中的樣式
        ttk.Style(self).configure("TwoLine.TButton", justify="center")
        self._style_notebook_tabs()

        self._quarantine_told: set = set()
        storage.ensure_data_files()
        self.shared = storage.load_shared()
        self._mark_shared_clean()
        self.last_shared_sync = "same"      # 最近一次 save_all 對共用設定做了什麼
        self._save_cancelled = False
        self.profile_id = storage.get_active_profile_id()
        self.profile = storage.load_profile(self.profile_id)
        storage.sync_levels(self.profile, self.shared)
        # 帳號裡的推導欄位可能跟紀錄對不上（見 sync_derived_from_log）。
        # 只修記憶體這份，不另外存檔——下次任何存檔都會一併寫回。
        self.sync_derived_from_log()

        self._switching = False
        # 上次存檔時帳號資料的樣子（_profile_sig）。None：還沒存過，下次一定寫檔
        self._profile_clean = None
        self._build_menubar()
        self._build_toolbar()

        self.notebook = ttk.Notebook(self)
        self.notebook.pack(fill="both", expand=True, padx=dp(10), pady=(0, dp(6)))
        self.last_plan = None       # 最近一次算出的排程，供每日紀錄帶入預設值
        # 分頁順序依實際使用流程：先設定 → 再計算 → 最後每天回來記錄
        self.tabs = [
            (StatusTab(self.notebook, self), "目前狀態"),
            (EventsTab(self.notebook, self), "活動設定"),
            (GlobalTab(self.notebook, self), "排程設定"),
            (RoutineTab(self.notebook, self), "任務進度"),
            (CalcTab(self.notebook, self), "計算結果"),
            (LogTab(self.notebook, self), "每日紀錄"),
        ]
        for tab, label in self.tabs:
            self.notebook.add(tab, text=label)
        # 每天第一次打開「每日紀錄」時提醒今天該領的體力（見 pending_claims）
        # 已經提醒過的 (帳號, 日期)：幾個帳號來回切，每個帳號每天只提醒一次
        self._claim_reminded: set[tuple] = set()
        self.notebook.bind("<<NotebookTabChanged>>", self._on_tab_changed)

        bottom = ttk.Frame(self)
        bottom.pack(fill="x", padx=dp(12), pady=(0, dp(8)))
        self._build_zoom_bar(bottom)
        self.status = ttk.Label(bottom, text="", anchor="w", justify="left",
                                foreground="#555555")
        self.status.pack(side="left", fill="x", expand=True)
        # 狀態列的字比視窗寬時換行（計算中的進度很長），寬度一變就重折
        self._status_text = ""
        self.status.bind("<Configure>", lambda _e: self._rewrap_status(), add="+")

        self.reload_tabs()
        self.protocol("WM_DELETE_WINDOW", self.on_close)
        self.after(400, self._warn_quarantined)

    def report_callback_exception(self, exc, val, tb):
        """按鈕／事件處理裡沒接住的例外。

        平常是用 pythonw 啟動的，沒有主控台——預設行為（印到 stderr）等於什麼都
        沒發生，看起來就是「按了沒反應」。寫進 error.log 並跳出來講。
        """
        try:
            text = "".join(traceback.format_exception(exc, val, tb))
        except RecursionError:
            # 遞迴太深的錯誤：呼叫到這裡時堆疊已經快滿了，連格式化都做不了。
            # 這裡再丟例外的話 Tk 會直接把整個程式結束掉，所以只寫錯誤名稱
            text = f"{getattr(exc, '__name__', exc)}: {val}（呼叫層數太深，無法列出細節）\n"
        try:
            with (storage.APP_DIR / "error.log").open("a", encoding="utf-8") as fh:
                fh.write(f"[{datetime.now():%Y-%m-%d %H:%M:%S}]\n{text}\n")
        except OSError:
            pass
        try:
            messagebox.showerror(
                "發生未預期的錯誤",
                "剛剛那個操作出錯了，沒有完成。詳細內容已寫進 error.log：\n\n"
                + text[-1500:], parent=self)
        except tk.TclError:
            pass

    @staticmethod
    def _rel(path):
        """資料夾內的相對路徑：profiles/main.json 和 logs/main.json 才分得出來。"""
        try:
            return path.relative_to(storage.APP_DIR).as_posix()
        except ValueError:
            return str(path)

    def _warn_quarantined(self):
        """資料檔讀不出來時講一聲，並說留底的檔案在哪（見 storage._quarantine）。"""
        fresh = {path: copy_path for path, copy_path in storage.quarantined.items()
                 if path not in self._quarantine_told}
        if not fresh:
            return
        self._quarantine_told.update(fresh)
        messagebox.showwarning(
            "資料檔讀不出來",
            "下面的資料檔讀不出來（格式壞掉或被別的程式佔用），"
            "這次先用空白的預設內容。\n"
            "之後一存檔就會把原檔蓋掉，所以已經先留了一份：\n\n"
            + "\n".join(f"　{self._rel(path)} → {copy_path.name}"
                        for path, copy_path in fresh.items()),
            parent=self)

    def _build_menubar(self):
        """視窗頂端的選單列（像記事本的「檔案／編輯」）。

        用 Windows 原生選單列：選單列那一排的字是系統畫的，不跟著縮放；
        展開的項目用 menu_font()，會跟著縮放。
        """
        menubar = tk.Menu(self, font="TkMenuFont")
        settings = tk.Menu(menubar, tearoff=False)
        profiles = tk.Menu(settings, tearoff=False)
        profiles.add_command(label="新增…", command=self._add_profile)
        profiles.add_command(label="刪除…", command=self._delete_profile)
        settings.add_cascade(label="帳號", menu=profiles)
        settings.add_separator()
        settings.add_command(label="重置與回復…", command=lambda: ClocksDialog(self))
        settings.add_command(label="任務清單…", command=lambda: RoutineTasksDialog(self))
        settings.add_command(label="獎勵道具…", command=lambda: ItemsDialog(self))
        settings.add_command(label="活動類型預設…", command=lambda: TypeDefaultsDialog(self))
        settings.add_separator()
        settings.add_command(label="補登開始前的進度…", command=self._open_start_progress)
        settings.add_separator()
        # 整個存出或換回：共用設定、所有帳號、每日紀錄。匯入前會確認並自動備份
        bundle = tk.Menu(settings, tearoff=False)
        bundle.add_command(label="匯入…", command=self._import_all)
        bundle.add_command(label="匯出…", command=self._export_all)
        settings.add_cascade(label="匯入/匯出", menu=bundle)
        menubar.add_cascade(label="設定", menu=settings)

        help_menu = tk.Menu(menubar, tearoff=False)
        help_menu.add_command(label="使用說明…", command=self._show_help)
        help_menu.add_separator()
        help_menu.add_command(label="關於…", command=self._show_about)
        menubar.add_cascade(label="說明", menu=help_menu)
        self.config(menu=menubar)

    # -- 畫面縮放 --------------------------------------------------------
    def _build_zoom_bar(self, box):
        """右下角的縮放列：－ 滑桿 ＋ 100%（像 Excel）。Ctrl +／−／0、Ctrl＋滾輪也行。"""
        bar = ttk.Frame(box)
        bar.pack(side="right")
        ttk.Button(bar, text="－", width=2,
                   command=lambda: self.zoom_by(-ZOOM_STEP)).pack(side="left")
        self.zoom_var = tk.DoubleVar(value=_zoom["percent"])
        self._slider_held = False
        self._slider_percent = None
        slider = ttk.Scale(bar, from_=ZOOM_MIN, to=ZOOM_MAX, variable=self.zoom_var,
                           length=dp(120), command=self._on_zoom_slide)
        slider.pack(side="left", padx=dp(4))
        slider.bind("<ButtonPress-1>", self._on_slider_press, add="+")
        slider.bind("<ButtonRelease-1>", self._on_slider_release, add="+")
        ttk.Button(bar, text="＋", width=2,
                   command=lambda: self.zoom_by(ZOOM_STEP)).pack(side="left")
        self.zoom_label = ttk.Label(bar, width=5, anchor="e", cursor="hand2")
        self.zoom_label.pack(side="left", padx=(dp(6), 0))
        # 點百分比回到 100%
        self.zoom_label.bind("<Button-1>", lambda _e: self.zoom_to(100))
        self._update_zoom_label()

        for seq in ("<Control-plus>", "<Control-equal>", "<Control-KP_Add>"):
            self.bind_all(seq, lambda _e: self.zoom_by(ZOOM_STEP))
        for seq in ("<Control-minus>", "<Control-KP_Subtract>"):
            self.bind_all(seq, lambda _e: self.zoom_by(-ZOOM_STEP))
        for seq in ("<Control-Key-0>", "<Control-KP_0>", "<Control-KP_Insert>"):
            self.bind_all(seq, lambda _e: self.zoom_to(100))
        self.bind_all("<Control-MouseWheel>",
                      lambda e: self.zoom_by(ZOOM_STEP if e.delta > 0 else -ZOOM_STEP))
        install_ime_font_sync(self)

    def _update_zoom_label(self, percent=None):
        self.zoom_label.config(text=f"{percent or _zoom['percent']}%")

    def zoom_by(self, step):
        # 以 10 為一格對齊：滑桿拖到 117% 時按 ＋ 會到 120%，不是 127%
        current = _zoom["percent"]
        target = (current // ZOOM_STEP + (1 if step > 0 else 0)) * ZOOM_STEP
        if step < 0 and current % ZOOM_STEP == 0:
            target = current - ZOOM_STEP
        self.zoom_to(target)
        return "break"

    def zoom_to(self, percent):
        if self._zoom_job is not None:
            self.after_cancel(self._zoom_job)
            self._zoom_job = None
        self._apply_zoom(percent)
        return "break"

    def _on_zoom_slide(self, value):
        # 拖動時只先改數字：每換一次字型整個畫面都要重排
        percent = round(float(value) / 5) * 5
        self._update_zoom_label(percent)
        self._slider_percent = percent
        if self._zoom_job is not None:
            self.after_cancel(self._zoom_job)
            self._zoom_job = None
        # 滑鼠還按著就等放開才縮放：縮放會讓右下角這排變寬、把滑桿往左推，
        # 滑鼠停在原地等於又往右拉了一段，一路被推到 200%
        if not self._slider_held:
            self._zoom_job = self.after(200, lambda: self.zoom_to(percent))

    def _on_slider_press(self, _event):
        self._slider_held = True
        self._slider_percent = None

    def _on_slider_release(self, _event):
        self._slider_held = False
        percent = self._slider_percent
        self._slider_percent = None
        if percent is not None and percent != _zoom["percent"]:
            # 用計時器而不是直接縮放：放開的事件可能是在縮放途中被處理到的
            # （_frozen_redraw 收尾會處理視窗事件），那時直接呼叫會被略過
            self._zoom_job = self.after(1, lambda: self.zoom_to(percent))

    def _apply_zoom(self, percent, save=True):
        # _frozen_redraw 收尾時會處理視窗事件，按著 Ctrl＋ 不放可能又跑進來；
        # 縮放到一半不能再套另一個比例，那一下就略過
        if self._zooming:
            return
        self._zooming = True
        try:
            self._apply_zoom_now(percent, save)
        finally:
            self._zooming = False

    def _zoom_minsize(self, percent):
        """縮放到 percent% 時視窗的最小尺寸（不超過螢幕的工作區域）。"""
        percent = max(ZOOM_MIN, min(ZOOM_MAX, int(round(percent))))
        scale = percent / 100 * _zoom["dpi"]
        _x, _y, area_w, area_h = self._work_area()
        extra_w, extra_h = self._frame_size()
        return (min(round(MIN_WIDTH * scale), area_w - extra_w),
                min(round(MIN_HEIGHT * scale), area_h - extra_h))

    # -- 主視窗大小與位置 ---------------------------------------------------
    def _work_area(self, rect=None):
        return work_area(rect, (self.winfo_screenwidth(), self.winfo_screenheight()))

    @staticmethod
    def _frame_size():
        """外框比內容區多出來的 (寬, 高)：左右邊框、標題列＋上下邊框。

        視窗還沒顯示量不到，用 Windows 10/11 的大概值估（含看不見的拖拉邊框）。
        """
        return dp(16), dp(_TITLE_BAR + 16)

    def _place_main_window(self):
        """照螢幕大小（和上次關閉時的大小位置）決定主視窗怎麼打開，見 plan_main_window。"""
        min_w, min_h = self._zoom_minsize(_zoom["percent"])
        plan = plan_main_window(
            (dp(_MAIN_SIZE[0]), dp(_MAIN_SIZE[1])), (min_w, min_h),
            storage.get_window_geometry(), self._work_area, self._frame_size())
        self.geometry(f"{plan['width']}x{plan['height']}+{plan['x']}+{plan['y']}")
        # 最大化時也要先記好一般大小：使用者按「還原」、或最大化著關掉，
        # 下次才有合理的大小可以回去
        self._normal_geometry = (plan["x"], plan["y"], plan["width"], plan["height"])
        if plan["zoomed"]:
            try:
                self.state("zoomed")
            except tk.TclError:
                pass
        self.bind("<Configure>", self._remember_geometry, add="+")

    def _remember_geometry(self, event):
        """記下「一般狀態」的大小位置。

        最大化、縮到工作列時 geometry 量到的不是使用者自己拉的大小，
        關窗時存那個的話下次打開就變成整個螢幕大的一般視窗。
        """
        if event.widget is not self:
            return
        try:
            if self.state() != "normal":
                return
            geometry = parse_geometry(self.geometry())
        except tk.TclError:
            return
        if geometry:
            self._normal_geometry = geometry

    def _save_geometry(self):
        geometry = getattr(self, "_normal_geometry", None)
        if not geometry:
            return
        try:
            zoomed = self.state() == "zoomed"
        except tk.TclError:
            zoomed = False
        try:
            storage.set_window_geometry(*geometry, zoomed=zoomed)
        except OSError:
            pass        # 存不了就下次照預設開，不擋關窗

    def _apply_zoom_now(self, percent, save):
        min_w, min_h = self._zoom_minsize(percent)
        if self.winfo_ismapped():
            # 新的最小尺寸比視窗大時，要在凍結「之前」先把視窗撐大：凍結中撐大的話，
            # 多出來那塊沒人畫，會先黑一塊直到解凍
            width, height = self.winfo_width(), self.winfo_height()
            if width < min_w or height < min_h:
                self.minsize(min_w, min_h)
                self.geometry(f"{max(width, min_w)}x{max(height, min_h)}")
                self.update_idletasks()
                _drain_window_events(self)
                self.update_idletasks()
        # 凍結重繪：所有重排跑完才一次畫出來，不會看到中間過程（見 _frozen_redraw）
        with _frozen_redraw(self):
            percent = apply_zoom(self, percent)
            self.minsize(min_w, min_h)
            if hasattr(self, "zoom_var"):
                self.zoom_var.set(percent)
                self._update_zoom_label()
            # 版面傳遞是一層層往外推的，跑兩輪讓它排完；捲軸要在排完後才補。
            # 啟動時視窗還沒顯示就不做——提早跑 idle 會讓空視窗先閃出來
            if self.winfo_ismapped():
                reloosen_all(self)
                # 排版 → 處理大小改變的事件 → 可捲動區塊重新折行／定大小；
                # 折行會再改變需要的高度，所以來兩輪
                for _ in range(2):
                    self.update_idletasks()
                    _drain_window_events(self)
                    # 開著的對話框釘住的欄寬是照舊字型量的（見 RecordDialog._pin_columns）
                    for dialog in _descendants(self, RecordDialog):
                        dialog._pin_columns()
                    for frame in _descendants(self, ScrollableFrame):
                        frame.settle()
                for dialog in _descendants(self, RecordDialog):
                    dialog.refit_after_zoom()
                self.update_idletasks()
            _refresh_tree_scrollbars(self)
        if save:
            try:
                storage.set_ui_zoom(percent)
            except OSError:
                pass        # 記不住就算了，不影響使用

    def _show_help(self):
        """用系統預設的瀏覽器打開程式資料夾裡的操作手冊（網頁版）。"""
        name = MANUAL_HTML.name
        if not MANUAL_HTML.is_file():
            messagebox.showerror(
                "使用說明", f"找不到操作手冊：\n{MANUAL_HTML}\n\n"
                            f"請確認程式資料夾裡有「{name}」。", parent=self)
            return
        try:
            os.startfile(MANUAL_HTML)
        except OSError as exc:
            messagebox.showerror(
                "使用說明", f"打不開操作手冊：{exc}\n\n"
                            f"可以直接到程式資料夾雙擊「{name}」。", parent=self)

    def _show_about(self):
        messagebox.showinfo(
            "關於",
            f"體力分配計算機\n版本 v{__version__}\n資料格式版本 {storage.SCHEMA_VERSION}\n\n"
            "非官方粉絲工具，與遊戲官方無關。\n專案網址（下載新版、回報問題）：",
            parent=self, link=PROJECT_URL)

    def _style_notebook_tabs(self):
        """選中的分頁頁籤用淺藍底，一眼看得出現在在哪一頁。

        Windows 的 vista 主題頁籤是系統畫的圖，background 設了也不理，
        選中跟沒選中只差一點點。換成 default 主題的頁籤元件（純色＋凸起邊框），
        background 才吃得到。
        """
        style = ttk.Style(self)
        try:
            style.element_create("Plain.Notebook.tab", "from", "default")
        except tk.TclError:
            pass        # 已經建過（同一個 Tk 只能建一次）
        style.layout("TNotebook.Tab", [
            ("Plain.Notebook.tab", {"sticky": "nswe", "children": [
                # 不放 Notebook.focus：它會在選中的頁籤字外面畫一圈虛線，
                # 淺藍底已經看得出選中哪一頁，虛線只是多餘
                ("Notebook.padding", {"side": "top", "sticky": "nswe", "children": [
                    ("Notebook.label", {"side": "top", "sticky": ""})]})]})])
        style.configure("TNotebook.Tab", padding=(dp(10), dp(3)),
                        background="#e5e7eb", borderwidth=1)
        style.map("TNotebook.Tab",
                  background=[("selected", "#bfdbfe"), ("active", "#eef2f7")],
                  foreground=[("selected", "#1e3a8a")])

    def _build_toolbar(self):
        bar = ttk.Frame(self, padding=(dp(10), dp(10), dp(10), dp(6)))
        bar.pack(fill="x")
        ttk.Label(bar, text="帳號").pack(side="left")
        self.profile_var = tk.StringVar()
        self.profile_box = ttk.Combobox(bar, textvariable=self.profile_var,
                                        state="readonly", width=18)
        self.profile_box.pack(side="left", padx=(dp(6), dp(12)))
        self.profile_box.bind("<<ComboboxSelected>>", self._on_profile_selected)
        ttk.Button(bar, text="儲存", command=lambda: self.save_all(silent=False)
                   ).pack(side="left")
        self._refresh_profile_box()

    def _refresh_profile_box(self):
        self._profiles = storage.list_profiles()
        self._switching = True
        self.profile_box["values"] = [name for _pid, name in self._profiles]
        for pid, name in self._profiles:
            if pid == self.profile_id:
                self.profile_var.set(name)
                break
        self._switching = False

    def _on_profile_selected(self, _event=None):
        if self._switching:
            return
        index = self.profile_box.current()
        if index < 0:
            return
        new_id = self._profiles[index][0]
        if new_id == self.profile_id:
            return
        # 切換前先把目前分頁的內容存回檔案
        if not self.save_all(silent=True):
            self._refresh_profile_box()
            return
        self._switch_to(new_id)
        self.set_status(f"已切換到「{self.profile.get('profile_name', new_id)}」")

    def _switch_to(self, profile_id: str):
        """載入另一個帳號並刷新畫面。呼叫前要自己決定要不要先存目前這份。"""
        self.profile_id = profile_id
        self.profile = storage.load_profile(profile_id)
        storage.sync_levels(self.profile, self.shared)
        self.sync_derived_from_log()
        storage.set_active_profile_id(profile_id)
        # save_all() 內的 _refresh_profile_box() 會把選單設回舊名稱，要再刷一次
        self._refresh_profile_box()
        self.reload_tabs()
        self._warn_quarantined()
        # 停在每日紀錄時換帳號不會觸發分頁切換，要自己檢查；等畫面刷完再跳
        self.after_idle(self._maybe_remind_claims)

    # -- 帳號增刪、匯入匯出 ----------------------------------------------
    def _add_profile(self):
        name = ask_string("新增帳號", "新帳號的名稱：", parent=self)
        if name is None:
            return
        name = name.strip()
        if not name:
            messagebox.showwarning("新增帳號", "名稱不能空白。", parent=self)
            return
        if profile_name_taken(name):
            messagebox.showwarning(
                "新增帳號", f"已經有叫「{name}」的帳號了，請換一個名稱。\n"
                            "（同名的帳號在上方的帳號選單分不出來）", parent=self)
            return
        current = self.profile.get("profile_name") or self.profile_id
        copy_it = messagebox.askyesnocancel(
            "新增帳號",
            f"要複製「{current}」目前的設定嗎？\n\n"
            "「是」：複製設定（每日紀錄不複製）\n"
            "「否」：從空白開始\n"
            "「取消」：不新增",
            parent=self)
        if copy_it is None:
            return
        if not self.save_all(silent=True):
            return
        new_id = storage.create_profile(name, self.profile if copy_it else None)
        self._switch_to(new_id)
        self.set_status(f"已新增並切換到「{name}」")

    def _delete_profile(self):
        if len(storage.list_profiles()) <= 1:
            messagebox.showinfo("刪除帳號", "只剩這一個帳號，不能刪除。",
                                parent=self)
            return
        name = self.profile.get("profile_name") or self.profile_id
        if not messagebox.askyesno(
                "刪除帳號",
                f"確定要刪除「{name}」嗎？\n\n"
                "它的每日紀錄會一起刪除。檔案會先搬到 _deleted 資料夾，"
                "需要的話還能找回來。\n\n"
                "如果有別的視窗正開著這個帳號，請先把它關掉，"
                "否則那個視窗存檔時又會把它寫回來。",
                icon="warning", parent=self):
            return
        # 不先 save_all：存了只是把馬上要刪的檔再寫一次。
        # 共用設定有改的話還是要存，不然會跟著這個帳號一起丟掉
        self._save_cancelled = False
        if not self.collect_all():
            return
        if self._sync_shared() == "cancel":
            return
        folder = storage.delete_profile(self.profile_id)
        self._switch_to(storage.list_profiles()[0][0])
        self.set_status(f"已刪除「{name}」，檔案留在 {folder}／")

    def _export_all(self):
        if not self.save_all(silent=True):
            return
        path = filedialog.asksaveasfilename(
            parent=self, title="匯出全部設定",
            initialdir=str(storage.APP_DIR),
            defaultextension=".json",
            initialfile=f"PSCalculator備份_{date.today():%Y%m%d}.json",
            filetypes=[("JSON 檔", "*.json"), ("所有檔案", "*.*")])
        if not path:
            return
        with open(path, "w", encoding="utf-8") as fh:
            json.dump(storage.export_bundle(), fh, ensure_ascii=False, indent=2)
        self.set_status(f"已匯出到 {path}")

    def _import_all(self):
        path = filedialog.askopenfilename(
            parent=self, title="匯入全部設定",
            initialdir=str(storage.APP_DIR),
            filetypes=[("JSON 檔", "*.json"), ("所有檔案", "*.*")])
        if not path:
            return
        try:
            with open(path, "r", encoding="utf-8-sig") as fh:
                bundle = json.load(fh)
            storage._check_bundle(bundle)
        except (OSError, ValueError) as exc:
            messagebox.showerror("匯入失敗", f"讀不出這個檔案：\n{exc}", parent=self)
            return
        names = "、".join((data.get("profile_name") or pid)
                         for pid, data in bundle["profiles"].items())
        if not messagebox.askyesno(
                "匯入全部設定",
                f"匯出時間：{bundle.get('exported_at') or '不明'}\n"
                f"帳號：{names}\n\n"
                "目前所有的設定、帳號、每日紀錄都會被這個檔案整個取代"
                "（取代前會自動備份）。\n\n"
                "請先關掉其他開著的視窗，否則它們存檔時會把舊資料蓋回去。\n\n"
                "確定要匯入嗎？",
                icon="warning", parent=self):
            return
        backup = storage.import_bundle(bundle)
        self.shared = storage.load_shared()
        self._mark_shared_clean()
        self.last_plan = None
        self._switch_to(storage.get_active_profile_id())
        self.set_status(f"已匯入，匯入前的資料備份在 {backup}／")

    # -- 存取 ------------------------------------------------------------
    def collect_all(self, skip=None) -> bool:
        for tab, _label in self.tabs:
            if tab is skip:
                continue
            if not tab.collect():
                return False
        return True

    def _mark_shared_clean(self):
        """記下「記憶體這份共用設定跟磁碟上的一樣」的當下狀態。讀檔、寫檔後呼叫。"""
        self._shared_stamp = storage.shared_stamp()
        self._shared_clean = storage.shared_fingerprint(self.shared)

    def _sync_shared(self) -> str:
        """把共用設定跟磁碟對齊。回傳 "same"／"written"／"reloaded"／"cancel"。

        同時開好幾個視窗（各用不同帳號）時，每個視窗都握著自己啟動時讀到的
        共用設定。無條件寫回的話，最後存檔的視窗會用舊版蓋掉別的視窗改過的
        活動設定／排程設定／「設定」選單。所以：沒改過就不寫；磁碟被別的視窗改過
        就重讀；兩邊都改過才問使用者。
        """
        dirty = storage.shared_fingerprint(self.shared) != self._shared_clean
        changed_outside = storage.shared_stamp() != self._shared_stamp
        if dirty and changed_outside:
            keep_mine = messagebox.askyesnocancel(
                "共用設定被其他視窗改過",
                "這個視窗改了共用設定（活動設定／排程設定／「設定」選單），\n"
                "但另一個視窗也改過並且已經存檔，兩份只能留一份。\n\n"
                "「是」：保留這個視窗的，蓋掉另一個視窗的修改\n"
                "「否」：改用另一個視窗的，放棄這個視窗對共用設定的修改\n"
                "「取消」：這次先不存",
                parent=self)
            if keep_mine is None:
                return "cancel"
            dirty, changed_outside = keep_mine, not keep_mine
        if dirty:
            storage.save_shared(self.shared)
            self._mark_shared_clean()
            return "written"
        if changed_outside:
            try:
                self.shared = storage.load_shared()
            except (OSError, ValueError):
                # 另一個視窗正寫到一半或檔案壞了：這次先維持原樣，下次存檔再對
                return "same"
            self._mark_shared_clean()
            return "reloaded"
        return "same"

    def save_all(self, silent: bool = True) -> bool:
        # 活動名稱散落在好幾個分頁（活動下拉選單、排程設定的優先序與特殊日、
        # 每日紀錄的分區標題），而那些只在各自的 load() 裡才重建。改名之後
        # 要整批刷新，否則到處都留著舊名字。
        before = {ev["id"]: scheduler.event_label(ev)
                  for ev in storage.events_of(self.shared)}
        self._save_cancelled = False
        if not self.collect_all():
            return False
        self.last_shared_sync = self._sync_shared()
        if self.last_shared_sync == "cancel":
            self._save_cancelled = True
            return False
        storage.sync_levels(self.profile, self.shared)
        # 切分頁每次都會走到這裡。帳號資料跟上次存的一模一樣、共用設定也沒寫入／重讀，
        # 就不必寫檔，也不必重建「任務進度」——重建會讓切過去的畫面看得到在重畫
        profile_sig = self._profile_sig()
        unchanged = (profile_sig == self._profile_clean
                     and self.last_shared_sync == "same")
        if not unchanged:
            storage.save_profile(self.profile_id, self.profile)
            self._profile_clean = profile_sig
        storage.set_active_profile_id(self.profile_id)
        self._refresh_profile_box()
        # 任務進度一個任務一列；活動任務是在「活動設定」改的，存檔後要重建那張表，
        # 新加的活動任務才看得到。它的編輯在 collect_all() 已收回 self.profile，重建不會丟
        for tab, _label in self.tabs:
            if isinstance(tab, RoutineTab) and not unchanged:
                self._load_tab(tab)
            elif isinstance(tab, EventsTab):
                tab.refresh_auto_rules()    # 排程設定的自動套用規則可能剛改過
        if self.last_shared_sync == "reloaded":
            # 下面「silent 不重載」的例外：共用設定整份換掉了，畫面不重載就會
            # 留著舊的，下次 collect 又把舊值收回來寫出去。帳號自己的欄位上面
            # 已經收進 self.profile，重載不會丟。
            self.reload_tabs()
            self.set_status("共用設定已被其他視窗更新，已重新載入")
            return True
        if not silent:
            self.set_status(f"已儲存（{datetime.now():%H:%M:%S}）")
            after = {ev["id"]: scheduler.event_label(ev)
                     for ev in storage.events_of(self.shared)}
            if after != before:
                # 只掛在使用者主動按「儲存」這條路上。silent=True 的幾個呼叫點
                # （切帳號、關視窗、開始計算）後面都還有自己的動作，
                # 中途把所有分頁重載會把它們正在讀的欄位洗掉。
                self.reload_tabs()
        return True

    def on_events_changed(self):
        """活動被新增／刪除之後，所有分頁都要重新載入。"""
        storage.sync_levels(self.profile, self.shared)
        self.reload_tabs()

    def _open_start_progress(self):
        if not self.collect_all() or not self.save_all(silent=True):
            return
        StartProgressDialog(self)

    def needs_start_progress(self) -> bool:
        """第一次計算前要不要先跳「補登開始前的進度」。

        這個帳號一筆每日紀錄都沒有、沒填過也沒略過、而且有進行中的活動才跳。
        """
        if self.profile.get("start_progress_done") or self.has_log_entries():
            return False
        now = datetime.now()
        return any(StartProgressDialog._running(ev, now)
                   for ev in storage.visible_events(self.shared)
                   if not storage.is_standing(ev))

    def reload_tabs(self):
        for tab, _label in self.tabs:
            self._load_tab(tab)

    def _profile_sig(self) -> str:
        return json.dumps(self.profile, sort_keys=True, ensure_ascii=False, default=str)

    def _view_key(self) -> tuple:
        """分頁畫面依賴的所有東西：帳號、共用設定、每日紀錄（含計畫）、現在幾點幾分。

        跟分頁上次 load() 時一樣，就代表畫面還是對的，不用重畫。
        倒數、今日待辦、重置時刻都看現在時間，所以時間算到分鐘。
        """
        return (self.profile_id, self._profile_sig(),
                storage.shared_fingerprint(self.shared),
                json.dumps(storage.load_log(self.profile_id), sort_keys=True,
                           ensure_ascii=False, default=str),
                id(self.last_plan), datetime.now().strftime("%Y-%m-%d %H:%M"))

    def _load_tab(self, tab):
        tab.load()
        tab._view_key = self._view_key()

    def has_log_entries(self) -> bool:
        """是否已經有每日紀錄（有的話積分/關數改由紀錄推導）。"""
        return storage.has_entries(storage.load_log(self.profile_id))

    def log_entries(self) -> list[dict]:
        """每日紀錄。計算時要用它把已經做掉的部分扣掉。"""
        return list(storage.load_log(self.profile_id).get("entries") or [])

    @staticmethod
    def plan_fingerprint(shared) -> list:
        """計畫算的是哪幾檔活動、什麼期間。

        存計畫時記下來，讀回來時比對——換了活動或改了起訖日之後，
        舊計畫就不再適用了，顯示它比顯示「還沒算過」更危險。
        名稱不算在內：計畫與紀錄都依活動 id，改名不影響計畫。
        """
        return [{"id": ev.get("id"),
                 "start": ev.get("start_date"), "end": ev.get("end_date")}
                for ev in storage.events_of(shared)]

    # -- 信箱／任務獎勵的領取提醒 ----------------------------------------
    def _today(self) -> str:
        reset = scheduler.parse_clock(self.shared.get("daily_reset_time"), "05:00")
        return scheduler.task_day_of(datetime.now(), reset).isoformat()

    def _mail_source(self, ref):
        """存入計畫時記下的信箱 ref → 現在 profile 裡的那一筆（刪掉了就是 None）。"""
        for source in self.profile.get("stamina_sources") or []:
            if (source.get("kind") == "mail"
                    and source.get("day_date") == ref.get("day_date")
                    and int(source.get("amount") or 0) == int(ref.get("amount") or 0)
                    and str(source.get("note") or "").strip() == (ref.get("note") or "")):
                return source
        return None

    def pending_claims(self) -> list[dict]:
        """存入的計畫建議今天（或更早）要領、還沒勾已領取的那幾筆。"""
        plan = self.stored_plan() or {}
        today = self._today()
        pending = []
        for claim in plan.get("claims") or []:
            if (claim.get("claim_day") or "9999") > today:
                continue
            ref = claim.get("ref") or {}
            if ref.get("kind") == "mail":
                source = self._mail_source(ref)
                if source is None or source.get("claimed"):
                    continue
            elif ref.get("kind") == "task":
                state = (self.profile.get("task_state") or {}).get(ref.get("key")) or {}
                if state.get("reward_claimed"):
                    continue
            else:
                continue
            pending.append(claim)
        return pending

    def mark_claimed(self, refs) -> bool:
        """把這幾筆記成已領取並存檔。畫面上還沒存的編輯先收進來，免得被蓋掉。"""
        if not refs:
            return True
        if not self.collect_all():
            return False
        for ref in refs:
            if ref.get("kind") == "mail":
                source = self._mail_source(ref)
                if source is not None:
                    source["claimed"] = True
                    source.setdefault("claimed_date", self._today())
            elif ref.get("kind") == "task":
                storage.task_state(self.profile, ref["key"])["reward_claimed"] = True
        storage.save_profile(self.profile_id, self.profile)
        for tab, _label in self.tabs:
            if isinstance(tab, (GlobalTab, RoutineTab)):
                tab.load()
        self.set_status(f"已記成已領取：{len(refs)} 筆")
        return True

    def _on_tab_changed(self, _event=None):
        current = self.notebook.index("current")
        previous = getattr(self, "_tab_index", None)
        self._tab_index = current
        if previous is not None and previous != current and not self._autosave():
            # 欄位格式有誤（collect 已經跳出錯誤訊息）：退回原本那頁讓使用者改，
            # 不然錯的值留在看不到的分頁裡，之後每次存檔都卡住
            if not self._save_cancelled:
                self._tab_index = previous
                self.notebook.select(previous)
            return
        self._maybe_remind_claims()

    def _autosave(self) -> bool:
        """切換分頁時自動存檔。跟按「儲存」一樣，活動改名後整批刷新各分頁。"""
        before = {ev["id"]: scheduler.event_label(ev) for ev in storage.events_of(self.shared)}
        if not self.save_all(silent=True):
            return False
        if self.last_shared_sync != "reloaded":     # reloaded 的話 save_all 已經重載過
            after = {ev["id"]: scheduler.event_label(ev) for ev in storage.events_of(self.shared)}
            if after != before:
                self.reload_tabs()
            else:
                self._refresh_arrived_tab()
            self.set_status(f"已自動儲存（{datetime.now():%H:%M:%S}）")
        return True

    def _refresh_arrived_tab(self):
        """切過去的那一頁照剛存好的資料重畫。

        改了活動的起訖日、加成、關卡、任務（名稱沒變）時，「目前狀態」「任務進度」
        「每日紀錄」顯示的都是舊的。這時所有分頁都已經存好了，重畫不會洗掉
        任何編輯。只重畫這幾個看資料的分頁；「計算結果」的 load() 自己會判斷
        要不要清掉已經填的體力。活動設定、排程設定是編輯頁，資料就是在那裡改的。

        資料跟這一頁上次 load() 時完全一樣（見 _view_key）就不重畫：重建表格會讓
        剛切過來的畫面看得到元件一個個畫出來。其他地方直接呼叫 tab.load() 的
        不會更新記號，下次切過來就照舊重畫，不會漏。
        """
        try:
            tab = self.tabs[self.notebook.index("current")][0]
        except (tk.TclError, IndexError):
            return
        if isinstance(tab, (StatusTab, RoutineTab, LogTab, CalcTab)):
            if getattr(tab, "_view_key", None) != self._view_key():
                self._load_tab(tab)

    def _maybe_remind_claims(self):
        """畫面停在「每日紀錄」時，提醒今天該領的體力（每個帳號每天一次）。

        切換分頁與切換帳號都會叫到這裡——停在每日紀錄時換帳號，分頁沒變，
        只掛在分頁切換事件上的話新帳號就不會檢查。
        """
        try:
            tab = self.tabs[self.notebook.index("current")][0]
        except (tk.TclError, IndexError):
            return
        if not isinstance(tab, LogTab):
            return
        key = (self.profile_id, self._today())
        if key in self._claim_reminded:
            return
        claims = self.pending_claims()
        if not claims:
            return
        self._claim_reminded.add(key)
        dialog = ClaimReminderDialog(self, claims)
        if dialog.result:
            self.mark_claimed(dialog.result)

    def stored_plan(self):
        """存下來的計畫（含分析文字）；沒有就回傳 None。

        計算後新增／刪除了活動、或改了起訖日，舊計畫照樣回傳，讓之前
        算好的每日打法還看得到；變了什麼由 plan_changes() 提醒。
        """
        plan = storage.load_log(self.profile_id).get("plan")
        return plan or None

    def plan_changes(self) -> dict:
        """存入計畫之後活動有什麼變動。

        回傳 {"added": [活動名稱], "removed": 檔數, "dated": [活動名稱]}；
        沒有計畫、舊格式計畫（沒記活動）或都沒變時三項都是空的。
        """
        changes = {"added": [], "removed": 0, "dated": []}
        plan = storage.load_log(self.profile_id).get("plan") or {}
        stamp = plan.get("events")
        if not stamp:
            return changes
        old = {e.get("id"): (e.get("start"), e.get("end")) for e in stamp}
        current = storage.events_of(self.shared)
        for ev in current:
            if ev.get("id") not in old:
                changes["added"].append(scheduler.event_label(ev))
            elif old[ev.get("id")] != (ev.get("start_date"), ev.get("end_date")):
                changes["dated"].append(scheduler.event_label(ev))
        ids = {ev.get("id") for ev in current}
        changes["removed"] = sum(1 for key in old if key not in ids)
        return changes

    def plan_date_changes(self) -> list[str]:
        """存入計畫之後改過起訖日的活動名稱；沒有計畫或沒改過就是空的。"""
        return self.plan_changes()["dated"]

    def plan_stale_note(self) -> str:
        """計算後活動有變動時的提醒文字；沒變就是空字串。"""
        changes = self.plan_changes()
        parts = []
        if changes["added"]:
            parts.append(f"新增了「{'、'.join(changes['added'])}」")
        if changes["removed"]:
            parts.append(f"刪除了 {changes['removed']} 檔活動")
        if changes["dated"]:
            parts.append(f"改過「{'、'.join(changes['dated'])}」的日期")
        if not parts:
            return ""
        return (f"⚠ 計算後{'，'.join(parts)}，"
                "此計畫沒有算到這些變動，建議重新計算")

    def remaining_today(self, now) -> tuple[str, bool]:
        """今天還要打什麼＝存入計畫的今天那份減掉今天已記錄的。

        回傳 (那一行文字, 是否還有沒打完的)。「目前狀態」的今日待辦與
        「每日紀錄」下方共用這一份，兩邊才不會說不一樣的話。
        """
        reset = scheduler.parse_clock(self.shared.get("daily_reset_time"), "05:00")
        today = scheduler.task_day_of(now, reset).isoformat()
        plan = (self.stored_plan() or {}).get("days") or {}
        if not plan:
            return "（還沒算過排程——到「計算結果」按一次就會列出今天要打什麼）", False
        planned = plan.get(today) or {}
        entry = storage.entry_for(storage.load_log(self.profile_id), today) or {}
        done = entry.get("counts") or {}
        table = storage.level_table(self.shared)
        multi = len(storage.events_of(self.shared)) > 1
        remain = []
        for key, count in planned.items():
            left = int(count) - int(done.get(key) or 0)
            if left <= 0:
                continue
            level = table.get(key)
            name = (scheduler.level_label(level["event_name"], level.get("series_name"),
                                          level["name"]) if level and multi
                    else (level or {}).get("name", key))
            remain.append(f"{name}×{left}")
        stale = "　（活動有變動，建議重算）" if self.plan_stale_note() else ""
        if remain:
            return "還要打：" + "、".join(remain) + stale, True
        return "關卡都打完了 ✓" + stale, False

    def save_plan(self, result):
        """把算好的排程存進紀錄檔，並刷新每日紀錄分頁。"""
        log = storage.load_log(self.profile_id)
        for event in storage.events_of(self.shared):
            storage.ensure_log_event(log, event, self.profile)
        snapshot = scheduler.plan_snapshot(result)
        snapshot["events"] = self.plan_fingerprint(self.shared)
        log["plan"] = snapshot
        storage.save_log(self.profile_id, log)
        for tab, _label in self.tabs:
            if isinstance(tab, LogTab):
                tab.load()
            elif isinstance(tab, StatusTab):
                # 今日待辦的「還要打」照這份計畫算；只重畫推導的部分，
                # 不動帳號名稱與體力上限那兩格（可能還沒存）
                tab.refresh_derived()

    def refresh_derived_fields(self):
        """每日紀錄改動後，讓顯示目前積分/已打關卡數的分頁重新載入。"""
        # 只刷推導欄位，不整頁 load()——那會把那兩頁還沒按「儲存」的編輯洗掉
        for tab, _label in self.tabs:
            if isinstance(tab, StatusTab):
                tab.refresh_derived()
            elif isinstance(tab, RoutineTab):
                tab.refresh_progress()
            elif isinstance(tab, LogTab):
                tab._refresh_summary()

    def apply_log(self, log):
        """以紀錄（起始值＋累計）重算目前積分／已打關卡數／已消耗體力並存檔。"""
        storage.apply_log_to_profile(self.profile, log, self.shared)
        storage.save_profile(self.profile_id, self.profile)
        self.refresh_derived_fields()

    def set_log_baselines(self, events=None):
        """改起始值（開始記錄之前就有的量）。

        起始值存在紀錄檔裡，目前值＝起始值＋紀錄累計。
        events：{event_id: {種類: 起始值}}（種類見 storage.EVENT_BASELINE_KINDS）。
        全域的起始耗體（baseline_stamina）已經沒有畫面可以改，檔案裡的值照舊保留。
        """
        log = storage.load_log(self.profile_id)
        for event in storage.events_of(self.shared):
            section = storage.ensure_log_event(log, event, self.profile)
            if events and event["id"] in events:
                storage.set_event_baselines(section, events[event["id"]])
        storage.save_log(self.profile_id, log)
        self.apply_log(log)

    def sync_derived_from_log(self) -> bool:
        """以每日紀錄為準，重新推導目前積分／已打關卡數／已消耗體力。回傳是否有變動。

        這三個欄位平常只在每日紀錄存檔時更新（LogTab._persist）。同時開了兩個視窗、
        舊視窗關閉時把整份舊帳號資料寫回，或是登記之後才改了關卡積分，欄位就會跟紀錄
        對不上——而排程直接拿它當「已經完成多少」。

        沒有紀錄時不動：那時候這幾個欄位是手填的，
        用紀錄的起始值去算只會把使用者填的數字蓋掉。
        """
        log = storage.load_log(self.profile_id)
        if not storage.has_entries(log):
            return False
        before = self._derived_snapshot()
        storage.apply_log_to_profile(self.profile, log, self.shared)
        return self._derived_snapshot() != before

    def _derived_snapshot(self):
        """推導欄位的快照，只用來判斷 sync_derived_from_log 有沒有改到東西。"""
        return (self.profile.get("current_stamina_spent"),
                {eid: (data.get("current_points"), data.get("current_clears"))
                 for eid, data in (self.profile.get("events") or {}).items()})

    def set_status(self, text: str):
        self._status_text = text
        self._rewrap_status()

    def _rewrap_status(self):
        """照狀態列現在的寬度把字折行（見 wrap_status）。"""
        width = self.status.winfo_width()
        font = tkfont.Font(font=self.status.cget("font") or "TkDefaultFont")
        text = wrap_status(self._status_text, font, max(1, width - dp(4)) if width > 1 else 0)
        if str(self.status.cget("text")) != text:
            self.status.config(text=text)

    def on_close(self):
        if self.save_all(silent=True):
            self._save_geometry()
            self.destroy()
            return
        if self._save_cancelled:    # 共用設定衝突時按了「取消」：留在視窗裡
            return
        if messagebox.askyesno("尚未儲存",
                               "有欄位格式不正確，無法儲存。\n仍要關閉並放棄這些變更嗎？"):
            self._save_geometry()
            self.destroy()


def _report_startup_error(text: str) -> None:
    """程式還沒開起來就出錯：寫進 error.log，再用一個臨時視窗講出來。

    平常是用 pythonw 啟動的，沒有主控台——不這樣做的話雙擊之後什麼都不會發生。
    """
    try:
        with (storage.APP_DIR / "error.log").open("a", encoding="utf-8") as fh:
            fh.write(f"[{datetime.now():%Y-%m-%d %H:%M:%S}]\n{text}\n")
    except OSError:
        pass
    # 用 tkinter 原生的對話框：自訂的 messagebox 靠主視窗建好的字型，這時還不一定有
    import tkinter.messagebox as native_messagebox
    try:
        root = tk.Tk()
        root.withdraw()
        native_messagebox.showerror("程式無法啟動",
                                    "啟動時發生錯誤，詳細內容已寫進 error.log：\n\n"
                                    + text[-1500:], parent=root)
        root.destroy()
    except tk.TclError:
        pass


def main():
    # 求解器的暫存檔（scheduler._remove_solver_files）寫在「目前所在的資料夾」。
    # 先切到程式自己的資料夾——從別的地方下 python 指令啟動時才不會灑到那裡、
    # 或因為那裡不能寫而算不出來。不改成絕對路徑：pulp 會把檔名用空白切開再交給
    # CBC，資料夾名稱有空白就壞了。
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    enable_dpi_awareness()
    try:
        app = App()
    except Exception:
        _report_startup_error(traceback.format_exc())
        return
    app.mainloop()


if __name__ == "__main__":
    main()
