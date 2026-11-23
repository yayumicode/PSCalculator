# -*- coding: utf-8 -*-
"""資料存取層：app_state / shared_config / profiles / logs 的讀寫。

檔案配置：
    PSCalculator/
      app_state.json
      shared_config.json        # 所有帳號共用的作息與重置設定 ＋ 並行活動清單 ＋ 固定任務 ＋ 道具
      profiles/<設定檔id>.json     # 一個帳號一份，第一次執行只建 main（主帳）
      logs/<設定檔id>.json         # 每日紀錄（單一時間軸，跨活動）

活動放在 shared_config 的 `events` 陣列，各種限制條件統一成「任務」。
"""

from __future__ import annotations

import copy
import hashlib
import json
import os
import re
import shutil
from datetime import datetime
from pathlib import Path

import scheduler
from version import __version__

# 資料檔預設放在程式旁邊。設環境變數 PSCALC_DATA_DIR 可以改指向別的目錄，
# 測試就靠這個把資料寫到暫存區，絕不碰到使用者的真實設定。
APP_DIR = Path(os.environ.get("PSCALC_DATA_DIR")
               or Path(__file__).resolve().parent)
PROFILES_DIR = APP_DIR / "profiles"
LOGS_DIR = APP_DIR / "logs"
APP_STATE_PATH = APP_DIR / "app_state.json"
SHARED_PATH = APP_DIR / "shared_config.json"

SCHEMA_VERSION = 3

# (profile_id, 顯示名稱) —— 第一次執行（一個帳號都沒有）時建立的帳號
FIRST_RUN_PROFILES = [
    ("main", "主帳"),
]

# (profile_id, 顯示名稱) —— 帳號清單排前面的固定順序，檔案裡沒寫名稱時也拿來補
DEFAULT_PROFILES = FIRST_RUN_PROFILES

# base_points＝沒有活動加成的基礎積分，是活動本身的數值，所有帳號共用。
# 各帳號實際拿到的積分＝base_points × (1 + 活動加成%)，存在 profile 的 level_points。
DEFAULT_LEVELS = [
    {"id": "lv1", "name": "關卡1", "stamina_cost": 15, "scoring": True,
     "enemies": 0, "drops": 0, "base_points": None},
    {"id": "lv2", "name": "關卡2", "stamina_cost": 20, "scoring": True,
     "enemies": 0, "drops": 0, "base_points": None},
    {"id": "lv3", "name": "關卡3", "stamina_cost": 30, "scoring": True,
     "enemies": 0, "drops": 0, "base_points": None},
    {"id": "lv4", "name": "關卡4", "stamina_cost": 40, "scoring": True,
     "enemies": 0, "drops": 0, "base_points": None},
    {"id": "lv5", "name": "關卡5", "stamina_cost": 50, "scoring": True,
     "enemies": 0, "drops": 0, "base_points": None},
]
# 跟上面不同的類型：新活動的關卡照這幾個耗體建，名稱一樣是關卡1、關卡2……
# 復刻沒有 15 體的關卡（20／30／40／50 體＝關卡1~4），照當期的五關建再套表會多一關
# 對不上表的，還會跳「這幾關的消耗體力不在表裡」。
DEFAULT_LEVEL_COSTS = {"rerun": (20, 30, 40, 50)}


def default_levels(event_type: str = "current") -> list[dict]:
    """新活動預設的關卡結構（還沒套基礎積分表）。"""
    costs = DEFAULT_LEVEL_COSTS.get(event_type)
    if costs is None:
        return copy.deepcopy(DEFAULT_LEVELS)
    return [{"id": f"lv{i}", "name": f"關卡{i}", "stamina_cost": cost, "scoring": True,
             "enemies": 0, "drops": 0, "base_points": None}
            for i, cost in enumerate(costs, start=1)]

# 活動類型：只是「預設值的來源」。選了類型會帶入對應的基礎積分表與
# 「吃不吃活動加成」，但兩者之後都能手動改——當期活動也可能改用復刻的積分表。
EVENT_TYPES = [
    ("current", "當期"),
    ("rerun", "復刻"),
    ("media", "音像"),
    # 分組解鎖型活動：沒有積分、沒有任務，關卡分成好幾組、組內照耗體順序解鎖，
    # 每一關至少要打一次，打過之後可以無限重複（會掉素材）。見 GROUPED_EVENT_PRESETS。
    ("collect", "蜜意蒐羅"),
    ("treasure", "祕寶探尋"),
    # 限期關卡：檢定、忘卻這種一檔一檔輪替的關卡。有起訖日與每檔總次數上限，
    # 但不是「活動」——不決定排程範圍、不當第 N 天的基準、沒有任務與加成。
    ("limited", "限期關卡"),
]
EVENT_TYPE_LABELS = dict(EVENT_TYPES)
# 沒有積分、也沒有活動加成的活動類型（限期關卡另外處理，它連活動任務都沒有）。
# 這幾類的活動設定頁不顯示加成、積分上限、盡量提早與起始積分。
NO_POINTS_TYPES = ("media", "collect", "treasure")
# 類型 -> 預設吃不吃活動加成
EVENT_TYPE_BONUS = {"current": True, "rerun": False, "media": False,
                    "collect": False, "treasure": False, "limited": False}
# 類型 -> app.BASE_POINT_TABLES 裡的表名（app 負責實際帶入數字）
# 音像不帶：它通常沒有自己的關卡，任務靠其他活動的耗體累積，沒有積分可以套。
# 「無加成類」那張表還留在「套用常見表」裡，需要時手動套。
EVENT_TYPE_TABLE = {"current": "一般活動", "rerun": "復刻活動"}

# 分組解鎖型活動（蜜意蒐羅、祕寶探尋）的組數／耗體／敵人數。定義在 scheduler
# （它要判斷哪些活動的解鎖鏈可以放寬，而 scheduler 不能反過來 import storage）。
# 之後再出現同類型的活動，到那邊加一行就好。
GROUPED_EVENT_PRESETS = scheduler.GROUPED_EVENT_PRESETS
# 這類活動一般持續 7 天：起始日 15:00 → 七天後 12:00
GROUPED_EVENT_DAYS = 7

# 活動的精確起訖時刻：起始日下午三點開始、結束日中午十二點結束
DEFAULT_EVENT_START_TIME = "15:00"
DEFAULT_EVENT_END_TIME = "12:00"

# 任務週期。公會任務跟每日一樣是每天 05:00 重置，分開一類是因為它在遊戲裡
# 是獨立的一頁，獎勵與項目都不同。
TASK_CYCLES = [
    ("daily", "每日"),
    ("weekly", "每週"),
    ("monthly", "每月"),
    ("event", "活動"),
    ("guild", "公會"),
]
TASK_CYCLE_LABELS = dict(TASK_CYCLES)
# 每天重置的週期（公會任務是每日重置）
DAILY_CYCLES = {"daily", "guild"}

# 任務的達成條件要怎麼量。manual＝程式看不出來（登入、簽到、公會捐獻），
# 只在任務清單上手動勾，不進求解。
TASK_METRICS = [
    ("stamina", "消耗體力"),
    ("clears", "關卡次數"),
    ("points", "活動積分"),
    ("enemies", "擊殺敵人"),
    ("drops", "取得道具"),
    ("manual", "手動勾選"),
]
TASK_METRIC_LABELS = dict(TASK_METRICS)

# 每月任務預設的獎勵入帳日（沿用每日簽到的 5/11/17/23）
DEFAULT_MONTH_DAYS = [5, 11, 17, 23]

# 獎勵道具登錄表。帶 stamina 的道具會自動接成體力來源，其餘只做統計。
# 預設只放體力道具；其他沒有體力值的道具要統計的話自己到「設定 → 獎勵道具」加。
DEFAULT_ITEMS = [
    {"id": "stamina100", "name": "體力100", "stamina": 100},
    {"id": "stamina30", "name": "體力30", "stamina": 30},
    {"id": "stamina10", "name": "體力10", "stamina": 10},
]

# 常駐關卡：不隸屬任何活動、永遠打得到的那一組。第一次執行就建好，不能刪除也不能改名
# （見 _normalise_event）。關卡一律沒有積分（scoring=False）。
STANDING_EVENT_ID = "st1"
STANDING_EVENT_NAME = "常駐關卡"
# 這三關是常駐關卡的基本盤，不能刪除、不能改名；其他常駐關卡可以自由增刪。
# 靠名稱認（改不了名，所以認得住）。
STANDING_LOCKED_LEVELS = ("蜜意時光", "經商貿易", "探索調查")
# 第一次執行時常駐關卡的關卡結構。default_enabled＝新帳號「這次計算要算」預設勾不勾
FIRST_RUN_STANDING_LEVELS = (
    {"id": "lv1", "name": "蜜意時光", "stamina_cost": 15, "enemies": 0},
    {"id": "lv2", "name": "經商貿易", "stamina_cost": 50, "enemies": 5},
    {"id": "lv3", "name": "探索調查", "stamina_cost": 50, "enemies": 8},
    {"id": "lv4", "name": "主線體力減半10", "stamina_cost": 10, "enemies": 0,
     "default_enabled": False},
)

# 第一次執行時「設定 → 任務清單」預先帶入的固定任務。只寫跟預設值不同的欄位，
# 其餘由 _normalise_task 補齊。之後使用者刪改都照他的，不會再自動加回來。
DEFAULT_ROUTINE_TASKS = (
    {"id": "r1", "name": "每日任務：打關卡", "cycle": "daily",
     "metric": "clears", "amount": 10},
    {"id": "r2", "name": "每日任務：擊殺敵人", "cycle": "guild",
     "metric": "enemies", "amount": 50},
    {"id": "r5", "name": "消耗體力一千點", "cycle": "weekly",
     "metric": "stamina", "amount": 1000,
     "rewards": [{"item": "stamina100", "qty": 1}]},
    {"id": "r3", "name": "升級任一角色一次", "cycle": "daily",
     "metric": "manual", "amount": 1,
     "rewards": [{"item": "stamina30", "qty": 1}]},
    {"id": "r4", "name": "升級任意角色五次", "cycle": "weekly",
     "metric": "manual", "amount": 1, "reward_weekday": 2,
     "rewards": [{"item": "stamina100", "qty": 1}]},
    {"id": "r6", "name": "簽到", "cycle": "monthly",
     "metric": "manual", "amount": 1,
     "rewards": [{"item": "stamina10", "qty": 2}]},
    {"id": "r7", "name": "商店購買", "cycle": "weekly",
     "metric": "manual", "amount": 1, "grant_on_done": True,
     "rewards": [{"item": "stamina30", "qty": 2}]},
)


def now_stamp() -> str:
    return datetime.now().astimezone().isoformat(timespec="seconds")


# --------------------------------------------------------------------------
# 預設值
# --------------------------------------------------------------------------

def default_event(event_id: str = "ev1", name: str = "",
                  event_type: str = "current", standing: bool = False) -> dict:
    return {
        "id": event_id,
        # 常駐關卡：不隸屬任何活動、永遠打得到的那一組（檢定、蜜話、經商貿易…）。
        # 借用活動的資料結構是為了沿用關卡編輯器、每日紀錄、各帳號的「這次不算」
        # 開關；但它沒有起訖日、沒有活動任務，也不參與排程範圍與活動優先序。
        "standing": bool(standing),
        # 活動名稱只是顯示用；紀錄與存下來的計畫都依 id 分區，改名不影響。
        # 留空的話顯示時退回用 id。
        "name": name,
        "type": event_type,
        # 限期關卡的期數（見 _normalise_event）；其他類型一律 None
        "period_no": None,
        "start_date": None,
        "start_time": DEFAULT_EVENT_START_TIME,
        "end_date": None,
        "end_time": DEFAULT_EVENT_END_TIME,
        # 這檔活動吃不吃「活動加成」。復刻與音像是固定積分、加成不生效，
        # 對應那個計算機網站活動資料的 stageExtras = null。由類型帶預設值，可改。
        "activity_bonus_applies": EVENT_TYPE_BONUS.get(event_type, True),
        # 積分獎勵表的封頂（加成後的積分）。超過這個數字再打也拿不到東西，
        # 所以排程不該為了多拿分去餵計分關卡。None＝沒有上限。
        "points_cap": None,
        # 「盡量提早」：這天之前（不含當天）盡量把這檔的積分拿完——填下一檔活動
        # 預計開始的日子。None＝不提早，排程只求總耗體最省。
        "early_finish_date": None,
        # 那天之前多餘的體力先打這檔的計分關卡（True），還是常駐加碼照打、
        # 只挪剩下的（False）。沒填日期時這個鍵沒有作用。
        "early_takes_surplus": True,
        "levels": default_levels(event_type),
        # 一般活動有活動簽到，預設帶上送體力的那兩天；其他類型沒有
        "tasks": (default_signin_tasks([])
                  if event_type == "current" and not standing else []),
    }


# 一般活動的「活動簽到」哪幾天送體力：（簽到第幾天, 體力100 道具幾個）。
# 簽到從活動開始日的**隔天**算第 1 天（活動 15:00 才開），所以第 N 天就是
# deadline_offset = N——比任務編輯器顯示的「第 N+1 天」少 1，那邊把開始日當第 1 天。
DEFAULT_SIGNIN_REWARDS = ((4, 1), (9, 2))
SIGNIN_TASK_PREFIX = "活動簽到"


# 當期、復刻活動「套用類型預設」時帶入的活動任務：
# 類型 -> ((達成條件, 目標, 獎勵), ...)，獎勵是 ((道具, 幾個), ...)。
# 數字照最近一檔填的，每檔不同就在任務清單改。同一種達成條件已經有任務就整組不加
# （復刻的兩條耗體任務一起看）。
# 復刻的積分目標要低於它的積分上限（DEFAULT_POINTS_CAP 15630），不然一存檔就被擋。
DEFAULT_EVENT_TASKS = {
    "current": (("points", 22575, ()), ("stamina", 6000, ())),
    "rerun": (("points", 15240, ()), ("stamina", 6000, ()),
              ("stamina", 5000, (("stamina100", 1),))),
}
EVENT_TASK_NAME = "活動任務"

# 復刻活動「套用類型預設」另外帶入的送體力積分任務：(積分, 道具, 幾個)。
# 照「舞動心願復刻」那一檔的獎勵表。同樣積分的任務已經有就不加。
DEFAULT_RERUN_REWARD_TASKS = (
    (540, "stamina10", 3),
    (5160, "stamina30", 1),
    (6210, "stamina30", 1),
    (6840, "stamina100", 10),
    (13020, "stamina100", 2),
)

# 基礎積分的常見表：(名稱, 吃不吃活動加成, {消耗體力: 基礎積分})。取自 nuCarnival
# 活動計算機的實際活動資料（linecross.github.io，res/json/activity/*.json）；
# 復刻與無加成類的 stageExtras 是 null，所以不吃加成。「套用類型預設」照
# EVENT_TYPE_TABLE 挑表，「套用常見表」選單列出全部。
BASE_POINT_TABLES = [
    ("一般活動", True, {15: 20, 20: 30, 30: 48, 40: 68, 50: 90}),
    ("復刻活動", False, {20: 55, 30: 85, 40: 115, 50: 150}),
    ("無加成類", False, {15: 40, 20: 54, 25: 69, 30: 84, 35: 100,
                         40: 116, 45: 133, 50: 150}),
]

# 「套用類型預設」帶入的積分上限（積分上限欄空白才帶，有值不蓋）。
# 復刻的獎勵表固定；當期每檔都不同，不帶——開始計算前會擋下沒填的（見
# scheduler.events_missing_points_cap）。
DEFAULT_POINTS_CAP = {"rerun": 15630}

# 當期、復刻「套用類型預設」帶入的每關敵人數：類型 -> {消耗體力: 敵人數}。
# 表上沒有的耗體不動。復刻的關卡是 20／30／40／50 體。
DEFAULT_LEVEL_ENEMIES = {
    "current": {15: 7, 20: 7, 30: 8, 40: 8, 50: 9},
    "rerun": {20: 7, 30: 7, 40: 8, 50: 9},
}

# 當期、復刻活動的 BOSS 關：活動開始後第 N 天開放、整檔 3 次、一定要打滿、
# 同一天打完；沒有積分、不算關卡次數。照「虛擬性悖論」那一檔的設定，
# 只是開放日提早到開始後第 7 天。
EVENT_BOSS_NAME = "活動BOSS"
EVENT_BOSS_LEVEL = {
    "stamina_cost": 10, "enemies": 0, "drops": 0,
    "scoring": False, "counts_clears": False,
    "available_from": 7, "max_total": 3, "must_finish": True,
    "same_day": True, "unlock_first": False, "group": None,
    "base_points": None, "tiers": [],
}
# BOSS 關開放日（相對活動起始日的天數）依類型：當期開始後第 7 天才開，
# 復刻一開始就能打（0＝跟活動起始日同一天）
EVENT_BOSS_OPEN_DAY = {"current": 7, "rerun": 0}


# 音像「套用類型預設」帶入的每日任務：(每天耗體, 最後一天要不要做)。
# 最後一天只剩上午半天，兩條都不做——期間的「訖」填倒數第 2 天。
DEFAULT_MEDIA_TASKS = ((150, False), (300, False))

# 音像「套用類型預設」另外帶入的商店任務：取得道具達標送體力。
# 不算進排程計算（排程不會為了它去排打法），獎勵跟當期／復刻的活動任務一樣
# 最晚活動結束後 scheduler.REWARD_CLAIM_DAYS 天內領。
MEDIA_SHOP_TASK_NAME = "音像商店體力"
MEDIA_SHOP_TASK_AMOUNT = 1500
MEDIA_SHOP_TASK_REWARDS = (("stamina30", 3),)


def default_media_shop_task(existing_tasks: list[dict]) -> list[dict]:
    """音像預設的商店體力任務；已經有同名任務就不加（回傳空清單）。"""
    if any((t.get("name") or "").strip() == MEDIA_SHOP_TASK_NAME
           for t in existing_tasks):
        return []
    return [_normalise_task({
        "id": next_task_id(list(existing_tasks)),
        "name": MEDIA_SHOP_TASK_NAME,
        "cycle": "event", "metric": "drops", "amount": MEDIA_SHOP_TASK_AMOUNT,
        "deadline_offset": -1, "enforce": False, "assume_done": False,
        "rewards": [{"item": item, "qty": qty} for item, qty in MEDIA_SHOP_TASK_REWARDS],
    })]


def default_media_tasks(existing_tasks: list[dict]) -> list[tuple[dict, bool]]:
    """音像預設的每日耗體任務；已經有同樣每天耗體數字的就跳過。

    回傳 [(任務, 最後一天要不要做)]——期間的日期要等畫面上的起訖日才算得出來。
    """
    have = {int(t.get("amount") or 0) for t in existing_tasks
            if t.get("cycle") == "daily" and t.get("metric") == "stamina"}
    out = []
    for amount, last_day in DEFAULT_MEDIA_TASKS:
        if amount in have:
            continue
        task = _normalise_task({
            "id": next_task_id(list(existing_tasks) + [t for t, _l in out]),
            "name": EVENT_TASK_NAME,
            "cycle": "daily", "metric": "stamina", "amount": amount,
            "deadline_offset": -1, "enforce": True, "assume_done": False,
        })
        out.append((task, last_day))
    return out


def default_event_tasks(existing_tasks: list[dict],
                        event_type: str = "current") -> list[dict]:
    """當期／復刻預設的活動任務；已經有同一種達成條件的就跳過。

    復刻另外帶入送體力的積分任務（DEFAULT_RERUN_REWARD_TASKS），同樣積分的已經有
    就跳過。那幾條不算進「已經有積分任務」——不然先加了獎勵任務，積分目標就補不上。
    """
    reward_amounts = ({amount for amount, _item, _qty in DEFAULT_RERUN_REWARD_TASKS}
                      if event_type == "rerun" else set())
    have = {t.get("metric") for t in existing_tasks
            if not (t.get("metric") == "points"
                    and int(t.get("amount") or 0) in reward_amounts)}
    defaults = DEFAULT_EVENT_TASKS.get(event_type, DEFAULT_EVENT_TASKS["current"])
    wanted = []      # (達成條件, 目標, 獎勵)
    for metric, amount, rewards in defaults:
        if metric not in have:
            wanted.append((metric, amount, [{"item": item, "qty": qty}
                                            for item, qty in rewards]))
    if event_type == "rerun":
        have_points = {int(t.get("amount") or 0) for t in existing_tasks
                       if t.get("cycle") == "event" and t.get("metric") == "points"}
        for amount, item, qty in DEFAULT_RERUN_REWARD_TASKS:
            if amount not in have_points:
                wanted.append(("points", amount, [{"item": item, "qty": qty}]))
    # 同一種達成條件排在一起、數量由小到大（積分 540、5160……15240，再來耗體
    # 5000、6000）；條件的先後照 DEFAULT_EVENT_TASKS。排好再發 id，id 才會照順序
    order = {metric: i for i, (metric, _a, _r) in enumerate(defaults)}
    wanted.sort(key=lambda w: (order.get(w[0], len(order)), w[1]))
    tasks = []
    for metric, amount, rewards in wanted:
        tasks.append(_normalise_task({
            "id": next_task_id(list(existing_tasks) + tasks),
            "name": EVENT_TASK_NAME,
            "cycle": "event", "metric": metric, "amount": amount,
            "deadline_offset": -1, "enforce": True, "assume_done": False,
            "rewards": rewards,
        }))
    return tasks


def default_signin_tasks(existing_tasks: list[dict]) -> list[dict]:
    """一般活動預設的簽到任務：手動勾選＋預設完成，獎勵在那一天入帳。

    只是預設值——天數、獎勵都能在任務清單改，沒領到就到每日紀錄標記。
    """
    tasks = []
    for day, qty in DEFAULT_SIGNIN_REWARDS:
        tasks.append(_normalise_task({
            "id": next_task_id(list(existing_tasks) + tasks),
            "name": f"{SIGNIN_TASK_PREFIX}第{day}天",
            "cycle": "event", "metric": "manual", "amount": 1,
            "deadline_offset": day, "enforce": False, "assume_done": True,
            "rewards": [{"item": "stamina100", "qty": qty}],
        }))
    return tasks


# 遊戲本身固定的回復速率與重置時刻：程式寫死，不開放修改（「重置與回復」只顯示說明）。
# 讀檔時 normalise_shared 一律蓋成這些值，排程那邊照樣從 shared 讀。
RECOVERY_RATE_PER_5MIN = 1
DAILY_RESET_TIME = "05:00"
WEEKLY_RESET_WEEKDAY = 0        # 週一
MONTHLY_RESET_DAY = 1


def fixed_clocks() -> dict:
    """寫死的回復速率與重置時刻，格式跟 shared_config.json 裡的欄位一樣。"""
    return {
        "recovery_rate_per_5min": RECOVERY_RATE_PER_5MIN,
        # 遊戲的每日重置時間：一個「任務日」從這個時刻算到隔天同一時刻。
        # 公會任務也是這個時刻重置。
        "daily_reset_time": DAILY_RESET_TIME,
        "weekly_reset": {"weekday": WEEKLY_RESET_WEEKDAY, "time": DAILY_RESET_TIME},
        "monthly_reset": {"day": MONTHLY_RESET_DAY, "time": DAILY_RESET_TIME},
    }


def default_shared() -> dict:
    return {
        "schema_version": SCHEMA_VERSION,
        "last_modified": now_stamp(),
        **fixed_clocks(),
        # 實際會上線打關卡的時段。這個時段以外只會累積自然回復，不會消耗；
        # 睡覺期間回復的體力如果超過上限就浪費掉了，所以睡前要把體力壓低。
        "active_window": {"start": "06:00", "end": "21:30"},
        # 排程的整理偏好（見 scheduler.LIGHT_WEEKDAYS）：同樣省的排法裡挑好照著打的
        "schedule_prefs": {"light_weekdays": True, "simplify_days": True,
                           "expire_late": True},
        "events": [default_event("ev1", "活動1")],
        # 每日／每週／每月／公會的固定任務（跟哪一檔活動無關）
        "routine_tasks": [],
        "items": copy.deepcopy(DEFAULT_ITEMS),
    }


def first_run_shared() -> dict:
    """第一次執行時建立的共用設定：預設值再加上常用的固定任務。

    固定任務不放進 default_shared：那是「缺什麼補什麼」的底，使用者把任務
    全刪光、或測試建的空設定，都不該被補回這幾個任務。
    """
    shared = default_shared()
    shared["routine_tasks"] = [_normalise_task(task, "daily")
                               for task in DEFAULT_ROUTINE_TASKS]
    shared["events"] = [first_run_current_event(), default_standing_event()]
    return shared


def first_run_current_event() -> dict:
    """第一次執行時預設的那檔當期活動：照當期的類型預設表建（起訖日留白）。"""
    return event_from_template("ev1", "活動1", "current",
                               builtin_type_defaults()["current"])


# --------------------------------------------------------------------------
# 類型預設表：當期、復刻的預設關卡結構與活動任務（「設定 → 活動類型預設」可改）
# --------------------------------------------------------------------------
# 「新增活動」「套用類型預設」「第一次執行」都從這張表來。存在 shared_config 的
# type_defaults；沒存的類型用內建的（builtin_type_defaults，由上面那些 DEFAULT_*
# 組出來）。每個類型：{"bonus_applies", "points_cap", "levels", "tasks"}，
# 關卡的 available_from 是「起始日後第幾天開放」（0＝起始日當天，None＝全期）。
TEMPLATE_TYPES = ("current", "rerun")


def builtin_type_defaults() -> dict:
    """內建的類型預設表（使用者沒改過、或按「還原成內建」時用）。"""
    out = {}
    for event_type in TEMPLATE_TYPES:
        _name, applies, table = base_table_for(event_type)
        enemies = DEFAULT_LEVEL_ENEMIES.get(event_type) or {}
        levels = default_levels(event_type)
        for level in levels:
            cost = level["stamina_cost"]
            level["base_points"] = table.get(cost)
            level["unlock_first"] = True
            if cost in enemies:
                level["enemies"] = enemies[cost]
        levels.append(dict(EVENT_BOSS_LEVEL, id=next_level_id(levels), name=EVENT_BOSS_NAME,
                           available_from=EVENT_BOSS_OPEN_DAY.get(
                               event_type, EVENT_BOSS_LEVEL["available_from"])))
        tasks = default_event_tasks([], event_type)
        if event_type == "current":
            tasks += default_signin_tasks(tasks)
        out[event_type] = normalise_type_default({
            "bonus_applies": applies, "points_cap": DEFAULT_POINTS_CAP.get(event_type),
            "levels": levels, "tasks": tasks})
    return out


def normalise_type_default(data: dict | None) -> dict:
    """整理一個類型的預設表：關卡、任務照活動的規則整理，id 重新編成 lv1／t1 起。"""
    data = data or {}
    levels = [_normalise_level(level) for level in data.get("levels") or []]
    for i, level in enumerate(levels, start=1):
        level["id"] = f"lv{i}"
    tasks = [_normalise_task(task, "event") for task in data.get("tasks") or []]
    for i, task in enumerate(tasks, start=1):
        task["id"] = f"t{i}"
        task["cycle"] = "event"
    cap = data.get("points_cap")
    return {"bonus_applies": data.get("bonus_applies") is not False,
            "points_cap": None if cap in (None, "") else max(0, int(cap)),
            "levels": levels, "tasks": tasks}


def type_defaults(shared: dict | None) -> dict:
    """{類型: 預設表}：使用者存過的優先，沒存的類型用內建的。"""
    out = builtin_type_defaults()
    for event_type, data in ((shared or {}).get("type_defaults") or {}).items():
        if event_type in TEMPLATE_TYPES and data:
            out[event_type] = normalise_type_default(data)
    return out


def type_default(shared: dict | None, event_type: str) -> dict | None:
    """一個類型的預設表；不是當期／復刻就是 None（那些類型的預設另有做法）。"""
    return type_defaults(shared).get(event_type)


def event_from_template(event_id: str, name: str, event_type: str,
                        template: dict) -> dict:
    """照類型預設表建一檔新活動：關卡、任務整套照抄（id 照表的順序重編）。"""
    event = default_event(event_id, name, event_type)
    event["levels"] = copy.deepcopy(template.get("levels") or [])
    event["tasks"] = copy.deepcopy(template.get("tasks") or [])
    event["activity_bonus_applies"] = bool(template.get("bonus_applies"))
    event["points_cap"] = template.get("points_cap")
    for i, level in enumerate(event["levels"], start=1):
        level["id"] = f"lv{i}"
    for i, task in enumerate(event["tasks"], start=1):
        task["id"] = f"t{i}"
    return _normalise_event(event)


def _default_is_scoring(level: dict) -> bool:
    return bool(level.get("scoring", True))


def base_table_for(event_type: str):
    """這個類型「套用類型預設」要套的基礎積分表 (名稱, 吃不吃加成, 表)；沒有就 None。"""
    name = EVENT_TYPE_TABLE.get(event_type)
    return next((t for t in BASE_POINT_TABLES if t[0] == name), None)


def apply_base_table(levels: list[dict], table: dict, is_scoring=None):
    """照消耗體力把基礎積分表套到關卡上（就地修改）。回傳 (套到的, 表裡沒有的, 清掉的)。

    不計分的關卡先擋掉——表是照消耗體力查的，不擋就會盲配（15 體力的蜜話拿到
    關卡1 的 20 分），它們的積分一律清空。表裡沒有的耗體也清空而不是留著：
    基礎積分是「這一檔活動」的數值，留著上一檔的舊值會算錯又很難發現。
    """
    is_scoring = is_scoring or _default_is_scoring
    done, skipped, cleared = [], [], []
    for level in levels:
        name = level.get("name", "")
        if not is_scoring(level):
            if level.get("base_points") is not None or level.get("points"):
                cleared.append(name)
            level["base_points"] = None
            level["points"] = None
            continue
        base = table.get(level.get("stamina_cost"))
        if base is None:
            level["base_points"] = None
            skipped.append(f"{name}（{level.get('stamina_cost')}）")
        else:
            level["base_points"] = base
            done.append(name)
    return done, skipped, cleared


def apply_event_type_defaults(event_type: str, levels: list[dict], tasks: list[dict],
                              points_cap=None, event_id: str | None = None,
                              is_scoring=None, template: dict | None = None) -> dict:
    """把類型預設表套到一檔**已經有關卡、任務**的活動上（活動設定頁的「套用類型預設」）。

    新活動不走這裡，直接照表建（event_from_template）。這裡是合併：
      * 計分關卡照消耗體力對上表裡的計分關卡，帶入基礎積分與敵人數；對不上的
        基礎積分清空（基礎積分是這一檔的數值，留著舊的會算錯）
      * 表裡的計分關卡有勾「開場先打一次」的話，這檔的計分關卡都設成解鎖鏈
      * 表裡不計分的關卡（活動BOSS）這檔沒有同名的就補上
      * 任務：手動勾選的看同名；有獎勵的看「同條件同數量」；沒獎勵的（積分、耗體目標）
        這檔已經有同條件的目標就不加——已經自己填了目標，不要再塞一個預設值
    levels 就地修改；要加的任務放在回傳值，呼叫端自己接上。

    is_scoring：怎麼判斷計分關卡（畫面上編輯中的記錄看的是下拉選的「類型」）。
    event_id：新關卡的 id 連這檔刪掉的關卡留下的 id 也跳過。

    回傳 {"applies", "base": (套到, 表裡沒有, 清掉), "cap"（要帶入的積分上限，已經
    有值或沒有預設就是 None）, "tasks", "chained", "enemies", "added_levels"}。
    """
    is_scoring = is_scoring or _default_is_scoring
    template = template or builtin_type_defaults()[event_type]
    tpl_scoring = [lv for lv in template["levels"] if lv.get("scoring")]
    by_cost = {}
    for level in tpl_scoring:
        by_cost.setdefault(level.get("stamina_cost"), level)
    report = {"applies": bool(template.get("bonus_applies"))}

    done, skipped, cleared = [], [], []
    matched = []
    for level in levels:
        name = level.get("name", "")
        if not is_scoring(level):
            if level.get("base_points") is not None or level.get("points"):
                cleared.append(name)
            level["base_points"] = None
            level["points"] = None
            continue
        tpl = by_cost.get(level.get("stamina_cost"))
        if tpl is None or tpl.get("base_points") is None:
            level["base_points"] = None
            skipped.append(f"{name}（{level.get('stamina_cost')}）")
        else:
            level["base_points"] = tpl["base_points"]
            done.append(name)
        if tpl is not None:
            matched.append((level, tpl))
    report["base"] = (done, skipped, cleared)

    cap = template.get("points_cap")
    report["cap"] = cap if cap is not None and points_cap in (None, "") else None

    chained = []
    if any(lv.get("unlock_first") for lv in tpl_scoring):
        chained = [lv for lv in levels if is_scoring(lv) and not lv.get("unlock_first")]
        for level in chained:
            level["unlock_first"] = True
    report["chained"] = [lv.get("name", "") for lv in chained]
    report["enemies"] = []
    for level, tpl in matched:
        level["enemies"] = int(tpl.get("enemies") or 0)
        report["enemies"].append(f"{level.get('name', '')} {level['enemies']}")

    names = {lv.get("name") for lv in levels}
    report["added_levels"] = []
    for tpl in template["levels"]:
        if tpl.get("scoring") or tpl.get("name") in names:
            continue
        level = dict(copy.deepcopy(tpl), id=next_level_id(levels, event_id))
        levels.append(level)
        names.add(level.get("name"))
        report["added_levels"].append(level)

    targets = {t.get("metric") for t in tasks
               if t.get("metric") != "manual" and not t.get("rewards")}
    amounts = {(t.get("metric"), int(t.get("amount") or 0)) for t in tasks}
    task_names = {t.get("name") for t in tasks}
    added = []
    for tpl in template["tasks"]:
        metric = tpl.get("metric")
        if metric == "manual":
            if tpl.get("name") in task_names:
                continue
        elif tpl.get("rewards"):
            if (metric, int(tpl.get("amount") or 0)) in amounts:
                continue
        elif metric in targets:
            continue
        added.append(dict(copy.deepcopy(tpl),
                          id=next_task_id(list(tasks) + added)))
    report["tasks"] = added
    return report


def default_standing_event() -> dict:
    """第一次執行時建立的常駐關卡（固定排在活動清單最後）。"""
    event = default_event(STANDING_EVENT_ID, STANDING_EVENT_NAME, standing=True)
    event["activity_bonus_applies"] = False
    event["levels"] = [{"scoring": False, "counts_clears": True, "drops": 0, **level}
                       for level in FIRST_RUN_STANDING_LEVELS]
    return _normalise_event(event)


# 要用代幣才能打的常駐關卡（代幣每天發、有上限）。一樣靠名稱認
TOKEN_LEVELS = ("經商貿易", "探索調查")


def is_token_level(event: dict | None, level: dict | None) -> bool:
    """經商貿易、探索調查：要用代幣才能打的常駐關卡。"""
    return (is_standing(event)
            and ((level or {}).get("name") or "") in TOKEN_LEVELS)


def is_locked_standing_level(event: dict | None, level: dict | None) -> bool:
    """常駐關卡的基本盤（蜜意時光、經商貿易、探索調查）：不能刪除、不能改名。"""
    return (is_standing(event)
            and ((level or {}).get("name") or "") in STANDING_LOCKED_LEVELS)


def default_profile_event() -> dict:
    """profile 裡「這個帳號在這檔活動」的資料。"""
    return {
        # 各關卡積分依帳號不同，預設留空（None）等使用者填
        "level_points": {},
        # 這次計算要不要算這一關。關卡本身所有帳號共用，但「這一檔活動這個帳號要打哪幾關」
        # 逐帳號不同，所以開關跟積分一樣放在 profile。預設全部都算。
        "level_enabled": {},
        # 活動加成（%）。來自隊伍，所以各帳號不同，跟 level_points 同性質。
        "activity_bonus": 0,
        # 限期關卡這一檔、這個帳號的總次數上限（level_id -> int）。每檔、每個帳號
        # 都可能不同，所以放在 profile。沒填＝沿用關卡本身的「總共最多幾次」。
        "level_max_total": {},
        "current_points": 0,   # 有每日紀錄時自動推導
        "current_clears": 0,   # 同上，只算「會進總量」的關卡
    }


def default_profile(profile_name: str) -> dict:
    return {
        "schema_version": SCHEMA_VERSION,
        "profile_name": profile_name,
        "last_modified": now_stamp(),
        "stamina_cap": 120,
        "current_stamina_spent": 0,   # 全域累計耗體（跨活動共用）
        # 體力來源：大月卡、小月卡、積分兌換……每一筆自己知道怎麼發，
        # 程式展開成每日發放量。任務獎勵的體力另外由 scheduler 自動接上。
        "stamina_sources": [],
        "special_days": [],           # 一次性、特定日期的規則（全域）
        # 每檔活動自動套用的規則：跟 special_days 同格式，但沒有 event_id，
        # 多一個 event_types（套到哪些類型的活動）。見 scheduler 特殊日規則那段。
        "event_default_rules": [],
        "daily_level_rules": [],      # 指定關卡次數限制，level_id 存 "ev1/lv8"
        # 指定日期打指定次數：{"level_id", "date", "count", "mode"}，
        # mode 是 "exact"（剛好）或 "min"（至少），count 是當天總數
        "daily_level_targets": [],
        "event_priority": [],        # 降級時由後往前放寬；空的照 events 順序
        # 關卡優先序（關卡鍵，排越前面越優先）。只在「同樣省體力時選誰」與
        # 「多餘體力先塞誰」兩個時機生效，不會為了它多花或多買體力。空的＝沒有偏好。
        "level_priority": [],
        "events": {},               # event_id -> default_profile_event()
        # 任務進度。鍵是 "<event_id>/<task_id>" 或 "routine/<task_id>"
        "task_state": {},
    }


def default_task_state() -> dict:
    return {
        # 開始用這個工具之前就已經累積的量（有每日紀錄時多半是 0）
        #
        # 逐日的完成狀況**不放這裡**——那是每日紀錄的事，存在 logs 的
        # entry["tasks_done"] / entry["tasks_missed"]。
        "baseline": 0,
        # 這個帳號要不要算這條任務、以及要不要改數字
        "enabled": True,
        "amount_override": None,
        # 活動任務的體力獎勵已經領出來了（之後就不再算這筆，見 scheduler.REWARD_CLAIM_DAYS）
        "reward_claimed": False,
        # 體力獎勵一達標就自動進包包（不能晚點再領）；False＝手動領取，排程決定哪一週
        "reward_auto": False,
    }


# --------------------------------------------------------------------------
# 低階讀寫
# --------------------------------------------------------------------------

def _read_json(path: Path):
    # utf-8-sig：有 BOM 就吃掉、沒有也照常讀。某些編輯器（含 PowerShell 的
    # Set-Content -Encoding UTF8）會寫入 BOM，純 utf-8 讀取會直接拋例外。
    with path.open("r", encoding="utf-8-sig") as fh:
        return json.load(fh)


def _write_json(path: Path, data: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    with tmp.open("w", encoding="utf-8") as fh:
        json.dump(data, fh, ensure_ascii=False, indent=2)
    tmp.replace(path)


def ensure_data_files() -> None:
    """第一次執行時建立預設檔案。"""
    PROFILES_DIR.mkdir(parents=True, exist_ok=True)
    LOGS_DIR.mkdir(parents=True, exist_ok=True)

    if not SHARED_PATH.exists():
        _write_json(SHARED_PATH, first_run_shared())

    # 預設的「主帳」只在一個帳號都沒有時（第一次執行）才建立——使用者可以自己
    # 刪帳號，刪掉 main 之後下次開程式不該又長回來
    if not any(PROFILES_DIR.glob("*.json")):
        for pid, pname in FIRST_RUN_PROFILES:
            _write_json(PROFILES_DIR / f"{pid}.json", default_profile(pname))

    if not APP_STATE_PATH.exists():
        _write_json(APP_STATE_PATH, {"last_active_profile": FIRST_RUN_PROFILES[0][0]})


# --------------------------------------------------------------------------
# 關卡鍵：跨活動一律用 "<event_id>/<level_id>"
# --------------------------------------------------------------------------

level_key = scheduler.level_key
split_level_key = scheduler.split_level_key


# --------------------------------------------------------------------------
# shared_config
# --------------------------------------------------------------------------

def load_shared() -> dict:
    return normalise_shared(_read_or_quarantine(SHARED_PATH))


def normalise_shared(data: dict) -> dict:
    base = default_shared()
    base.update(data or {})
    base["schema_version"] = SCHEMA_VERSION
    window = base.get("active_window") or {}
    base["active_window"] = {
        "start": window.get("start") or "06:00",
        "end": window.get("end") or "21:30",
    }
    prefs = base.get("schedule_prefs") or {}
    base["schedule_prefs"] = {
        "light_weekdays": prefs.get("light_weekdays") is not False,
        "simplify_days": prefs.get("simplify_days") is not False,
        # 多的限時體力留在晚到期的那批（先用快過期的）
        "expire_late": prefs.get("expire_late") is not False,
    }
    base.update(fixed_clocks())     # 舊檔裡改過的值一律蓋回寫死的
    base["events"] = [_normalise_event(ev, i)
                      for i, ev in enumerate(base.get("events") or [])]
    if not base["events"]:
        base["events"] = [default_event()]
    base["routine_tasks"] = [_normalise_task(t, "daily")
                             for t in base.get("routine_tasks") or []]
    base["items"] = [_normalise_item(it) for it in base.get("items") or []]
    if not base["items"]:
        base["items"] = copy.deepcopy(DEFAULT_ITEMS)
    # 活動類型預設表：只留使用者存過的類型，沒存的照內建（見 type_defaults）
    base["type_defaults"] = {
        event_type: normalise_type_default(data)
        for event_type, data in (base.get("type_defaults") or {}).items()
        if event_type in TEMPLATE_TYPES and data}
    return base


def _normalise_event(event: dict, index: int = 0) -> dict:
    event = dict(event or {})
    event_type = event.get("type")
    if event_type not in EVENT_TYPE_LABELS:
        event_type = "current"
    period = event.get("period") or {}
    standing = bool(event.get("standing"))
    name = (event.get("name") or "").strip()
    # 限期關卡的期數（第幾檔）。跟名稱分開存：名稱是系列（「忘卻」），期數只用來
    # 分辨檔次，顯示時才接在一起（scheduler.event_label）。
    period_no = event.get("period_no")
    result = {
        "id": event.get("id") or f"ev{index + 1}",
        "name": name,
        "period_no": (int(period_no) if period_no not in (None, "")
                      and event_type == "limited" and not standing else None),
        "standing": standing,
        "type": event_type,
        "start_date": event.get("start_date") or period.get("start_date"),
        "end_date": event.get("end_date") or period.get("end_date"),
        "start_time": event.get("start_time") or DEFAULT_EVENT_START_TIME,
        "end_time": event.get("end_time") or DEFAULT_EVENT_END_TIME,
        # 舊檔沒有這個鍵（或寫成 null）一律當「吃加成」，只有明確的 false 才關掉
        "activity_bonus_applies": event.get("activity_bonus_applies") is not False,
        # 積分上限（加成後）。舊檔沒有這個鍵 → None → 沒有上限，行為不變。
        "points_cap": (None if event.get("points_cap") is None
                       else max(0, int(event["points_cap"]))),
        # 「盡量提早」。舊檔沒有這兩個鍵 → 不提早，行為不變。
        "early_finish_date": event.get("early_finish_date") or None,
        "early_takes_surplus": event.get("early_takes_surplus") is not False,
        # 限期關卡「結束當天不打」：這一檔的次數要在前一天打完（接下一期會帶過去）
        "skip_last_day": (event.get("skip_last_day") is True
                          and event_type == "limited" and not standing),
        "levels": [_normalise_level(lv, standing)
                   for lv in event.get("levels") or []],
        "tasks": [_normalise_task(t, "event") for t in event.get("tasks") or []],
    }
    if event_type == "limited" and not standing:
        # 限期關卡只有起訖日與關卡；任務、加成、積分上限都是活動才有的概念
        result["activity_bonus_applies"] = False
        result["points_cap"] = None
        result["early_finish_date"] = None
        result["tasks"] = []
    if event_type in NO_POINTS_TYPES and not standing:
        # 音像、蜜意蒐羅、祕寶探尋沒有積分與加成；任務照留
        result["activity_bonus_applies"] = False
        result["points_cap"] = None
        result["early_finish_date"] = None
    if standing:
        # 常駐關卡不能改名（活動設定頁的名稱欄也鎖住了），也沒有加成
        result["name"] = STANDING_EVENT_NAME
        result["activity_bonus_applies"] = False
        # 常駐沒有起訖日、也不會有活動任務。留著空值只會讓別處誤以為填了一半。
        # 積分上限同理——常駐關卡沒有積分獎勵表可言。
        result["start_date"] = result["end_date"] = None
        result["points_cap"] = None
        result["early_finish_date"] = None
        result["tasks"] = []
    # 手動封存的標記。只在有封存時才留這個鍵（還原是直接把鍵拿掉），常駐不能封存。
    # 這裡漏掉的話，封存只活到下次重開程式——讀檔時就被洗掉了。
    if event.get("archived") and not standing:
        result["archived"] = True
    return result


def _normalise_level(level: dict, standing: bool = False) -> dict:
    if standing:
        # 「開放起日」「總次數上限」「必打滿」「同一天打完」「開場先打一次」都是相對活動
        # 起訖日／整檔活動總量的概念，常駐沒有起訖日可以相對、也沒有「活動開始」
        # 可言，一律清掉。要限次數請用「指定關卡次數限制」。組別只對解鎖鏈有意義，
        # 一併清掉。
        level = dict(level or {})
        level["available_from"] = None
        level["max_total"] = None
        level["must_finish"] = False
        level["same_day"] = False
        level["unlock_first"] = False
        level["group"] = None
        # 常駐關卡一律沒有積分
        level["scoring"] = False
        level["base_points"] = None
    return {
        "id": level.get("id") or "",
        "name": level.get("name") or "",
        "stamina_cost": int(level.get("stamina_cost") or 0),
        "scoring": bool(level.get("scoring", True)),
        # 敵人人數跟消耗體力一樣是關卡本身的屬性，所有帳號共用。可以是 0。
        "enemies": max(0, int(level.get("enemies") or 0)),
        # 打一次拿到幾個活動道具（「取得道具」類任務用）。跟敵人人數一樣是關卡
        # 本身的屬性，所有帳號共用、不吃加成。舊檔沒有這個鍵 → 0。
        "drops": max(0, int(level.get("drops") or 0)),
        # 新帳號（或第一次看到這關的帳號）「這次計算要算」預設勾不勾（見 sync_levels）。
        # 每個帳號之後怎麼勾存在各自的 level_enabled，這裡只是起點
        "default_enabled": level.get("default_enabled") is not False,
        # 基礎積分（未加成）也是活動本身的數值，所有帳號共用；留空代表積分純手填
        "base_points": (int(level["base_points"])
                        if level.get("base_points") else None),
        # 算不算進「關卡次數」類的活動任務。計分關卡一定算；活動BOSS關這種
        # 「沒積分但算次數」的就是 scoring=False + counts_clears=True。
        # 舊資料沒有這個鍵，跟著 scoring 走（計分→算、不計分→不算）。
        "counts_clears": bool(level.get("counts_clears",
                                        level.get("scoring", True))),
        # 開放起日：相對活動起始日的偏移量，None＝整檔活動都能打
        "available_from": (int(level["available_from"])
                           if level.get("available_from") is not None else None),
        # 整檔活動總共最多打幾次（不是每天）。None＝沒有上限。
        "max_total": (int(level["max_total"])
                      if level.get("max_total") else None),
        # 這個次數是不是「一定要打滿」（活動BOSS關是必打的）。
        # 只在有 max_total 時才有意義。
        "must_finish": bool(level.get("must_finish")),
        # 剩下的次數要集中在同一天打完，不拆成好幾天（活動BOSS關一口氣打掉）。
        # 跟 must_finish 一樣只在有 max_total 時才有意義；兩個各自獨立——
        # 只勾這個＝「要打就同一天打」，不保證打滿。
        # 舊檔沒有這個鍵 → False。
        "same_day": bool(level.get("same_day")),
        # 活動開始後要先打過一次才會開下一關——遊戲的解鎖鏈。勾起來的關卡會照
        # 消耗體力由小到大各先打一次，而且**比它貴的關卡在它打過之前完全不能打**。
        #
        # 跟 max_total／must_finish **完全解耦**：那兩個是「總共只能打幾次」＋
        # 「一定要打滿那個數字」（上下界夾成等式），這一個是「至少先打一次、
        # 之後還能猛打」。兩者可以並用（max_total=1 ＋ unlock_first ＝ 恰好一次）。
        #
        # 舊檔沒有這個鍵 → False。
        "unlock_first": bool(level.get("unlock_first")),
        # 解鎖鏈的組別。同一組的關卡照耗體由小到大解鎖，不同組互不相干
        # （蜜意蒐羅 11 組 × 20/30/40）。None＝跟這檔活動其他沒填組別的關卡同一條鏈，
        # 舊檔沒有這個鍵 → None。
        "group": (int(level["group"])
                  if level.get("group") not in (None, "") else None),
        # 難度分組（只有限期關卡——檢定、忘卻——用得到）：依序解鎖的第幾關，
        # 例如 [[35, 40, 45], [50, 55, 60], [61, 62, 63]]。所有帳號共用；各帳號在
        # 「指定關卡次數限制」選某個難度只能在星期幾打。舊檔沒有 → []。
        "tiers": _normalise_tiers(level.get("tiers")) if not standing else [],
    }


def _normalise_tiers(raw) -> list[list[int]]:
    groups = []
    for group in raw or []:
        stages = sorted({int(x) for x in group or [] if int(x) >= 1})
        if stages:
            groups.append(stages)
    return groups


def _normalise_task(task: dict, default_cycle: str = "event") -> dict:
    task = dict(task or {})
    cycle = task.get("cycle")
    if cycle not in TASK_CYCLE_LABELS:
        cycle = default_cycle
    metric = task.get("metric")
    if metric not in TASK_METRIC_LABELS:
        metric = "manual"
    scope = task.get("scope")
    if scope is not None:
        scope = [str(s) for s in scope if s]
        if not scope:
            scope = None
    month_days = task.get("reward_days")
    if month_days:
        month_days = sorted({max(1, min(31, int(d))) for d in month_days})
    else:
        month_days = list(DEFAULT_MONTH_DAYS)
    return {
        "id": task.get("id") or "",
        "name": (task.get("name") or "").strip(),
        "cycle": cycle,
        "metric": metric,
        "scope": scope,
        # 手動勾選只有做到／沒做到，數量用不到，一律 1（讀到舊檔的 10、0 也統一）
        "amount": 1 if metric == "manual" else max(0, int(task.get("amount") or 0)),
        # cycle=event 專用，沿用 resolve_day_offset 慣例（負數＝從活動最後一天算）
        "deadline_offset": (int(task["deadline_offset"])
                            if task.get("deadline_offset") is not None else -1),
        # 非 event 週期的任務可以再限縮到某一段期間。活動任務相對該活動的起始日，
        # 固定任務相對「所有活動涵蓋的期間」的起始日（見 scheduler._task_span）。
        "from_offset": (int(task["from_offset"])
                        if task.get("from_offset") is not None else None),
        "to_offset": (int(task["to_offset"])
                      if task.get("to_offset") is not None else None),
        # 固定任務的期間改存絕對日期（偏移量的基準會隨活動增減而漂移）。
        # 活動任務不用這兩個鍵；舊檔沒有 → None，照舊用上面的偏移量。
        "from_date": task.get("from_date") or None,
        "to_date": task.get("to_date") or None,
        # 要不要當成求解的硬條件。manual 一律不進求解。
        "enforce": bool(task.get("enforce", True)) and metric != "manual",
        # 「預設完成」：當作每個週期你都會做到，只有沒做到時才去每日紀錄標記。
        # 登入、簽到這種每天一定會做的任務，每天勾一次太煩了。
        # 手動勾選類預設開，其餘（程式算得出來的）預設關——那些本來就不必勾。
        "assume_done": bool(task.get("assume_done", metric == "manual")),
        # 每週任務出現的時間不固定（商店購買）：到每日紀錄勾「已完成」的那天才
        # 入帳；那週沒勾就照舊算在 reward_weekday（見 scheduler.task_reward_sources）
        "grant_on_done": bool(task.get("grant_on_done")) and cycle == "weekly",
        "rewards": [_normalise_reward(r) for r in task.get("rewards") or []],
        # 獎勵入帳時機：每週任務算在星期幾拿到、每月任務算在幾號拿到
        "reward_weekday": max(0, min(6, int(task.get("reward_weekday", 6) or 0))),
        "reward_days": month_days,
        "note": (task.get("note") or "").strip(),
    }


def _normalise_reward(reward: dict) -> dict:
    return {
        "item": reward.get("item") or "",
        "qty": max(0, int(reward.get("qty") or 0)),
    }


def _normalise_item(item: dict) -> dict:
    return {
        "id": item.get("id") or "",
        "name": item.get("name") or item.get("id") or "",
        "stamina": max(0, int(item.get("stamina") or 0)),
    }


def save_shared(data: dict) -> None:
    data["schema_version"] = SCHEMA_VERSION
    data["last_modified"] = now_stamp()
    _write_json(SHARED_PATH, data)


def shared_stamp() -> tuple[int, int, str] | None:
    """磁碟上那份共用設定的指紋，用來認「還是不是我上次讀／寫的那一份」。

    同時開好幾個視窗時，每個視窗都握著自己啟動時讀到的共用設定；別的視窗存過
    之後這裡就會變。只看 mtime 和大小不夠：兩次存檔落在同一個 mtime 刻度、
    長度又一樣（例如 05:00 改成 04:00）就認不出來，所以再加上內容雜湊。
    檔案不在回傳 None。
    """
    try:
        stat = SHARED_PATH.stat()
        digest = hashlib.sha256(SHARED_PATH.read_bytes()).hexdigest()
    except OSError:
        return None
    return (stat.st_mtime_ns, stat.st_size, digest)


def shared_fingerprint(data: dict) -> str:
    """共用設定的內容指紋，用來判斷這個視窗有沒有改過它。

    last_modified 每次存檔都會變，不算內容。先過一次 normalise_shared：分頁的
    collect() 寫回來的形狀跟讀檔時不完全一樣（例如固定任務少了空的 note），
    不正規化的話每個視窗一開就會被當成改過。
    """
    content = normalise_shared(copy.deepcopy(data or {}))
    content.pop("last_modified", None)
    return json.dumps(content, ensure_ascii=False, sort_keys=True, default=str)


def next_level_id(levels: list[dict], event_id: str | None = None) -> str:
    """產生一個沒被用過的關卡 id（lv1, lv2, ... 或 lvN）。

    給了 `event_id` 就連這檔活動「刪掉的關卡」留下的 id 也跳過
    （見 `_used_level_ids`）。
    """
    used = {lv.get("id") for lv in levels}
    if event_id:
        used |= _used_level_ids(event_id)
    i = 1
    while f"lv{i}" in used:
        i += 1
    return f"lv{i}"


def _used_level_ids(event_id: str) -> set[str]:
    """這檔活動在各帳號與紀錄檔裡用過的關卡 id——含已經刪掉的關卡。

    跟 `_used_event_ids` 同一個洞：每日紀錄的鍵是 "<event_id>/<level_id>"，
    各帳號的本帳號積分、計算開關也用關卡 id 記。刪掉的關卡 id 再發給新關卡，
    舊關卡的紀錄與設定就會被算到新關卡頭上（耗體、積分全部算錯）。
    """
    prefix = f"{event_id}/"
    used: set[str] = set()

    def from_keys(keys):
        used.update(key[len(prefix):] for key in keys
                    if isinstance(key, str) and key.startswith(prefix))

    for path in list(PROFILES_DIR.glob("*.json")) + list(LOGS_DIR.glob("*.json")):
        try:
            data = _read_json(path)
        except (OSError, ValueError):
            continue
        if not isinstance(data, dict):
            continue
        section = (data.get("events") or {}).get(event_id) or {}
        if isinstance(section, dict):
            for field in ("level_points", "level_enabled", "level_max_total"):
                used.update((section.get(field) or {}).keys())
        for entry in data.get("entries") or []:
            from_keys((entry.get("counts") or {}).keys())
            for play in entry.get("plays") or []:
                from_keys((play.get("counts") or {}).keys())
    return used


def _used_event_ids() -> set[str]:
    """刪掉的活動在各帳號與紀錄檔裡留下的 id。

    每日紀錄的鍵是 "<event_id>/<level_id>"，活動刪掉之後紀錄還在。那個 id 如果
    再發給新活動，舊活動的紀錄就會被算到新活動頭上。
    """
    used: set[str] = set()
    for path in list(PROFILES_DIR.glob("*.json")) + list(LOGS_DIR.glob("*.json")):
        try:
            data = _read_json(path)
        except (OSError, ValueError):
            continue
        if not isinstance(data, dict):
            continue
        used.update((data.get("events") or {}).keys())
        used.update(key.split("/", 1)[0] for key in (data.get("task_state") or {}))
        for entry in data.get("entries") or []:
            used.update(key.split("/", 1)[0]
                        for key in (entry.get("counts") or {}))
    return used


def next_event_id(events: list[dict]) -> str:
    used = {ev.get("id") for ev in events} | _used_event_ids()
    i = 1
    while f"ev{i}" in used:
        i += 1
    return f"ev{i}"


def next_task_id(tasks: list[dict], prefix: str = "t") -> str:
    used = {t.get("id") for t in tasks}
    i = 1
    while f"{prefix}{i}" in used:
        i += 1
    return f"{prefix}{i}"


def next_item_id(items: list[dict]) -> str:
    used = {it.get("id") for it in items}
    i = 1
    while f"item{i}" in used:
        i += 1
    return f"item{i}"


def events_of(shared: dict) -> list[dict]:
    return list((shared or {}).get("events") or [])


def is_standing(event: dict) -> bool:
    return bool((event or {}).get("standing"))


def is_limited(event: dict) -> bool:
    """限期關卡（檢定、忘卻……）：有起訖日，但不是活動。"""
    return (event or {}).get("type") == "limited" and not is_standing(event)


def is_archived(event: dict) -> bool:
    """手動封存的活動：畫面上收起來、排程不排，但留在 events 裡。

    留著是為了每日紀錄——過去那幾天的打法、耗體、積分都是拿關卡去對照
    紀錄算出來的，刪掉就對不回去了。
    """
    return scheduler.is_archived(event)


def visible_events(shared: dict) -> list[dict]:
    """畫面上要列出來的活動＝沒被封存的。要看全部（紀錄加總、找 id）用 events_of。"""
    return [ev for ev in events_of(shared) if not is_archived(ev)]


def archived_events(shared: dict) -> list[dict]:
    return [ev for ev in events_of(shared) if is_archived(ev)]


def real_events(shared: dict) -> list[dict]:
    """真正的活動——排程範圍、活動優先序、特殊日的「第 N 天」都只看這些。

    常駐關卡與限期關卡都不算：前者沒有起訖日，後者的起訖日跟活動無關，
    拿來當基準會把排程拉長、或讓「第 N 天」落在不相干的日子。
    已封存的也不算：這份清單是各種下拉與優先序的來源。
    """
    return [ev for ev in visible_events(shared)
            if not is_standing(ev) and not is_limited(ev)]


def limited_events(shared: dict) -> list[dict]:
    return [ev for ev in visible_events(shared) if is_limited(ev)]


def next_period_event(shared: dict, event: dict) -> dict:
    """接下一期限期關卡：關卡結構照抄，起始日＝上一檔的結束日，結束日留空。

    上一檔 12:00 結束、同一天 15:00 開下一檔，所以起始日直接沿用結束日。
    新一檔有新的 id，每日紀錄的鍵跟著換，已打次數自然從 0 開始算。
    """
    clone = copy.deepcopy(event)
    clone["id"] = next_event_id(events_of(shared))
    clone["start_date"] = event.get("end_date")
    clone["end_date"] = None
    # 期數接著往下數；名稱（系列）不變，關卡優先序才會自動跟過來
    if event.get("period_no") is not None:
        clone["period_no"] = int(event["period_no"]) + 1
    return clone


def find_event(shared: dict, event_id: str) -> dict | None:
    for event in events_of(shared):
        if event.get("id") == event_id:
            return event
    return None


def all_levels(shared: dict) -> list[dict]:
    """把所有活動的關卡攤平成一張表，每筆帶 event_id / key / event_name。

    key 是跨活動唯一的 "<event_id>/<level_id>"，每日紀錄、任務的 scope、
    指定關卡規則都用它指稱關卡。
    """
    rows = []
    for event in events_of(shared):
        for level in event.get("levels") or []:
            row = dict(level)
            row["event_id"] = event.get("id")
            row["event_name"] = scheduler.event_label(event)
            row["series_name"] = event.get("name") or ""
            row["key"] = level_key(event.get("id"), level.get("id"))
            rows.append(row)
    return rows


def event_choice_label(event: dict, now: datetime | None = None) -> str:
    """下拉選單裡指稱一檔活動。

    限期關卡靠期數分辨（「忘卻23」），已結束的再標出來；其他活動就是名稱。
    """
    label = scheduler.event_label(event)
    if is_limited(event) and period_ended(event, now):
        return label + "・已結束"
    return label


def period_ended(event: dict, now: datetime | None = None) -> bool:
    try:
        return scheduler.event_bounds(event)[1] <= (now or datetime.now())
    except scheduler.PlanError:
        return False


def level_choices(shared: dict, include_archived: bool = False) -> list[tuple[str, str]]:
    """所有關卡的 (關卡鍵, 顯示名稱)，顯示成「活動·關卡」，限期關卡帶期間。

    下拉選單不列已封存活動的關卡；要把既有規則的關卡鍵還原成名稱時傳
    `include_archived=True`，舊規則才不會印出裸的鍵。
    """
    events = {ev.get("id"): ev for ev in events_of(shared)}
    return [(row["key"],
             scheduler.level_label(event_choice_label(events[row["event_id"]]),
                                   row["series_name"], row.get("name") or row.get("id")))
            for row in all_levels(shared)
            if include_archived or not is_archived(events[row["event_id"]])]


def priority_key_of(shared: dict, key: str) -> str:
    """關卡優先序要存的鍵：限期關卡換成系列鍵（跟著換檔），其他照舊。"""
    event_id, level_id = split_level_key(key)
    event = find_event(shared, event_id)
    if event is not None and is_limited(event):
        return scheduler.limited_series_key(event.get("name") or event_id, level_id)
    return key


def priority_label(shared: dict, key: str) -> str:
    """關卡優先序清單的顯示名稱。"""
    series = scheduler.split_limited_series_key(key)
    if series is None:
        return dict(level_choices(shared, include_archived=True)).get(key, key)
    name, level_id = series
    periods = [ev for ev in limited_events(shared) if (ev.get("name") or "") == name]
    level_name = next((lv.get("name") for ev in periods
                       for lv in ev.get("levels") or [] if lv.get("id") == level_id),
                      level_id)
    open_now = any(not period_ended(ev) for ev in periods
                   if any(lv.get("id") == level_id for lv in ev.get("levels") or []))
    return (scheduler.level_label(name, name, level_name)
            + ("（限期，自動跟著換期）" if open_now else "（目前沒有進行中的一期）"))


def priority_choices(shared: dict) -> list[tuple[str, str]]:
    """關卡優先序「加入」的選項：限期關卡每個系列只列一次，已結束的檔次不列。"""
    choices, seen = [], set()
    events = {ev.get("id"): ev for ev in events_of(shared)}
    for key, label in level_choices(shared):
        event = events[split_level_key(key)[0]]
        if not is_limited(event):
            choices.append((key, label))
            continue
        if period_ended(event):
            continue
        pkey = priority_key_of(shared, key)
        if pkey not in seen:
            seen.add(pkey)
            choices.append((pkey, priority_label(shared, pkey)))
    return choices


def level_table(shared: dict) -> dict[str, dict]:
    return {row["key"]: row for row in all_levels(shared)}


# --------------------------------------------------------------------------
# profiles
# --------------------------------------------------------------------------

def list_profiles() -> list[tuple[str, str]]:
    """回傳 [(profile_id, 顯示名稱), ...]，DEFAULT_PROFILES 裡有的排前面。"""
    result = []
    seen = set()
    for pid, fallback in DEFAULT_PROFILES:
        path = PROFILES_DIR / f"{pid}.json"
        if path.exists():
            result.append((pid, _profile_name(path, fallback)))
            seen.add(pid)
    for path in sorted(PROFILES_DIR.glob("*.json")):
        pid = path.stem
        if pid in seen:
            continue
        result.append((pid, _profile_name(path, pid)))
    return result


def _profile_name(path: Path, fallback: str) -> str:
    """帳號檔裡的顯示名稱；檔案壞掉時用 fallback（真正讀檔時才會留底，見 load_profile）。"""
    try:
        return _read_json(path).get("profile_name") or fallback
    except (OSError, ValueError, AttributeError):
        return fallback


def load_profile(profile_id: str) -> dict:
    path = PROFILES_DIR / f"{profile_id}.json"
    fallback_name = dict(DEFAULT_PROFILES).get(profile_id, profile_id)
    if not path.exists():
        data = default_profile(fallback_name)
        _write_json(path, data)
        return data
    base = default_profile(fallback_name)
    base.update(_read_or_quarantine(path))
    base["schema_version"] = SCHEMA_VERSION
    base["special_days"] = list(base.get("special_days") or [])
    base["event_default_rules"] = list(base.get("event_default_rules") or [])
    base["daily_level_rules"] = list(base.get("daily_level_rules") or [])
    base["daily_level_targets"] = list(base.get("daily_level_targets") or [])
    base["stamina_sources"] = list(base.get("stamina_sources") or [])
    base["event_priority"] = list(base.get("event_priority") or [])
    base["level_priority"] = list(base.get("level_priority") or [])
    base["events"] = dict(base.get("events") or {})
    for event_id, data in base["events"].items():
        merged = default_profile_event()
        merged.update(data or {})
        merged["level_points"] = dict(merged.get("level_points") or {})
        merged["level_enabled"] = dict(merged.get("level_enabled") or {})
        merged["activity_bonus"] = merged.get("activity_bonus") or 0
        base["events"][event_id] = merged
    base["task_state"] = dict(base.get("task_state") or {})
    for key, state in base["task_state"].items():
        merged = default_task_state()
        merged.update(state or {})
        base["task_state"][key] = merged
    return base


def save_profile(profile_id: str, data: dict) -> None:
    data["schema_version"] = SCHEMA_VERSION
    data["last_modified"] = now_stamp()
    _write_json(PROFILES_DIR / f"{profile_id}.json", data)


def profile_event(profile: dict, event_id: str) -> dict:
    """取得（必要時建立）這個帳號在某檔活動的資料。"""
    events = profile.setdefault("events", {})
    data = events.get(event_id)
    if data is None:
        data = default_profile_event()
        events[event_id] = data
    return data


def task_state(profile: dict, task_key: str) -> dict:
    states = profile.setdefault("task_state", {})
    state = states.get(task_key)
    if state is None:
        state = default_task_state()
        states[task_key] = state
    return state


def sync_levels(profile: dict, shared: dict) -> None:
    """確保每個活動的每個關卡在 level_points / level_enabled 都有欄位。

    已不存在的關卡 id 保留不刪，避免使用者暫時移除關卡後積分數字消失。
    """
    for event in events_of(shared):
        data = profile_event(profile, event.get("id"))
        points = data.setdefault("level_points", {})
        enabled = data.setdefault("level_enabled", {})
        data.setdefault("level_max_total", {})
        bonus = (float(data.get("activity_bonus") or 0)
                 if event.get("activity_bonus_applies") is not False else 0)
        for level in event.get("levels") or []:
            # 第一次看到這關：填了基礎積分的照本帳號的加成先算好積分，跟活動設定頁
            # 改基礎積分時一樣；沒填的留空（積分自己填）
            points.setdefault(level["id"], scheduler.points_with_bonus(
                level.get("base_points"), bonus) if level.get("scoring", True) else None)
            enabled.setdefault(level["id"], level.get("default_enabled") is not False)


# --------------------------------------------------------------------------
# app_state
# --------------------------------------------------------------------------

def get_active_profile_id() -> str:
    try:
        pid = _read_json(APP_STATE_PATH).get("last_active_profile")
    except (OSError, ValueError, AttributeError):
        pid = None
    known = [p for p, _ in list_profiles()]
    if pid in known:
        return pid
    return known[0] if known else DEFAULT_PROFILES[0][0]


def _update_app_state(**fields) -> None:
    """只改 app_state 裡指定的欄位，其他欄位（例如畫面縮放）原樣保留。"""
    try:
        state = _read_json(APP_STATE_PATH)
    except (OSError, ValueError):
        state = {}
    if not isinstance(state, dict):
        state = {}
    state.update(fields)
    _write_json(APP_STATE_PATH, state)


def set_active_profile_id(profile_id: str) -> None:
    _update_app_state(last_active_profile=profile_id)


def get_ui_zoom() -> int:
    """畫面縮放比例（%），沒存過或壞掉就是 100。"""
    try:
        return int(_read_json(APP_STATE_PATH).get("ui_zoom") or 100)
    except (OSError, ValueError, TypeError, AttributeError):
        return 100


def set_ui_zoom(percent: int) -> None:
    _update_app_state(ui_zoom=int(percent))


def get_window_geometry() -> dict | None:
    """上次關閉時主視窗的大小與位置：{"x","y","width","height","zoomed"}。

    沒存過或內容不對就回 None（照預設大小開）。數字是螢幕實際像素，
    換螢幕後可能已經不在畫面上——那是呼叫端要檢查的事。
    """
    try:
        raw = _read_json(APP_STATE_PATH).get("window")
        result = {key: int(raw[key]) for key in ("x", "y", "width", "height")}
        result["zoomed"] = bool(raw.get("zoomed"))
    except (OSError, ValueError, TypeError, AttributeError, KeyError):
        return None
    if result["width"] <= 0 or result["height"] <= 0:
        return None
    return result


def set_window_geometry(x: int, y: int, width: int, height: int,
                        zoomed: bool) -> None:
    _update_app_state(window={"x": int(x), "y": int(y), "width": int(width),
                              "height": int(height), "zoomed": bool(zoomed)})


# --------------------------------------------------------------------------
# 設定檔增刪
# --------------------------------------------------------------------------

# 設定檔 id 就是檔名，只收安全字元（匯入時也用這個擋怪檔名）
_PROFILE_ID_RE = re.compile(r"^[A-Za-z0-9_-]+$")


def new_profile_id() -> str:
    """產生沒被用過的設定檔 id（p1, p2, ...）。

    紀錄檔也要避開：刪掉的設定檔紀錄若還在 logs/，同一個 id 再發出去，
    新設定檔就會繼承到別人的每日紀錄。
    """
    used = {path.stem for path in PROFILES_DIR.glob("*.json")}
    used |= {path.stem for path in LOGS_DIR.glob("*.json")}
    i = 1
    while f"p{i}" in used:
        i += 1
    return f"p{i}"


def create_profile(name: str, copy_from: dict | None = None) -> str:
    """新增設定檔，回傳新 id。copy_from 給了就複製它的設定（每日紀錄不複製）。"""
    pid = new_profile_id()
    if copy_from is None:
        data = default_profile(name)
    else:
        data = copy.deepcopy(copy_from)
        data["profile_name"] = name
    save_profile(pid, data)
    return pid


def delete_profile(profile_id: str) -> str:
    """刪除設定檔與它的每日紀錄，回傳留底的資料夾名稱。

    不真的刪掉，而是搬進 _deleted/<id>_<時間>/，按錯了還救得回來。
    至少要留一個設定檔。
    """
    if len(list_profiles()) <= 1:
        raise ValueError("至少要留一個帳號")
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    folder = APP_DIR / "_deleted" / f"{profile_id}_{stamp}"
    folder.mkdir(parents=True, exist_ok=True)
    for kind, base in (("profiles", PROFILES_DIR), ("logs", LOGS_DIR)):
        src = base / f"{profile_id}.json"
        if src.exists():
            (folder / kind).mkdir(exist_ok=True)
            shutil.move(str(src), str(folder / kind / src.name))
    return f"_deleted/{folder.name}"


# --------------------------------------------------------------------------
# 全部資料匯出／匯入（單一 json 檔）
# --------------------------------------------------------------------------

BUNDLE_FORMAT = "nu_app_bundle"
BUNDLE_VERSION = 1


def _read_folder(folder: Path) -> dict:
    result = {}
    for path in sorted(folder.glob("*.json")):
        try:
            result[path.stem] = _read_json(path)
        except (OSError, ValueError):
            continue
    return result


def export_bundle() -> dict:
    """把共用設定、所有設定檔、每日紀錄原封不動打包成一個 dict。"""
    def read_or(path, default):
        try:
            return _read_json(path)
        except (OSError, ValueError):
            return default

    return {
        "format": BUNDLE_FORMAT,
        "bundle_version": BUNDLE_VERSION,
        "exported_at": now_stamp(),
        "app_version": __version__,     # 只是記錄是哪一版匯出的，匯入時不檢查
        "schema_version": SCHEMA_VERSION,
        "app_state": read_or(APP_STATE_PATH, {}),
        "shared_config": read_or(SHARED_PATH, None),
        "profiles": _read_folder(PROFILES_DIR),
        "logs": _read_folder(LOGS_DIR),
    }


def _check_bundle(bundle) -> None:
    if not isinstance(bundle, dict) or bundle.get("format") != BUNDLE_FORMAT:
        raise ValueError("這不是本程式匯出的備份檔")
    if int(bundle.get("bundle_version") or 0) > BUNDLE_VERSION:
        raise ValueError("備份檔是較新版本的程式匯出的，請先更新程式")
    if not isinstance(bundle.get("shared_config"), dict):
        raise ValueError("備份檔缺少共用設定")
    profiles = bundle.get("profiles")
    if not isinstance(profiles, dict) or not profiles:
        raise ValueError("備份檔裡沒有任何帳號")
    for key in ("profiles", "logs"):
        section = bundle.get(key) or {}
        if not isinstance(section, dict):
            raise ValueError(f"備份檔的 {key} 格式不對")
        for name, data in section.items():
            if not isinstance(data, dict):
                raise ValueError(f"備份檔的 {key}/{name} 格式不對")
            if not _PROFILE_ID_RE.match(str(name)):
                raise ValueError(f"備份檔裡有不合法的帳號名稱：{name}")


def import_bundle(bundle: dict) -> str:
    """用備份檔整個取代目前資料，回傳匯入前的備份資料夾名稱。

    格式不對就丟 ValueError，此時什麼都還沒動。
    """
    _check_bundle(bundle)
    backup = _backup_data_dir("import")
    for folder in (PROFILES_DIR, LOGS_DIR):
        folder.mkdir(parents=True, exist_ok=True)
        for path in folder.glob("*.json"):
            path.unlink()
    _write_json(SHARED_PATH, bundle["shared_config"])
    for pid, data in bundle["profiles"].items():
        _write_json(PROFILES_DIR / f"{pid}.json", data)
    for pid, data in (bundle.get("logs") or {}).items():
        _write_json(LOGS_DIR / f"{pid}.json", data)
    app_state = bundle.get("app_state")
    _write_json(APP_STATE_PATH, app_state if isinstance(app_state, dict)
                else {"last_active_profile": next(iter(bundle["profiles"]))})
    return backup


# --------------------------------------------------------------------------
# 每日紀錄
#
# 單一時間軸：一天一列，counts 的鍵是跨活動唯一的 "<event_id>/<level_id>"。
# 每檔活動只留「開始記錄之前就已經有的量」（baseline_*）。
#
#     目前積分 = baseline_points + 紀錄累計
# --------------------------------------------------------------------------

def load_log(profile_id: str) -> dict:
    path = LOGS_DIR / f"{profile_id}.json"
    if not path.exists():
        return _empty_log()
    data = _read_or_quarantine(path)
    if not data:
        return _empty_log()
    base = _empty_log()
    base.update(data)
    base["entries"] = list(base.get("entries") or [])
    for entry in base["entries"]:
        entry.setdefault("counts", {})
        # tasks_done ＝「要主動勾才算」的任務那天做到了
        # tasks_missed ＝「預設完成」的任務那天**沒**做到（只記例外）
        entry.setdefault("tasks_done", [])
        entry.setdefault("tasks_missed", [])
        # plays ＝ 分筆紀錄（每筆帶一個時刻，時刻必填）；counts 是當天的總量
        entry["plays"] = clean_plays(entry.get("plays"))
    base["events"] = dict(base.get("events") or {})
    base["archive"] = dict(base.get("archive") or {})
    return base


# 讀不出來的資料檔（共用設定、帳號、紀錄）：{原檔路徑: 留底的複本路徑}。
# 讀失敗時回傳的是預設值，下一次存檔就會把原檔整份蓋掉，所以蓋掉之前先留
# 一份。每個檔案每次執行只留一次底——
# load_log 被呼叫得很頻繁，每次都複製會堆出一排一模一樣的檔案。
quarantined: dict[Path, Path] = {}


def _read_or_quarantine(path: Path) -> dict:
    """讀 JSON 物件；讀不出來就先留底（見 _quarantine），回傳空的 dict。"""
    try:
        data = _read_json(path)
        if not isinstance(data, dict):
            raise ValueError("最外層不是物件")
        return data
    except (OSError, ValueError):
        _quarantine(path)
        return {}


def _quarantine(path: Path) -> None:
    if path in quarantined:
        return
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    copy_path = path.with_name(f"{path.name}.corrupt_{stamp}")
    try:
        shutil.copy(path, copy_path)
    except OSError:
        return          # 連複製都不行（檔案被鎖住）：下次讀取時再試
    quarantined[path] = copy_path


# 每檔活動的起始值（開始記錄之前就有的量）有哪幾種。log 的活動區段存成
# baseline_<種類>；積分、關卡數推導成 current_points／current_clears，
# 耗體、敵人、道具抄成 profile 裡那檔活動的 baseline_<種類>，給任務進度用
# （活動預設範圍的任務：目前值＝起始值＋活動開始後的紀錄累計）。
EVENT_BASELINE_KINDS = ("points", "clears", "stamina", "enemies", "drops")


def _empty_log() -> dict:
    return {
        "schema_version": SCHEMA_VERSION,
        "entries": [],
        "baseline_stamina": 0,
        "events": {},     # event_id -> {baseline_<EVENT_BASELINE_KINDS>, name, period}
        "archive": {},    # 已結束活動的舊紀錄，留著不刪
        "plan": None,
    }


def save_log(profile_id: str, log: dict) -> None:
    log["schema_version"] = SCHEMA_VERSION
    log["last_modified"] = now_stamp()
    _write_json(LOGS_DIR / f"{profile_id}.json", log)


def ensure_log_event(log: dict, event: dict, profile: dict) -> dict:
    """取得（必要時建立）某檔活動的基準值。

    建立時把設定檔當下的積分/關卡數快照成起始值，之後就以
    「起始值 + 紀錄累計」推導，不會重複計算。
    """
    event_id = event.get("id")
    events = log.setdefault("events", {})
    section = events.get(event_id)
    if section is None:
        data = profile_event(profile, event_id)
        section = {
            "baseline_points": int(data.get("current_points") or 0),
            "baseline_clears": int(data.get("current_clears") or 0),
        }
        events[event_id] = section
    for kind in EVENT_BASELINE_KINDS:
        section.setdefault(f"baseline_{kind}", 0)
    # 開始記錄之前就打過幾次：{level_id: 次數}（「補登開始前的進度」填的）
    section.setdefault("baseline_levels", {})
    section["name"] = scheduler.event_label(event)
    if event.get("start_date") and event.get("end_date"):
        section["period"] = {"start": event["start_date"], "end": event["end_date"]}
    return section


def set_event_baselines(section: dict, values: dict | None) -> None:
    """把起始值寫進紀錄檔裡一檔活動的區段。

    values：{種類: 數字}（種類見 EVENT_BASELINE_KINDS），另外可以有
    "levels": {level_id: 開始前打過幾次}。沒給的種類不動；次數 0 的關卡不留。
    """
    for kind, value in (values or {}).items():
        if kind == "levels":
            section["baseline_levels"] = {
                level_id: int(count) for level_id, count in value.items()
                if int(count or 0) > 0}
        else:
            section[f"baseline_{kind}"] = int(value)


def entry_for(log: dict, day: str) -> dict | None:
    for entry in log.get("entries") or []:
        if entry.get("date") == day:
            return entry
    return None


PLAY_TIME_FORMAT = "%Y-%m-%dT%H:%M"


def clean_plays(plays) -> list[dict]:
    """把分筆紀錄清乾淨：次數只留正整數，依時刻排序。

    時刻（`at`，YYYY-MM-DDTHH:MM）是必填的，讀不出時刻的分筆丟掉（手改壞的檔案）。
    整筆都沒有打法的也丟掉——留著只會在分筆清單裡變成一列空白。
    """
    out = []
    for play in plays or []:
        if not isinstance(play, dict):
            continue
        counts = {}
        for key, value in (play.get("counts") or {}).items():
            try:
                value = int(value or 0)
            except (TypeError, ValueError):
                continue
            if value > 0:
                counts[key] = value
        if not counts:
            continue
        at = str(play.get("at") or "")
        try:
            datetime.strptime(at, PLAY_TIME_FORMAT)
        except ValueError:
            continue
        out.append({"at": at, "counts": counts})
    out.sort(key=lambda x: x["at"])
    return out


def counts_of_plays(plays) -> dict:
    """分筆紀錄的加總。entry["counts"] 永遠是這個值。"""
    total: dict[str, int] = {}
    for play in plays or []:
        for key, value in (play.get("counts") or {}).items():
            total[key] = total.get(key, 0) + int(value or 0)
    return total


# {任務鍵: {沒做到的日期字串}}，給 scheduler 扣掉那幾筆獎勵用。
# 實作在 scheduler（它不能反過來 import storage），這裡只是別名。
missed_by_task = scheduler._missed_by_task
done_by_task = scheduler._done_by_task


def log_totals(entries: list[dict], levels: dict[str, dict],
               points_of: dict[str, int]) -> dict:
    """把紀錄加總成各種累計值。

    回傳 {"clears", "stamina", "enemies", "points_by_event", "clears_by_event",
          "counts"}。`points_by_event` / `clears_by_event` 逐活動分開，因為
    積分與「會進總量的關卡數」都是活動各自的。

    ※ 「會進總量」的判斷必須跟 scheduler 那條關卡次數限制式一致，
       一邊多算一邊少算就會對不起來。
    """
    totals = {"clears": 0, "stamina": 0, "enemies": 0,
              "points_by_event": {}, "clears_by_event": {}, "counts": {}}
    for entry in entries or []:
        for key, count in (entry.get("counts") or {}).items():
            try:
                count = int(count or 0)
            except (TypeError, ValueError):
                continue
            if count <= 0:
                continue
            level = levels.get(key)
            totals["counts"][key] = totals["counts"].get(key, 0) + count
            totals["clears"] += count
            if level is None:
                continue
            event_id = level.get("event_id")
            totals["stamina"] += int(level.get("stamina_cost") or 0) * count
            totals["enemies"] += int(level.get("enemies") or 0) * count
            if level.get("scoring"):
                gained = int(points_of.get(key) or 0) * count
                totals["points_by_event"][event_id] = (
                    totals["points_by_event"].get(event_id, 0) + gained)
            if level.get("counts_clears", level.get("scoring", True)):
                totals["clears_by_event"][event_id] = (
                    totals["clears_by_event"].get(event_id, 0) + count)
    return totals


def points_map(shared: dict, profile: dict) -> dict[str, int]:
    """{關卡鍵: 這個帳號在這關拿到的積分}。"""
    result = {}
    for event in events_of(shared):
        data = profile_event(profile, event.get("id"))
        level_points = data.get("level_points") or {}
        for level in event.get("levels") or []:
            key = level_key(event["id"], level["id"])
            result[key] = int(level_points.get(level["id"]) or 0)
    return result


def apply_log_to_profile(profile: dict, log: dict, shared: dict) -> None:
    """把紀錄累計寫回設定檔的目前積分／已打關卡數／已消耗體力。"""
    totals = log_totals(log.get("entries"), level_table(shared),
                        points_map(shared, profile))
    profile["current_stamina_spent"] = (
        int(log.get("baseline_stamina") or 0) + totals["stamina"])
    for event in events_of(shared):
        event_id = event.get("id")
        section = (log.get("events") or {}).get(event_id) or {}
        data = profile_event(profile, event_id)
        data["current_points"] = (int(section.get("baseline_points") or 0)
                                  + totals["points_by_event"].get(event_id, 0))
        data["current_clears"] = (int(section.get("baseline_clears") or 0)
                                  + totals["clears_by_event"].get(event_id, 0))
        for kind in ("stamina", "enemies", "drops"):
            data[f"baseline_{kind}"] = int(section.get(f"baseline_{kind}") or 0)
        data["baseline_levels"] = {
            level_id: int(count) for level_id, count
            in (section.get("baseline_levels") or {}).items() if int(count or 0) > 0}


def has_entries(log: dict) -> bool:
    return bool(log.get("entries"))


# --------------------------------------------------------------------------
# 備份
# --------------------------------------------------------------------------

def _backup_data_dir(tag: str) -> str:
    """搬資料之前先把整個資料目錄複製一份，出事還救得回來。"""
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    backup = APP_DIR / f"_backup_{tag}_{stamp}"
    backup.mkdir(parents=True, exist_ok=True)
    for name in ("shared_config.json", "app_state.json"):
        src = APP_DIR / name
        if src.exists():
            shutil.copy(src, backup / name)
    for folder in ("profiles", "logs"):
        src = APP_DIR / folder
        if src.exists():
            shutil.copytree(src, backup / folder, dirs_exist_ok=True)
    return backup.name
