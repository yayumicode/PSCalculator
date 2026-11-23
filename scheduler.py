# -*- coding: utf-8 -*-
"""排程計算引擎。

依遊戲的體力與任務規則，用整數規劃（ILP, pulp）求解
「達成所有活動的任務所需的最省體力排程」，而非用比例手算估計。

同一時間可能有多檔活動並行（當期／復刻／音像）。它們**共用同一個體力池**，
但各自有關卡與積分：耗體類的任務跨活動一起累計，積分與關卡次數各算各的。

體力來源分成四種各自獨立追蹤：
  1. 自然回復池 —— 會受體力上限限制，超過上限的回復直接浪費
  2. 特殊日一次性資源 —— 發放後可留到之後使用，不受上限限制
  3. 限時體力（含任務獎勵）—— 依到期日分池，到期沒用完就消失
  4. 額外補充（買體力）—— 目標是把這個數字壓到最小
"""

from __future__ import annotations

import math
import os
from fractions import Fraction
import time
import unicodedata
from datetime import date, datetime, time as dtime, timedelta

TICKS_PER_DAY = 288  # 24 * 60 / 5，每天的回復次數
WEEKDAY_NAMES = ["一", "二", "三", "四", "五", "六", "日"]


# ---- PuLP 3.x／4.x 相容 ----------------------------------------------------
# PuLP 4.0 拿掉了這個程式原本用的幾種寫法：PULP_CBC_CMD（CBC 改由
# `pip install "pulp[cbc]"` 另外裝、用 COIN_CMD）、直接 LpVariable(...) 建變數、
# 把 prob.constraints 當 dict 刪除、pulp.LpStatus 與 prob.status。
# 所有求解相關的呼叫都經過下面這幾個函式，3.3.x 與 4.x 都能跑。

PULP_INSTALL_HINT = '找不到 pulp 套件，請先執行：pip install "pulp[cbc]"'
CBC_INSTALL_HINT = ('找不到 CBC 求解器（PuLP 4.x 起要另外裝），'
                    '請先執行：pip install "pulp[cbc]"')


def solver_available() -> bool:
    """pulp 與 CBC 都裝好了沒有（PSCalculator.bat 啟動前也用這個檢查）。"""
    try:
        import pulp
    except ImportError:
        return False
    if getattr(pulp, "PULP_CBC_CMD", None) is not None:
        return True             # 3.x 內建 CBC
    try:
        return bool(pulp.COIN_CMD(msg=0).available())
    except Exception:           # pragma: no cover - 各平台找不到執行檔的方式不同
        return False


def _cbc_solver(pulp, **options):
    """CBC 求解器。4.x 只有 COIN_CMD；3.x 優先用內建 CBC（PULP_CBC_CMD）。"""
    legacy = getattr(pulp, "PULP_CBC_CMD", None)
    if legacy is not None:
        import warnings
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", DeprecationWarning)
            return legacy(**options)
    return pulp.COIN_CMD(**options)


def _new_var(prob, name, lowBound=None, upBound=None, cat="Continuous"):
    """建立掛在 prob 上的變數（3.3 起就有 add_variable；4.x 只剩這個寫法）。"""
    return prob.add_variable(name, lowBound, upBound, cat)


def _solve(pulp, prob, **options) -> str:
    """求解，回傳 3.x 那種狀態字串：Optimal／Not Solved／Infeasible／Unbounded。

    3.x 在 CBC 因時間上限停下、手上有一組可行解時也回報 Optimal，沒有解則是
    Not Solved；呼叫端照這個語意判斷（是否收斂另外看實際耗時），4.x 照樣對應。
    """
    if options.get("keepFiles"):
        # 留著暫存檔時，新版 CBC 會把解「接在」上一次的解檔後面，PuLP 4.x 讀到的
        # 是檔案開頭那份舊解。先清掉，每次都從空檔開始（warmStart 的起點檔是
        # 求解當下才寫的，不受影響）。
        _remove_solver_files()
    result = prob.solve(_cbc_solver(pulp, **options))
    legacy_names = getattr(pulp, "LpStatus", None)
    if legacy_names is not None:
        return legacy_names[result]
    status = _status_name(result)
    if status == "Optimal" and not _solution_feasible(prob):
        # PuLP 4.x 搭的 CBC（cbcbox）偶爾在前處理還原時出錯，交回一組違反限制式
        # 的解（日誌寫 "Postprocessed model is infeasible - possible tolerance
        # issue - try without preprocessing"）。照它的建議關掉前處理重算一次。
        retry = dict(options)
        retry["options"] = list(options.get("options") or []) + ["preprocess off"]
        if retry.get("keepFiles"):
            _remove_solver_files()
        result = prob.solve(_cbc_solver(pulp, **retry))
        status = _status_name(result)
        if status == "Optimal" and not _solution_feasible(prob):
            status = "Not Solved"
    return status


def _status_name(result) -> str:
    """PuLP 4.x 的求解結果 → 3.x 的狀態字串（見 _solve）。"""
    status = getattr(result.status, "name", str(result.status))
    if status == "Infeasible":
        return "Infeasible"
    if status == "Unbounded":
        return "Unbounded"
    if status in ("Optimal", "GapLimit"):
        return "Optimal"
    return "Optimal" if getattr(result, "has_solution", False) else "Not Solved"


def _solution_feasible(prob, tolerance: float = 1e-3) -> bool:
    """求解器交回來的解是不是真的滿足每一道限制式與變數上下界。"""
    for constraint in prob.constraints():
        value = constraint.value()
        if value is None:
            continue
        slack = tolerance * max(1.0, abs(constraint.constant))
        if constraint.sense < 0 and value > slack:
            return False
        if constraint.sense > 0 and value < -slack:
            return False
        if constraint.sense == 0 and abs(value) > slack:
            return False
    for var in prob.variables():
        x = var.varValue
        if x is None:
            continue
        if var.lowBound is not None and x < var.lowBound - tolerance:
            return False
        if var.upBound is not None and x > var.upBound + tolerance:
            return False
    return True


_FREE_ROW_RHS = 1e30      # CBC 把這麼大的右邊當成沒有限制


def _drop_constraint(prob, name: str, missing_ok: bool = False) -> None:
    """拿掉一道具名的限制式。

    3.x 直接從 dict 刪掉；4.x 沒有刪除的寫法，改成把它變成 0 >= 0 並改名，
    原本的名稱空出來，之後可以再用同一個名稱加回去。
    """
    constraint = prob.get_constraint_by_name(name)
    if constraint is None:
        if missing_ok:
            return
        raise KeyError(name)
    mapping = prob.constraints
    if hasattr(mapping, "pop"):          # 3.x：還是 dict 的寫法
        import warnings
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", DeprecationWarning)
            mapping.pop(name, None)
        return
    # 不把係數歸零（變成空列）：右邊放到「無限大」，這一列就永遠成立
    sense = constraint.sense
    if sense < 0:
        constraint.changeRHS(_FREE_ROW_RHS)
    elif sense > 0:
        constraint.changeRHS(-_FREE_ROW_RHS)
    else:
        raise ValueError(f"等式限制式不能拿掉：{name}")
    counter = prob.__dict__.setdefault("_dropped_count", [0])
    counter[0] += 1
    constraint.name = f"{name}__dropped{counter[0]}"

# 求解分成兩階段（字典序最佳化），不用單一加權目標函數。
#
# 不把「補充體力」乘上 10000 塞進同一條目標函數：跟 0.0001 的微調係數混在一起，
# 係數跨越 10^8 個量級，對分支定界法是災難——遇到吃緊的題目（體力上限低、
# 目標積分接近極限）時，求解器會為了證明最佳解而無止盡地跑下去。
#
#   第一階段：只問「最少要額外補充多少體力」，係數全是 1.0，很好解
#   第二階段：固定補充量，再求最省耗體，順便處理顯示用的細節
#
# 第二階段的微調係數都遠小於 1（耗體係數），只用來打破平手，不影響「打幾關」。
#
# 取用順序：先動用自然回復，限時資源留到最後。理由是兩種「用不完」的後果不同：
#   * 自然回復頂到體力上限而溢出 → 永久損失，救不回來
#   * 限時資源到期沒用完 → 還能拿去打不計分的關卡，不是全損
# 所以把體力條先花掉、空出回復空間，才是損失最小的順序。
# （反過來「優先消耗限時資源」的話，體力條會整天卡在上限一直溢出。）
WASTE_PENALTY = 0.05      # 自然回復溢出＝永久損失，最該避免
PREFER_NATURAL = 0.01     # 同樣付得起時，寧可動用自然回復而不是限時資源
LAST_WEEK_PENALTY = 0.02  # 最後一週的限時體力盡量留著不動

# 到期日在活動結束當天或之後的限時體力＝可以留到下一檔活動用，等於沒有損失，
# 所以要優先燒掉「這檔內就會過期」的池子，把它留著。
#
# 係數必須夠大：目標函數的主項是總耗體（約 10^4），而 GAP_TOLERANCE 是相對
# 誤差，0.5% 就有數十個單位的容忍空間。係數如果跟 PREFER_NATURAL 一樣是
# 0.01，那「少燒 800 點可留存體力」只值 8 個單位，整個被容差吃掉，求解器根本
# 不會理它（實測：基礎排程燒掉好幾百點可留存的，卻放著上千點反正要過期的沒用）。
SAVE_FOR_NEXT = 0.3

# 同樣要花掉的體力，儘量花在**計分**的關卡上，而且儘量多拿分。
#
# 第二階段的目標是最省耗體，裡面沒有積分項——積分只是一條「≥ 目標」的約束。
# 所以當某一天被逼著花掉 N 點（例如音像活動的「當日至少 300」），怎麼花對它
# 完全等價，它就隨手挑一個。這個係數同時修掉兩層等價：
#
#   1. 不計分的每一點體力多算一點成本——否則那 300 點拿去打常駐關卡，
#      一分都沒換到。
#   2. 每一分積分折抵一點成本——否則同樣 300 點、同樣 10 關，850 分跟
#      865 分的組合它也不在乎。
#
# 兩層是同一個概念（平手時的偏好），共用一個係數，不必分開調。上下界：
#
#   * 夠大——要壓得過 GAP_TOLERANCE 的容忍空間（主項約 10^4，0.5% 就是數十個
#     單位），不然求解器根本不會理它。0.2 × 300 點 ＝ 60，壓得過。
#   * 夠小——不能大到為了搶分而多花體力。每一點體力的主項成本是 1.0，而 CP
#     最高的關卡是 3 分／體力，0.2 × 3 ＝ 0.6 < 1.0，所以多花一點體力永遠
#     划不來；把一點體力從不計分挪到計分則是淨賺 0.2。
#   * 也不會為了省這 0.2 而改用更貴的關卡：10 點的常駐關卡是 10×1.2 ＝ 12，
#     仍然比 20 點的活動關卡便宜。真正的耗體差距壓得過這個係數。
#
# > 已知副作用：並行兩檔都有積分目標、加成又不同的活動時，兩邊都花得掉的體力
# > 會偏向 CP 高的那一檔。兩檔的目標各自獨立，服務過頭的那一檔沒有額外好處。
PREFER_SCORING = 0.2

# 活動的「積分上限」＝獎勵表封頂，超過再打就什麼都拿不到。作法是對那檔活動的積分
# 加一條上界，再給一個罰得很重的溢出變數（見 build_and_solve 的 cap_over）。
#
# 為什麼不是「超過的積分在目標函數裡價值歸零」那種軟上限：那樣寫的話，求解器會
# 發現「用 CP 低的關卡把積分攤平」比較划算——反正封頂前的積分照樣折抵成本，而
# idle_spend 又在罰不計分關卡。實測某檔復刻排出 **關卡2 × 兩百多次**（多花好幾百
# 體力才湊到封頂），關數暴增、常駐關卡反而打得少，完全不是使用者要的。
# 直接壓住積分總量就沒有這個縫：求解器只能用最省體力的方式湊到上限，剩下的體力
# 自然流向不計分的關卡。
#
# 係數要夠大：
#   * 壓得過 GAP_TOLERANCE（主項約 10^4、0.5% 就是數十個單位）——超出 10 分
#     要值 100 個單位才不會被容差吃掉，所以不能用 0.x 的量級
#   * 壓得過「多拿 1 分」的最大好處：折抵成本 0.2 ＋ 省下的 idle 罰則約 0.07
# 真的被硬條件逼著超過時（解鎖鏈、積分任務目標高於上限）它只是變貴，不會無解。
CAP_OVERSHOOT_PENALTY = 10.0

# 「盡量提早」：活動設了日期時，那天之前拿到的每一分積分值多少。
#
# 體力存不住（上限、限時體力會過期），所以下一檔活動開始之前的體力拿去換這檔
# 的積分是零成本的，之後的體力卻要跟新活動搶。提早階段鎖住總耗體與補充量，
# 只在「一樣省」的排法裡挑日期前積分最多的那個——目標是第二階段那條式子減掉
# 這個係數 × 日期前的積分。
#
# 係數只要壓得過第二階段那些平手用的小係數就好：把一點體力從後面挪到前面，
# 最多多付 WASTE_PENALTY ＋ PREFER_NATURAL ＋ LAST_WEEK_PENALTY < 0.1，而它換到
# 的積分至少 2 分（CP 最低的關卡），所以 1.0 綽綽有餘。總耗體有鎖，不會因此多打。
EARLY_WEIGHT = 1.0

# 整理階段（`shared["schedule_prefs"]`，見 build_and_solve 的 run_tidy）：算出來的
# 排程每天都要對照「今天打哪幾關、各幾次」，同樣省的排法裡要挑最好照著打的。
#
#   * 平日減量（light_weekdays）——週一到週五，活動與常駐關卡盡量壓在當天每日
#     任務要求的關數，多的挪到星期日。限時體力本來就是星期日到期，集中在那天不會多浪費。
#     星期六多出來的也會盡量再挪到隔天星期日（挪不動才留在星期六）。
#   * 打法簡化（simplify_days）——每天打的關卡種類越少越好。
#
# 兩個都是鎖住之後才挑（總耗體、補充、浪費、可留存體力、日期前的積分……全部
# 不准變差），不是加小係數——理由同偏好階段：小係數會被 gap 吞掉。
#
# 星期六只給一個很小的權重（不算進「平日超過幾關」）；整理時另外把星期六多出來的
# 關卡往後挪到星期日（見 move_to_weekend），鎖住的耗體、補充、浪費都不會變差。
# 只靠這個權重在平手時讓星期日先收的話，CBC 版本不同就會一個排星期六、一個排星期日。
LIGHT_WEEKDAYS = (0, 1, 2, 3, 4)
LIGHT_SATURDAY_WEIGHT = 0.1

# 分組解鎖型活動（蜜意蒐羅、祕寶探尋）：關卡分成好幾組，組內照耗體順序解鎖，
# 每一關至少要打一次。放在 scheduler 而不是 storage，是因為 storage 會 import
# scheduler（反過來會循環）；storage 直接沿用這一份。
#
# 這張表同時決定：
#   * 「套用類型預設」要產生幾組、每組哪幾種耗體、每關幾個敵人（app）
#   * 這類活動的「每關至少打一次」在資源不夠時可以被放寬（這裡）
# group_names（可省略）＝第 1 組起每組的名稱，關卡叫「八雲·20」；沒給就叫「第1組·20」。
# max_total（可省略）＝每關整檔活動最多打幾次；None＝沒有上限。
GROUPED_EVENT_PRESETS = {
    "collect": {"groups": 11, "costs": (20, 30, 40), "enemies": 8, "max_total": 1,
                "group_names": ("八雲", "艾德蒙特", "奧利文", "崑西", "玖夜", "可爾",
                                "布儡", "啖天", "歛", "艾斯特", "墨菲")},
    "treasure": {"groups": 5, "costs": (20, 30, 40), "enemies": 8, "max_total": 1,
                 "group_names": ("爪系列", "木材系列", "露水系列", "果實系列", "晶簇系列")},
}

# 每階段的求解時間上限（秒）。超時就採用當下找到的最佳可行解，並提示使用者
# 這個答案不保證是最省的——總比讓程式看起來當掉好。
DEFAULT_TIME_LIMIT = 30

# 某個階段時間到了還沒找到任何可行解時，延長成幾倍再算一次。
# 「超時」不等於「無解」——條件吃緊的模型只是需要比較久才找得到第一組解。
TIMEOUT_RETRY_FACTOR = 4

# 第一階段（要補充多少）時間到了、答案又不是 0 時，接著那組解再算這麼多倍的時間。
# 補充量是後面所有階段的鎖，第一階段沒算完的誤差會一路帶到最後（實測
# 30 秒時還要補一百多點、再給時間降到個位數）；不用補充或算得完的情況完全不受影響。
BUY_RETRY_FACTOR = 4

# 允許的最佳性誤差。分支定界法真正花時間的是「證明」最後那零點幾個百分比，
# 而不是找到好解。容許 0.5% 的誤差可以讓求解快非常多，對排程來說毫無差別
# （7000 點體力的 0.5% 是 35 點，遠小於單一關卡的消耗）。
GAP_TOLERANCE = 0.005


class PlanError(Exception):
    """參數不足或不合理，無法計算。"""


# --------------------------------------------------------------------------
# 關卡鍵：跨活動一律用 "<event_id>/<level_id>" 指稱一個關卡
# --------------------------------------------------------------------------

def level_key(event_id: str, level_id: str) -> str:
    return f"{event_id}/{level_id}"


def split_level_key(key: str) -> tuple[str, str]:
    """回傳 (event_id, level_id)；沒有前綴的舊鍵回傳 ("", 原字串)。"""
    text = str(key or "")
    if "/" not in text:
        return "", text
    event_id, level_id = text.split("/", 1)
    return event_id, level_id


# 關卡優先序裡的限期關卡不指某一檔，而是指「這個名稱的限期關卡、現在開著的
# 那一檔」：`limited:忘卻/lv1`。忘卻一檔一檔輪替，每檔 id 都不同，用檔次的鍵
# 的話每次「接下一期」都得重排一次優先序、每個帳號各做一次。
# 「接下一期」會沿用名稱與關卡 id，所以正常換檔不會斷；改名才會斷。
LIMITED_SERIES_PREFIX = "limited:"


def limited_series_key(event_name: str, level_id: str) -> str:
    return f"{LIMITED_SERIES_PREFIX}{event_name}/{level_id}"


def split_limited_series_key(key: str) -> tuple[str, str] | None:
    """系列鍵 → (活動名稱, 關卡 id)；不是系列鍵回 None。"""
    text = str(key or "")
    if not text.startswith(LIMITED_SERIES_PREFIX) or "/" not in text:
        return None
    name, level_id = text[len(LIMITED_SERIES_PREFIX):].rsplit("/", 1)
    return name, level_id


# --------------------------------------------------------------------------
# 日期工具
# --------------------------------------------------------------------------

def parse_clock(text: str | None, default: str) -> dtime:
    """把 "05:00" 這種字串轉成 time；格式不對就用預設值。"""
    try:
        hour, minute = str(text or default).strip().split(":")
        return dtime(int(hour) % 24, int(minute) % 60)
    except (ValueError, AttributeError):
        hour, minute = default.split(":")
        return dtime(int(hour), int(minute))


def minutes_of(clock: dtime) -> int:
    return clock.hour * 60 + clock.minute


def task_day_of(moment: datetime, reset: dtime) -> date:
    """這個時刻屬於哪個「任務日」。重置時刻之前算前一天。"""
    if moment.time() < reset:
        return moment.date() - timedelta(days=1)
    return moment.date()


def parse_date(text: str | None, field: str) -> date:
    if not text:
        raise PlanError(f"尚未設定{field}")
    try:
        return datetime.strptime(text.strip(), "%Y-%m-%d").date()
    except ValueError:
        raise PlanError(f"{field}格式錯誤（需為 YYYY-MM-DD）：{text}")


def week_index_of(day: date, event_start: date) -> int:
    """活動第幾週，從 1 起算。

    週的邊界是星期一到星期日；「包含活動起始日的那一週就是第1週」，
    就算活動不是星期一開始、第1週只有殘週幾天也一樣算第1週。
    """
    monday_of_day = day - timedelta(days=day.weekday())
    monday_of_start = event_start - timedelta(days=event_start.weekday())
    return (monday_of_day - monday_of_start).days // 7 + 1



def _bonus_rate(bonus_percent) -> Fraction:
    """加成百分比換成倍率。

    **一定要走 Fraction(str(...))，不能用浮點數。** `Fraction(20.5)` 拿到的是
    浮點數的近似分數，`Fraction("20.5")` 才是精確的 41/2。
    用 `b * (1 + p/100)` 浮點數算的話，基礎 1~200 × 加成 1~100% 裡有 38 組會多進一位
    ——例如基礎 50、加成 10%：50×1.1 在浮點數裡是 55.00000000000001，
    ceil 之後變成 56，正確答案是 55。
    """
    return 1 + Fraction(str(bonus_percent or 0)) / 100


def points_with_bonus(base_points, bonus_percent) -> int | None:
    """基礎積分套上活動加成 ——「基礎積分 × (1 + 加成%)」，**無條件進位**。

    公式與 nuCarnival 活動計算機（linecross.github.io）的 `battleScore` 一致。
    拿實際數字驗過，例如：
    基礎 [20,30,48,68,90] 套 +70% ＝ [34,51,82,116,153]、套 +48% ＝
    [30,45,72,101,134]，十個全中。四捨五入會錯——90×1.48 = 133.2，
    四捨五入是 133，實際是 134。

    沒填基礎積分就回傳 None，代表「這關的積分由使用者自己填」。
    """
    if not base_points:
        return None
    return math.ceil(Fraction(int(base_points)) * _bonus_rate(bonus_percent))


def base_points_for(points, bonus_percent) -> int | None:
    """反推：積分是多少的基礎積分套上加成來的。

    `ceil(b × r) == t` 等價於 `b ∈ ((t−1)/r, t/r]`，區間寬度 1/r < 1，
    所以整數解**最多一個**——不是多解，也可能無解（代表那個積分不是這個加成
    從整數基礎積分算出來的，多半是手填的）。無解就回 None，不要亂猜。
    """
    if not points:
        return None
    rate = _bonus_rate(bonus_percent)
    candidate = math.floor(Fraction(int(points)) / rate)
    if candidate < 1:
        return None
    return candidate if points_with_bonus(candidate, bonus_percent) == int(points) else None


# --------------------------------------------------------------------------
# 活動目標分析：不排日期，只回答「這檔活動的任務目標，最少要花多少體力、拿多少分」
# --------------------------------------------------------------------------
#
# 排程（compute_plan）求的是「怎麼在體力池裡排最省」，遇到目標互相矛盾——例如
# 道具目標 2008 要的體力（每 50 體力最多 10 個道具 → 至少約 10040）遠高於體力
# 目標 7000——只會在缺口裡出現一個數字，看不出是哪個任務在主導。這裡把一檔活動
# 的「活動週期」任務單獨拿出來算，讓使用者在排程之前就看得出來。
#
# 範圍：只看這一檔活動自己的關卡與 cycle == "event" 的任務；體力與敵人任務在排程
# 裡是跨活動累計的，這裡只算這一檔的關卡。已經打過的紀錄不扣（只扣 baseline 與
# 設定檔裡的 current_points / current_clears），所以結果是「從頭打」的需求量。

ANALYSIS_METRICS = ("stamina", "points", "drops", "enemies", "clears")
ANALYSIS_METRIC_LABELS = {"stamina": "消耗體力", "points": "積分", "drops": "道具",
                          "enemies": "敵人", "clears": "通關次數"}


def _task_weights(task: dict, levels: list[dict]) -> list[int]:
    """一個任務每打一次各關卡能貢獻多少（跟 compute_plan 的 scope_of 同一套規則）。"""
    metric = task.get("metric")
    scope = set(task.get("scope") or [])
    weights = []
    for lv in levels:
        if scope and lv["key"] not in scope:
            weights.append(0)
        elif metric == "stamina":
            weights.append(lv["cost"])
        elif metric == "points":
            weights.append(lv["points"] if lv["scoring"] else 0)
        elif metric == "drops":
            weights.append(lv["drops"])
        elif metric == "enemies":
            weights.append(lv["enemies"])
        else:  # clears
            weights.append(1 if lv["counts_clears"] else 0)
    return weights


def _solve_counts(pulp, levels, lbs, ubs, rows, objective, maximize=False,
                  stamina_max=None):
    """整數規劃：各關卡打幾次。無解（或求不出）回傳 None。

    rows＝[(每關貢獻, 至少要多少)]；objective＝每關的目標函數係數。
    """
    prob = pulp.LpProblem("event_targets",
                          pulp.LpMaximize if maximize else pulp.LpMinimize)
    plays = [_new_var(prob, f"n{i}", lowBound=lbs[i], upBound=ubs[i], cat="Integer")
             for i in range(len(levels))]
    prob += pulp.lpSum(objective[i] * plays[i] for i in range(len(levels)))
    for weights, need in rows:
        prob += pulp.lpSum(weights[i] * plays[i] for i in range(len(levels))) >= need
    if stamina_max is not None:
        prob += pulp.lpSum(levels[i]["cost"] * plays[i]
                           for i in range(len(levels))) <= stamina_max
    if _solve(pulp, prob, msg=0) != "Optimal":
        return None
    return [int(round(v.value() or 0)) for v in plays]


def _plan_totals(levels: list[dict], counts: list[int]) -> dict:
    return {
        "counts": {lv["label"]: n for lv, n in zip(levels, counts) if n},
        "stamina": sum(lv["cost"] * n for lv, n in zip(levels, counts)),
        "points": sum(lv["points"] * n for lv, n in zip(levels, counts)),
        "drops": sum(lv["drops"] * n for lv, n in zip(levels, counts)),
        "enemies": sum(lv["enemies"] * n for lv, n in zip(levels, counts)),
        "clears": sum(n for lv, n in zip(levels, counts) if lv["counts_clears"]),
    }


def analyze_event_targets(shared: dict, profile: dict, event_id: str,
                          stamina_budget: int | None = None) -> dict:
    """分析一檔活動的任務目標：最少要多少體力、那時積分的最少／最多是多少。

    - 每個任務單獨達標最少要多少體力 → 看出誰是瓶頸、誰會「順便達成」
    - 全部任務同時達標的最少體力，以及在那個體力下積分的範圍與各關次數
    - 給了 `stamina_budget` 就改問「這個體力預算夠不夠、積分範圍」

    關卡的硬規則照排程器處理：勾了「解鎖」（unlock_first）的每關至少打一次、
    「一定要打滿」（must_finish）的限次關卡要打滿。沒有填積分的計分關卡當 0 分。
    """
    try:
        import pulp
    except ImportError:
        raise PlanError(PULP_INSTALL_HINT)
    if not solver_available():
        raise PlanError(CBC_INSTALL_HINT)
    event = next((ev for ev in (shared or {}).get("events") or []
                  if ev.get("id") == event_id), None)
    if event is None:
        raise PlanError(f"找不到活動 {event_id}")
    data = (profile.get("events") or {}).get(event_id) or {}
    level_points = data.get("level_points") or {}
    level_enabled = data.get("level_enabled") or {}
    level_caps = data.get("level_max_total") or {}
    warnings: list[str] = []

    levels: list[dict] = []
    for lv in event.get("levels") or []:
        if not level_enabled.get(lv["id"], True):
            continue
        max_total = lv.get("max_total")
        if level_caps.get(lv["id"]) is not None:
            max_total = int(level_caps[lv["id"]])
        scoring = bool(lv.get("scoring"))
        points = int(level_points.get(lv["id"]) or 0) if scoring else 0
        if scoring and not points:
            warnings.append(f"「{lv['name']}」是計分關卡但沒有填積分，這裡當 0 分算")
        cost = int(lv.get("stamina_cost") or 0)
        if cost <= 0:
            raise PlanError(f"「{lv['name']}」的消耗體力必須大於 0")
        levels.append({
            "key": level_key(event_id, lv["id"]), "label": lv["name"],
            "cost": cost, "points": points, "scoring": scoring,
            "drops": int(lv.get("drops") or 0),
            "enemies": int(lv.get("enemies") or 0),
            "counts_clears": bool(lv.get("counts_clears", scoring) or scoring),
            "max_total": None if max_total is None else int(max_total),
            "must_finish": bool(lv.get("must_finish")),
            "unlock_first": bool(lv.get("unlock_first")),
        })
    if not levels:
        raise PlanError("這檔活動沒有可以打的關卡（沒填，或都被設成「這次不算」）")

    # 每關次數的下界／上界
    lbs, ubs = [], []
    for lv in levels:
        lb = 1 if lv["unlock_first"] else 0
        if lv["must_finish"] and lv["max_total"]:
            lb = max(lb, lv["max_total"])
        ub = lv["max_total"]
        if ub is not None and ub < lb:
            ub = lb
        lbs.append(lb)
        ubs.append(ub)

    task_states = profile.get("task_state") or {}
    tasks: list[dict] = []
    rows = []
    for task in event.get("tasks") or []:
        key = f"{event_id}/{task.get('id')}"
        state = task_states.get(key) or {}
        metric = task.get("metric")
        if task.get("cycle") != "event" or metric not in ANALYSIS_METRICS:
            continue
        if state.get("enabled") is False or not task.get("enforce", True):
            continue
        amount = state.get("amount_override")
        amount = int(task.get("amount") or 0) if amount is None else int(amount)
        if amount <= 0:
            continue
        if not task.get("scope") and metric in EVENT_COUNTED_METRICS:
            done = event_baseline(data, metric)
        else:
            done = int(state.get("baseline") or 0)
        if metric == "points" and not task.get("scope"):
            done += int(data.get("current_points") or 0)
        elif metric == "clears" and not task.get("scope"):
            done += int(data.get("current_clears") or 0)
        need = max(0, amount - done)
        weights = _task_weights(task, levels)
        label = f"{task.get('name') or '活動任務'}（{ANALYSIS_METRIC_LABELS[metric]}）"
        info = {"label": label, "metric": metric, "amount": amount,
                "need": need, "min_stamina": None, "role": ""}
        tasks.append(info)
        rows.append((weights, need))

    result = {"event_id": event_id, "event_name": event_label(event),
              "levels": levels, "tasks": tasks, "warnings": warnings,
              "points_cap": event.get("points_cap"), "feasible": False,
              "stamina_budget": stamina_budget,
              "min_stamina": None, "min_points": None, "max_points": None}
    if not tasks:
        warnings.append("這檔活動沒有可分析的任務（活動週期、且是體力／積分／道具／敵人／通關次數）")
        return result

    costs = [lv["cost"] for lv in levels]

    # 單獨達標：每個任務各自最少要多少體力
    for info, row in zip(tasks, rows):
        counts = _solve_counts(pulp, levels, lbs, ubs, [row], costs)
        info["min_stamina"] = (None if counts is None
                               else _plan_totals(levels, counts)["stamina"])
        if counts is None:
            warnings.append(f"「{info['label']}」目標 {info['amount']:,} 打不到"
                            "（關卡次數上限或可貢獻的關卡不夠）")

    base = _solve_counts(pulp, levels, lbs, ubs, rows, costs)
    if base is None:
        warnings.append("所有任務同時達標是不可能的（關卡次數上限不夠）")
        return result
    best = _plan_totals(levels, base)["stamina"]
    result["min_stamina"] = best
    budget = best if stamina_budget is None else stamina_budget
    result["feasible"] = budget >= best
    if not result["feasible"]:
        warnings.append(f"體力預算 {budget:,} 不夠，全部任務同時達標至少要 {best:,}")
        return result

    points = [lv["points"] for lv in levels]
    for slot, maximize in (("min_points", False), ("max_points", True)):
        counts = _solve_counts(pulp, levels, lbs, ubs, rows, points,
                               maximize=maximize, stamina_max=budget)
        result[slot] = _plan_totals(levels, counts) if counts else None

    # 角色：誰是瓶頸、誰會順便達成
    for info in tasks:
        m = info["min_stamina"]
        if m is None:
            info["role"] = "打不到"
        elif m >= best:
            info["role"] = "瓶頸"
        elif info["metric"] == "stamina":
            info["role"] = "自動達成"
            warnings.append(
                f"體力任務 {info['amount']:,} 低於其他目標需要的 {best:,}，"
                "不用特別為它多打——其他任務打完就達成了")
        else:
            info["role"] = "順便達成"
    cap = event.get("points_cap")
    if cap and result["min_points"] and result["min_points"]["points"] > cap:
        warnings.append(f"達標最少要 {result['min_points']['points']:,} 分，"
                        f"超過積分上限 {cap:,}")
    for info in tasks:
        if info["metric"] == "points" and cap and info["amount"] > cap:
            warnings.append(f"積分任務 {info['amount']:,} 高於積分上限 {cap:,}，永遠拿不到")
    return result


def format_event_analysis(result: dict) -> str:
    """把 analyze_event_targets 的結果印成中文報表。"""
    lines = [f"【{result['event_name']}】活動目標分析", ""]
    lines.append("任務（單獨達標最少體力）")
    for info in result["tasks"]:
        need = (f"{info['need']:,}" if info["need"] == info["amount"]
                else f"{info['amount']:,}（還差 {info['need']:,}）")
        m = "—" if info["min_stamina"] is None else f"{info['min_stamina']:,}"
        lines.append(f"  · {info['label']} 目標 {need}　→ 至少 {m} 體力"
                     + (f"　［{info['role']}］" if info["role"] else ""))
    if result["min_stamina"] is not None:
        lines += ["", f"全部任務同時達標：至少 {result['min_stamina']:,} 體力"]
        if result["stamina_budget"] is not None:
            lines.append(f"體力預算 {result['stamina_budget']:,}："
                         + ("夠" if result["feasible"] else "不夠"))
    low, high = result["min_points"], result["max_points"]
    # 最少體力下常常只有一種打法（例如道具是瓶頸、只能幾乎全打關卡5），
    # 這時分兩段印出一模一樣的內容沒有意義，合併成一段
    unique = bool(low and high and low["points"] == high["points"]
                  and low["counts"] == high["counts"])
    if unique:
        sections = [("打法（唯一，這個體力量下沒有其他選擇）", low)]
    else:
        sections = [("積分最少的打法", low), ("積分最多的打法", high)]
    for title, plan in sections:
        if not plan:
            continue
        counts = "、".join(f"{name}×{n}" for name, n in plan["counts"].items())
        lines += ["", f"{title}（{plan['stamina']:,} 體力）",
                  f"  積分 {plan['points']:,}　道具 {plan['drops']:,}"
                  f"　敵人 {plan['enemies']:,}　通關 {plan['clears']:,}",
                  f"  {counts}"]
    if result["points_cap"]:
        lines += ["", f"積分上限：{result['points_cap']:,}"]
    if result["warnings"]:
        lines += ["", "注意"] + [f"  ! {text}" for text in result["warnings"]]
    lines += ["", "※ 只算這一檔活動、從頭打的需求量：不扣已打紀錄，也不排日期與體力池。"]
    return "\n".join(lines)


# --------------------------------------------------------------------------
# 活動
# --------------------------------------------------------------------------

# 活動任務在預設範圍時，起始值用「活動設定」那檔活動的起始值（storage.EVENT_BASELINE_KINDS）。
# 積分、關卡數已經併進 current_points／current_clears，這裡是另外三種。
EVENT_COUNTED_METRICS = ("stamina", "enemies", "drops")


def event_baseline(data: dict | None, metric: str) -> int:
    """這個帳號在這檔活動開始記錄之前就有的耗體／敵人／道具（沒填＝0）。"""
    return int((data or {}).get(f"baseline_{metric}") or 0)


def baseline_level_counts(profile_events: dict | None) -> dict[str, int]:
    """開始記錄之前就打過的次數：{關卡鍵: 次數}（「補登開始前的進度」填的）。

    跟每日紀錄的次數一樣算進「已經打了幾次」：總次數上限、一定要打滿、
    開場先打一次、限期關卡這期的上限都扣掉它。
    """
    out: dict[str, int] = {}
    for event_id, data in (profile_events or {}).items():
        for level_id, count in ((data or {}).get("baseline_levels") or {}).items():
            try:
                count = max(0, int(count or 0))
            except (TypeError, ValueError):
                continue
            if count:
                out[level_key(event_id, level_id)] = count
    return out


def period_done_before(state: dict | None, win_first: date) -> int:
    """固定任務在開始記錄之前，這一期就已經做掉的量。

    只對填的那一期有效（`period_done.from` 是那一期的第一天）：
    每週任務填了「這週已耗 700」，下週一重置後就不再加。
    """
    period = (state or {}).get("period_done") or {}
    if period.get("from") != win_first.isoformat():
        return 0
    try:
        return max(0, int(period.get("amount") or 0))
    except (TypeError, ValueError):
        return 0


def is_standing(event: dict) -> bool:
    """常駐關卡那一組：不隸屬任何活動、永遠打得到。"""
    return bool((event or {}).get("standing"))


def is_limited(event: dict) -> bool:
    """限期關卡（檢定、忘卻……）：有起訖日與每檔上限，但不是活動。

    它的起訖日只管「這一檔的關卡什麼時候打得到」，不決定排程範圍、
    不當「第 N 天」與體力來源的基準——跟常駐關卡一樣不算「真正的活動」。
    """
    return (event or {}).get("type") == "limited" and not is_standing(event)


def is_archived(event: dict) -> bool:
    """使用者手動封存的活動：畫面上收起來、排程不排，但紀錄照樣認它的關卡。"""
    return bool((event or {}).get("archived")) and not is_standing(event)


def event_bounds(event: dict) -> tuple[datetime, datetime]:
    """活動的精確起訖時刻。

    起始日下午三點開始、結束日中午十二點結束（可逐活動調整）。
    時間會影響排程：起始時刻之前排不到這檔活動的關卡，結束時刻之後也一樣，
    所以最後一天必須在中午前把該打的打完。

    常駐關卡沒有起訖日——回傳一個涵蓋一切的區間，`build_segments()` 的
    `seg["live"]` 就會每一段都含它，其餘的程式一行都不用改。
    """
    if is_standing(event):
        return datetime.min, datetime.max
    name = event_label(event)
    start = parse_date(event.get("start_date"), f"「{name}」的起始日")
    end = parse_date(event.get("end_date"), f"「{name}」的結束日")
    start_dt = datetime.combine(start, parse_clock(event.get("start_time"), "15:00"))
    end_dt = datetime.combine(end, parse_clock(event.get("end_time"), "12:00"))
    if end_dt <= start_dt:
        raise PlanError(f"「{name}」的結束時刻早於起始時刻")
    return start_dt, end_dt


def event_label(event: dict) -> str:
    """給人看的活動名稱。限期關卡把期數接在名稱後面（忘卻＋23 → 「忘卻23」）。

    名稱和期數分開存：名稱是系列（關卡優先序靠它跨檔次對上），期數只用來
    分辨是哪一檔。所有顯示都走這裡，才不會有的地方有期數、有的沒有。
    """
    name = event.get("name") or event.get("id") or "活動"
    number = event.get("period_no")
    if number is not None and is_limited(event):
        return f"{name}{number}"
    return name


def level_label(event_text: str, series_name: str | None, level_name: str) -> str:
    """「活動·關卡」。關卡名稱跟活動（系列）名稱一樣時只寫活動那段——
    檢定、忘卻的關卡就叫「檢定」「忘卻」，寫成「檢定27·檢定」只是重複。"""
    if level_name and level_name == series_name:
        return event_text
    return f"{event_text}·{level_name}"


def events_missing_bonus(shared: dict, profile: dict, query_dt: datetime) -> list[str]:
    """還沒結束、有吃加成的當期活動裡，這個帳號「活動加成」是 0 或空白的那幾檔。

    當期活動的加成一定不是 0——漏填的話每關積分只剩基礎分，排程會以為要多打
    很多關、多買很多體力（實際發生過：就這樣多算了上千點）。計算前擋下來。
    起訖日沒填好的不在這裡管，compute_plan 自己會講。
    """
    missing = []
    for event in (shared or {}).get("events") or []:
        if (event.get("type") or "current") != "current" or is_standing(event) \
                or is_archived(event) or event.get("activity_bonus_applies") is False:
            continue
        try:
            _start, end_dt = event_bounds(event)
        except PlanError:
            continue
        if end_dt <= query_dt:
            continue
        data = (profile.get("events") or {}).get(event.get("id")) or {}
        try:
            bonus = float(data.get("activity_bonus") or 0)
        except (TypeError, ValueError):
            bonus = 0
        if bonus <= 0:
            missing.append(event_label(event))
    return missing


def events_missing_points_cap(shared: dict, query_dt: datetime) -> list[str]:
    """還沒結束的當期／復刻活動裡，「積分上限」沒填的那幾檔。

    這兩類一定有積分獎勵表、一定有封頂；沒填的話排程以為分數拿不滿，會為了多拿分
    繼續餵計分關卡。音像、分組型、限期關卡沒有積分上限，不檢查。計算前擋下來。
    """
    missing = []
    for event in (shared or {}).get("events") or []:
        if (event.get("type") or "current") not in ("current", "rerun") \
                or is_standing(event) or is_archived(event):
            continue
        try:
            _start, end_dt = event_bounds(event)
        except PlanError:
            continue
        if end_dt <= query_dt:
            continue
        if event.get("points_cap") is None:
            missing.append(event_label(event))
    return missing


# --------------------------------------------------------------------------
# 體力來源
# --------------------------------------------------------------------------

# 一筆來源的日期有兩種寫法：偏移量鍵 → 對應的絕對日期鍵。
# 「依據某一檔活動」寫偏移量，換一檔活動時整組規則跟著移動——每日／每週任務、
# 簽到都該這樣。「不依據活動」寫絕對日期：月卡是真實世界的 30 天，綁在某一檔
# 活動上的話活動一結束就不再發體力，那不是使用者的意思。
SOURCE_DATE_KEYS = {"day_offset": "day_date",
                    "from_offset": "from_date",
                    "to_offset": "to_date"}


def source_date_keys(kind) -> tuple[str, ...]:
    """這種型態的來源會用到哪幾個絕對日期鍵。"""
    return (("day_date",) if (kind or "daily") in ("once", "mail")
            else ("from_date", "to_date"))


def source_is_absolute(source) -> bool:
    """這一筆是「不依據活動」（自己帶絕對日期）嗎？

    判定**只看絕對日期鍵在不在**：依據活動的來源寫偏移量，`event_id` 沒填時
    以第一檔活動的起始日當基準。
    """
    if source.get("preset") == "gift" and source.get("claimed_date"):
        return True       # 積分兌換填了領取日：那一天就是真實日期，不必靠活動
    return any(source.get(key) for key in source_date_keys(source.get("kind")))


def source_day(source: dict, offset_key: str, base):
    """一筆來源的某一個日期。絕對日期鍵優先，沒有就用 base ＋ 偏移量。

    回傳 None ＝這一欄讀不出日期（沒填、格式壞掉，或偏移量型但 base 是 None）。
    呼叫端一律跳過那一筆——來源清單是使用者手填的，壞一筆不該讓整個排程算不出來。
    """
    text = source.get(SOURCE_DATE_KEYS[offset_key])
    if text:
        try:
            return datetime.strptime(str(text).strip(), "%Y-%m-%d").date()
        except ValueError:
            return None
    try:
        return offset_from_start(int(source[offset_key]), base)
    except (KeyError, TypeError, ValueError):
        # base 是 None 也走到這裡：date + timedelta 會丟 TypeError。
        return None


def expand_stamina_sources(sources, event_start: date) -> dict:
    """把每一筆來源展開成 {發放日: 點數}。

    daily   期間內每一天都發
    weekly  期間內每個指定星期幾那天發（預設週日）
    monthly 期間內每個月的指定幾號各發一次（每日簽到那種）
    once    指定那一天發一次

    來源自己帶 `from_date`/`to_date`/`day_date`（絕對日期字串）時**以它們為準**
    ——那是「不依據活動」的來源（月卡那種綁在真實日期上的東西），不需要基準。
    否則用 `start_date`（來源自己的基準，任務獎勵來源會帶）或 `event_start`
    當偏移量的基準——多活動並行時每一筆來源各自掛在自己的參考活動上。
    基準是 None（一檔活動都沒填起訖日）時，偏移量型的來源讀不出日期而被跳過，
    絕對日期型的照樣算得出來。

    `skip_days`（日期字串集合）裡的日子不發——「預設完成」的任務被標記成
    那天沒做到時，那天的獎勵就不該入帳。
    """
    grants: dict[date, int] = {}
    skip: set = set()

    def add(day: date, amount: int) -> None:
        if amount and day.isoformat() not in skip:
            grants[day] = grants.get(day, 0) + amount

    for source in sources or []:
        try:
            amount = int(source.get("amount") or 0)
        except (TypeError, ValueError):
            continue
        if amount <= 0:
            continue
        skip = {str(x) for x in (source.get("skip_days") or ())}
        base = source.get("start_date") or event_start
        kind = source.get("kind") or "daily"
        if kind == "mail":
            continue      # 信箱：哪天領由排程決定（compute_plan 的 claim_lots）
        if kind == "once":
            day = (gift_claim_day(source) if source.get("preset") == "gift"
                   else source_day(source, "day_offset", base))
            if day is None:
                continue
            add(day, amount)
            continue
        first = source_day(source, "from_offset", base)
        last = source_day(source, "to_offset", base)
        if first is None or last is None:
            continue
        if last < first:
            first, last = last, first
        if kind == "weekly":
            # 同一個 Mon–Sun 週內哪一天拿到，到期日都一樣（都是下個星期日），
            # 差別只在幾號開始能用。預設記成週日是保守的：不會叫使用者去動
            # 還沒到手的體力，而且仍有 8 天可以用。
            try:
                weekday = int(source.get("weekday", 6))
            except (TypeError, ValueError):
                weekday = 6
            day = first
            while day <= last:
                if day.weekday() == weekday % 7:
                    add(day, amount)
                day += timedelta(days=1)
            continue
        if kind == "monthly":
            # 每日簽到那種：獎勵綁在「每個月的第幾號」。逐日走訪順便把
            # 「那個月沒有這一號」（例如 2 月的 31 號）處理掉——不發，也不會爆。
            try:
                month_days = {int(x) for x in (source.get("month_days") or [])}
            except (TypeError, ValueError):
                continue
            day = first
            while day <= last:
                if day.day in month_days:
                    add(day, amount)
                day += timedelta(days=1)
            continue
        day = first
        while day <= last:
            add(day, amount)
            day += timedelta(days=1)
    return grants


def expiry_of(grant_day: date) -> date:
    """某一天拿到的限時體力什麼時候過期。

    規則只有一種：**下一週的星期日**。
    例：8/31~9/6（週一~週日）那週拿到的，到 9/13 過期；
        9/7~9/13 那週拿到的，到 9/20 過期。
    所以同一個 Mon–Sun 週內拿到的，到期日都一樣。
    """
    this_sunday = grant_day + timedelta(days=6 - grant_day.weekday())
    return this_sunday + timedelta(days=7)


# 「先放著、晚點再領」的體力：一筆只能整筆一次領，領出來那天才開始算效期
# （照 expiry_of）。同一週內哪天領到期日都一樣，所以排程只決定「哪一週領」。
#   * 信箱——收到那天起放 MAIL_HOLD_DAYS 天（10/1 收到 → 10/30 當天還能領）
#   * 活動任務的體力獎勵——達標那天起能領，最晚活動結束後 REWARD_CLAIM_DAYS 天
MAIL_HOLD_DAYS = 29
REWARD_CLAIM_DAYS = 7


def gift_deadline(event_end: date) -> date:
    """積分兌換最晚哪天要換：活動結束後 REWARD_CLAIM_DAYS 天（活動都是週四中午
    結束，所以是下一個週四、中午 12 點前）。"""
    return event_end + timedelta(days=REWARD_CLAIM_DAYS)


def gift_claim_day(source: dict) -> date | None:
    """積分兌換的體力算在哪一天入帳（＝領取日，效期從這天照 expiry_of 算）。

    1. 有填領取日就是那天（已領取的是實際領的那天，沒領的是打算哪天領）
    2. 沒填：當成最後一天才領——`claim_deadline`（resolved_sources 依它
       依據的那檔活動算好的 gift_deadline）
    都算不出來回 None，呼叫端跳過這一筆。
    """
    claimed_on = _iso_date(source.get("claimed_date") or "")
    if claimed_on is not None:
        return claimed_on
    deadline = source.get("claim_deadline")
    if isinstance(deadline, str):
        deadline = _iso_date(deadline)
    return deadline

# 體力來源的種類名稱（跟 app.STAMINA_SOURCE_PRESETS 一致），報表點名來源時用
SOURCE_PRESET_NAMES = {"big_card": "大月卡", "small_card": "小月卡",
                       "daily_task": "每日任務", "weekly_task": "每週任務",
                       "checkin": "每日簽到", "gift": "積分兌換", "mail": "信箱",
                       "custom": "自訂"}


def source_label(source: dict) -> str:
    """報表裡怎麼稱呼這一筆體力：使用者填的說明優先，沒填就用種類名稱。"""
    if source.get("preset") == "task":
        owner = source.get("event_name")
        name = source.get("task_name") or source.get("task_key") or "任務"
        return f"{owner}「{name}」" if owner else f"「{name}」"
    kind = SOURCE_PRESET_NAMES.get(source.get("preset"), "自訂")
    note = str(source.get("note") or "").strip()
    return f"{kind}「{note}」" if note else kind


def stale_source_reason(source: dict, base, today: date) -> str | None:
    """這一筆體力來源已經完全派不上用場了嗎？是的話回傳原因，否則 None。

    「派不上用場」＝它發的體力（或還能領的那封信）全部都過了最後能用的那一天。
    到期日當天還能用，所以一律是「到期日 < 今天」才算失效。

    | 型態 | 失效條件 |
    |---|---|
    | 信箱、沒領 | 收到日＋MAIL_HOLD_DAYS 的領取期限已過（排程也會略過它） |
    | 信箱、已領 | 領取日那一批的到期日已過；沒記領取日的當成期限當天才領（保守，不會早刪） |
    | 一次 | 發放日那一批的到期日已過 |
    | 積分兌換 | 領取日那一批的到期日已過；沒填領取日的當成最後一天（活動結束後第 7 天）才領 |

    週期性的來源（每天／每週／每月：月卡、每日／每週任務、簽到）一律不清——
    使用者會改訖日續用那一列。

    讀不出日期的（沒填、依據的活動被刪掉或沒起始日）一律回 None——
    算不出來就不替使用者決定刪掉。`base` 是偏移量型來源的基準日。
    """
    kind = source.get("kind") or "daily"
    if kind == "mail":
        received = source_day(source, "day_offset", base)
        if received is None:
            return None
        deadline = received + timedelta(days=MAIL_HOLD_DAYS)
        if source.get("claimed"):
            # 有記領取日就用它；沒記的（加這一欄之前勾的）當成期限當天才領
            claimed_on = _iso_date(source.get("claimed_date"))
            expire = expiry_of(min(claimed_on, deadline) if claimed_on else deadline)
            if expire < today:
                return f"已領取，最晚 {expire:%m/%d} 就到期了"
            return None
        if deadline < today:
            return f"沒領，{deadline:%m/%d} 已經過了領取期限"
        return None
    if kind == "once" and source.get("preset") == "gift":
        day = gift_claim_day(source)
        if day is None:
            return None
        expire = expiry_of(day)
        if expire >= today:
            return None
        if source.get("claimed") or source.get("claimed_date"):
            return f"{day:%m/%d} 領取，{expire:%m/%d} 已到期"
        return f"沒填領取日，當成最後一天 {day:%m/%d} 才領，{expire:%m/%d} 也已到期"
    if kind == "once":
        day = source_day(source, "day_offset", base)
        if day is None:
            return None
        expire = expiry_of(day)
        return f"{expire:%m/%d} 已到期" if expire < today else None
    return None       # 週期性的（每天／每週／每月）不清：使用者會改訖日續用


def resolved_sources(shared: dict, profile: dict,
                     orphans: list | None = None) -> list[dict]:
    """使用者手填的體力來源，偏移量的基準已解析成絕對日期。

    每一筆可以用 `event_id` 指定參考哪一檔活動的起始日，沒指定就用第一檔。
    「不依據活動」的那些自己帶絕對日期（`from_date`/`to_date`/`day_date`），
    `expand_stamina_sources` 會優先用它們，所以這裡設的基準對它們無害。

    指定了 `event_id`、但那檔活動已經被刪掉（或沒有起始日）的偏移量型來源會被
    略過，並放進 `orphans`（有給的話）——默默改掛到第一檔活動上，體力會落在
    完全不相干的日子（特殊日規則也是這樣處理）。
    """
    events = (shared or {}).get("events") or []
    starts = {}
    ends = {}
    for event in events:
        if is_limited(event):
            continue
        if event.get("start_date"):
            try:
                starts[event.get("id")] = parse_date(event["start_date"], "起始日")
            except PlanError:
                continue
        if event.get("end_date"):
            try:
                ends[event.get("id")] = parse_date(event["end_date"], "結束日")
            except PlanError:
                pass
    # 一檔活動都沒填起訖日時基準是 None。這時不能直接 return []，那會把
    # 「不依據活動」的月卡也一起丟掉——它根本不需要任何活動當基準。偏移量型的
    # 來源讀不出日期，會在 expand_stamina_sources 裡自己被跳過。
    default_start = None
    if starts:
        # 常駐關卡沒有起訖日，永遠進不了 starts，所以就算它排在 events[0]，
        # 第一個 get 落空之後也只是退到下一個有日期的活動。
        default_start = (starts.get(events[0].get("id"))
                         or next(iter(starts.values())))
    result = []
    for source in profile.get("stamina_sources") or []:
        row = dict(source)
        event_id = source.get("event_id")
        if source.get("preset") == "gift" and event_id in ends:
            # 積分兌換沒填領取日時，當成最後一天才領（見 gift_claim_day）
            row["claim_deadline"] = gift_deadline(ends[event_id])
        if event_id and event_id not in starts and not source_is_absolute(source):
            if orphans is not None:
                orphans.append(source)
            continue
        # `event_id` 可能是 None（「不依據活動」明確寫 null），get 會退到預設基準。
        base = starts.get(event_id, default_start)
        # 沒有基準時**不要**寫這個鍵：留一個 None 進去，只會讓
        # `source.get("start_date") or event_start` 那行看起來像是有設。
        if base is not None:
            row["start_date"] = base
        result.append(row)
    return result


PLAY_TIME_FORMAT = "%Y-%m-%dT%H:%M"


def entry_day(entry: dict) -> date | None:
    try:
        return datetime.strptime(entry.get("date"), "%Y-%m-%d").date()
    except (TypeError, ValueError):
        return None


def plays_in(entry: dict):
    """把一列紀錄的分筆（`plays`）攤成 (時刻, 關卡鍵, 次數)。

    分筆的時刻是必填的；讀不出時刻的分筆（手改壞的檔案）跳過。
    """
    for play in entry.get("plays") or []:
        try:
            moment = datetime.strptime(str(play.get("at")), PLAY_TIME_FORMAT)
        except (TypeError, ValueError):
            continue
        for key, count in (play.get("counts") or {}).items():
            yield moment, key, count


def _done_by_task(entries) -> dict[str, set]:
    """{任務鍵: {勾了「做到了／已完成」的日期字串}}。`storage.done_by_task` 是這個的別名。"""
    done: dict[str, set] = {}
    for entry in entries or []:
        day = entry.get("date")
        if not day:
            continue
        for key in entry.get("tasks_done") or []:
            done.setdefault(key, set()).add(day)
    return done


def _done_grant_days(done_dates, reward_weekday: int, first: date, last: date,
                     skip: set) -> dict[date, date]:
    """「出現時間不固定」的每週任務：{那週原本的入帳日: 改成哪天入帳}。

    每一週（Mon–Sun，跟 `_missed_grant_days` 同一套週界）取最早勾的那天。
    那週已經標了沒做到（入帳日在 `skip` 裡）就以沒做到為準，不移。
    勾的日子不在任務期間內的不算。
    """
    moved: dict[date, date] = {}
    for text in sorted(done_dates or ()):
        try:
            moment = datetime.strptime(str(text), "%Y-%m-%d").date()
        except (TypeError, ValueError):
            continue
        if moment < first or moment > last:
            continue
        monday = moment - timedelta(days=moment.weekday())
        grant = monday + timedelta(days=reward_weekday % 7)
        if grant in skip or grant in moved:
            continue
        moved[grant] = moment
    return moved


def _missed_by_task(entries) -> dict[str, set]:
    """{任務鍵: {沒做到的日期字串}}。`storage.missed_by_task` 是這個的別名。"""
    missed: dict[str, set] = {}
    for entry in entries or []:
        day = entry.get("date")
        if not day:
            continue
        for key in entry.get("tasks_missed") or []:
            missed.setdefault(key, set()).add(day)
    return missed


def _missed_grant_days(cycle: str, missed_dates, reward_weekday: int,
                       month_days, event_grant: date | None) -> set:
    """把「哪幾天沒做到」換算成「哪幾筆獎勵不該入帳」。

    使用者標記的是**做這件事的那一天**，但獎勵未必落在同一天：

    | 週期 | 標了某天 → 扣掉 |
    |---|---|
    | 每日／公會 | 就是那天的獎勵 |
    | 每週 | 那一週（Mon–Sun）的入帳日，也就是「這週沒做到」 |
    | 每月 | 那個月裡**下一個**入帳日（簽到是累積制，漏一天就少領一次） |
    | 活動 | 期限當天那一筆（整條任務只發一次） |
    """
    out: set[date] = set()
    for text in missed_dates or ():
        try:
            moment = datetime.strptime(str(text), "%Y-%m-%d").date()
        except (TypeError, ValueError):
            continue
        if cycle in ("daily", "guild"):
            out.add(moment)
        elif cycle == "weekly":
            monday = moment - timedelta(days=moment.weekday())
            out.add(monday + timedelta(days=reward_weekday % 7))
        elif cycle == "monthly":
            later = [d for d in sorted(month_days or ()) if d >= moment.day]
            if later:
                try:
                    out.add(moment.replace(day=later[0]))
                except ValueError:      # 那個月沒有那一號
                    continue
        elif event_grant is not None:
            out.add(event_grant)
    return out


def task_reward_sources(shared: dict, profile: dict,
                        missed: dict | None = None,
                        done: dict | None = None) -> list[dict]:
    """任務獎勵裡的體力，展開成體力來源。

    每日／公會任務＝期間內每天拿到；每週任務算在該週的指定星期幾（預設週日，
    保守）；每月任務算在指定的幾號（預設 5/11/17/23，跟每日簽到一致）；
    活動任務算在期限當天。沒有體力獎勵的任務不會產生來源。

    `missed` ＝ `{任務鍵: {沒做到的日期字串}}`（`storage.missed_by_task()`）。
    「預設完成」的任務平常就當你每天都做到，只有標記成沒做到的那幾天不發獎勵。
    不給就當沒有人漏做。

    `done` ＝ `{任務鍵: {勾了已完成的日期字串}}`（`storage.done_by_task()`）。
    勾了「出現時間不固定」（`grant_on_done`）的每週任務，那週的獎勵改算在勾的
    那天——已經在包包裡了，不能再在週日發一次（實測商店購買週中買了、週中重算
    會多算一次獎勵）。沒勾的週照舊算在 `reward_weekday`。

    > 這裡刻意**只看 `task_state[key]["enabled"]`、不看 `enforce`**：
    > 手動勾選類的任務永遠 `enforce=False`，但體力照領。
    > 「`enforce` 為假卻有體力獎勵」會不會出事，由 `compute_plan` 另外出提醒。
    """
    from_items = item_stamina_table(shared)
    # 固定任務不屬於任何一檔活動，用「所有活動涵蓋的期間」當它的基準
    overall = _overall_span(shared)
    sources = []
    for task, owner, key in iter_tasks(shared):
        state = (profile.get("task_state") or {}).get(key) or {}
        if state.get("enabled") is False:
            continue
        amount = sum(from_items.get(r.get("item"), 0) * int(r.get("qty") or 0)
                     for r in task.get("rewards") or [])
        if amount <= 0:
            continue
        span = _task_span(task, owner, overall)
        if span is None:
            continue
        start_date, from_offset, to_offset = span
        cycle = task.get("cycle")
        # 使用者標的是「做這件事的那一天」，換算成「哪一筆獎勵不入帳」
        skip = _missed_grant_days(
            cycle, (missed or {}).get(key),
            int(task.get("reward_weekday", 6)),
            task.get("reward_days") or [],
            offset_from_start(to_offset, start_date))
        base = {"preset": "task", "amount": amount, "start_date": start_date,
                "task_key": key, "task_name": task.get("name"),
                "skip_days": {d.isoformat() for d in skip}}
        if cycle in ("daily", "guild"):
            sources.append(dict(base, kind="daily", from_offset=from_offset,
                                to_offset=to_offset))
        elif cycle == "weekly":
            weekday = int(task.get("reward_weekday", 6))
            if task.get("grant_on_done"):
                lo = offset_from_start(from_offset, start_date)
                hi = offset_from_start(to_offset, start_date)
                if hi < lo:
                    lo, hi = hi, lo
                moved = _done_grant_days((done or {}).get(key), weekday, lo, hi, skip)
                if moved:
                    base = dict(base, skip_days=base["skip_days"]
                                | {d.isoformat() for d in moved})
                    for actual in sorted(moved.values()):
                        sources.append(dict(base, kind="once", skip_days=set(),
                                            day_date=actual.isoformat()))
            sources.append(dict(base, kind="weekly", from_offset=from_offset,
                                to_offset=to_offset, weekday=weekday))
        elif cycle == "monthly":
            sources.append(dict(base, kind="monthly", from_offset=from_offset,
                                to_offset=to_offset,
                                month_days=list(task.get("reward_days") or [])))
        else:  # event：期限當天入帳
            # 算得出進度的（不是手動勾選）改成「達標起可領」，由 compute_plan
            # 決定哪一週領；這裡先標起來，期限當天入帳只是排程沒辦法追進度時的
            # 退路。已經領出來的不再算，包包裡剩多少照計算頁填的。
            claimable = task.get("metric") != "manual"
            if claimable and state.get("reward_claimed"):
                continue
            sources.append(dict(base, kind="once", day_offset=to_offset,
                                claimable=claimable,
                                auto_claim=bool(state.get("reward_auto")),
                                event_id=owner.get("id") if owner else None,
                                event_name=event_label(owner) if owner else None))
    return sources


def item_stamina_table(shared: dict) -> dict[str, int]:
    return {it.get("id"): int(it.get("stamina") or 0)
            for it in (shared or {}).get("items") or []}


def iter_tasks(shared: dict):
    """走訪所有任務，產出 (task, owner_event or None, task_key)。"""
    for event in (shared or {}).get("events") or []:
        for task in event.get("tasks") or []:
            yield task, event, f"{event.get('id')}/{task.get('id')}"
    for task in (shared or {}).get("routine_tasks") or []:
        yield task, None, f"routine/{task.get('id')}"


def _overall_span(shared: dict):
    """所有活動涵蓋的期間，回傳 (最早起始日, 0, 到最晚結束日的天數)。"""
    starts, ends = [], []
    for event in (shared or {}).get("events") or []:
        if is_standing(event) or is_limited(event):
            continue        # 常駐／限期關卡不構成「所有活動涵蓋的期間」
        try:
            start = parse_date(event.get("start_date"), "起始日")
            end = parse_date(event.get("end_date"), "結束日")
        except PlanError:
            continue        # 起訖日只填了一半的活動不能半套加進去，兩邊會對不齊
        starts.append(start)
        ends.append(end)
    if not starts:
        return None
    first, last = min(starts), max(ends)
    return first, 0, (last - first).days


def _task_span(task: dict, owner: dict | None, overall=None):
    """任務有效的日期範圍，回傳 (基準日, from_offset, to_offset)。

    活動任務以**該活動**的起訖日為基準，吃任務自己的 `from_offset` / `to_offset`；
    固定任務不屬於任何一檔活動，期間存絕對日期（`from_date` / `to_date`），
    換算成相對 `overall`（所有活動涵蓋的期間，見 `_overall_span`）的偏移量。
    沒填的那一頭用整段。

    > **呼叫端只准走這一個函式。** `task_reward_sources()` 與 `compute_plan()`
    > 各自判斷 `owner is None` 的話，很容易一邊照做、一邊忽略固定任務的
    > 「只算這段期間」——畫面讓你填、程式卻沒照做。
    """
    if owner is None:
        abs_from = _iso_date(task.get("from_date"))
        abs_to = _iso_date(task.get("to_date"))
        if overall is None:
            if abs_from is None or abs_to is None:
                return None
            return abs_from, 0, (abs_to - abs_from).days
        start, _zero, last = overall
        from_offset = None if abs_from is None else (abs_from - start).days
        to_offset = None if abs_to is None else (abs_to - start).days
    else:
        try:
            start = parse_date(owner.get("start_date"), "起始日")
            end = parse_date(owner.get("end_date"), "結束日")
        except PlanError:
            return None
        last = (end - start).days
        if task.get("cycle") == "event":
            offset = task.get("deadline_offset", -1)
            deadline = resolve_day_offset(int(offset), start, end)
            return start, 0, (deadline - start).days
        from_offset = task.get("from_offset")
        to_offset = task.get("to_offset")
    return (start,
            0 if from_offset is None else int(from_offset),
            last if to_offset is None else int(to_offset))


def _iso_date(text) -> date | None:
    """"YYYY-MM-DD" → date；空的或格式不對回 None。"""
    try:
        return datetime.strptime(str(text).strip(), "%Y-%m-%d").date()
    except ValueError:
        return None


def held_pools(shared: dict, profile: dict, today: date,
               missed: dict | None = None,
               done: dict | None = None) -> list[tuple[date, int]]:
    """今天（含）以前發放、還沒過期的限時體力，依到期日彙總。

    這是排程「假設你手上有」的量——它假設發過的一點都還沒用掉，所以
    計算前要列給使用者對照修正（`compute_plan` 的 held_by_expiry）。
    今天之後才發的不列：那些還沒到手，沒什麼好校正的。

    `missed` 不給就當沒有人漏做任務，估出來的量會偏高——這一欄本來就是
    給使用者手動校正的，高估比低估安全。
    """
    totals: dict[date, int] = {}
    # 達標起可領的任務獎勵不會自己進包包（要使用者去領），所以不列
    sources = (resolved_sources(shared, profile)
               + [src for src in task_reward_sources(shared, profile, missed, done)
                  if not src.get("claimable")])
    grants = expand_stamina_sources(sources, today)
    for grant_day, amount in grants.items():
        if grant_day > today:
            continue
        expire_day = expiry_of(grant_day)
        if expire_day < today:
            continue
        totals[expire_day] = totals.get(expire_day, 0) + amount
    return sorted(totals.items())


def offset_from_start(offset: int, start: date) -> date:
    """區間類規則專用：偏移量一律從活動起始日算，負數就是起始日之前。

    不能用 resolve_day_offset——那個把負數解讀成「從最後一天往回算」，
    是給「特殊日」「活動任務期限」那種用 day_ref 控制項輸入的欄位用的。
    區間規則是直接輸入日期換算來的，起始日之前的日期會得到負數，
    兩種解讀混用會讓日期讀回來時整個跑掉。
    """
    return start + timedelta(days=offset)


def resolve_day_offset(offset: int, start: date, end: date) -> date:
    """day_offset 換算成實際日期。

    正數/0 從活動第一天算起（0 = 第1天）；
    負數從最後一天算起（-1 = 最後一天，-2 = 倒數第二天）。
    """
    if offset >= 0:
        return start + timedelta(days=offset)
    return end + timedelta(days=offset + 1)


# 「每檔活動自動套用的規則」沒填套用類型時，預設套到當期與復刻
DEFAULT_RULE_EVENT_TYPES = ("current", "rerun")


def default_rule_applies(rule: dict, event_type: str) -> bool:
    """這條自動套用規則要不要套到這種類型的活動。"""
    types = rule.get("event_types")
    return event_type in (DEFAULT_RULE_EVENT_TYPES if types is None else types)


def special_rule_key(idx, kind, event_id):
    """哪兩條特殊日規則算「同一條」：同一天同類型；單檔上限還要同一檔活動。"""
    return (idx, kind, event_id) if kind == "event_cap_override" else (idx, kind)


def storage_event_name(shared: dict, event_id: str) -> str:
    """設定檔裡那檔活動的名稱——連已經結束、沒列入排程的也找得到。"""
    for event in (shared or {}).get("events") or []:
        if event.get("id") == event_id:
            return event_label(event)
    return event_id or "?"


def format_day(day: date) -> str:
    return f"{day:%m/%d}（{WEEKDAY_NAMES[day.weekday()]}）"


# ---- 代幣關卡 ---------------------------------------------------------------
# 有些常駐關卡（經商貿易、探索調查）要用代幣才能打：每天發 1 個、最多存 3 個。
# 「指定關卡次數限制」的規則多一個 tokens 欄位：
#   {"count": 那天開始時（發完當天的、還沒打）有幾個, "date": "YYYY-MM-DD",
#    "max": 最多存幾個, "per_day": 每天發幾個}
# 之後每天有幾個由每日紀錄推算：前一天剩的＋當天發的，頂到上限就不再多。
TOKEN_DEFAULT_MAX = 3
TOKEN_DEFAULT_PER_DAY = 1


def token_spec(entry: dict) -> dict | None:
    """規則裡的代幣設定；沒有或填壞了 → None（當成一般的每日上限規則）。"""
    tokens = entry.get("tokens")
    if not isinstance(tokens, dict):
        return None
    try:
        count = max(0, int(tokens["count"]))
        anchor = datetime.strptime(str(tokens["date"]), "%Y-%m-%d").date()
        cap = max(1, int(tokens.get("max") or TOKEN_DEFAULT_MAX))
        per_day = max(0, int(tokens.get("per_day") or TOKEN_DEFAULT_PER_DAY))
    except (KeyError, TypeError, ValueError):
        return None
    return {"count": min(count, cap), "date": anchor, "max": cap,
            "per_day": per_day}


def _plays_by_day(log_entries, key: str) -> dict[date, int]:
    played: dict[date, int] = {}
    for entry in log_entries or []:
        day = entry_day(entry)
        if day is None:
            continue
        try:
            count = max(0, int((entry.get("counts") or {}).get(key) or 0))
        except (TypeError, ValueError):
            continue
        if count:
            played[day] = played.get(day, 0) + count
    return played


def token_stock(entry: dict, log_entries, day: date) -> int | None:
    """day 那天開始時（發完當天的代幣、還沒打）手上有幾個；不是代幣規則 → None。"""
    spec = token_spec(entry)
    if spec is None:
        return None
    played = _plays_by_day(log_entries, entry.get("level_id"))
    stock, current = spec["count"], spec["date"]
    while current < day:
        stock = max(0, stock - played.get(current, 0))
        stock = min(spec["max"], stock + spec["per_day"])
        current += timedelta(days=1)
    return stock


def tokens_held(entry: dict, log_entries, today: date) -> int | None:
    """現在手上有幾個（今天開始時的扣掉今天已經記錄打過的）。"""
    stock = token_stock(entry, log_entries, today)
    if stock is None:
        return None
    played = _plays_by_day(log_entries, entry.get("level_id")).get(today, 0)
    return max(0, stock - played)


def token_anchor(level_id: str, held_now: int, log_entries, today: date,
                 cap: int = TOKEN_DEFAULT_MAX,
                 per_day: int = TOKEN_DEFAULT_PER_DAY) -> dict:
    """使用者填「現在手上有幾個」→ 存檔用的 tokens 欄位（換算成今天開始時的數量）。"""
    played = _plays_by_day(log_entries, level_id).get(today, 0)
    return {"count": max(0, int(held_now)) + played, "date": today.isoformat(),
            "max": cap, "per_day": per_day}


def _stage_rule(entry: dict, level: dict, idx: int, weekdays: set[int],
                prior: int, limited_ids: set[str],
                warnings: list[str]) -> dict | None:
    """「指定關卡次數限制」裡選了難度的那種規則 → 給 build_and_solve 的資料。

    限期關卡（檢定、忘卻）是依序解鎖的：第 N 次通關就是第 N 關。所以「第 50 關
    只能在週六日打」＝「累計次數從 49 跨到 50 的那天必須是週六或週日」。
    回傳的 stages 只留還沒打到的關（prior 之後、上限之內）；沒有要管的就回 None。
    """
    label = level["label"]
    if level["event_id"] not in limited_ids:
        warnings.append(f"「{label}」不是限期關卡，它的難度規則已略過")
        return None
    if not weekdays:
        warnings.append(f"「{label}」的難度規則沒有勾星期幾，已略過")
        return None
    max_total = level.get("max_total")
    if not max_total:
        warnings.append(f"「{label}」沒有總次數上限，分不出第幾關，它的難度規則已略過")
        return None
    max_total = int(max_total)
    if entry.get("stages_other"):
        grouped = {int(x) for group in level.get("tiers") or [] for x in group}
        stages = set(range(1, max_total + 1)) - grouped
        what = "其他關"
    else:
        stages = {int(x) for x in entry.get("stages") or []}
        what = "第 " + "、".join(map(str, sorted(stages))) + " 關"
    stages = sorted(k for k in stages if prior < k <= max_total)
    if not stages:
        return None
    names = "".join(WEEKDAY_NAMES[d] for d in sorted(weekdays))
    return {"idx": idx, "stages": stages, "prior": prior, "max_total": max_total,
            "text": f"「{label}」{what}只在週{names}打"}


def level_target_dates(entry: dict, first: date, last: date) -> list[date]:
    """「指定日期打指定次數」一條規則落在哪幾天。

    repeat：
      "once"（舊檔沒有這個鍵也算）＝ date 那一天
      "dates" ＝ dates 清單裡的每一天
      "weekly"＝ from_date～to_date 之間、星期幾在 weekdays 裡的每一天；
                起訖留白就是整個排程範圍（first～last）
    once／dates 照填的日期回傳，不裁切——超出範圍要不要講由呼叫端決定。
    weekly 只回傳 first～last 之內的日子（沒有範圍可言，裁掉不算錯）。
    日期格式不對丟 PlanError。
    """
    repeat = entry.get("repeat") or "once"
    if repeat == "weekly":
        weekdays = {int(x) for x in entry.get("weekdays") or []}
        lo = (parse_date(entry["from_date"], "指定次數規則的起始日")
              if entry.get("from_date") else first)
        hi = (parse_date(entry["to_date"], "指定次數規則的結束日")
              if entry.get("to_date") else last)
        lo, hi = max(lo, first), min(hi, last)
        result = []
        day = lo
        while day <= hi:
            if day.weekday() in weekdays:
                result.append(day)
            day += timedelta(days=1)
        return result
    if repeat == "dates":
        texts = entry.get("dates") or []
    else:
        texts = [entry.get("date")]
    return sorted({parse_date(text, "指定次數規則的日期") for text in texts})


def format_countdown(target: datetime, now: datetime) -> str:
    """距離某個時刻還有多久，用「N 天 N 小時」表示。"""
    delta = target - now
    if delta.total_seconds() <= 0:
        return "已結束"
    days = delta.days
    hours = delta.seconds // 3600
    if days:
        return f"{days} 天 {hours} 小時"
    minutes = (delta.seconds % 3600) // 60
    return f"{hours} 小時 {minutes} 分"


def next_reset(now: datetime, reset: dtime, weekday: int | None = None,
               month_day: int | None = None) -> datetime:
    """下一次重置是什麼時候。

    weekday／month_day 都不給＝每日重置；給 weekday＝每週；給 month_day＝每月。
    一律回傳「嚴格晚於 now」的那一個時刻。
    """
    day = now.date()
    if weekday is not None:
        for step in range(0, 8):
            candidate = datetime.combine(day + timedelta(days=step), reset)
            if candidate > now and candidate.weekday() == weekday % 7:
                return candidate
        return datetime.combine(day + timedelta(days=7), reset)
    if month_day is not None:
        for step in range(0, 40):
            candidate = datetime.combine(day + timedelta(days=step), reset)
            if candidate > now and candidate.day == month_day:
                return candidate
        return datetime.combine(day + timedelta(days=31), reset)
    candidate = datetime.combine(day, reset)
    return candidate if candidate > now else candidate + timedelta(days=1)


PROGRESS_FILL = "█"


def progress_bar(done: int, total: int, width: int = 10, empty: str = "░") -> str:
    """用方塊字元畫的進度條——Treeview 塞不下真的 Progressbar，但塞得下文字。

    `empty`：空白段的字元。比例字型裡「░」常比「█」寬（微軟正黑體 9 對 12 像素），
    越空的條越長；畫面那邊量過字型後傳一個跟 `PROGRESS_FILL` 等寬的進來。
    """
    if total <= 0:
        return ""
    ratio = min(1.0, max(0.0, done / total))
    filled = int(round(ratio * width))
    return PROGRESS_FILL * filled + empty * (width - filled) + f" {ratio * 100:.0f}%"


# --------------------------------------------------------------------------
# 主計算
# --------------------------------------------------------------------------

SOLVER_PROBLEM_NAME = "stamina_schedule"


def _remove_solver_files() -> None:
    """收掉 CBC 留在工作目錄的暫存檔（keepFiles 的副作用，見 run_stage）。

    工作目錄就是程式所在的資料夾——PSCalculator.main() 啟動時會切過去。
    """
    for suffix in ("mps", "mst", "sol", "lp"):
        try:
            os.remove(f"{SOLVER_PROBLEM_NAME}-pulp.{suffix}")
        except OSError:
            pass


def _level_row(event: dict, level: dict, data: dict, label: str) -> dict:
    """關卡攤平成一列（compute_plan 與 task_progress 共用）。"""
    row = dict(level)
    # 限期關卡每檔、每個帳號的上限可能不同，帳號填的優先於關卡預設
    level_caps = data.get("level_max_total") or {}
    if event.get("limited") and level_caps.get(level["id"]) is not None:
        row["max_total"] = int(level_caps[level["id"]])
    row["key"] = level_key(event["id"], level["id"])
    row["event_id"] = event["id"]
    row["event_name"] = event["name"]
    # 系列名稱（不含期數）：限期關卡的關卡優先序靠它跨檔次對上
    row["series_name"] = (event.get("raw") or {}).get("name") or event["name"]
    row["label"] = label
    raw_points = (data.get("level_points") or {}).get(level["id"])
    row["points"] = int(raw_points) if (level.get("scoring") and raw_points) else 0
    row["counts_clears"] = bool(
        level.get("counts_clears", level.get("scoring", True))
        or level.get("scoring"))
    return row


def _flatten_levels(events: list[dict], past_events: list[dict], profile: dict):
    """把各活動的關卡攤平成一張表。

    回傳 (這次要算的關卡, 這次不算的關卡, all_levels, points_all)。
    「這次計算要不要算」是各帳號獨立的開關（關卡本身所有帳號共用，但這一檔活動
    哪幾關開放、哪幾關這個帳號要打，逐帳號不同）。沒設定的一律視為要算。
    過去的活動只進 all_levels（量紀錄用），不進 levels——不會被排到。
    """
    multi = len(events) > 1
    levels, excluded = [], []
    all_levels: dict[str, dict] = {}   # 含沒被算進來的，用來還原名稱與已打紀錄
    points_all: dict[str, int] = {}
    for event in events:
        data = (profile.get("events") or {}).get(event["id"]) or {}
        level_enabled = data.get("level_enabled") or {}
        for level in event["raw"].get("levels") or []:
            row = _level_row(event, level, data,
                             level_label(event["name"], event["raw"].get("name"),
                                         level["name"]) if multi
                             else level["name"])
            all_levels[row["key"]] = row
            points_all[row["key"]] = row["points"]
            if level_enabled.get(level["id"], True):
                levels.append(row)
            else:
                excluded.append(row)
    for event in past_events:
        data = (profile.get("events") or {}).get(event["id"]) or {}
        for level in event["raw"].get("levels") or []:
            row = _level_row(event, level, data,
                             level_label(event["name"], event["raw"].get("name"),
                                         level["name"]))
            all_levels[row["key"]] = row
            points_all[row["key"]] = row["points"]
    return levels, excluded, all_levels, points_all


def _scope_keys(task: dict, owner_id: str | None, all_levels: dict) -> set[str]:
    """這條任務算哪幾關的紀錄（關卡鍵集合）。"""
    scope = task.get("scope")
    if scope:
        return set(scope)
    metric = task.get("metric")
    if metric == "points":
        rows = [lv for lv in all_levels.values() if lv["scoring"]
                and (owner_id is None or lv["event_id"] == owner_id)]
    elif metric == "clears":
        if owner_id is None:
            rows = list(all_levels.values())
        else:
            rows = [lv for lv in all_levels.values()
                    if lv["event_id"] == owner_id and lv["counts_clears"]]
    elif metric == "drops":
        # 道具是活動各自的：只算這檔活動裡有填道具數量的關卡
        rows = [lv for lv in all_levels.values() if int(lv.get("drops") or 0)
                and (owner_id is None or lv["event_id"] == owner_id)]
    else:  # stamina / enemies：跨活動一起算
        rows = list(all_levels.values())
    return {lv["key"] for lv in rows}


def _measure(entries, metric: str, scope: set[str] | None, all_levels: dict,
             points_all: dict, live=None) -> int:
    """紀錄裡符合條件的量。

    `scope` 限制關卡，`live` 再多一層「這一筆算不算」——活動任務要看打的
    當下那檔活動開沒開（見 _live_filter）。`live` 是 None 就全算。
    """
    if metric == "manual":
        return 0       # 手動勾選的任務從關卡紀錄看不出來，只能靠打勾
    total = 0
    for entry in entries:
        for at, key, count in plays_in(entry):
            try:
                count = max(0, int(count or 0))
            except (TypeError, ValueError):
                continue
            if not count or (scope is not None and key not in scope):
                continue
            if live is not None and not live(key, at):
                continue
            level = all_levels.get(key)
            if level is None:
                continue
            if metric == "stamina":
                total += int(level.get("stamina_cost") or 0) * count
            elif metric == "enemies":
                total += int(level.get("enemies") or 0) * count
            elif metric == "drops":
                total += int(level.get("drops") or 0) * count
            elif metric == "points":
                total += points_all.get(key, 0) * count
            else:
                total += count
    return total


def _live_filter(event_id: str | None, owners: dict, bounds_by_id: dict):
    """「這一筆打法算不算進這檔活動的任務」，給 _measure 用。

    看打的那一刻雙方開沒開——活動交接日（舊活動中午收、新活動下午開）
    才不會把早上打的算進下午那檔。

    `owners`：任務所屬活動查得到起訖時刻的那份表；`bounds_by_id`：打的那一關
    所屬活動（連過去的）的起訖時刻。
    """
    if event_id is None:
        return None

    def keep(key: str, at: datetime) -> bool:
        owner = owners.get(event_id)
        if owner is None or not (owner["start_dt"] <= at < owner["end_dt"]):
            return False
        played = bounds_by_id.get(split_level_key(key)[0])
        return played is not None and (
            played["start_dt"] <= at < played["end_dt"])

    return keep


PERIOD_NAMES = {"daily": "今天", "guild": "今天", "weekly": "本週", "monthly": "本月"}


def task_progress(shared: dict, profile: dict, log_entries: list[dict] | None,
                  now: datetime) -> dict[str, dict]:
    """每條任務**目前這一期**做到哪裡，給「任務進度」分頁看，不跑求解器。

    會重置的任務（每日／公會／每週／每月）只看包含今天的那個重置窗；活動任務
    看整檔活動累計。量法跟 `compute_plan` 同一把尺（`_measure`、`_live_filter`、
    `_scope_keys`）。

    回傳 `{任務鍵: {...}}`：
      * `state`：`active`／`not_started`／`ended`（今天在不在任務期間內）
      * `period`：期間標籤（今天、本週、本月、活動累計）
      * `once`：一次性的活動任務（期間過了照樣看達標沒有）；`deadline` 是它的期限
        MM/DD，期限就是活動最後一天時為 None（不必另外標）
      * `since`：量紀錄的起點（date）：週期任務＝目前這一期的第一天，
        活動任務＝活動起始日；不在期間內的週期任務是 None
      * `archived`：所屬活動已封存
      * `kind`：`count`＝看數字（`done` 與目標比）；`ticked`＝手動勾選；
        `assumed`＝預設完成（本期沒標記沒做到就算完成）
      * `done`：已完成的量（`count` 才有意義）
      * `uses_baseline`：`done` 還要加上任務自己的起始值——由畫面加，
        才能反映還沒存檔的編輯
      * `met`：`ticked`／`assumed` 的完成與否；`count` 由畫面拿目標比
    """
    entries = list(log_entries or [])
    reset = parse_clock(shared.get("daily_reset_time"), "05:00")
    weekly_weekday = int((shared.get("weekly_reset") or {}).get("weekday", 0) or 0) % 7
    monthly_day = max(1, min(28, int(
        (shared.get("monthly_reset") or {}).get("day", 1) or 1)))
    today = task_day_of(now, reset)

    events = []
    for raw in shared.get("events") or []:
        try:
            start_dt, end_dt = event_bounds(raw)
        except PlanError:
            continue
        events.append({"id": raw.get("id"), "name": event_label(raw), "raw": raw,
                       "limited": is_limited(raw),
                       "start_dt": start_dt, "end_dt": end_dt})
    # 結束與否不影響量法：全部當成同一張表，關卡名稱這裡用不到
    _lv, _ex, all_levels, points_all = _flatten_levels(events, [], profile)
    bounds_by_id = {ev["id"]: ev for ev in events}

    def between(first: date | None, last: date | None) -> list[dict]:
        rows = []
        for entry in entries:
            day = entry_day(entry)
            if day is None or (first and day < first) or (last and day > last):
                continue
            rows.append(entry)
        return rows

    def ticked(key: str, field: str, first: date | None, last: date | None) -> bool:
        return any(key in (entry.get(field) or []) for entry in between(first, last))

    profile_events = profile.get("events") or {}
    task_states = profile.get("task_state") or {}
    overall = _overall_span(shared)
    out: dict[str, dict] = {}
    for task, owner, key in iter_tasks(shared):
        metric = task.get("metric")
        cycle = task.get("cycle")
        owner_id = owner.get("id") if owner else None
        span = _task_span(task, owner, overall)
        if span is None:
            first = last = None
        else:
            base, lo, hi = span
            first, last = offset_from_start(lo, base), offset_from_start(hi, base)
            if last < first:
                first, last = last, first
        state = ("not_started" if first and today < first
                 else "ended" if last and today > last else "active")
        info = {"state": state, "kind": "count", "done": 0,
                "uses_baseline": False, "met": None, "once": cycle == "event",
                "since": None, "archived": bool(owner and is_archived(owner))}
        out[key] = info

        if cycle == "event":
            if owner is None or first is None:
                info["state"] = "ended"      # 對不到活動，算不出來
                info["period"] = "活動累計"
                continue
            info["period"] = "活動累計"
            # 期限就是活動最後一天的話不必講；比活動早截止的（簽到第 N 天）才標
            event_end = _iso_date(owner.get("end_date"))
            info["deadline"] = (f"{last:%m/%d}" if event_end is None or last < event_end
                                else None)
            win_first, win_last = first, None
        else:
            info["period"] = PERIOD_NAMES.get(cycle, "本期")
            if state != "active":
                continue
            # 包含今天的那個重置窗：頭不裁（本期已過的日子也算），尾裁到任務期間
            win_first, win_last = next(_reset_windows(
                cycle, today, last or today, weekly_weekday, monthly_day))
        # 這條任務從哪一天起的紀錄還用得到（每日紀錄靠它決定最早列到哪天）
        info["since"] = win_first

        if task.get("assume_done") and metric == "manual":
            # 預設完成：當你有做到，只有標了「沒做到」才不算。
            # 有目標數字的照實際量——量得出來就不必假設
            info["kind"] = "assumed"
            info["met"] = not ticked(key, "tasks_missed", win_first, win_last)
            if cycle == "weekly" and info["met"] and not task.get("grant_on_done"):
                # 每週的預設在入帳那天（例如週三）才算做完；之前還不算數，
                # 真的沒做到再到「每日紀錄」標
                monday = today - timedelta(days=today.weekday())
                due = monday + timedelta(days=int(task.get("reward_weekday", 6)) % 7)
                if today < due:
                    info["met"] = None
                    info["assumed_on"] = due
            continue
        if metric == "manual":
            info["kind"] = "ticked"
            info["met"] = ticked(key, "tasks_done", win_first, win_last)
            continue

        keys = _scope_keys(task, owner_id, all_levels)
        default_scope = not task.get("scope")
        live = _live_filter(owner_id, bounds_by_id, bounds_by_id)
        if cycle == "event":
            # 跟 compute_plan 的 derived_progress 同一套規則
            data = profile_events.get(owner_id) or {}
            if default_scope and metric == "points":
                info["done"] = int(data.get("current_points") or 0)
            elif default_scope and metric == "clears":
                info["done"] = int(data.get("current_clears") or 0)
            elif default_scope and metric in ("stamina", "enemies"):
                info["done"] = (event_baseline(data, metric)
                                + _measure(between(first, None), metric, keys,
                                           all_levels, points_all, live))
            elif default_scope and metric == "drops":
                info["done"] = (event_baseline(data, metric)
                                + _measure(entries, metric, keys, all_levels, points_all))
            else:
                info["done"] = _measure(entries, metric, keys, all_levels, points_all)
                info["uses_baseline"] = True
        else:
            info["done"] = (_measure(between(win_first, win_last), metric, keys,
                                     all_levels, points_all, live)
                            + period_done_before(task_states.get(key), win_first))
            # 補登視窗要知道「這一期」從哪天算，填的數字才對得上
            info["window_from"] = win_first.isoformat()
    return out


def compute_plan(shared: dict, profile: dict, current_stamina: int,
                 query_dt: datetime, time_limit: int = DEFAULT_TIME_LIMIT,
                 reclaim_surplus: bool = True,
                 log_entries: list[dict] | None = None,
                 held_by_expiry: dict | None = None,
                 plan_until: date | None = None,
                 pinned: dict | None = None,
                 progress=None) -> dict:
    """求解排程。

    current_stamina / query_dt 是「當下即時查到的體力與查詢時間」，
    不會被寫回設定檔（體力每 5 分鐘就在變，沿用舊值沒有意義）。

    log_entries 是每日紀錄（`[{"date": ..., "counts": {"ev1/lv3": 5}}, ...]`）。
    用來把**已經做掉的部分**從任務的剩餘量裡扣掉。

    plan_until 是「要排到哪一天」。留空就排到最晚那檔活動結束為止；活動空窗期
    （所有活動都結束了、只剩常駐關卡）沒有結束日可以依據，這時它是必填的。

    held_by_expiry 是 `{到期日: 手上還有幾點}`，用來校正「今天以前發放的限時體力
    還剩多少」。不給就沿用推算——那個推算假設發過的一點都還沒用掉，而已經打過幾天
    之後那多半是高估的（見 held_pools）。

    pinned 是 `{日期: {關卡鍵: 次數}}`——使用者手動指定的打法（計算頁的「對調日期」）。
    那幾天**整天**照這個打（沒列的關卡＝0），其餘日子由求解器重新配平。鎖定日上的
    每日／每週要求與當日上限改以使用者的調整為準，達不到的列在「湊不齊的目標」；
    解鎖鏈、開放起日、總次數上限這些遊戲規則照樣是硬條件。

    progress 是 `progress(文字)`：每進入一個求解階段就呼叫一次，告訴介面現在
    算到哪裡。它在計算的執行緒裡被呼叫，不能直接碰 Tk 元件。
    """
    try:
        import pulp
    except ImportError as exc:  # pragma: no cover - 環境問題
        raise PlanError(PULP_INSTALL_HINT) from exc
    if not solver_available():
        raise PlanError(CBC_INSTALL_HINT)

    warnings: list[str] = []
    log_entries = list(log_entries or [])

    # ---- 基本參數 -------------------------------------------------------
    rate = shared.get("recovery_rate_per_5min") or 0
    if rate <= 0:
        raise PlanError("自然回復速率必須大於 0")
    per_day_recovery = rate * TICKS_PER_DAY

    cap = profile.get("stamina_cap")
    if not cap or cap <= 0:
        raise PlanError("體力上限必須大於 0")

    reset = parse_clock(shared.get("daily_reset_time"), "05:00")
    window = shared.get("active_window") or {}
    act_start = parse_clock(window.get("start"), "06:00")
    act_end = parse_clock(window.get("end"), "21:30")
    weekly_reset = shared.get("weekly_reset") or {}
    weekly_weekday = int(weekly_reset.get("weekday", 0) or 0) % 7
    monthly_reset = shared.get("monthly_reset") or {}
    monthly_day = max(1, min(28, int(monthly_reset.get("day", 1) or 1)))

    today = task_day_of(query_dt, reset)

    # ---- 活動 -----------------------------------------------------------
    raw_events = list(shared.get("events") or [])
    if not raw_events:
        raise PlanError("尚未設定任何活動")
    events = []
    # 已結束／已封存的活動不排，但紀錄裡打過的照樣要認——本週前幾天打在
    # 舊活動上的體力，一樣算進「每週消耗體力」的進度（見下面的 all_levels）。
    past_events = []
    for raw in raw_events:
        start_dt, end_dt = event_bounds(raw)
        ended = end_dt <= query_dt and not is_standing(raw)
        if ended or is_archived(raw):
            # 限期關卡的舊檔次會一直留著、封存的是使用者自己收起來的，
            # 每次都報「已結束」只是噪音
            if not is_limited(raw) and not is_archived(raw):
                warnings.append(
                    f"「{event_label(raw)}」已於 {end_dt:%m/%d %H:%M} 結束，不列入排程")
            past_events.append({"id": raw.get("id"), "name": event_label(raw),
                                "raw": raw, "start_dt": start_dt, "end_dt": end_dt})
            continue
        # 限期關卡「結束當天不打」：排程只排到前一個任務日結束（當天的重置時刻）。
        # 只有「排程能不能打」用它；紀錄歸屬、截止提示照用真正的結束時刻，
        # 最後一天早上真的打了也照樣算進這一檔。
        plan_end_dt = end_dt
        if is_limited(raw) and raw.get("skip_last_day"):
            cut = min(end_dt, datetime.combine(end_dt.date(), reset))
            if cut <= start_dt:
                warnings.append(f"「{event_label(raw)}」這一期只開一天，"
                                "「結束當天不打」沒有作用")
            else:
                plan_end_dt = cut
                warnings.append(
                    f"「{event_label(raw)}」設了結束當天不打：{end_dt:%m/%d} 不排它，"
                    f"次數要在 {cut - timedelta(days=1):%m/%d} 前打完（下一期照常）")
        events.append({
            "id": raw.get("id"),
            "name": event_label(raw),
            "type": raw.get("type") or "current",
            "standing": is_standing(raw),
            "limited": is_limited(raw),
            # 積分獎勵表的封頂（加成後）。None＝沒有上限。
            "points_cap": (None if raw.get("points_cap") is None
                           else max(0, int(raw["points_cap"]))),
            # 「盡量提早」的日期與開關（見 EARLY_WEIGHT）。None＝不提早。
            "early_date": _iso_date(raw.get("early_finish_date")),
            "early_takes_surplus": raw.get("early_takes_surplus") is not False,
            "raw": raw,
            "start": start_dt.date(),
            "end": end_dt.date(),
            "start_date": start_dt.date().isoformat(),
            "end_date": end_dt.date().isoformat(),
            "start_dt": start_dt,
            "end_dt": end_dt,
            "plan_end_dt": plan_end_dt,
        })
    events_by_id = {ev["id"]: ev for ev in events}
    # 起訖時刻連過去的活動也查得到：量紀錄時要知道「打的當下那檔開沒開」
    bounds_by_id = {ev["id"]: ev for ev in events + past_events}
    # 排程範圍、活動優先序、特殊日的「第 N 天」都只看真正的活動；
    # 常駐關卡沒有起訖日、限期關卡的起訖日跟活動無關，拿它們當基準都不對。
    real_events = [ev for ev in events
                   if not ev["standing"] and not ev["limited"]]
    if not events:
        raise PlanError("尚未設定任何活動或常駐關卡")

    # ---- 關卡：把各活動的關卡攤平成一張表 -------------------------------
    # 「這次計算要不要算」是各帳號獨立的開關（關卡本身所有帳號共用，但這一檔活動
    # 哪幾關開放、哪幾關這個帳號要打，逐帳號不同）。沒設定的一律視為要算。
    multi = len(events) > 1
    levels, excluded, all_levels, points_all = _flatten_levels(
        events, past_events, profile)
    if not levels:
        # 兩種原因要分開講——訊息指錯方向比沒有訊息還糟
        if excluded:
            raise PlanError(
                "所有關卡都被設成「這次不算」，沒有東西可以排。\n"
                "請到「活動設定」的關卡結構，把這次要打的關卡勾回「計算」。")
        raise PlanError(
            "還沒有任何活動填了關卡，沒有東西可以排。\n"
            "請到「活動設定」至少填一關。\n"
            "（單獨一檔活動可以沒有自己的關卡——像任務只有「累計消耗體力」的"
            "音像活動——但總得有某一檔有關卡可以打。）")
    if excluded:
        warnings.append(
            "這次計算沒有算進這些關卡（在關卡結構取消了「計算」）："
            + "、".join(lv["label"] for lv in excluded))
    for lv in levels:
        if lv["stamina_cost"] <= 0:
            raise PlanError(f"「{lv['label']}」的消耗體力必須大於 0")
    n_levels = len(levels)
    level_index = {lv["key"]: i for i, lv in enumerate(levels)}
    costs = [lv["stamina_cost"] for lv in levels]
    enemies_of = [lv["enemies"] for lv in levels]
    drops_of = [int(lv.get("drops") or 0) for lv in levels]
    points_of = [lv["points"] for lv in levels]

    # ---- 排程天數 -------------------------------------------------------
    # 常駐關卡不參與：它沒有結束日，算進來排程就變成無限長了。
    first_start = min((ev["start"] for ev in real_events), default=today)
    event_end = max((ev["end"] for ev in real_events), default=None)
    sched_start = max(first_start, today)
    last_end = event_end
    if plan_until is not None:
        last_end = plan_until if last_end is None else max(last_end, plan_until)
    if last_end is None:
        raise PlanError(
            "目前沒有任何活動在進行。\n"
            "請在計算頁的「排到」填一個日期，排程才知道要排到哪一天——\n"
            "這段空窗期只會排固定任務，用常駐關卡去達成。")
    if sched_start > last_end:
        raise PlanError(
            f"「排到」的日期（{last_end:%Y-%m-%d}）在排程首日"
            f"（{sched_start:%Y-%m-%d}）之前，沒有東西可以排"
            if plan_until is not None else
            f"所有活動已於 {last_end:%Y-%m-%d} 結束")
    # primary 是各種「相對起始日」的基準（限時體力的週次、體力來源的偏移量、
    # 特殊日的 fallback）。常駐關卡沒有起訖日，不能拿它當基準。
    primary = real_events[0] if real_events else {
        "id": None, "name": "（目前沒有活動）",
        "start": sched_start, "end": last_end,
    }
    days = [sched_start + timedelta(days=i)
            for i in range((last_end - sched_start).days + 1)]
    n_days = len(days)

    # ---- 盡量提早 -------------------------------------------------------
    # 設了日期的活動：那天之前（不含當天）盡量把它的積分拿完。依開關分兩組，
    # 兩組在求解裡的位置不同（見 build_and_solve 的提早階段）。
    early_first, early_after = [], []
    for event in real_events:
        target = event["early_date"]
        if target is None:
            continue
        indices = [i for i in range(n_levels)
                   if levels[i]["event_id"] == event["id"] and points_of[i]]
        if not indices:
            continue
        before = [d for d in range(n_days) if days[d] < target]
        if not before or target > event["end"]:
            warnings.append(
                f"「{event['name']}」的「盡量提早」日期 {target:%m/%d} "
                + ("已經到了" if not before else "在活動結束之後")
                + "，這次沒有作用")
            continue
        entry = {"event": event, "date": target, "days": before, "levels": indices}
        (early_first if event["early_takes_surplus"] else early_after).append(entry)
    early_note = {}

    # ---- 每天切成幾段 ---------------------------------------------------
    # 一個「任務日」從重置時刻算到隔天同一時刻，中間只有「上線時段」會打關卡；
    # 其餘時間（睡覺）只累積回復。睡覺期間回復到超過上限的部分會浪費掉，
    # 所以睡前的體力必須壓在「上限 − 睡覺期間回復量」以下。
    #
    # 活動的起訖時刻（下午三點開始、中午十二點結束）也是切點：那之前／之後
    # 就打不到這檔活動的關卡了。只有活動起訖日會多切一刀，其他日子照舊三段。
    def day_bounds(day: date):
        begin = datetime.combine(day, reset)
        finish = begin + timedelta(days=1)
        active_from = datetime.combine(day, act_start)
        active_to = datetime.combine(day, act_end)
        if active_from < begin:       # 上線時段落在重置之後的隔天凌晨
            active_from += timedelta(days=1)
            active_to += timedelta(days=1)
        if active_to <= active_from:  # 跨過午夜的上線時段
            active_to += timedelta(days=1)
        return begin, finish, max(active_from, begin), min(active_to, finish)

    def build_segments(day: date, since: datetime | None):
        begin, finish, active_from, active_to = day_bounds(day)
        start = max(begin, since) if since else begin
        if start >= finish:
            return []
        cuts = {start, finish}
        for moment in (active_from, active_to):
            if start < moment < finish:
                cuts.add(moment)
        # 過去的活動也要切、也要進 live：排程開始前的日子（segments_on 現算）
        # 開著的是它們。
        for event in events + past_events:
            for moment in (event["start_dt"], event["end_dt"],
                           event.get("plan_end_dt", event["end_dt"])):
                if start < moment < finish:
                    cuts.add(moment)
        points = sorted(cuts)

        def ticks(moment):
            # 累進計算，段與段之間不會因為各自取整而多算或少算
            return int(rate * (moment - start).total_seconds() / 60.0 / 5)

        # 加班時段：查詢時間已經過了今天的上線時段（但還沒到每日重置）。人其實還
        # 醒著，今天剩下的時間只拿來補完今天還沒完成的任務（見「加班階段」）。
        overtime = since is not None and since >= active_to
        segments = []
        for lo, hi in zip(points, points[1:]):
            live = {ev["id"] for ev in events + past_events
                    if ev["start_dt"] <= lo
                    and hi <= ev.get("plan_end_dt", ev["end_dt"])}
            segments.append({
                "lo": lo, "hi": hi,
                "recovery": ticks(hi) - ticks(lo),
                "playable": overtime or (lo >= active_from and hi <= active_to),
                "overtime": overtime,
                "live": live,
                "before_bed": hi <= active_to,
                # 整段落在當天開工之前：這段的回復其實是前一晚「過夜」的尾巴
                "before_open": hi <= active_from,
            })
        return segments

    segments = []
    for day in days:
        since = query_dt if day == today else None
        segments.append(build_segments(day, since))
    recovery = [sum(seg["recovery"] for seg in day_segs) for day_segs in segments]
    # 每天的「收工」是最後一個還在上線時段內的段落結束時
    bed_index = []
    for day_segs in segments:
        idx = None
        for s, seg in enumerate(day_segs):
            if seg["before_bed"]:
                idx = s
        bed_index.append(idx)

    playable_of = [[bool(seg["playable"] and any(
        lv["event_id"] in seg["live"] for lv in levels)) for seg in day_segs]
        for day_segs in segments]
    no_play_today = days[0] == today and not any(playable_of[0])
    # 今天已經過了上線時段、還有加班時段可以補任務（見 build_segments）
    overtime_cells = [(0, s) for s, seg in enumerate(segments[0])
                      if seg["overtime"] and playable_of[0][s]] if days else []

    def live_segments(event_id: str | None, d: int) -> list[int]:
        """那一天有哪幾段是這檔活動還開著的。固定任務（event_id 為 None）＝整天。

        活動任務只計入這幾段。「累計消耗體力」這種任務的關卡範圍是**跨活動**的
        （打別檔活動的關卡也會累積），但時間範圍不是——音像活動下午三點才開，
        當天早上打舊活動花掉的體力它根本不會記錄到。
        """
        if event_id is None:
            return list(range(len(segments[d])))
        return [s for s, seg in enumerate(segments[d]) if event_id in seg["live"]]

    def live_playable(event_id: str | None, d: int) -> list[int]:
        """上面那些段落裡，真的打得到關卡的（在上線時段內、而且有關卡可打）。"""
        return [s for s in live_segments(event_id, d) if playable_of[d][s]]

    _segments_cache: dict[date, list] = {}

    def segments_on(day: date) -> list:
        """那一天切成哪幾段。

        排程內的直接用開頭算好的那份；排程**開始之前**的現算——週期任務要回頭
        量「本期已經做掉多少」，那幾天沒有索引可以查。
        """
        idx = (day - sched_start).days
        if 0 <= idx < n_days:
            return segments[idx]
        if day not in _segments_cache:
            _segments_cache[day] = build_segments(day, None)
        return _segments_cache[day]

    def live_filter(event_id: str | None):
        """「這一筆打法算不算進這檔活動的任務」，給 measure 用（見 _live_filter）。"""
        return _live_filter(event_id, events_by_id, bounds_by_id)
    if no_play_today:
        warnings.append(
            f"查詢時間 {query_dt:%H:%M} 已經超過當日上線時段"
            f"（{act_start:%H:%M}~{act_end:%H:%M}）或所有活動的可打時段，"
            f"{days[0]:%m/%d} 不安排關卡，體力只會累積到隔天")
    elif overtime_cells:
        warnings.append(
            f"查詢時間 {query_dt:%H:%M} 已經超過當日上線時段"
            f"（{act_start:%H:%M}~{act_end:%H:%M}），{days[0]:%m/%d} 只排補完今天"
            f"還沒完成的任務需要的量（{reset:%H:%M} 每日重置前打完）；沒有要補的就不排")
    # 活動當天才開打／當天中午截止，提醒使用者那幾天有時間壓力。
    # 沒有自己關卡的活動（任務只有累計耗體的音像活動）不必提醒——
    # 它根本沒有「排不到」或「要在中午前打完」的東西。
    events_with_levels = {lv["event_id"] for lv in levels}
    for event in events:
        # 限期關卡只是「有多的體力才打」的上限，換檔是常態，沒有時間壓力可言
        if event["id"] not in events_with_levels or event["limited"]:
            continue
        if sched_start <= event["start_dt"].date() <= last_end and multi:
            warnings.append(
                f"「{event['name']}」{event['start_dt']:%m/%d %H:%M} 才開始，"
                "那天之前排不到它的關卡")
        if sched_start <= event["end"] <= last_end:
            warnings.append(
                f"「{event['name']}」{event['end_dt']:%m/%d %H:%M} 結束，"
                f"{event['end_dt']:%m/%d} 當天要在 {event['end_dt']:%H:%M} 之前打完")

    # 活動還沒開始時，從查詢時間到排程首日之間也會回復（頂到上限就不再累積）
    sched_start_dt = datetime.combine(sched_start, reset)
    if sched_start_dt > query_dt:
        pre_minutes = (sched_start_dt - query_dt).total_seconds() / 60.0
        initial_stamina = min(cap, current_stamina + int(rate * pre_minutes / 5))
    else:
        initial_stamina = current_stamina

    # ---- 已經做掉的量 ---------------------------------------------------
    # 任務的剩餘量要扣掉紀錄裡已經完成的部分。關卡用**全部**關卡算，不是過濾後的：
    # 某一關這次不列入計算，但真的打了就照樣佔掉當天的額度。
    def entries_between(first: date | None, last: date | None):
        rows = []
        for entry in log_entries:
            try:
                day = datetime.strptime(entry.get("date"), "%Y-%m-%d").date()
            except (TypeError, ValueError):
                continue
            if first and day < first:
                continue
            if last and day > last:
                continue
            rows.append(entry)
        return rows

    def measure(entries, metric: str, scope: set[str] | None, live=None) -> int:
        return _measure(entries, metric, scope, all_levels, points_all, live)

    # 開始記錄之前就打過的次數當成起點（見 baseline_level_counts）
    played_total: dict[str, int] = baseline_level_counts(profile.get("events"))
    for entry in log_entries:
        for key, count in (entry.get("counts") or {}).items():
            try:
                count = max(0, int(count or 0))
            except (TypeError, ValueError):
                continue
            played_total[key] = played_total.get(key, 0) + count

    # 今天已經打掉的（只有排程首日就是今天時才要扣）
    today_entries = (entries_between(today, today)
                     if days[0] == today and not no_play_today else [])
    done_counts: dict[str, int] = {}
    for entry in today_entries:
        for key, count in (entry.get("counts") or {}).items():
            try:
                count = max(0, int(count or 0))
            except (TypeError, ValueError):
                continue
            if count:
                done_counts[key] = done_counts.get(key, 0) + count
    done_label = "、".join(
        f"{(all_levels.get(k) or {}).get('label', k)}×{v}"
        for k, v in done_counts.items())

    # ---- 特殊日規則（全域） ---------------------------------------------
    usage_cap: dict[int, int] = {}
    # (第幾天, 活動 id) -> 那天花在該活動關卡上的體力上限。
    # 跟 usage_cap 的差別是它只管一檔活動：某一天早上舊活動收尾、下午新活動開打時，
    # 「舊活動只再花 140」跟「當天總共只花 140」是兩件完全不同的事。
    event_cap: dict[tuple[int, str], int] = {}
    # 第幾天 -> (當天結束的活動 id, 合計上限)。見 "ending_cap_override"。
    ending_cap: dict[int, tuple[frozenset, int]] = {}
    min_clears_override: dict[int, int] = {}
    min_enemies_override: dict[int, int] = {}
    min_stamina_override: dict[int, int] = {}

    # 先把明確的特殊日規則落到哪一天算出來：(entry, 第幾天, 日期, 依據活動, 是否預設)
    resolved = []
    for entry in profile.get("special_days") or []:
        try:
            offset = int(entry.get("day_offset"))
        except (TypeError, ValueError):
            continue
        # 「第 N 天」是相對哪一檔活動算的。那檔活動已經結束（或被刪掉）就沒有
        # 基準可用——默默改掛到別檔活動上，規則會落在完全不相干的日子。
        ref_id = entry.get("event_id")
        ref = events_by_id.get(ref_id) if ref_id else primary
        if (ref is None or ref.get("id") is None or ref.get("standing")
                or ref.get("limited")):
            where = (f"{storage_event_name(shared, ref_id)} 第 {offset} 天"
                     if ref_id else f"第 {offset} 天")
            warnings.append(
                f"特殊日規則（{where}）依據的活動已經結束或沒有起訖日，"
                "算不出是哪一天，已略過")
            continue
        day = resolve_day_offset(offset, ref["start"], ref["end"])
        if day < sched_start or day > last_end:
            warnings.append(
                f"特殊日規則（{ref['name']} 第 {offset} 天 → {day:%m/%d}）"
                "不在剩餘排程範圍內，已略過")
            continue
        resolved.append((entry, (day - sched_start).days, day, ref, False))

    # 再展開「每檔活動自動套用的規則」：每一檔符合類型的活動各套一次。
    # 同一天同類型已經有明確規則就讓它（明確的蓋過預設，不是取小）；
    # 兩檔同一天結束也只套一次。活動已經結束、落在範圍外就靜默略過——
    # 自動套用的規則本來就會碰到這種檔次，每次都報只是噪音。
    taken = {special_rule_key(idx, entry.get("type"), ref["id"])
             for entry, idx, _day, ref, _d in resolved}
    for rule in profile.get("event_default_rules") or []:
        try:
            offset = int(rule.get("day_offset"))
        except (TypeError, ValueError):
            continue
        for ref in real_events:
            if not default_rule_applies(rule, ref["type"]):
                continue
            day = resolve_day_offset(offset, ref["start"], ref["end"])
            if day < sched_start or day > last_end:
                continue
            idx = (day - sched_start).days
            key = special_rule_key(idx, rule.get("type"), ref["id"])
            if key in taken:
                continue
            taken.add(key)
            resolved.append(({**rule, "event_id": ref["id"]}, idx, day, ref, True))

    for entry, idx, day, ref, is_default in resolved:
        offset = entry.get("day_offset")
        kind = entry.get("type")
        if kind == "stamina_cap_override":
            value = int(entry.get("value") or 0)
            usage_cap[idx] = min(usage_cap.get(idx, value), value)
        elif kind == "daily_min_override":
            value = max(0, int(entry.get("value") or 0))
            # 同一天填了多筆就取最寬鬆的，免得自己把自己卡死
            min_clears_override[idx] = min(min_clears_override.get(idx, value), value)
        elif kind == "daily_enemy_min_override":
            value = max(0, int(entry.get("value") or 0))
            min_enemies_override[idx] = min(min_enemies_override.get(idx, value),
                                            value)
        elif kind == "daily_stamina_min_override":
            value = max(0, int(entry.get("value") or 0))
            min_stamina_override[idx] = min(min_stamina_override.get(idx, value),
                                            value)
        elif kind == "event_cap_override":
            # 上限套在哪一檔活動，就是「第 N 天」依據的那一檔——欄位只有一個，
            # 兩個意思共用。ref 已經在上面補過預設值了。
            value = max(0, int(entry.get("value") or 0))
            key = (idx, ref["id"])
            event_cap[key] = min(event_cap.get(key, value), value)
        elif kind == "ending_cap_override":
            # 當天結束的活動（當期／復刻）合計。依據的活動只用來決定是哪一天——
            # 收尾那天下午常有新活動開打，不能跟著被卡住（那是 usage_cap 的事）。
            value = max(0, int(entry.get("value") or 0))
            group = frozenset(ev["id"] for ev in real_events if ev["end"] == day)
            if not group:
                if not is_default:
                    warnings.append(
                        f"特殊日規則「當日結束活動體力上限」（{ref['name']} 第 {offset} 天"
                        f" → {day:%m/%d}）：那天沒有活動結束，已略過")
                continue
            old = ending_cap.get(idx)
            ending_cap[idx] = (group, value if old is None else min(old[1], value))

    def event_room(d: int, eid: str):
        """那天那檔活動最多花多少體力（單檔上限與「當日結束活動」上限取小）。"""
        caps = []
        if (d, eid) in event_cap:
            caps.append(event_cap[(d, eid)])
        if d in ending_cap and eid in ending_cap[d][0]:
            caps.append(ending_cap[d][1])
        return min(caps) if caps else None

    # ---- 任務 → 限制條件 ------------------------------------------------
    task_states = profile.get("task_state") or {}
    profile_events = profile.get("events") or {}

    def window_indices(first: date, last: date) -> list[int]:
        return [d for d in range(n_days) if first <= days[d] <= last]

    def scope_of(task: dict, owner: dict | None) -> tuple[set[str] | None, list[int]]:
        """(給紀錄用的關卡鍵集合, 給求解用的關卡索引)。"""
        keys = _scope_keys(task, owner["id"] if owner else None, all_levels)
        return keys, sorted(level_index[k] for k in keys if k in level_index)

    def derived_progress(task, owner, metric, keys, default_scope) -> int:
        """活動任務「已經完成多少」。

        預設範圍的積分/關卡數直接用設定檔推導好的欄位（跟畫面一致），
        自訂範圍的才從紀錄現算，並加上任務自己的起始值。

        耗體不能照辦：`current_stamina_spent` 是**全域**的累計值（跨活動共用，
        見 storage 的註解），拿來當某一檔活動的進度，會把別檔活動花掉的體力
        算進來——新活動的「累計消耗體力」一建立就自動達成。所以只算那檔活動
        起始日之後的紀錄，再加上任務自己的起始值。
        """
        state = task_states.get(task["_key"]) or {}
        baseline = int(state.get("baseline") or 0)
        if default_scope and owner is not None and metric in EVENT_COUNTED_METRICS:
            # 活動預設範圍：起始值看「活動設定」那檔活動的起始耗體／敵人／道具，
            # 任務自己的起始值只給指定了關卡的任務用
            baseline = event_baseline(profile_events.get(owner["id"]), metric)
        if default_scope and owner is not None and metric == "points":
            return int((profile_events.get(owner["id"]) or {}).get("current_points") or 0)
        if default_scope and owner is not None and metric == "clears":
            return int((profile_events.get(owner["id"]) or {}).get("current_clears") or 0)
        # 敵人數跟耗體一樣是跨活動累計的（預設範圍＝全部關卡），同一個洞：
        # 不限日期的話，別檔活動、甚至活動開始前殺的敵人都會算進來。
        if default_scope and metric in ("stamina", "enemies") and owner is not None:
            return baseline + measure(entries_between(owner["start"], None),
                                      metric, keys,
                                      live=live_filter(owner["id"]))
        if default_scope and metric == "drops" and owner is not None:
            # 預設範圍＝這檔活動有填道具數量的關卡，紀錄全部算（別檔的關卡本來就不在範圍裡）
            return baseline + measure(log_entries, metric, keys)
        if default_scope and metric == "stamina":
            # 固定任務不走這條（週期任務另有視窗），保險用
            return int(profile.get("current_stamina_spent") or 0)
        return baseline + measure(log_entries, metric, keys)

    # 固定任務不屬於任何一檔活動，「只算這段期間」那兩格以它為基準
    overall_span = _overall_span(shared)
    # 「預設完成」的任務被標記成沒做到的那幾天，獎勵不入帳
    missed_days = {key: set(days)
                   for key, days in _missed_by_task(log_entries).items()}

    constraints = []       # 送進求解器的
    # 整檔活動的積分任務已經達成的活動。那條任務不會送進 constraints，但積分的
    # 天花板（build_and_solve 的 ceiling）還是要認得它：不然天花板會退回「積分
    # 上限」，求解器以為還能多拿分，就把用不完的體力拿去刷一檔早已達標的活動。
    met_points_events: set = set()
    task_rows = []         # 報表用的
    for task, owner, key in iter_tasks(shared):
        task = dict(task)
        task["_key"] = key
        state = task_states.get(key) or {}
        if state.get("enabled") is False:
            continue
        if owner is not None:
            # iter_tasks 給的是設定檔裡的原始活動，換成已經解析好日期的那份
            owner = events_by_id.get(owner.get("id"))
            if owner is None:
                continue      # 活動已結束或沒列入這次排程
        amount = state.get("amount_override")
        amount = int(amount) if amount not in (None, "") else int(task.get("amount") or 0)
        metric = task.get("metric")
        cycle = task.get("cycle")
        row = {"key": key, "name": task.get("name") or key, "cycle": cycle,
               "metric": metric, "amount": amount,
               "event_id": owner["id"] if owner else None,
               "event_name": owner["name"] if owner else None,
               "rewards": task.get("rewards") or [], "windows": [],
               "assume_done": bool(task.get("assume_done")),
               "missed": sorted(missed_days.get(key) or ())}
        task_rows.append(row)
        # 要不要送進求解器。manual 與沒勾「當成條件」的只做進度與獎勵統計，
        # 但**視窗照樣算**——獎勵總表要知道這段期間會做幾次。
        enforce = bool(task.get("enforce")) and metric != "manual" and amount > 0
        row["enforce"] = enforce

        default_scope = not task.get("scope")
        keys, indices = scope_of(task, owner)
        if (enforce and metric == "drops"
                and not any(drops_of[i] for i in indices)):
            # 沒有一關拿得到道具的話，這條送進求解器只會得到一句「無解」
            warnings.append(
                f"任務「{row['name']}」要取得道具，但範圍內這次有算的關卡都沒有填"
                "「取得道具」的數量，已略過。請到「活動設定」的關卡結構填上")
            enforce = False
            row["enforce"] = False
        if enforce and metric in ("clears", "points", "enemies") and not indices:
            warnings.append(f"任務「{row['name']}」指定的關卡這次都沒有列入計算，已略過")
            enforce = False
            row["enforce"] = False

        if cycle == "event":
            if owner is None:
                warnings.append(f"固定任務「{row['name']}」的週期是「活動」，無法對應到"
                                "哪一檔活動，已略過")
                continue
            deadline = resolve_day_offset(int(task.get("deadline_offset", -1)),
                                          owner["start"], owner["end"])
            done = derived_progress(task, owner, metric, keys, default_scope)
            remaining = amount - done
            label = f"{deadline:%m/%d} 前"
            win = {"need": max(0, remaining), "done": done, "days": [],
                   "label": label, "met": remaining <= 0}
            row["windows"].append(win)
            if not enforce:
                continue
            if remaining <= 0:
                if metric == "points" and default_scope:
                    met_points_events.add(owner["id"])
                # 講出來——不然使用者會以為這條被漏掉了
                warnings.append(
                    f"任務「{row['name']}」的目標 {amount} 已經達成"
                    f"（目前 {done}），不再是限制")
                continue
            if deadline < sched_start:
                warnings.append(
                    f"任務「{row['name']}」的期限（{deadline:%m/%d}）已經過了，"
                    f"目前 {done} / {amount}，已略過這條限制")
                continue
            win["days"] = window_indices(sched_start, deadline)
            win["met"] = False
            # whole_event：這條的 need 是「整檔活動累計還要再拿多少」。積分的
            # 天花板（build_and_solve 的 ceiling）要靠這個鍵認出它——下面週期性
            # 任務那條是「每個重置窗一條」，need 只是單一視窗的量，拿來當上界
            # 會把模型壓爛。不要改用 soft_ok 代替，那個鍵講的是「可不可以降級」。
            constraints.append({"row": row, "metric": metric, "levels": indices,
                                "days": win["days"], "need": remaining,
                                "event_id": row["event_id"], "soft_ok": True,
                                "whole_event": True,
                                "default_scope": default_scope, "label": label})
            continue

        # 週期性任務：先算出每一個「重置窗」涵蓋哪幾天。
        # 固定任務也吃「只算這段期間」那兩格（基準是所有活動涵蓋的期間）。
        span = _task_span(task, owner, overall_span)
        if span is None:
            first, last = sched_start, last_end
        else:
            base, from_offset, to_offset = span
            first = offset_from_start(from_offset, base)
            last = offset_from_start(to_offset, base)
            if last < first:
                first, last = last, first
        declared_first, declared_last = first, last
        first = max(first, sched_start)
        last = min(last, last_end)
        if last < first:
            continue
        # 規則跨過今天時，前面那段已經排不了了——講出來，免得使用者以為漏算。
        # 只對自己填了「只算這段期間」的任務講：沒填的期間是程式推出來的
        # （整檔活動、或所有活動涵蓋的範圍），每條固定任務都報一次只是雜訊。
        own_period = any(task.get(key) is not None and task.get(key) != ""
                         for key in ("from_date", "to_date",
                                     "from_offset", "to_offset"))
        if own_period and declared_first < sched_start:
            past = (min(sched_start, declared_last + timedelta(days=1))
                    - declared_first).days
            if past > 0:
                warnings.append(
                    f"任務「{row['name']}」的期間"
                    f"（{declared_first:%m/%d}~{declared_last:%m/%d}）有 {past} 天"
                    f"已經過了，只有剩下的 {(last - first).days + 1} 天會納入計算")
        for win_first, win_last in _reset_windows(cycle, first, last,
                                                  weekly_weekday, monthly_day):
            day_idx = window_indices(win_first, win_last)
            if not day_idx:
                continue
            # 特殊日的「當日最低關卡數／敵人數」是**覆蓋**每日任務的要求，
            # 那是拿來解「當天體力上限太低、湊不滿關數」這種死結的逃生口。
            # 只蓋每天重置的任務：每週／每月任務的重置窗在排程裡剛好只剩一天時
            # （週日、排程最後一天），不能被「當日」的覆蓋值換掉。
            need_amount = amount
            if (default_scope and len(day_idx) == 1
                    and cycle in ("daily", "guild")):
                d = day_idx[0]
                if metric == "clears" and d in min_clears_override:
                    need_amount = min_clears_override[d]
                elif metric == "enemies" and d in min_enemies_override:
                    need_amount = min_enemies_override[d]
                elif metric == "stamina" and d in min_stamina_override:
                    need_amount = min_stamina_override[d]
            # 這個窗已經做掉的部分要扣掉。量的是**整個重置窗**、不是只有排程內
            # 那幾天——本期已經過掉的日子（今天是週日的話就是前六天）也算數，
            # 否則一條早就達成的每週任務會被當成「這週還沒開始做」，整份量壓到
            # 最後一天，還會變成「當日至少 N」的硬下限。
            # live_filter 負責「活動任務只算那檔活動開著的時候打的」。
            done = (measure(entries_between(win_first, win_last), metric, keys,
                            live=live_filter(row["event_id"]))
                    + period_done_before(state, win_first))
            remaining = max(0, need_amount - done)
            label = (format_day(win_first) if win_first == win_last
                     else f"{win_first:%m/%d}~{win_last:%m/%d}")
            row["windows"].append({"need": remaining, "done": done,
                                   "days": day_idx, "label": label,
                                   "met": remaining <= 0})
            if not enforce or remaining <= 0:
                continue
            if no_play_today and day_idx == [0]:
                warnings.append(
                    f"{format_day(days[0])} 的「{row['name']}」還差 {remaining}，"
                    "但今天的上線時段已經過了，這條略過")
                continue
            constraints.append({"row": row, "metric": metric, "levels": indices,
                                "days": day_idx, "need": remaining,
                                "event_id": row["event_id"], "soft_ok": False,
                                "default_scope": default_scope, "label": label})

    # ---- 每條限制條件涵蓋哪些「日×段」 ----------------------------------
    # 活動任務只計入那檔活動還開著的段落（見 live_segments）。求解、報表、
    # 衝突檢查共用這一份，三邊的尺才會一樣。
    kept = []
    for spec in constraints:
        spec["cells"] = [(d, s) for d in spec["days"]
                         for s in live_segments(spec["event_id"], d)]
        if any(playable_of[d][s] for d, s in spec["cells"]):
            kept.append(spec)
            continue
        # 那段期間沒有一刻是「活動開著、又在上線時段內、又有關卡可打」的。
        # 送進模型只會得到一句「無解」，不如在這裡講清楚是哪一條。
        row = spec["row"]
        owner = row.get("event_name") or ""
        warnings.append(
            f"{spec['label']} 的{owner}「{row['name']}」還差 {spec['need']}，"
            "但那段期間沒有一個時段是這檔活動開著、而且在上線時段內有關卡可打的，"
            "這條略過")
    constraints = kept

    # 活動頭尾那天只開半天，每日任務卻仍然要求整份量——照算，但要講出來。
    for spec in constraints:
        if len(spec["days"]) != 1 or spec["event_id"] is None:
            continue
        d = spec["days"][0]
        live = live_playable(spec["event_id"], d)
        playable = [s for s in range(len(segments[d])) if playable_of[d][s]]
        if not live or len(live) == len(playable):
            continue
        row = spec["row"]
        lo = f"{segments[d][live[0]]['lo']:%H:%M}"
        hi = f"{segments[d][live[-1]]['hi']:%H:%M}"
        # 活動第一天＝中途才開（從幾點開始）；活動最後一天＝提早收（只開到幾點）。
        late_start = live[0] > playable[0]
        early_end = live[-1] < playable[-1]
        if late_start and not early_end:
            when = f"從 {lo} 才開始（{lo}~{hi}）"
        elif early_end and not late_start:
            when = f"只開到 {hi}（{lo}~{hi}）"
        else:
            when = f"只開 {lo}~{hi}"
        warnings.append(
            f"{format_day(days[d])} 的「{row['name']}」要求 {spec['need']}，"
            f"但當天「{row['event_name']}」{when}，"
            "只有這段時間內打的才算數。真的做不到的話，用特殊日的"
            "「當日最低耗體」或任務的「只算這段期間」把那天排除")

    # 使用者可能同時手填了體力來源、又把同一條任務的獎勵填進任務裡，
    # 兩邊都算就會憑空多出體力。
    reward_sources = task_reward_sources(shared, profile, missed_days,
                                         _done_by_task(log_entries))
    orphan_sources: list[dict] = []
    manual_sources = resolved_sources(shared, profile, orphan_sources)
    if orphan_sources:
        warnings.append(
            f"「體力來源」有 {len(orphan_sources)} 筆依據的活動已經被刪掉或沒有起始日"
            f"（共 {sum(int(src.get('amount') or 0) for src in orphan_sources)} 點／次），"
            "算不出是哪一天，已略過。請到「排程設定」把那幾筆改成"
            "「不依據活動」或重新選一檔活動")
    if reward_sources:
        # 一、preset 一看就是任務的（每日／每週任務、每日簽到）
        TASK_PRESETS = {"daily_task": "每日任務", "weekly_task": "每週任務",
                        "checkin": "每日簽到"}
        clashing = {TASK_PRESETS[src["preset"]] for src in manual_sources
                    if src.get("preset") in TASK_PRESETS}
        # 二、單次點數跟某條任務的獎勵總量一樣——這只是推測，講清楚別講死
        reward_amounts = {src["amount"]: src.get("task_name") or src["task_key"]
                          for src in reward_sources}
        for src in manual_sources:
            if src.get("preset") in TASK_PRESETS:
                continue
            name = reward_amounts.get(int(src.get("amount") or 0))
            if name:
                clashing.add(f"{source_label(src)}（每次 {src['amount']} 點，"
                             f"像是「{name}」）")
        if clashing:
            warnings.append(
                "「體力來源」裡可能還留著跟任務獎勵重複的手填項目："
                + "、".join(sorted(clashing))
                + "。任務獎勵已經自動變成體力來源，兩邊都留會多算一次體力——"
                  "請自己確認一下，重複的話刪掉其中一邊")

    # 月卡是真實世界的 30 天，綁在某一檔活動上的話，日期會存成「相對那檔活動起
    # 始日的第幾天」——活動一結束月卡就不再發體力，那通常不是使用者的意思。
    CARD_PRESETS = {"big_card": "大月卡", "small_card": "小月卡"}
    bound_cards = []
    for card in manual_sources:
        label = CARD_PRESETS.get(card.get("preset"))
        if label and not source_is_absolute(card):
            grant_days = len(expand_stamina_sources([card], card.get("start_date")))
            bound_cards.append(f"{label}（只發 {grant_days} 天）")
    if bound_cards:
        warnings.append(
            "「體力來源」的" + "、".join(bound_cards)
            + "是綁在某一檔活動上的，日期存成相對那檔活動起始日的偏移量——"
              "活動一結束就不再發體力。月卡跟活動檔期無關，"
              "建議把那幾列的「依據哪一檔活動」改成「不依據活動」，直接填月卡的實際起訖日")

    # 有體力獎勵、達成條件程式算得出來、卻沒勾「算進排程計算」——
    # 排程會算你拿得到那筆體力，卻不保證排出達成它的打法，計畫會偏樂觀。
    stamina_of_item = item_stamina_table(shared)
    for row in task_rows:
        if row["enforce"] or row["metric"] == "manual":
            continue
        per_time = sum(stamina_of_item.get(r.get("item"), 0) * int(r.get("qty") or 0)
                       for r in row["rewards"])
        if per_time <= 0:
            continue
        times = len(row["windows"]) or 1
        warnings.append(
            f"「{row['name']}」有體力獎勵（這段期間共 {per_time * times} 點）"
            "但沒勾「算進排程計算」——排程會算你拿得到那筆體力，"
            "卻不保證排出達成它的打法。要嘛把它勾起來，要嘛把獎勵拿掉")

    # ---- 指定關卡的每日次數上限 -----------------------------------------
    # （例：多餘體力拿去打「經商貿易」，每天最多 3 次）
    # 這是「上限」不是「下限」——達成任務的計畫不會被迫去打它們，
    # 只有第三階段有多餘體力時才會安排，而且不超過這個次數。
    level_cap: dict[tuple[int, int], int] = {}
    # 難度規則（見 _stage_rule）：{"idx", "stages", "prior", "days"（不能打的那幾天）, "text"}
    stage_rules: list[dict] = []
    # 代幣關卡：{"idx", "start"（排程首日從現在起還有幾個）, "max", "per_day",
    # "days"（規則區間內的第幾天）}
    token_rules: list[dict] = []
    limited_ids ={ev["id"] for ev in events if ev["limited"]}
    for entry in profile.get("daily_level_rules") or []:
        key = entry.get("level_id")
        if key not in level_index:
            level = all_levels.get(key)
            if level is not None:
                warnings.append(
                    f"「{level['label']}」這次不列入計算，它的每日上限規則自動略過")
            else:
                warnings.append(
                    f"指定關卡的每日次數規則找不到關卡「{key}」，已略過"
                    "（可能是關卡被刪掉或改了 id）")
            continue
        idx = level_index[key]
        # 日期是絕對日期，不是相對活動起始日的偏移量——常駐關卡沒有起始日
        # 可以相對，而這種規則本來就跟著關卡走，換一檔活動它也跟著作廢。
        #
        # weekdays（可省略）：只在這幾個星期幾打。區間內其他日子上限 0。
        # 有勾星期幾時 max_count 可以留白＝那幾天不限次數——這時**不寫**
        # level_cap，所以也不會吃到「多餘體力優先塞指定關卡」的獎勵（designated），
        # 那幾天它就跟一般關卡一樣由求解器決定要不要打。
        # 起訖留白＝整個排程範圍（有勾星期幾的、常駐的基本關卡才給留白，
        # 畫面那邊擋；這裡留白一律照整個範圍算）。
        weekdays = {int(x) for x in entry.get("weekdays") or []}
        try:
            raw = entry.get("max_count", entry.get("min_count"))
            limit = None if raw is None and weekdays else int(raw or 0)
            first = (parse_date(entry["from_date"], "指定關卡規則的起始日")
                     if entry.get("from_date") else days[0])
            last = (parse_date(entry["to_date"], "指定關卡規則的結束日")
                    if entry.get("to_date") else days[-1])
        except (TypeError, ValueError, KeyError, PlanError):
            warnings.append(
                f"「{levels[idx]['label']}」的每日上限規則日期不完整，已略過")
            continue
        if last < first:
            first, last = last, first
        if entry.get("stages") or entry.get("stages_other"):
            # 難度規則：只限制那幾關（第幾次通關）落在哪幾個星期幾，不碰 level_cap
            # ——每日上限、優先獎勵照舊。約束在 build_and_solve 裡加（要等
            # 指定次數 level_target 建好，那幾天以指定次數為準）。
            rule = _stage_rule(entry, levels[idx], idx, weekdays,
                               played_total.get(key, 0), limited_ids, warnings)
            if rule is not None:
                rule["days"] = [d for d in window_indices(first, last)
                                if days[d].weekday() not in weekdays]
                if rule["days"]:
                    stage_rules.append(rule)
            continue
        tokens = token_spec(entry)
        if tokens is not None:
            # 代幣關卡：次數看當天手上有幾個代幣（約束在 build_and_solve 的
            # token_rules）。level_cap 填代幣上限——一天最多就打那麼多，而且這樣
            # 也會吃到「多餘體力優先塞指定關卡」的獎勵，代幣才會被打掉。
            start = token_stock(entry, log_entries, days[0])
            if days[0] == today:
                start -= _plays_by_day(log_entries, key).get(today, 0)
            token_rules.append({
                "idx": idx, "start": max(0, start), "max": tokens["max"],
                "label": levels[idx]["label"],
                "per_day": tokens["per_day"],
                "days": set(window_indices(first, last))})
            limit = tokens["max"]
        if limit is not None and limit <= 0 and not weekdays:
            continue
        for d in window_indices(first, last):
            if weekdays and days[d].weekday() not in weekdays:
                level_cap[(d, idx)] = 0
            elif limit is not None and limit > 0:
                level_cap[(d, idx)] = min(level_cap.get((d, idx), limit), limit)

    # ---- 怎麼打都湊不到的週期任務 ---------------------------------------
    # 每日／每週任務是硬條件。那段期間打得到的關卡全部打到上限還是湊不滿的話
    # （例：最後一天只剩一檔沒有關卡的音像活動，常駐關卡又不算通關次數），
    # 買再多體力也沒用，送進模型只會得到一句「無解」。這裡先算出上界，湊不到的
    # 講清楚是哪一天哪一條、直接略過——只湊一部分的每日任務沒有任何好處，
    # 硬去湊只是白花體力，所以不做成「差多少由求解器決定」。
    #
    # 上界只看「關卡打不打得到、每關的次數上限」，不看當日體力上限。
    unit_of = {"stamina": costs, "enemies": enemies_of, "drops": drops_of,
               "points": points_of}

    def reachable(spec) -> float:
        weight = unit_of.get(spec["metric"])
        total = 0
        for i in (range(n_levels) if spec["metric"] == "stamina"
                  else spec["levels"]):
            unit = weight[i] if weight else 1
            if not unit:
                continue
            open_days = {d for d, s in spec["cells"]
                         if playable_of[d][s]
                         and levels[i]["event_id"] in segments[d][s]["live"]}
            if not open_days:
                continue
            limit = levels[i].get("max_total")
            plays_max = (math.inf if limit is None else
                         max(0, int(limit) - played_total.get(levels[i]["key"], 0)))
            if all((d, i) in level_cap for d in open_days):
                plays_max = min(plays_max,
                                sum(level_cap[(d, i)] for d in open_days))
            if plays_max == math.inf:
                return math.inf
            total += unit * plays_max
        return total

    kept = []
    for spec in constraints:
        best = math.inf if spec["soft_ok"] else reachable(spec)
        if best >= spec["need"]:
            kept.append(spec)
            continue
        row = spec["row"]
        warnings.append(
            f"{spec['label']} 的「{row['name']}」要求 {spec['need']}，但那段期間"
            f"打得到的關卡全部打到上限也只湊得到 {int(best)}，這條略過。"
            "通常是排程尾巴那幾天已經沒有活動關卡可打（例如某檔沒有關卡的活動"
            "比其他活動晚結束）——把那檔活動的結束日對齊，或不理它也可以")
    constraints = kept

    # ---- 限時體力：所有來源展開成每日發放，再依到期日分池 --------------
    week_of_day = [week_index_of(day, primary["start"]) for day in days]
    weeks_in_scope = sorted(set(week_of_day))

    # 「先放著、晚點再領」的體力（見 MAIL_HOLD_DAYS）：一筆一批，排程決定哪一週領。
    #   reach —— 任務獎勵要等那條任務達標；None＝現在就能領
    claim_lots = []
    for src in manual_sources:
        if src.get("kind") != "mail" or src.get("claimed"):
            continue
        received = _iso_date(src.get("day_date"))
        amount = int(src.get("amount") or 0)
        if received is None or amount <= 0:
            continue
        deadline = received + timedelta(days=MAIL_HOLD_DAYS)
        if deadline < sched_start:
            warnings.append(f"{source_label(src)}（{received:%m/%d} 收到，{amount} 點）"
                            f"已經超過 {deadline:%m/%d} 的領取期限，已略過")
            continue
        claim_lots.append({"label": source_label(src), "amount": amount,
                           "open": received, "deadline": deadline, "reach": None,
                           "received": received,
                           # 提醒視窗要找回這一筆打勾；清單會重排，所以不用索引
                           "ref": {"kind": "mail", "day_date": src.get("day_date"),
                                   "amount": amount,
                                   "note": str(src.get("note") or "").strip()}})
    spec_by_task = {spec["row"]["key"]: spec for spec in constraints
                    if spec.get("whole_event")}
    rows_by_key = {row["key"]: row for row in task_rows}
    past_by_id = {ev["id"]: ev for ev in past_events}
    raw_task_by_key = {key: task for task, _owner, key in iter_tasks(shared)}

    def past_task_met(key: str, past: dict) -> bool:
        """已結束活動的任務達標了沒有（量法跟 task_rows 那邊同一套）。"""
        task = dict(raw_task_by_key.get(key) or {})
        task["_key"] = key
        state = task_states.get(key) or {}
        amount = state.get("amount_override")
        amount = int(amount) if amount not in (None, "") else int(task.get("amount") or 0)
        owner = {"id": past["id"], "name": past["name"],
                 "start": past["start_dt"].date(), "end": past["end_dt"].date()}
        keys, _indices = scope_of(task, owner)
        done = derived_progress(task, owner, task.get("metric"), keys,
                                not task.get("scope"))
        return done >= amount

    fallback_rewards = []
    for src in reward_sources:
        if not src.get("claimable"):
            continue
        past = past_by_id.get(src.get("event_id"))
        if past is not None:
            # 活動已結束：進度不會再動，獎勵要在結束後 REWARD_CLAIM_DAYS 天內領。
            # 不能當成活動最後一天就進了包包（效期會從那週算、而且會被計算頁填的
            # 包包數量蓋掉）——實際上獎勵是活動結束後一週內領、再過十天左右才到期。
            #   * 沒達標：拿不到，不算
            #   * 自動進包包：達標當下就進了包包，計算頁填的數量已經含它
            #   * 手動領：跟信箱一樣排一批「整筆一次領」，排程決定哪一週領
            if src.get("auto_claim") or not past_task_met(src["task_key"], past):
                continue
            deadline = past["end_dt"].date() + timedelta(days=REWARD_CLAIM_DAYS)
            if deadline < sched_start:
                continue          # 領取期限已過（舊活動沒勾已領的不必每次都講）
            claim_lots.append({"label": source_label(src), "amount": src["amount"],
                               "open": sched_start, "deadline": deadline,
                               "reach": None, "received": None, "auto": False,
                               "ref": {"kind": "task", "key": src["task_key"]}})
            continue
        row = rows_by_key.get(src["task_key"])
        event = events_by_id.get(src.get("event_id"))
        spec = spec_by_task.get(src["task_key"])
        met = bool(row and row["windows"] and row["windows"][0]["met"])
        if met and src.get("auto_claim"):
            # 自動進包包又已經達標：體力早就在包包裡，計算頁填的包包數量已經
            # 算進去了，再算一次會重複（不管有沒有勾「已領取」）
            continue
        if (event is not None and not met and spec is None and row is not None
                and not row.get("enforce") and not src.get("auto_claim")):
            # 沒勾「算進排程計算」的活動任務（例：音像商店體力）：排程不保證達標，
            # 當作期限當天會做到；獎勵跟其他活動任務一樣，最晚活動結束後
            # REWARD_CLAIM_DAYS 天內領，哪一週領由排程決定
            due = offset_from_start(src["day_offset"], src["start_date"])
            claim_lots.append({"label": source_label(src), "amount": src["amount"],
                               "open": due,
                               "deadline": event["end"] + timedelta(days=REWARD_CLAIM_DAYS),
                               "reach": None, "received": None, "auto": False,
                               "ref": {"kind": "task", "key": src["task_key"]}})
            continue
        if event is None or not (met or spec):
            # 排程追不到它的進度（那段期間打不到）：照舊在期限當天入帳
            fallback_rewards.append(src)
            continue
        claim_lots.append({"label": source_label(src), "amount": src["amount"],
                           "open": sched_start,
                           "deadline": event["end"] + timedelta(days=REWARD_CLAIM_DAYS),
                           "reach": None if met else spec, "received": None,
                           "auto": bool(src.get("auto_claim")),
                           "ref": {"kind": "task", "key": src["task_key"]}})
    reward_sources = ([src for src in reward_sources if not src.get("claimable")]
                      + fallback_rewards)

    granted_sources = manual_sources + reward_sources
    day_grants = expand_stamina_sources(granted_sources, primary["start"])
    # 每個到期日由哪幾筆來源組成（報表在每一列後面點名）
    labels_by_expiry: dict[date, list[str]] = {}
    for src in granted_sources:
        for grant_day in expand_stamina_sources([src], primary["start"]):
            names = labels_by_expiry.setdefault(expiry_of(grant_day), [])
            if source_label(src) not in names:
                names.append(source_label(src))
    buckets: dict[date, dict[int, int]] = {}
    for grant_day, amount in sorted(day_grants.items()):
        expire_day = expiry_of(grant_day)
        # 排程開始前就發放的，算成現在手上已經有的（第 0 天）
        idx = max(0, (grant_day - sched_start).days)
        # 今天以前就到期的（月卡、固定任務從幾週前就開始發）是過去的帳，
        # 排程結束後才發的是之後才拿得到的——兩種都不進池子
        if expire_day < sched_start or idx >= n_days:
            continue
        slot = buckets.setdefault(expire_day, {})
        slot[idx] = slot.get(idx, 0) + amount
    # 只講「排程結束後才發放」的那些：之後拿得到、這次卻沒算進來。今天以前就
    # 到期的不講——每次都報一大筆過去的帳只是雜訊。
    later: dict[str, int] = {}
    for src in granted_sources:
        for grant_day, amount in expand_stamina_sources([src],
                                                        primary["start"]).items():
            if (grant_day - sched_start).days >= n_days:
                later[source_label(src)] = later.get(source_label(src), 0) + amount
    if later:
        warnings.append(
            f"有 {sum(later.values())} 點體力在排程結束（{days[-1]:%m/%d}）之後才發放，"
            "這次沒算進來：" + "、".join(f"{name} {amount}"
                                       for name, amount in later.items()))

    # 使用者在計算頁填的「包包裡實際還剩多少」。index 0 依定義正好就是
    # 「今天以前發放」的總和（上面那個 max(0, ...) 把它們全壓到第 0 天），
    # 所以直接換掉；今天之後才發的（index > 0）不動。
    for expire_day, in_hand in (held_by_expiry or {}).items():
        slot = buckets.get(expire_day)
        if slot is not None:
            slot[0] = max(0, int(in_hand))

    pools = []
    for expire_day, by_index in sorted(buckets.items()):
        grants = [0] * n_days
        for idx, amount in by_index.items():
            grants[idx] += amount
        indexes = sorted(by_index)
        first, last = indexes[0], indexes[-1]
        span_label = (f"{days[first]:%m/%d}" if first == last
                      else f"{days[first]:%m/%d}~{days[last]:%m/%d}")
        pools.append({
            "label": span_label,
            "grants": grants,
            "last_idx": min((expire_day - sched_start).days, n_days - 1),
            "total": sum(by_index.values()),
            "start": days[first],
            # end 是分類 doomed/savable 用的、expire 是顯示用的
            "end": expire_day, "expire": expire_day,
            "sources": labels_by_expiry.get(expire_day, []),
        })

    # 每一批對它能領的每一週各開一個候選池；發放量由求解器決定（claim 變數），
    # 所以 grants 全是 0、total 是「整筆領的話」的量。doomed／savable 的分類、
    # 留給下一檔的偏好、報表的限時體力表都跟一般的池子共用。
    for k, lot in enumerate(claim_lots):
        lot["pools"] = []
        first = max(lot["open"], sched_start)
        last = min(lot["deadline"], days[-1])
        monday = first - timedelta(days=first.weekday())
        while monday <= last:
            start = max(first, monday)
            expire_day = expiry_of(monday)
            lot["pools"].append(len(pools))
            pools.append({
                "label": f"{start:%m/%d}",
                "grants": [0] * n_days,
                "last_idx": min((expire_day - sched_start).days, n_days - 1),
                "total": lot["amount"],
                "start": start, "end": expire_day, "expire": expire_day,
                "sources": [lot["label"]],
                "claim": k,
                "open_idx": (start - sched_start).days,
                # 這一週最後一天能領的日子（排程內）
                "week_last_idx": (min(monday + timedelta(days=6), last)
                                  - sched_start).days,
            })
            monday += timedelta(days=7)

    # ---- 每日下限（由每日/公會任務推出來，特殊日可以覆蓋）--------------
    daily_clear_floor: dict[int, int] = {}
    daily_enemy_floor: dict[int, int] = {}
    daily_stamina_floor: dict[int, int] = {}
    for spec in constraints:
        if len(spec["days"]) != 1:
            continue
        d = spec["days"][0]
        if spec["metric"] == "clears" and spec["default_scope"]:
            daily_clear_floor[d] = max(daily_clear_floor.get(d, 0), spec["need"])
        elif spec["metric"] == "enemies":
            daily_enemy_floor[d] = max(daily_enemy_floor.get(d, 0), spec["need"])
        elif spec["metric"] == "stamina":
            daily_stamina_floor[d] = max(daily_stamina_floor.get(d, 0), spec["need"])

    wants_enemies = any(daily_enemy_floor.values())
    if wants_enemies and not any(enemies_of):
        raise PlanError(
            "有任務要求擊殺敵人數，但所有關卡的敵人人數都是 0。\n"
            "請到「活動設定」的關卡結構把各關卡的敵人人數填上。")

    # ---- 送進求解器前先抓明顯的條件衝突 ---------------------------------
    # 求解器只會回報「無解」，不會告訴你是哪兩條規則打架。這種一眼可證的矛盾
    # 先自己抓出來，直接指名是哪一天、差多少。
    def playable_levels_on(d: int) -> list[int]:
        live = set()
        for s, seg in enumerate(segments[d]):
            if seg["playable"]:
                live |= seg["live"]
        return [i for i, lv in enumerate(levels) if lv["event_id"] in live]

    def day_ceiling(d: int, options: list[int]) -> int | None:
        """那天總共最多能花多少體力。沒有任何上限就回傳 None。

        「當日該活動體力上限」只有在當天**每一檔**打得到的活動都被限住時，
        才構成整天的天花板；只要有一檔沒設，剩下的體力就有地方去，
        不能拿來判定衝突（早上舊活動收尾、下午新活動開打那天就是這種）。
        """
        caps = [usage_cap[d]] if d in usage_cap else []
        live = {levels[i]["event_id"] for i in options}
        if live and all(event_room(d, eid) is not None for eid in live):
            group, limit = ending_cap.get(d, (frozenset(), None))
            inside = [eid for eid in live if eid in group]
            total = sum(event_room(d, eid) for eid in live if eid not in group)
            if inside:
                # 群組那幾檔共用一個上限，只算一次
                total += min(limit, sum(event_room(d, eid) for eid in inside))
            caps.append(total)
        return min(caps) if caps else None

    def floor_tasks(d: int, metric: str) -> str:
        """是哪幾條任務把那天的下限撐上去的——訊息要指名，不然沒得改。"""
        names = []
        for spec in constraints:
            if spec["metric"] != metric or spec["days"] != [d]:
                continue
            row = spec["row"]
            label = f"「{row['name']}」"
            if row.get("event_name"):
                label = f"{row['event_name']}的{label}"
            if label not in names:
                names.append(label)
        return "、".join(names)

    def floor_window_text(d: int, metric: str) -> str:
        """那天這個下限是幾點到幾點算的。

        活動下午三點才開的話，「當天至少耗體 300」其實是「15:00 之後至少 300」——
        不寫出來，使用者會拿當天的總耗體去對，怎麼看怎麼不合。
        """
        live, playable = set(), {s for s in range(len(segments[d]))
                                 if playable_of[d][s]}
        for spec in constraints:
            if spec["metric"] == metric and spec["days"] == [d]:
                live |= {s for _d, s in spec["cells"] if s in playable}
        if not live or live == playable:
            return ""
        order = sorted(live)
        return (f"只有 {segments[d][order[0]]['lo']:%H:%M}~"
                f"{segments[d][order[-1]]['hi']:%H:%M} 打的算數")

    def enemy_blocked_day(d: int, options: list[int]) -> bool:
        """那天要求打敵人、但當天打得到的關卡敵人人數全是 0。

        上面那條全域檢查（所有關卡都 0）擋不住這種：舊活動的關卡有敵人，
        但它中午就結束了，下午開打的復刻活動關卡卻一個敵人也沒有。
        """
        return bool(daily_enemy_floor.get(d, 0)
                    and not any(enemies_of[i] for i in options))

    for d in range(n_days):
        options = playable_levels_on(d)
        if not options:
            continue
        if enemy_blocked_day(d, options):
            blocked = [k for k in range(d, n_days)
                       if enemy_blocked_day(k, playable_levels_on(k))]
            blame = floor_tasks(d, "enemies") or "每日任務"
            live_names = sorted({
                (events_by_id.get(levels[i]["event_id"]) or primary)["name"]
                for i in options})
            more = (f"（到 {days[blocked[-1]]:%m/%d} 為止共 {len(blocked)} 天都是這樣）"
                    if len(blocked) > 1 else "")
            raise PlanError(
                "條件互相衝突，無法計算：\n\n"
                f"　{format_day(days[d])} 要求打 {daily_enemy_floor[d]} 個敵人"
                f"（來自{blame}），\n"
                f"　但那天打得到的關卡（{'、'.join(live_names)}）敵人人數全是 0。"
                f"{more}\n\n"
                "可以這樣調整：\n"
                "　• 到「活動設定」的關卡結構把那幾關的敵人人數填上\n"
                "　• 那天如果不必打滿敵人數，到「排程設定」的特殊日規則新增一筆\n"
                "　　「當日最低敵人數」設成 0\n"
                "　• 如果那段期間本來就沒有敵人可打，到「設定」選單的任務清單把這條任務的\n"
                "　　「算進排程計算」取消，或用「只算這段期間」限制在打得到的日子")
        cap_value = day_ceiling(d, options)
        if cap_value is None:
            continue
        floor_value = daily_stamina_floor.get(d, 0)
        if floor_value > cap_value:
            blame = floor_tasks(d, "stamina")
            detail = "，".join(x for x in (f"來自{blame}" if blame else "",
                                           floor_window_text(d, "stamina")) if x)
            # 天花板來自整天的上限、還是各活動的上限加總，講法不一樣——
            # 已經是各活動分開設的話，叫人家「改成各活動分開設」就很蠢。
            whole_day = d in usage_cap
            cap_text = ("當日體力使用上限" if whole_day
                        else "當天各活動的體力上限加起來只有")
            escape = ("　• 如果那個上限其實只想限制某一檔活動（例如當天中午就結束、\n"
                      "　　不想再多投的那檔），把該筆規則的類型改成\n"
                      "　　「當日該活動體力上限」，同一天的其他活動就不受它限制\n"
                      if whole_day else "")
            raise PlanError(
                "條件互相衝突，無法計算：\n\n"
                f"　{format_day(days[d])} 同時被要求\n"
                f"　　「每天至少耗體 {floor_value} 點」"
                + (f"\n　　（{detail}）" if detail else "")
                + "與\n"
                f"　　「{cap_text} {cap_value} 點」。\n\n"
                "可以這樣調整：\n"
                "　• 那天如果不必湊滿耗體，到「排程設定」的特殊日規則新增一筆\n"
                f"　　「當日最低耗體」，把 {format_day(days[d])} 設成 0"
                f"（或 {cap_value} 以下）\n"
                + escape
                + "　• 檢查那天的體力上限數字是否正確")
        day_enemies = daily_enemy_floor.get(d, 0)
        best_ratio = max((enemies_of[i] / costs[i] for i in options
                          if enemies_of[i]), default=0)
        if day_enemies and best_ratio:
            need = math.ceil(day_enemies / best_ratio)
            if need > cap_value:
                best = max((i for i in options if enemies_of[i]),
                           key=lambda i: enemies_of[i] / costs[i])
                raise PlanError(
                    "條件互相衝突，無法計算：\n\n"
                    f"　{format_day(days[d])} 的體力使用上限是 {cap_value} 點，\n"
                    f"　但當天要求打 {day_enemies} 個敵人，"
                    f"就算全打效率最高的「{levels[best]['label']}」\n"
                    f"　（{costs[best]} 體力 / {enemies_of[best]} 人）"
                    f"也至少要 {need} 點。\n\n"
                    "可以這樣調整：\n"
                    "　• 那天如果不必打滿敵人數，到特殊日規則新增一筆\n"
                    f"　　「當日最低敵人數」，把 {format_day(days[d])} 設成 0\n"
                    "　• 檢查那天的體力上限、或各關卡的敵人人數是否正確")
        day_min = daily_clear_floor.get(d, 0)
        if day_min:
            cheapest = min(options, key=lambda i: costs[i])
            need = costs[cheapest] * day_min
            if need > cap_value:
                raise PlanError(
                    "條件互相衝突，無法計算：\n\n"
                    f"　{format_day(days[d])} 的體力使用上限是 {cap_value} 點，\n"
                    f"　但當天最低 {day_min} 關 × 最便宜的"
                    f"「{levels[cheapest]['label']}」{costs[cheapest]} 體力 "
                    f"= {need} 點，\n"
                    f"　超出上限 {need - cap_value} 點。\n\n"
                    "可以這樣調整：\n"
                    "　• 那天如果不必打滿最低關數，到「排程設定」的特殊日規則新增一筆\n"
                    f"　　「當日最低關卡數」，把 {format_day(days[d])} 設成 0"
                    f"（或 {cap_value // costs[cheapest]} 以下）\n"
                    "　• 如果遊戲有更便宜的關卡（例如不計分的掃蕩關），"
                    "到「活動設定」把它加進關卡清單\n"
                    "　• 檢查那天的體力上限數字是否正確")

    # 關卡的開放日晚於活動結束：求解器只會回報「無解」，這裡先指名是哪一關。
    for lv in levels:
        offset = lv.get("available_from")
        if offset is None:
            continue
        event = events_by_id.get(lv["event_id"]) or primary
        opens = offset_from_start(int(offset), event["start"])
        if opens <= event["end"]:
            continue
        if lv.get("must_finish") and lv.get("max_total"):
            raise PlanError("\n".join([
                f"「{lv['label']}」設成活動結束前一定要打滿 "
                f"{lv['max_total']} 次，",
                f"但它的開放日 {opens:%m/%d} 在活動結束日 "
                f"{event['end']:%m/%d} 之後，不可能打得到。",
                "請檢查開放起日或取消「一定要打滿」。"]))
        warnings.append(
            f"「{lv['label']}」的開放日 {opens:%m/%d} 在活動結束之後，這次排不到它")

    # 限期關卡勾了「一定要打滿」、但那一檔的結束日在排程範圍之後：這次不強制，
    # 只當上限。排程範圍只到真正的活動結束（例如月初），某檔限期關卡卻開到兩個月後——
    # 強制的話二十幾次會全塞進這一週，吃掉本來能留給下一檔的體力。等排程範圍涵蓋
    # 結束日時自然會強制；在那之前只用多餘的體力打（見下面的先到期優先）。
    deferred_finish = {
        i for i, lv in enumerate(levels)
        if lv.get("must_finish") and events_by_id[lv["event_id"]]["limited"]
        and events_by_id[lv["event_id"]]["end"] > last_end}

    # 有總次數上限、而且已經打掉一部分的關卡，講清楚還剩幾次——
    # 不然使用者會以為排程漏排了。
    for i, lv in enumerate(levels):
        limit = lv.get("max_total")
        already = played_total.get(lv["key"], 0)
        if i in deferred_finish and limit:
            left = max(0, int(limit) - already)
            if left:
                warnings.append(
                    f"「{lv['label']}」這一期要打滿 {limit} 次（還差 {left} 次），"
                    f"結束日 {events_by_id[lv['event_id']]['end']:%m/%d} 在排程範圍之後，"
                    "這次只用多餘的體力打，不強制")
            continue
        if not limit or not already:
            continue
        left = max(0, int(limit) - already)
        warnings.append(
            f"「{lv['label']}」"
            + ("這一期" if events_by_id.get(lv["event_id"], {}).get("limited")
               else "整檔活動")
            + ("要打滿" if lv.get("must_finish") else "最多")
            + f" {limit} 次，已經打了 {already} 次，"
            + (f"還要打 {left} 次" if left else "已經打完了")
            + ("（剩下的排在同一天）" if lv.get("same_day") and left > 1 else ""))

    # ---- 解鎖鏈：勾了「開場先打一次」的關卡 ------------------------------
    # 遊戲的關卡是一條解鎖鏈：關卡1 打過才開關卡2、關卡2 打過才開關卡3……不先各
    # 打過一次，後面的關卡根本點不開。排程沒有這個概念的話，只會挑 CP 最高的
    # 那一關猛打，算出來的打法在遊戲裡其實執行不了。
    #
    # 「已經解鎖了沒有」跟 max_total 同一套判準：**只相信每日紀錄**。沒記就當沒
    # 打過——寧可多排一次，也不要給出一個打不到的計畫。實際上「打過但沒記」很常見
    # （例如關卡5 有上百次紀錄、關卡1~4 卻全是 0，遊戲裡不可能），
    # 所以下面會特別提醒去補記錄。
    unlock_prior = {i: played_total.get(lv["key"], 0)
                    for i, lv in enumerate(levels)}

    def unlock_playable_days(index: int) -> list[int]:
        """這一關在剩下的排程裡，哪幾天真的打得到。

        條件跟 `build_and_solve` 建 plays 變數的條件**一字不差**，再加上開放起日。
        兩邊只要不一致，就會出現「預檢說可以、求解卻說無解」這種最難查的狀況。
        """
        lv = levels[index]
        opens = None
        if lv.get("available_from") is not None:
            owner = events_by_id.get(lv["event_id"]) or primary
            opens = offset_from_start(int(lv["available_from"]), owner["start"])
        out = []
        for d in range(n_days):
            if opens is not None and days[d] < opens:
                continue
            if any(seg["playable"] and not seg["overtime"]
                   and lv["event_id"] in seg["live"] for seg in segments[d]):
                out.append(d)
        return out

    def unlock_order_text(indexes) -> str:
        """把一串關卡索引印成解鎖順序。

        耗體由小到大用「→」隔開，但**同耗體的關卡是同一階、彼此沒有先後**，
        要用「・」並列——寫成「活動BOSS關1→活動BOSS關2」會讓人以為有順序，
        而遊戲裡那三關都是 10 體、想先打哪個都行。
        """
        groups: list[list[int]] = []
        for i in sorted(indexes, key=lambda i: (costs[i], i)):
            if groups and costs[groups[-1][0]] == costs[i]:
                groups[-1].append(i)
            else:
                groups.append([i])
        return "→".join("・".join(levels[i]["name"] for i in group)
                        for group in groups)

    # 一檔活動的每個「組別」一條鏈——ev1 的關卡1 不會解鎖 ev2 的關卡2，同一檔
    # 活動裡第 1 組的 20 體也不會解鎖第 2 組的 30 體（蜜意蒐羅 11 組 × 20/30/40）。
    # 沒填組別的關卡是同一條鏈，所以沒有組別的舊資料行為完全不變。
    # 常駐關卡沒有「活動開始」可言（storage 已經把欄位清成 False），這裡再擋一次：
    # 手改過的檔案不該讓排程算出奇怪的東西。
    unlock_chains = []
    for owner in events:
        if owner["standing"]:
            continue
        picked_all = [i for i, lv in enumerate(levels)
                      if lv["event_id"] == owner["id"] and lv.get("unlock_first")]
        groups_seen = sorted({levels[i].get("group") for i in picked_all},
                             key=lambda g: (g is not None, g or 0))
        for group in groups_seen:
            picked = [i for i in picked_all if levels[i].get("group") == group]
            # 依耗體升冪分「階」。**同耗體的關卡要視為同一階**，不能串成一條線：
            # ev1 三個活動BOSS關都是 10 體，彼此在遊戲裡沒有先後關係，硬串會捏造出
            # 不存在的順序，還可能讓排程變成無解。單關的階自然退化成相鄰配對。
            tiers: list[list[int]] = []
            for i in sorted(picked, key=lambda i: (costs[i], i)):
                if tiers and costs[tiers[-1][0]] == costs[i]:
                    tiers[-1].append(i)
                else:
                    tiers.append([i])
            need = [i for i in picked if unlock_prior[i] < 1]
            unlock_chains.append({
                "event": owner,
                "group": group,
                "tiers": tiers,
                "levels": picked,
                "need": need,
                "cost": sum(costs[i] for i in need),
                # 展示順序：攤平的耗體升冪，報表與訊息都用這個
                "order": [i for tier in tiers for i in tier],
                # 分組解鎖型活動的「每關至少打一次」是目標、不是遊戲規則：資源真的
                # 湊不出來時可以依活動優先序放寬（跟活動任務同一套）。閘門——貴的
                # 要等便宜的打過——永遠是硬的，那才是遊戲規則。
                "soft_ok": owner["type"] in GROUPED_EVENT_PRESETS,
            })

    def group_label(chain) -> str:
        """一組的稱呼：組內關卡名稱「·」前面都一樣（如「八雲·20」「八雲·30」）
        就用那個名字，否則照舊叫「第N組」。"""
        prefixes = {levels[i]["name"].split("·", 1)[0]
                    for i in chain["levels"] if "·" in levels[i]["name"]}
        if len(prefixes) == 1 and all("·" in levels[i]["name"]
                                      for i in chain["levels"]):
            return prefixes.pop()
        return f"第{chain['group']}組"

    def chain_title(chain) -> str:
        """訊息裡指稱一條鏈：「蜜意蒐羅」或「蜜意蒐羅」第3組（有改名就用組名）。"""
        group = chain["group"]
        return (f"「{chain['event']['name']}」"
                + (group_label(chain) if group is not None else ""))

    def chain_order_text(chain, order=None) -> str:
        """有組別的鏈用耗體講順序（「八雲 20→30→40」），名稱裡本來就帶著組別，
        照印會變成一長串「八雲·20→八雲·30→…」；沒組別的照舊印關卡名稱。"""
        order = chain["order"] if order is None else order
        if chain["group"] is None:
            return unlock_order_text(order)
        tiers: list[list[int]] = []
        for i in sorted(order, key=lambda i: (costs[i], i)):
            if tiers and costs[tiers[-1][0]] == costs[i]:
                tiers[-1].append(i)
            else:
                tiers.append([i])
        return (f"{group_label(chain)} "
                + "→".join("・".join(str(costs[i]) for i in tier) for tier in tiers))

    # big-M：閘門右邊的係數（見 build_and_solve 裡的 unlock_gate）。
    #
    # plays 沒有上界、buy（補充體力）也沒有上界，所以推不出一個**可證明安全**的
    # 有限上界。二元指示變數、min() 線性化都一樣要 big-M——「無上界整數 > 0 蘊含
    # 另一個量 >= 1」本質上就是指示約束，沒有 M-free 的正確寫法。
    #
    # 取「單日最多可能花掉的體力 ÷ 這一關的耗體」：體力上限（最多存這麼多）＋
    # 當天回復 ＋ 整段的限時資源。除了 buy 以外，這是模型裡真的成立的
    # 上界（balance 的上界就是 cap、pool_use 受累積發放量限制）。buy 不算進來是因為第一階段正在**最小化**它：要讓單日次數超過這個
    # 上界，就得額外買 (M × 耗體 − 供給) 點體力，那正是第一階段拼命想壓低的東西；
    # 第二、三階段更安全，那時 Σbuy 已經被 lock_buy 鎖死。
    #
    # 不要因為怕拖慢求解就把 M 壓小。M 太小的失敗模式是**默默算出更差的解**
    # （不會報錯）；而實測實際使用的資料（約二十天 × 十幾關）M 從個位數拉到上萬，只從
    # 不到半秒變成不到一秒，每一次都證明到最佳。寧可寬鬆，再靠求解後的檢查兜底。
    unlock_supply = (cap + max(recovery, default=0)
                     + sum(pool["total"] for pool in pools))
    unlock_gated = [i for chain in unlock_chains
                    for tier in chain["tiers"][1:] for i in tier]
    unlock_cap = {i: max(1, math.ceil(unlock_supply / max(1, costs[i])))
                  for i in unlock_gated}

    def unlock_fits_somewhere(i: int, owner) -> bool:
        """這一關的耗體塞得進它某一個可打日的上限（見下面的 (a2)）。"""
        for d in unlock_playable_days(i):
            caps = [usage_cap[d]] if d in usage_cap else []
            if event_room(d, owner["id"]) is not None:
                caps.append(event_room(d, owner["id"]))
            if not caps or min(caps) >= costs[i]:
                return True
        return False

    # 可放寬的鏈（分組解鎖型活動）：一定打不到的關卡不能留在「至少一次」裡——
    # 求解器面對一定做不到的要求只會回「無解」，連帶其他活動的排程也看不到。
    # 那幾關直接拿掉並講出來；比它貴的同組關卡因為閘門是硬的，也一起打不到。
    # 其餘「時間／體力湊不出來」的情況交給求解後的放寬機制處理。
    for chain in unlock_chains:
        if not chain["soft_ok"] or not chain["need"]:
            continue
        owner = chain["event"]
        dead = [i for i in chain["need"]
                if not unlock_playable_days(i)
                or not unlock_fits_somewhere(i, owner)]
        if not dead:
            continue
        first_dead_tier = min(t for t, tier in enumerate(chain["tiers"])
                              if any(i in dead for i in tier))
        blocked = {i for tier in chain["tiers"][first_dead_tier + 1:] for i in tier}
        dropped = [i for i in chain["order"]
                   if i in chain["need"] and (i in dead or i in blocked)]
        chain["need"] = [i for i in chain["need"] if i not in dropped]
        chain["cost"] = sum(costs[i] for i in chain["need"])
        warnings.append(
            f"{chain_title(chain)}的 "
            + "、".join(str(costs[i]) if chain["group"] is not None
                       else levels[i]["name"] for i in dropped)
            + " 在剩下的排程裡打不到（活動快結束了、或那幾天的體力上限塞不下），"
              "這次不排它們的「至少打一次」")

    # 送求解前先抓能一眼證明的矛盾。理由跟上面那一整區預檢一樣：求解器只會回
    # 「無解」，不會告訴你是哪一關的解鎖鏈打不通。不可放寬的解鎖鏈是硬約束
    # （可放寬的只有分組解鎖型活動，打不到的已經在上面拿掉了），掉到通用的無解
    # 訊息會把使用者指向特殊日規則，找不到真正的原因。
    for chain in unlock_chains:
        owner = chain["event"]
        names = unlock_order_text(chain["order"])

        # (a) 勾了、卻在剩下的排程裡一天都打不到 → 這條鏈不可能打通
        for i in chain["need"]:
            if unlock_playable_days(i):
                continue
            reason = ("它的開放起日在活動結束之後"
                      if levels[i].get("available_from") is not None
                      else f"活動 {owner['end_dt']:%m/%d %H:%M} 就結束了")
            raise PlanError(
                "條件互相衝突，無法計算：\n\n"
                f"　「{levels[i]['label']}」勾了「開場先打一次」，"
                "但它在剩下的排程裡一次都打不到\n"
                f"　（{reason}）。解鎖鏈打不通，比它貴的關卡就全部打不了。\n\n"
                "可以這樣調整：\n"
                "　• 這一關已經打過的話，到「每日紀錄」補記上 1 次（哪一天都行），"
                "排程就不會再排解鎖\n"
                "　• 到「活動設定」的關卡結構取消它的「開場先打一次」\n"
                "　• 檢查它的「開放起日」是不是填錯了")

        # (a2) 這一關的耗體塞不進它任何一個可打日的上限——單獨一次都打不下去，
        #      整條鏈就死在這裡。(b) 的「加總起來夠不夠」抓不到這種：15 天 × 上限
        #      10 點加起來有 150 點，看起來塞得下 50 點的關卡，但那 50 點沒辦法
        #      拆到兩天去打。
        for i in chain["need"]:
            if unlock_fits_somewhere(i, owner):
                continue
            raise PlanError(
                "條件互相衝突，無法計算：\n\n"
                f"　「{levels[i]['label']}」勾了「開場先打一次」，一次要 "
                f"{costs[i]} 點體力，\n"
                "　但它打得到的每一天，當日體力上限都比這個數字小——"
                "一次都打不下去。\n"
                "　解鎖鏈打不通，比它貴的關卡就全部打不了。\n\n"
                "可以這樣調整：\n"
                "　• 到「排程設定」的特殊日規則放寬那幾天的"
                "「當日體力使用上限」／「當日該活動體力上限」\n"
                "　• 這一關已經打過的話，到「每日紀錄」補記上 1 次，"
                "排程就不會再排解鎖\n"
                "　• 到關卡結構取消它的「開場先打一次」")

        # (b) 解鎖鏈的總成本超過那幾天的體力天花板。只有**那幾天每一天都有上限**
        #     時才算得準——有一天沒設上限，剩下的體力就有地方去，不能拿來判定衝突
        #     （理由同 day_ceiling）。可放寬的鏈不在這裡擋：湊不出來就交給放寬機制，
        #     報表會列出還差哪幾關。
        if chain["cost"] and not chain["soft_ok"]:
            span = sorted({d for i in chain["need"]
                           for d in unlock_playable_days(i)})
            room, bounded = 0, bool(span)
            for d in span:
                caps = [usage_cap[d]] if d in usage_cap else []
                if event_room(d, owner["id"]) is not None:
                    caps.append(event_room(d, owner["id"]))
                if not caps:
                    bounded = False
                    break
                room += min(caps)
            if bounded and room < chain["cost"]:
                where = (format_day(days[span[0]]) if len(span) == 1
                         else f"{format_day(days[span[0]])}~"
                              f"{days[span[-1]]:%m/%d} 這 {len(span)} 天")
                raise PlanError(
                    "條件互相衝突，無法計算：\n\n"
                    f"　「{owner['name']}」的解鎖鏈要先打 {names} 各一次"
                    f"（共 {chain['cost']} 點），\n"
                    f"　但 {where} 的體力上限加起來只有 {room} 點，"
                    f"差 {chain['cost'] - room} 點。\n\n"
                    "可以這樣調整：\n"
                    "　• 這幾關已經打過的話，到「每日紀錄」補記錄，"
                    "排程就不會再排解鎖\n"
                    "　• 到「排程設定」的特殊日規則放寬那幾天的"
                    "「當日體力使用上限」／「當日該活動體力上限」\n"
                    "　• 到關卡結構取消其中幾關的「開場先打一次」")

    # 分組解鎖型活動一檔有十幾條鏈，逐條講會洗版——整檔講一句就好。
    # 「活動開始了卻是 0 次」在這裡也不是「一定打過但沒記」：這類活動本來就是
    # 慢慢把每一關打過一次，所以只提醒有打過的記得補記。
    grouped_need: dict[str, list[int]] = {}
    for chain in unlock_chains:
        if chain["soft_ok"] and chain["need"]:
            grouped_need.setdefault(chain["event"]["id"], []).extend(chain["need"])
    for event_id, need in grouped_need.items():
        owner = events_by_id[event_id]
        warnings.append(
            f"「{owner['name']}」還有 {len(need)} 關沒打過（每日紀錄裡是 0 次），"
            f"共 {sum(costs[i] for i in need)} 點——每關至少打一次，同一組照耗體"
            "由小到大解鎖。已經打過的請到「每日紀錄」補記上 1 次")

    for chain in unlock_chains:
        owner = chain["event"]
        names = unlock_order_text(chain["order"])

        # 解鎖鏈要先花掉多少。就算算得出來也要講——這幾次是被強制排進去的，
        # 不講的話使用者會覺得排程忽然挑了幾關便宜的卻不知道為什麼。
        # 注意：這**不是**「總耗體多了這麼多」——那幾次也算積分與關卡次數，會替掉
        # 一部分主力關卡（實測只多十幾點）。真正的代價是 CP 變差。
        # 分組解鎖型活動已經在上面整檔講過了。
        if chain["cost"] and not chain["soft_ok"]:
            part = ("" if len(chain["need"]) == len(chain["levels"])
                    else "（"
                         + "、".join(levels[i]["name"] for i in chain["need"])
                         + " 還沒打過）")
            warnings.append(
                f"「{owner['name']}」的解鎖鏈 {names} 要先各打過一次{part}，"
                f"共 {chain['cost']} 點體力——就算效益不高也一定會排，"
                "那是開下一關的必要成本")

        # 活動已經開始、卻有勾選的關卡紀錄是 0 次。解鎖鏈的存在本身就代表你不可能
        # 跳過它，所以這幾乎一定是「打過但沒記」。排程只相信紀錄，會再排一次。
        if owner["start_dt"] <= query_dt and chain["need"] and not chain["soft_ok"]:
            missing = "、".join(levels[i]["name"] for i in chain["need"])
            warnings.append(
                f"「{owner['name']}」{owner['start']:%m/%d} 就開始了，"
                f"但這幾關在每日紀錄裡是 0 次：{missing}。"
                f"排程只相信每日紀錄，所以會再排一次解鎖（共 {chain['cost']} 點）。"
                "已經打過的話請到「每日紀錄」補記上 1 次（哪一天都行）")

        # 開放起日把鏈的順序倒過來了：便宜的那關晚開，比它貴的就全部要等到那天。
        # 這是陷阱——數字看起來沒錯，但整個排程被往後推。它仍然算得出解，
        # 所以是提醒不是錯誤。
        for prev_tier, tier in zip(chain["tiers"], chain["tiers"][1:]):
            for j in prev_tier:
                if (unlock_prior[j] >= 1
                        or levels[j].get("available_from") is None):
                    continue
                opens = offset_from_start(int(levels[j]["available_from"]),
                                          owner["start"])
                blocked = []
                for i in tier:
                    open_days = unlock_playable_days(i)
                    if not open_days or days[open_days[0]] < opens:
                        blocked.append(i)
                if blocked:
                    warnings.append(
                        f"「{levels[j]['label']}」要 {opens:%m/%d} 才開放，"
                        "而它是解鎖鏈上比 "
                        + "、".join(levels[i]["name"] for i in blocked)
                        + f" 便宜的那一關——所以那幾關也要等到 {opens:%m/%d} "
                        "才排得到")

    # ---- 關卡優先序 -----------------------------------------------------
    # 各帳號自己排的順序。只在兩個時機生效：第二階段之後的「偏好階段」（同樣省
    # 體力、同樣積分的打法裡挑排前面的）、以及第三階段消化多餘體力時。
    # 第 r 名（共 N 項）的權重是 (N − r) / N，沒列進去的是 0＝沒有偏好。
    #
    # 限期關卡的系列鍵（limited:忘卻/lv1）展開成排程裡所有同名、同關卡的檔次，
    # 共用同一個名次——交接日新舊兩檔都在排程範圍內時兩邊都適用。
    listed = list(dict.fromkeys(profile.get("level_priority") or []))
    resolved: list[tuple[str, list[int]]] = []   # (顯示名稱, 關卡索引)
    skipped_priority = []
    for key in listed:
        series = split_limited_series_key(key)
        if series is None:
            if key in level_index:
                resolved.append((levels[level_index[key]]["label"],
                                 [level_index[key]]))
            else:
                skipped_priority.append(
                    all_levels[key]["label"] if key in all_levels else key)
            continue
        name, level_id = series
        hits = [i for i, lv in enumerate(levels)
                if events_by_id[lv["event_id"]]["limited"]
                and lv["series_name"] == name and lv["id"] == level_id]
        if hits:
            resolved.append((level_label(name, name, levels[hits[0]]["name"]), hits))
        else:
            skipped_priority.append(f"{name}（目前沒有進行中的一期）")
    priority_weight = {i: (len(resolved) - r) / len(resolved)
                       for r, (_label, hits) in enumerate(resolved) for i in hits}
    if resolved:
        warnings.append(
            "關卡優先序："
            + " > ".join(label for label, _hits in resolved)
            + "（只在同樣省體力時、以及消化多餘體力時生效，不會因此多花或多買體力）")
    # 手動沒排到的限期關卡：先到期的先打。權重整段落在手動清單最低那一名之下，
    # 所以順序是「手動優先序 > 先到期的限期 > 晚到期的限期 > 其他（0）」。
    # 沿用偏好階段而不是加小係數，理由同偏好階段的註解（小係數會被 gap 吞掉）。
    # 副作用：只要有開著的限期關卡就會跑偏好階段與 surplus_only；多餘體力也會先
    # 給限期關卡、再給常駐關卡——限期的會過期、常駐的不會，這正是要的方向。
    floor_w = 1 / len(resolved) if resolved else 1.0
    by_deadline = [i for i, lv in enumerate(levels)
                   if events_by_id[lv["event_id"]]["limited"]
                   and i not in priority_weight]
    deadlines = sorted({events_by_id[levels[i]["event_id"]]["end_dt"]
                        for i in by_deadline})
    rank_of = {moment: k for k, moment in enumerate(deadlines)}
    for i in by_deadline:
        k = rank_of[events_by_id[levels[i]["event_id"]]["end_dt"]]
        priority_weight[i] = floor_w * (len(deadlines) - k) / (len(deadlines) + 1)
    if len(deadlines) > 1:
        seen = []
        for i in sorted(by_deadline, key=lambda i: -priority_weight[i]):
            event = events_by_id[levels[i]["event_id"]]
            text = f"{levels[i]['label']}（{event['end']:%m/%d}）"
            if text not in seen:
                seen.append(text)
        warnings.append("限期關卡同樣條件下先打先到期的：" + " > ".join(seen))
    if skipped_priority:
        warnings.append(
            "關卡優先序裡這幾關這次沒有算進來（已停用、活動已結束或已刪除），略過："
            + "、".join(skipped_priority))

    # ---- 手動鎖定的日子 -------------------------------------------------
    # 那天那關到底打不打得到：有可打的段落、而且已經過了開放起日。跟 build_and_solve
    # 建變數＋開放起日那兩處是同一個條件，UI 對調日期前也靠這張表先擋。
    playable_days = []
    for d in range(n_days):
        row = []
        for lv in levels:
            # 加班時段只拿來補今天的任務，指定次數、對調日期都不算它打得到
            ok = any(seg["playable"] and not seg["overtime"]
                     and lv["event_id"] in seg["live"] for seg in segments[d])
            if ok and lv.get("available_from") is not None:
                owner = events_by_id.get(lv["event_id"]) or primary
                ok = days[d] >= offset_from_start(int(lv["available_from"]),
                                                  owner["start"])
            row.append(ok)
        playable_days.append(row)

    pinned_idx: dict[int, list[int]] = {}
    for day, counts in (pinned or {}).items():
        d = (day - sched_start).days
        if not 0 <= d < n_days:
            continue          # 已經過去、或排程範圍變短了，那天不用再鎖
        fixed = [0] * n_levels
        for key, count in (counts or {}).items():
            count = int(count or 0)
            if count <= 0:
                continue
            if key not in level_index:
                name = (all_levels.get(key) or {}).get("label") or key
                raise PlanError(
                    f"你把 {format_day(day)} 調整成要打「{name}」，"
                    "但這一關這次沒有列入計算（已停用、活動已結束或已刪除）。")
            fixed[level_index[key]] = count
        blocked = [levels[i]["label"] for i in range(n_levels)
                   if fixed[i] and not playable_days[d][i]]
        if blocked:
            raise PlanError(
                f"你把 {format_day(day)} 調整成要打 " + "、".join(blocked)
                + "，但那天打不到（活動還沒開始／已經結束、關卡還沒開放，"
                  "或已經過了上線時段）。")
        pinned_idx[d] = fixed
    if pinned_idx:
        warnings.append(
            "這幾天照你手動調整的打法鎖住，其餘日子是配合它重新排的："
            + "、".join(format_day(days[d]) for d in sorted(pinned_idx)))
        # 當日上限在鎖定日不套用（你的調整說了算），但超過了要講
        over = []
        for d, fixed in sorted(pinned_idx.items()):
            spent = sum(costs[i] * fixed[i] for i in range(n_levels))
            if d in usage_cap and spent > usage_cap[d]:
                over.append(f"{format_day(days[d])} 耗體 {spent}"
                            f"（當日上限 {usage_cap[d]}）")
            for (cap_day, cap_event), limit in event_cap.items():
                used = sum(costs[i] * fixed[i] for i in range(n_levels)
                           if levels[i]["event_id"] == cap_event)
                if cap_day == d and used > limit and cap_event in events_by_id:
                    over.append(f"{format_day(days[d])}「"
                                f"{events_by_id[cap_event]['name']}」耗體 {used}"
                                f"（當日上限 {limit}）")
            if d in ending_cap:
                group, limit = ending_cap[d]
                used = sum(costs[i] * fixed[i] for i in range(n_levels)
                           if levels[i]["event_id"] in group)
                if used > limit:
                    over.append(f"{format_day(days[d])} 當天結束的活動耗體 {used}"
                                f"（當日上限 {limit}）")
            for (cap_day, i), limit in level_cap.items():
                if cap_day == d and fixed[i] > limit:
                    over.append(f"{format_day(days[d])} {levels[i]['label']}"
                                f"×{fixed[i]}（每日上限 {limit}）")
        if over:
            warnings.append("手動調整的打法超過了你設的上限，這次以調整為準："
                            + "、".join(over))

    # ---- 整理階段的範圍（見 LIGHT_WEEKDAYS 的說明）------------------------
    # 鍵不存在＝關：直接呼叫 compute_plan 的舊程式與測試，行為跟沒有這個功能時一樣
    # （storage.normalise_shared 才會把預設補成開）。
    prefs = shared.get("schedule_prefs") or {}
    simplify_days = bool(prefs.get("simplify_days"))
    # 多的限時體力留在晚到期的那批（見 build_and_solve 的效期階段）
    expire_late = bool(prefs.get("expire_late"))
    expiry_note: dict = {}
    # 打法簡化、活動優先序只管真正的活動（當期／復刻）的關卡；限期關卡照舊。
    real_ids = {ev["id"] for ev in real_events}
    event_level_idx = [i for i in range(n_levels)
                       if levels[i]["event_id"] in real_ids]
    # 平日減量另外也管常駐關卡：常駐關卡多半是消化多餘體力的加碼，對求解器來說
    # 平日打或星期日打一樣省，不罰的話它會隨手排在平日（實測：平日
    # 多打了好幾次主線體力減半，用的是星期日才到期的限時體力）。
    standing_ids = {ev["id"] for ev in events if ev["standing"]}
    standing_level_idx = [i for i in range(n_levels)
                          if levels[i]["event_id"] in standing_ids]
    light_level_idx = event_level_idx + standing_level_idx
    # 星期六多出來的要挪到星期日時，限期關卡（檢定、忘卻的加碼）也一起挪；
    # 平日那一輪照舊不管它們
    limited_level_idx = [i for i in range(n_levels)
                         if i not in light_level_idx
                         and (events_by_id.get(levels[i]["event_id"]) or {}).get("limited")]
    # 第幾天 -> 超過當天每日關數的每一關罰多少。手動鎖定的日子打法已經定了；
    # 沒有每日關數任務的日子沒有「幾關算多」可以依據，都不管。
    light_days: dict[int, float] = {}
    if prefs.get("light_weekdays") and light_level_idx:
        for d in range(n_days):
            if d in pinned_idx or d not in daily_clear_floor:
                continue
            weekday = days[d].weekday()
            if weekday in LIGHT_WEEKDAYS:
                light_days[d] = 1.0
            elif weekday == 5:
                light_days[d] = LIGHT_SATURDAY_WEIGHT
        if not any(w == 1.0 for w in light_days.values()):
            light_days = {}
            warnings.append("「平日減量」這次沒有作用：排程範圍內的平日沒有"
                            "「每日打幾關」的任務，沒有關數可以當基準")
    # 活動優先序也管「重疊時誰先打」：排越上面權重越大，整理階段在平日減量之後、
    # 打法簡化之前，把排前面那檔的計分關卡往前換、排後面的往後換。只列一檔或
    # 沒列就不排。
    order_ids = [eid for eid in dict.fromkeys(profile.get("event_priority") or [])
                 if eid in real_ids]
    order_weight: dict[int, int] = {}
    if len(order_ids) >= 2:
        rank = {eid: len(order_ids) - r for r, eid in enumerate(order_ids)}
        order_weight = {i: rank[levels[i]["event_id"]] for i in event_level_idx
                        if levels[i]["event_id"] in rank and points_of[i]}
        if len({levels[i]["event_id"] for i in order_weight}) < 2:
            order_weight = {}
    tidy_note: dict = {}

    # ---- 指定日期打指定次數 ---------------------------------------------
    # 跟上面的手動鎖定不同：只管那一關，當天其他關卡照常由求解器排，當日上限與
    # 任務也照常生效。跟「指定關卡次數限制」也不同：這是「一定要打」。
    # (第幾天, 關卡) -> (方式, 還要打幾次, 你指定的當天總數)。
    # 首日的「還要打幾次」已經扣掉今天記錄過的——模型裡首日的變數本來就是
    # 「從現在起還要打的」，plan_snapshot 會把已打的加回去，合起來正好是指定的總數。
    #
    # 一條規則可以是單一日期、好幾個日期，或「每週星期幾」（level_target_dates）。
    # 每週的先套、有寫日期的後套：「每週六 ×3，但 11/02 那天 ×5」這種例外
    # 不管兩條在清單裡誰先誰後，都是寫日期的那條為準，也不必警告。
    # 每週的規則碰到打不到那一關的日子（活動還沒開始、已經結束……）直接跳過，
    # 不像寫死日期的那樣當成錯誤——「每週六」本來就沒說每個週六都打得到。
    level_target: dict[tuple[int, int], tuple[str, int, int]] = {}
    target_weekly: set[tuple[int, int]] = set()     # level_target 裡哪幾格來自每週規則
    beyond_range = []
    last_day = sched_start + timedelta(days=n_days - 1)
    target_entries = sorted(profile.get("daily_level_targets") or [],
                            key=lambda e: e.get("repeat") != "weekly")
    for entry in target_entries:
        key = entry.get("level_id")
        if key not in level_index:
            level = all_levels.get(key)
            if level is not None:
                warnings.append(
                    f"「{level['label']}」這次不列入計算，它的指定次數規則自動略過")
            else:
                warnings.append(
                    f"指定日期次數的規則找不到關卡「{key}」，已略過"
                    "（可能是關卡被刪掉或改了 id）")
            continue
        i = level_index[key]
        weekly = entry.get("repeat") == "weekly"
        try:
            wanted = int(entry.get("count") or 0)
            target_days = level_target_dates(entry, sched_start, last_day)
        except (TypeError, ValueError, KeyError, PlanError):
            warnings.append(
                f"「{levels[i]['label']}」的指定次數規則日期或次數不完整，已略過")
            continue
        if wanted <= 0:
            continue
        mode = "min" if entry.get("mode") == "min" else "exact"
        applied = 0
        for day in target_days:
            d = (day - sched_start).days
            if d < 0:
                continue          # 已經過去的日子，沒有東西可排
            text = (f"{format_day(day)} {levels[i]['label']}"
                    f"{'至少' if mode == 'min' else ''}×{wanted}")
            if d >= n_days:
                beyond_range.append(text)
                continue
            if weekly and not playable_days[d][i]:
                continue          # 那個星期幾剛好打不到，不算錯
            done = done_counts.get(key, 0) if d == 0 else 0
            remaining = wanted - done
            if remaining < 0:
                if mode == "exact":
                    warnings.append(
                        f"你指定 {text}，但今天已經打了 {done} 次，超過指定的次數；"
                        "今天不會再排這一關")
                remaining = 0
            if d in pinned_idx:
                # 對調日期鎖的是整天，兩邊都硬套只會無解——以鎖定為準
                fixed = pinned_idx[d][i]
                if fixed < remaining or (mode == "exact" and fixed != remaining):
                    warnings.append(
                        f"你指定 {text}，但那天已經照手動調整的打法鎖住"
                        f"（這一關排 {fixed} 次），這次以手動調整為準")
                applied += 1
                continue
            if remaining and not playable_days[d][i]:
                raise PlanError(
                    f"你指定 {text}，但那天打不到這一關"
                    "（活動還沒開始／已經結束、關卡還沒開放，或已經過了上線時段）。\n"
                    "請到「排程設定」的「指定日期打指定次數」改日期或刪掉這條規則。")
            if (d, i) in level_target and not ((d, i) in target_weekly
                                               and not weekly):
                warnings.append(
                    f"{format_day(day)} 的「{levels[i]['label']}」有不只一條指定次數規則，"
                    "以排在後面的那條為準")
            level_target[(d, i)] = (mode, remaining, wanted)
            if weekly:
                target_weekly.add((d, i))
            else:
                target_weekly.discard((d, i))
            applied += 1
        if weekly and not applied and target_days:
            warnings.append(
                f"「{levels[i]['label']}」的每週指定次數規則，在這次的排程範圍裡"
                "沒有一天打得到這一關，沒有排進去")
    if beyond_range:
        warnings.append(
            "這幾條指定次數規則的日期超出這次的排程範圍，沒有排進去"
            "（要排的話把「排到」的日期拉長）：" + "、".join(beyond_range))

    if level_target:
        # 關卡的總次數是遊戲規則，讓不了路——指定的加起來超過就直接講
        target_sum: dict[int, int] = {}
        for (d, i), (_mode, remaining, _wanted) in level_target.items():
            target_sum[i] = target_sum.get(i, 0) + remaining
        for i, need in target_sum.items():
            limit = levels[i].get("max_total")
            if limit is None:
                continue
            left = max(0, int(limit) - played_total.get(levels[i]["key"], 0))
            if need > left:
                raise PlanError(
                    f"你指定的次數排不進去：「{levels[i]['label']}」"
                    f"指定的日子加起來還要打 {need} 次，"
                    f"但它的總次數上限只剩 {left} 次。\n"
                    "請到「排程設定」的「指定日期打指定次數」把次數調低。")

        # 你設的上限讓路（指定優先），但放寬了哪些要講
        over = []
        day_need: dict[int, int] = {}
        event_need: dict[tuple[int, str], int] = {}
        for (d, i), (_mode, remaining, _wanted) in sorted(level_target.items()):
            limit = level_cap.get((d, i))
            if limit is not None and remaining > limit:
                over.append(f"{format_day(days[d])} {levels[i]['label']}"
                            f"×{remaining}（每日上限 {limit}）")
                level_cap[(d, i)] = remaining
            day_need[d] = day_need.get(d, 0) + costs[i] * remaining
            event_key = (d, levels[i]["event_id"])
            event_need[event_key] = (event_need.get(event_key, 0)
                                     + costs[i] * remaining)
        for d, need in sorted(day_need.items()):
            if d in usage_cap and need > usage_cap[d]:
                over.append(f"{format_day(days[d])} 耗體 {need}"
                            f"（當日上限 {usage_cap[d]}）")
                usage_cap[d] = need
        for (d, event_id), need in sorted(event_need.items()):
            limit = event_cap.get((d, event_id))
            if limit is not None and need > limit:
                name = (events_by_id[event_id]["name"]
                        if event_id in events_by_id else event_id)
                over.append(f"{format_day(days[d])}「{name}」耗體 {need}"
                            f"（當日上限 {limit}）")
                event_cap[(d, event_id)] = need
        for d, (group, limit) in sorted(ending_cap.items()):
            need = sum(n for (day, eid), n in event_need.items()
                       if day == d and eid in group)
            if need > limit:
                over.append(f"{format_day(days[d])} 當天結束的活動耗體 {need}"
                            f"（當日上限 {limit}）")
                ending_cap[d] = (group, need)
        if over:
            warnings.append("指定次數超過了你設的上限，這次以指定為準："
                            + "、".join(over))

    # ---- 同一天打完 -----------------------------------------------------
    # 勾了「同一天打完」的關卡：剩下的次數只能落在同一天（約束在 build_and_solve
    # 的 same_day）。跟 must_finish 一樣依附 max_total，而且只剩一次以下時沒有
    # 東西可管。已經打掉的那幾次改不了，這裡只管剩下的。
    same_day_left: dict[int, int] = {}
    for i, lv in enumerate(levels):
        if not lv.get("same_day") or lv.get("max_total") is None:
            continue
        left = max(0, int(lv["max_total"]) - played_total.get(lv["key"], 0))
        if left < 2:
            continue
        # 手動鎖定的日子裡已經排了這一關：你的調整說了算，硬套只會變成無解。
        # 剛好一天排滿的話本來就符合，不必講。
        pinned_days = [d for d, fixed in sorted(pinned_idx.items()) if fixed[i]]
        if pinned_days:
            if len(pinned_days) > 1 or pinned_idx[pinned_days[0]][i] < left:
                warnings.append(
                    f"「{lv['label']}」設了「同一天打完」，但你手動調整的日子（"
                    + "、".join(format_day(days[d]) for d in pinned_days)
                    + "）已經排了它，這次以調整為準，不強制同一天")
            continue
        # 指定次數把它分到好幾天、或「剛好」的次數比剩下的少：同理，以指定為準。
        # 只指定一天而且打得完（或是「至少」）的話兩邊不衝突，照常套。
        target_days = sorted(d for (d, j), spec in level_target.items()
                             if j == i and spec[1])
        if target_days:
            mode, remaining, _wanted = level_target[(target_days[0], i)]
            if len(target_days) > 1 or (mode == "exact" and remaining < left):
                warnings.append(
                    f"「{lv['label']}」設了「同一天打完」，但你指定次數的日子（"
                    + "、".join(format_day(days[d]) for d in target_days)
                    + "）排不成同一天打完，這次以指定為準，不強制同一天")
                continue
        same_day_left[i] = left
        # 送求解前先抓能一眼證明的矛盾（理由同解鎖鏈的預檢）：一定要打滿、又要
        # 同一天，卻沒有任何一天塞得下這麼多次。只勾同一天的話頂多是不打，不會無解。
        if not lv.get("must_finish") or i in deferred_finish:
            continue
        open_days = [d for d in range(n_days)
                     if playable_days[d][i] and d not in pinned_idx]
        if not open_days:
            continue

        def room_on(d: int, i=i, lv=lv) -> int:
            """那一天最多塞得下幾次（當日體力上限與指定關卡次數限制）。"""
            caps = [usage_cap[d]] if d in usage_cap else []
            if event_room(d, lv["event_id"]) is not None:
                caps.append(event_room(d, lv["event_id"]))
            room = min(caps) // costs[i] if caps else left
            return min(room, level_cap.get((d, i), left))

        best = max(open_days, key=room_on)
        if room_on(best) < left:
            raise PlanError(
                "條件互相衝突，無法計算：\n\n"
                f"　「{lv['label']}」設成一定要打滿、而且要同一天打完，"
                f"還剩 {left} 次（共 {left * costs[i]} 點體力），\n"
                "　但它打得到的每一天，當日上限都塞不下這麼多次"
                f"（最寬的 {format_day(days[best])} 也只塞得下 "
                f"{room_on(best)} 次）。\n\n"
                "可以這樣調整：\n"
                "　• 到「排程設定」放寬那幾天的「當日體力使用上限」／"
                "「當日該活動體力上限」／「指定關卡次數限制」\n"
                "　• 到「活動設定」的關卡結構取消它的「同一天打完」")

    # ---- 難度規則：哪幾天真的要擋 ---------------------------------------
    # 手動鎖定的日子打法已經定了；有「指定日期打指定次數」的那天以指定次數為準
    # （原本的功能照常可用）。這兩種日子都不套難度限制，指定次數那種講一聲。
    for rule in stage_rules:
        i = rule["idx"]
        skipped = [d for d in rule["days"] if (d, i) in level_target]
        rule["days"] = [d for d in rule["days"]
                        if d not in pinned_idx and (d, i) not in level_target]
        if skipped:
            warnings.append(
                f"{rule['text']}，但 "
                + "、".join(format_day(days[d]) for d in skipped)
                + " 有「指定日期打指定次數」，那幾天以指定次數為準")

    # ---- 建模與求解 -----------------------------------------------------
    doomed_marker = {}
    priority_note = {}
    plays_note: dict = {}              # 場數階段的前後場數（見 build_and_solve）
    extended_stages: list[str] = []    # 哪幾個階段超時沒解、延長時間重算過
    buy_retry: dict = {}                # 第一階段沒算完時多算的那一輪（見 BUY_RETRY_FACTOR）
    # 這一輪整體在做什麼（放寬目標重算、找排不出來的原因），接在階段名稱前面
    round_label = {"text": ""}

    def report(stage_name: str, detail: str = "") -> None:
        if progress is not None:
            progress(round_label["text"] + stage_name
                     + (f"（{detail}）" if detail else ""))

    def build_and_solve(soft_events: set[str]):
        """建模並跑三（或四）階段。無解回傳 None。

        soft_events 裡的活動，它的「活動期限」類任務改成軟約束——差多少
        由求解器決定並回報，而不是整個算不出來。
        """
        prob = pulp.LpProblem(SOLVER_PROBLEM_NAME, pulp.LpMinimize)

        plays = []
        for d in range(n_days):
            day_rows = []
            for s, seg in enumerate(segments[d]):
                row = []
                for i, lv in enumerate(levels):
                    if seg["playable"] and lv["event_id"] in seg["live"]:
                        row.append(_new_var(prob, f"n_{d}_{s}_{i}", lowBound=0,
                                                   cat="Integer"))
                    else:
                        row.append(None)
                day_rows.append(row)
            plays.append(day_rows)

        day_plays = [[pulp.lpSum([plays[d][s][i] for s in range(len(segments[d]))
                                  if plays[d][s][i] is not None])
                      for i in range(n_levels)] for d in range(n_days)]
        seg_spend = [[pulp.lpSum(costs[i] * plays[d][s][i]
                                 for i in range(n_levels)
                                 if plays[d][s][i] is not None)
                      for s in range(len(segments[d]))] for d in range(n_days)]
        spend = [pulp.lpSum(seg_spend[d]) for d in range(n_days)]

        # 手動鎖定的日子：整天照使用者給的次數打（哪一段打由求解器決定）。
        # 打不到的組合在進來之前就擋掉了，所以這裡一定有變數可以綁。
        for d, fixed in pinned_idx.items():
            for i in range(n_levels):
                if any(plays[d][s][i] is not None
                       for s in range(len(segments[d]))):
                    prob += day_plays[d][i] == fixed[i], f"pin_{d}_{i}"

        # 指定日期打指定次數：只綁那一關，當天其他關卡不受影響。
        # 沒有變數可綁的只會是「還要打 0 次」的（打不到的在進來之前就擋掉了）。
        for (d, i), (mode, remaining, _wanted) in level_target.items():
            if not any(plays[d][s][i] is not None
                       for s in range(len(segments[d]))):
                continue
            if mode == "min":
                if remaining:
                    prob += day_plays[d][i] >= remaining, f"target_{d}_{i}"
            else:
                prob += day_plays[d][i] == remaining, f"target_{d}_{i}"

        use_nat, use_other, waste, balance = [], [], [], []
        for d in range(n_days):
            n_segs = len(segments[d])
            use_nat.append([_new_var(prob, f"nat_{d}_{s}", lowBound=0)
                            for s in range(n_segs)])
            use_other.append([_new_var(prob, f"oth_{d}_{s}", lowBound=0)
                              for s in range(n_segs)])
            waste.append([_new_var(prob, f"waste_{d}_{s}", lowBound=0)
                          for s in range(n_segs)])
            balance.append([_new_var(prob, f"bal_{d}_{s}", lowBound=0, upBound=cap)
                            for s in range(n_segs)])

        pool_use = [[_new_var(prob, f"pool_{p}_{d}", lowBound=0)
                     for d in range(n_days)] for p in range(len(pools))]
        use_wk = [pulp.lpSum(pool_use[p][d] for p in range(len(pools)))
                  for d in range(n_days)]
        buy = [_new_var(prob, f"buy_{d}", lowBound=0) for d in range(n_days)]

        prev = initial_stamina
        for d in range(n_days):
            for s in range(len(segments[d])):
                # 自然回復池逐段結算：這一段回復進來、打關卡花掉，
                # 超過上限的部分就在這一段浪費掉（balance 的上界是體力上限）
                prob += (balance[d][s] == prev + segments[d][s]["recovery"]
                         - waste[d][s] - use_nat[d][s])
                prob += seg_spend[d][s] == use_nat[d][s] + use_other[d][s]
                if not playable_of[d][s]:
                    prob += use_nat[d][s] == 0
                    prob += use_other[d][s] == 0
                prev = balance[d][s]
            # 非自然回復的來源是「當天」結算的：限時體力依日期發放，
            # 買體力也沒有段落之分，所以只要求各段用掉的總量等於當天的供給。
            prob += (pulp.lpSum(use_other[d]) == use_wk[d] + buy[d])

            # 每日最低關卡數／敵人數／耗體都由任務條件產生（見 constraints），
            # 這裡不再重複加，否則特殊日的「當日覆蓋」會被原始要求蓋回去。
            # 手動鎖定的日子不套當日上限——打法已經定了，再加只會變成無解
            if d in pinned_idx:
                continue
            if d in usage_cap:
                prob += spend[d] <= usage_cap[d]
            for (cap_day, cap_event), limit in event_cap.items():
                if cap_day == d:
                    prob += pulp.lpSum(
                        costs[i] * day_plays[d][i] for i in range(n_levels)
                        if levels[i]["event_id"] == cap_event) <= limit
            if d in ending_cap:
                group, limit = ending_cap[d]
                prob += pulp.lpSum(
                    costs[i] * day_plays[d][i] for i in range(n_levels)
                    if levels[i]["event_id"] in group) <= limit
            for (cap_day, cap_level), limit in level_cap.items():
                if cap_day == d:
                    prob += day_plays[d][cap_level] <= limit

        # 代幣關卡：每天最多打「當天手上的代幣」那麼多次。
        # held[d]＝那天開始時有幾個（首日是常數＝從現在起還有幾個）；
        # 隔天 ≤ 今天剩的＋每天發的，也 ≤ 上限。用「≤」不用 min()：模型裡的
        # 代幣數只會比實際少，排得出來的打法實際一定打得到。
        # 手動鎖定、指定次數的日子以你的安排為準，不擋；區間外的日子沒有這條
        # 規則。這幾種日子之後的代幣數不再往前推，只當成頂多存滿。
        for r, rule in enumerate(token_rules):
            i, held = rule["idx"], rule["start"]
            for d in range(n_days):
                free = (d not in rule["days"] or d in pinned_idx
                        or (d, i) in level_target)
                if not free:
                    prob += day_plays[d][i] <= held, f"token_{r}_{d}"
                if d == n_days - 1:
                    break
                after = _new_var(prob, f"token_held_{r}_{d + 1}", lowBound=0,
                                        upBound=rule["max"])
                if not free:
                    prob += (after <= held - day_plays[d][i] + rule["per_day"],
                             f"token_flow_{r}_{d}")
                held = after

        # 難度規則：第 k 關（第 k 次通關）只能在允許的星期幾打。
        # passed[k][d]＝那天結束時累計次數 ≥ k（跟 claim 的 reached_ 同一個寫法）。
        # 不能打的那天 passed 不准變：前一天沒到 k，這天也不能到。
        for r, rule in enumerate(stage_rules):
            if not rule["days"]:
                continue
            i, big = rule["idx"], rule["max_total"]
            blocked = set(rule["days"])
            running = rule["prior"]
            totals = []
            for d in range(n_days):
                running = running + day_plays[d][i]
                totals.append(running)
            for k in rule["stages"]:
                passed = [_new_var(prob, f"stage_{r}_{k}_{d}", cat="Binary")
                          for d in range(n_days)]
                for d in range(n_days):
                    prob += totals[d] >= k * passed[d]
                    prob += totals[d] <= k - 1 + big * passed[d]
                    if d in blocked:
                        # 寫成「相減 == 0」：PuLP 4.x 的「變數 == 變數」是比較兩個物件，
                        # 會得到 False 而不是一道限制式
                        prob += passed[d] - (passed[d - 1] if d else 0) == 0

        # 限時體力：發放日之後才能用（不能預支明天才會拿到的），到期日之後就消失
        for p, pool in enumerate(pools):
            if "claim" in pool:
                continue          # 候選池在下面另外處理
            cumulative = 0
            for d in range(n_days):
                cumulative += pool["grants"][d]
                if d > pool["last_idx"]:
                    prob += pool_use[p][d] == 0
                else:
                    prob += (pulp.lpSum(pool_use[p][k] for k in range(d + 1))
                             <= cumulative)

        # 先放著、晚點再領的體力（見 claim_lots）：每批最多選一週整筆領，
        # 都不選＝排程範圍內不領、留到之後。任務獎勵還要等達標——達標那天的
        # 體力隔天才算進來，否則它會拿「達標後才有」的體力去湊同一個目標。
        claim_y = {}
        reached = {}
        for k, lot in enumerate(claim_lots):
            for p in lot["pools"]:
                claim_y[p] = _new_var(prob, f"claim_{p}", cat="Binary")
            if lot["pools"]:
                prob += pulp.lpSum(claim_y[p] for p in lot["pools"]) <= 1
            spec = lot["reach"]
            if spec is None:
                continue
            flags = [_new_var(prob, f"reached_{k}_{d}", cat="Binary")
                     for d in range(n_days)]
            reached[k] = flags
            for d in range(n_days):
                upto = dict(spec, cells=[c for c in spec["cells"] if c[0] <= d])
                prob += (_metric_expr(pulp, upto, plays, seg_spend, enemies_of,
                                      points_of, drops_of)
                         >= spec["need"] * flags[d])
                if d:
                    prob += flags[d - 1] <= flags[d]
        for p, pool in enumerate(pools):
            if "claim" not in pool:
                continue
            k = pool["claim"]
            flags = reached.get(k)
            amount = pool["total"]
            for d in range(n_days):
                if d < pool["open_idx"] or d > pool["last_idx"]:
                    prob += pool_use[p][d] == 0
                    continue
                used = pulp.lpSum(pool_use[p][j] for j in range(d + 1))
                prob += used <= amount * claim_y[p]
                if flags is not None:
                    prob += used <= (amount * flags[d - 1] if d else 0)
            if flags is not None and not claim_lots[k].get("auto"):
                last = pool["week_last_idx"]
                prob += claim_y[p] <= (flags[last - 1] if last >= 1 else 0)
        # 達標自動領取：沒有「晚點再領」的選擇——達標那一週就是領的那一週
        # （效期從那週算；體力照樣隔天才能用，上面的 flags[d - 1] 管）。
        # 第 w 週領 ＝ 這週結束時已達標、這週開始前還沒。已經達標的就是第一週。
        for k, lot in enumerate(claim_lots):
            if not lot.get("auto") or not lot["pools"]:
                continue
            flags = reached.get(k)
            if flags is not None:
                # 手動領取時 flags 可以「明明達標了卻記 0」（等於晚點再領），自動
                # 領取不行：進度一到就一定記 1。big-M 取整個排程拿得到的上界。
                spec = lot["reach"]
                weight = {"points": points_of, "enemies": enemies_of,
                          "drops": drops_of}.get(spec["metric"])
                ratio = max(((weight[i] if weight else 1) / max(1, costs[i])
                             for i in spec["levels"]), default=1)
                if spec["metric"] == "stamina":
                    ratio = 1
                big_m = math.ceil(unlock_supply * n_days * ratio) + spec["need"]
                for d in range(n_days):
                    upto = dict(spec, cells=[c for c in spec["cells"] if c[0] <= d])
                    prob += (_metric_expr(pulp, upto, plays, seg_spend, enemies_of,
                                          points_of, drops_of)
                             - spec["need"] + 1 <= big_m * flags[d])
            for p in lot["pools"]:
                pool = pools[p]
                if flags is None:
                    prob += claim_y[p] == (1 if p == lot["pools"][0] else 0)
                    continue
                before = flags[pool["open_idx"] - 1] if pool["open_idx"] >= 1 else 0
                prob += claim_y[p] == flags[pool["week_last_idx"]] - before

        # 關卡的開放起日：還沒開放的日子一次都不能打
        for i, lv in enumerate(levels):
            offset = lv.get("available_from")
            if offset is None:
                continue
            event = events_by_id.get(lv["event_id"]) or primary
            opens = offset_from_start(int(offset), event["start"])
            for d in range(n_days):
                if days[d] < opens:
                    prob += day_plays[d][i] == 0

        # 關卡的總次數：整檔活動總共幾次，要扣掉已經打掉的。
        # 勾了「一定要打滿」（活動BOSS關）就同時是下限——體力不夠時會反映在
        # 購買量上，不會因此無解。
        for i, lv in enumerate(levels):
            limit = lv.get("max_total")
            # 用 is None：限期關卡的帳號上限可以填 0（這個帳號這一檔不能打）
            if limit is None:
                continue
            left = max(0, int(limit) - played_total.get(lv["key"], 0))
            total_plays = pulp.lpSum(day_plays[d][i] for d in range(n_days))
            prob += total_plays <= left
            if lv.get("must_finish") and left and i not in deferred_finish:
                prob += total_plays >= left, f"must_finish_{i}"

        # 同一天打完：剩下的次數只能落在同一天。pick 是「這天打不打這一關」的
        # 0/1 指示變數；右邊的係數就是總次數的上界（上面的 total_plays <= left），
        # 所以是緊的，不是解鎖閘門那種估出來的 big-M。搭配 must_finish 就是
        # 「挑一天一次打滿」；沒勾 must_finish 則是「要打就只在一天打」。
        for i, left in same_day_left.items():
            picks = []
            for d in range(n_days):
                if not any(plays[d][s][i] is not None
                           for s in range(len(segments[d]))):
                    continue
                pick = _new_var(prob, f"same_day_{i}_{d}", cat="Binary")
                prob += day_plays[d][i] <= left * pick, f"same_day_use_{i}_{d}"
                picks.append(pick)
            if picks:
                prob += pulp.lpSum(picks) <= 1, f"same_day_once_{i}"

        # 解鎖鏈：便宜的那關沒先打過一次，比它貴的關卡整天都不能打。
        #
        # 跟 must_finish 刻意**完全解耦**：must_finish 依附 max_total，而且上下界
        # 會把總次數夾成等式（「整檔活動只能打 1 次」）；這裡要的是「至少先打
        # 1 次、之後還能猛打」，所以是獨立的 >= 1 再加一道閘門。
        #
        # cum 含**當天**的次數，這是刻意的：LP 裡沒有任何東西能表達日內先後
        # （schedule 的 counts 會把段落加總掉，一般日子也只有一個可打段），所以
        # 閘門只保證「同一天或更早」。同一天「關卡1 打 1 次 → 關卡2 開了 → 關卡5
        # 猛打」是允許的，那正好就是實際玩法。真正的日內順序靠
        # schedule[d]["unlocks"] 在報表上講——跟 deadlines 同一個路子：有先後
        # 語意但不進 LP。**這是唯一一處排程說可行、現實需要照順序打的地方。**
        #
        # shorts：被放寬的目標「還差多少」。鍵是任務在 constraints 的索引，或
        # ("unlock", 關卡索引)——分組解鎖型活動被放寬時的「至少打一次」。
        shorts = {}
        for chain in unlock_chains:
            cum = {}
            for i in chain["levels"]:
                running = unlock_prior[i]
                for d in range(n_days):
                    running = running + day_plays[d][i]
                    cum[(d, i)] = running
            for i in chain["need"]:
                once = pulp.lpSum(day_plays[d][i] for d in range(n_days))
                if chain["soft_ok"] and chain["event"]["id"] in soft_events:
                    # 分組解鎖型活動被放寬時，「至少一次」跟活動任務一樣變成
                    # 「差多少由求解器決定並回報」。閘門不動。
                    short = _new_var(prob, f"short_unlock_{i}", lowBound=0,
                                            upBound=1)
                    shorts[("unlock", i)] = short
                    prob += once + short >= 1, f"unlock_once_{i}"
                else:
                    prob += once >= 1, f"unlock_once_{i}"
            for prev_tier, tier in zip(chain["tiers"], chain["tiers"][1:]):
                # 同耗體的關卡是同一階、彼此沒有先後，所以第 t 階的每一關要對第
                # t-1 階的**每一關**各建一條閘門，不能串成一條線。已經打過的那幾關
                # 不必再當閘門（cum 恆 >= 1，等於沒有限制）。
                gates = [j for j in prev_tier if unlock_prior[j] < 1]
                for i in tier:
                    for d in range(n_days):
                        # 那天根本沒建變數（活動還沒開／已經收攤／不在上線時段）
                        # → day_plays 是常數 0，加進去只是一條沒有任何變數的空
                        # 約束，白佔矩陣一列。
                        if not any(plays[d][s][i] is not None
                                   for s in range(len(segments[d]))):
                            continue
                        for j in gates:
                            prob += (day_plays[d][i]
                                     <= unlock_cap[i] * cum[(d, j)],
                                     f"unlock_gate_{i}_{j}_{d}")

        # 任務
        for index, spec in enumerate(constraints):
            expr = _metric_expr(pulp, spec, plays, seg_spend,
                                enemies_of, points_of, drops_of)
            soft = spec["soft_ok"] and spec["event_id"] in soft_events
            # 週期性任務（每日／每週…）平常是硬條件；它的重置窗碰到手動鎖定的
            # 日子時，以使用者的調整為準——差多少由求解器壓到最小並回報。
            if (not spec["soft_ok"]
                    and any(d in pinned_idx for d in spec["days"])):
                spec["pinned_soft"] = True
                soft = True
            if soft:
                short = _new_var(prob, f"short_{index}", lowBound=0)
                shorts[index] = short
                prob += expr + short >= spec["need"]
            else:
                prob += expr >= spec["need"]

        def run_stage(objective, stage_name, limits=None):
            """解一個階段。回傳 (是否收斂, 是否可行)。

            limits：依序試的時間上限；沒給就是平常的「一般 → 延長重算」兩段。
            """
            prob.setObjective(objective)
            # 「Not Solved」＝時間到了還沒找到任何一組可行解。這時變數裡留的不是
            # 可行解，當成有解往下走的話，後面的階段會鎖在一組不存在的排法上而
            # 變成「無解」（實測偏好階段就發生過）。所以延長時間重算一次，
            # 還是找不到才算這個階段失敗。
            #
            # warmStart：把上一階段的解交給 CBC 當起點。每一階段都只是在上一階段
            # 的解上多加一道鎖，那組解本身一定還可行——有了起點就不會「時間到了
            # 一組解都沒有」（實測總時間少了大半）。Windows 上的 CBC 要
            # keepFiles 才吃 warmStart，留下的暫存檔由 _remove_solver_files 收掉。
            # 暫存檔寫在工作目錄，寫不進去就不用 warmStart（只是慢，不會錯）。
            warm = os.access(os.getcwd(), os.W_OK)
            for attempt_no, limit in enumerate(
                    limits or (time_limit, time_limit * TIMEOUT_RETRY_FACTOR)):
                report(stage_name, f"最多 {limit} 秒" if attempt_no == 0
                       else f"時間不夠還沒找到解，已延長到 {limit} 秒重算")
                started = time.monotonic()
                status = _solve(pulp, prob,
                                msg=0, timeLimit=limit, gapRel=GAP_TOLERANCE,
                                warmStart=warm, keepFiles=warm)
                elapsed = time.monotonic() - started
                if status != "Not Solved":
                    break
                if limit == time_limit and stage_name not in extended_stages:
                    extended_stages.append(stage_name)
            if status in ("Infeasible", "Not Solved"):
                return False, False
            if status == "Unbounded":
                raise PlanError(f"模型無界（{stage_name}），請檢查關卡的體力與積分數值")
            if pulp.value(prob.objective) is None:
                return False, False
            # pulp 在 CBC 因時間上限停止時仍可能回報 Optimal，所以改用實際耗時判斷
            return elapsed < limit * 0.95, True

        # 第零階段（只有降級時才有）：先讓「差多少」最小
        if shorts:
            # 「至少打一次」差的是關數（0~1），任務差的是分數／體力／次數。漏打一關
            # 以它的耗體計價，才不會被當成跟「差 1 分」一樣便宜。
            short_total = pulp.lpSum(
                (costs[key[1]] if isinstance(key, tuple) else 1) * var
                for key, var in shorts.items())
            proven_0, ok = run_stage(short_total, "缺口階段")
            if not ok:
                return None
            min_short = pulp.value(short_total) or 0.0
            prob += short_total <= min_short + 0.001, "lock_short"
        else:
            proven_0 = True

        # 加班階段（只有查詢時已經過了上線時段才有）：今天剩下的時間只拿來補完
        # 今天還沒完成的任務。先把加班時段的耗體壓到最低、鎖住，後面的階段
        # （補充量、耗體、加碼、整理……）都不准在加班時段多排——就算多打幾關
        # 能讓排程更省，也不該叫已經過了休息時間的人繼續打。
        if overtime_cells:
            overtime_spend = pulp.lpSum(
                costs[i] * plays[d][s][i] for d, s in overtime_cells
                for i in range(n_levels) if plays[d][s][i] is not None)
            proven_ot, ok = run_stage(overtime_spend, "加班階段")
            if not ok:
                return None
            proven_0 = proven_0 and proven_ot
            prob += (overtime_spend <= (pulp.value(overtime_spend) or 0.0) + 0.001,
                     "lock_overtime")

        # 第一階段：最少要額外補充多少體力（係數全為 1.0，好解）
        proven_1, ok = run_stage(pulp.lpSum(buy), "第一階段")
        if not ok:
            return None
        min_buy = pulp.value(pulp.lpSum(buy)) or 0.0
        buy_retry.clear()
        if not proven_1 and min_buy > 0.5:
            # 接著剛才那組解再算一輪（warmStart）。沒有變少就退回原本那組。
            saved = {v: v.varValue for v in prob.variables()}
            longer = time_limit * BUY_RETRY_FACTOR
            proven_retry, ok = run_stage(pulp.lpSum(buy), "第一階段（補充量多算一輪）",
                                         limits=(longer,))
            after = (pulp.value(pulp.lpSum(buy)) or 0.0) if ok else None
            if after is not None and after < min_buy - 0.5:
                buy_retry.update(before=min_buy, after=after, proven=proven_retry,
                                 seconds=longer)
                min_buy, proven_1 = after, proven_retry
            else:
                for v, old in saved.items():
                    v.varValue = old
                buy_retry.update(before=min_buy, after=None, proven=False,
                                 seconds=longer)

        # 第二階段：補充量維持不變的前提下，求最省耗體。
        # 容差是為了吸收浮點誤差，避免第二階段因為 0.0000001 的差距變成無解。
        prob += pulp.lpSum(buy) <= min_buy + 0.001, "lock_buy"
        last_week = max(weeks_in_scope) if weeks_in_scope else None
        last_week_days = [d for d in range(n_days) if week_of_day[d] == last_week]
        # 依到期日把池子分成兩種：
        #   doomed  —— 排程結束前就過期，不用掉就是全損
        #   savable —— 排程結束當天或之後才到期，可以留到下一檔活動
        # 兩者對求解器不能等價，否則它會隨手挑一個用（見 SAVE_FOR_NEXT 的說明）。
        doomed = [p for p, pool in enumerate(pools) if pool["end"] < last_end]
        savable = [p for p in range(len(pools)) if p not in doomed]
        doomed_marker["doomed"] = doomed
        savable_use = pulp.lpSum(pool_use[p][d] for p in savable
                                 for d in range(n_days))
        # 信箱／任務獎勵「哪一週領」決定它是 doomed 還是 savable：晚點領就到期在
        # 排程之後（或乾脆排程內不領），早點領就變成「排程內會過期」。只罰
        # savable 的用量的話，提早領是零成本的——求解器會把留得住的信箱提早
        # 領出來當成會過期的體力用，第三階段再拿它去刷不計分的關卡（實測曾把
        # 兩千多點下個月才到期的信箱提早領出來，結果當月就過期）。
        # 所以留得住的那幾批，領進 doomed 的那一週＝整筆按 SAVE_FOR_NEXT 計價，
        # 跟「領進 savable、用掉多少罰多少」同一把尺。
        savable_lots = {k for k, lot in enumerate(claim_lots)
                        if not lot.get("auto") and (
                            lot["deadline"] > days[-1]
                            or any(p in savable for p in lot["pools"]))}
        early_claim = pulp.lpSum(pools[p]["total"] * claim_y[p]
                                 for k in savable_lots for p in claim_lots[k]["pools"]
                                 if p in doomed)
        savable_use = savable_use + early_claim
        all_waste = pulp.lpSum(w for day_w in waste for w in day_w)
        # 花在不計分關卡上的體力、以及排出來的總積分。總耗體被逼著花掉時，
        # 這兩項決定它花到哪裡去：先別花在沒分的關卡，再來同樣耗體多拿分。
        idle_spend = pulp.lpSum(costs[i] * day_plays[d][i]
                                for d in range(n_days)
                                for i in range(n_levels)
                                if not levels[i]["scoring"])
        scoring_points = pulp.lpSum(points_of[i] * day_plays[d][i]
                                    for d in range(n_days)
                                    for i in range(n_levels) if points_of[i])
        # 積分的天花板（見 CAP_OVERSHOOT_PENALTY 的註解）。兩個來源取較嚴的那個：
        #   * 積分上限——獎勵表封頂，超過再打什麼都拿不到
        #   * 積分任務的目標——達標之後再多拿也不會讓任務更達成
        # 兩個都沒有的活動下面整段是空的，送進 CBC 的模型跟沒有這個功能時完全一樣，
        # 排出來的結果才不會無謂地飄。上面那條 scoring_points 一個字都不動。
        cap_overshoot = []
        cap_idle_relief = []
        for event in events:
            indices = [i for i in range(n_levels)
                       if levels[i]["event_id"] == event["id"] and points_of[i]]
            if not indices:
                continue
            limits = []
            # 變數名不能叫 cap——那是這個函式裡的體力上限，會被變成區域變數
            points_cap = event.get("points_cap")
            if points_cap is not None:
                # 剩餘額度以**這個帳號**目前的積分為準，跟 derived_progress 同一個來源
                done_points = int((profile_events.get(event["id"]) or {})
                                  .get("current_points") or 0)
                limits.append(max(0, int(points_cap) - done_points))
            # 任務目標。need 已經是「這次排程還要再拿多少」，跟下面的 gained 同一個
            # 單位，不必再扣一次已完成量。
            #   * 取 max 不是 min——同一檔活動的多條積分任務都是下界，天花板低於
            #     其中任何一條的話，模型一定要付溢出的罰金才可行
            #   * 只認預設範圍的——gained 是整檔活動所有計分關卡的總和，scope 指定
            #     子集的任務目標對不上這個式子
            targets = [spec["need"] for spec in constraints
                       if spec.get("whole_event") and spec["metric"] == "points"
                       and spec["event_id"] == event["id"] and spec["default_scope"]]
            # 已經達成的積分任務＝這次排程不必再拿分（取 max，所以還有別條沒達成
            # 時以那條為準）
            if event["id"] in met_points_events:
                targets.append(0)
            if targets:
                limits.append(max(targets))
            if not limits:
                continue
            ceiling = min(limits)
            gained = pulp.lpSum(points_of[i] * day_plays[d][i]
                                for d in range(n_days) for i in indices)
            # 溢出變數讓這條上界「很貴但不是死的」：解鎖鏈一定要打的那幾關、或是
            # 積分任務的目標高於上限時，寧可貴也不要整份排程算不出來
            over = _new_var(prob, f"cap_over_{event['id']}", lowBound=0)
            prob += gained <= ceiling + over, f"points_cap_{event['id']}"
            cap_overshoot.append(over)
            # 光壓住積分總量還不夠。idle_spend 在罰不計分關卡，所以求解器會改用
            # **CP 最低**的關卡把同樣的積分攤到更多體力上——實測排出關卡2×兩百多次、
            # 比改用最高 CP 的關卡多花了將近一成的體力才湊到封頂。
            # 湊滿天花板最少要 ceiling ÷ 最高CP 的體力，超過那條線的計分體力就不再
            # 換到任何有效積分，罰則要壓過 idle_spend 才會把體力讓給常駐關卡：
            # 每點 1.0 ＋ 0.4 ＝ 1.4 > 不計分關卡的 1.0 ＋ 0.2 ＝ 1.2。
            # （這條線是「最好情況」的下界；解鎖鏈逼著先打便宜關卡時會略為低估，
            #   那點差額只是多算一點成本，不會讓它放棄湊滿上限——放棄要賠 0.2×CP。）
            best_cp = max((points_of[i] / costs[i] for i in indices if costs[i]),
                          default=0)
            if best_cp:
                scoring_spend = pulp.lpSum(costs[i] * day_plays[d][i]
                                           for d in range(n_days) for i in indices)
                waste_spend = _new_var(prob, f"cap_spend_{event['id']}", lowBound=0)
                prob += (waste_spend >= scoring_spend - ceiling / best_cp,
                         f"cap_spend_{event['id']}")
                cap_idle_relief.append(waste_spend)
        stage2 = (
            pulp.lpSum(spend)
            + WASTE_PENALTY * all_waste
            + PREFER_NATURAL * pulp.lpSum(use_wk)
            + LAST_WEEK_PENALTY * pulp.lpSum(use_wk[d] for d in last_week_days)
            + SAVE_FOR_NEXT * savable_use
            + PREFER_SCORING * idle_spend
            - PREFER_SCORING * scoring_points
            + (CAP_OVERSHOOT_PENALTY * pulp.lpSum(cap_overshoot)
               if cap_overshoot else 0)
            + (2 * PREFER_SCORING * pulp.lpSum(cap_idle_relief)
               if cap_idle_relief else 0))
        proven_2, ok = run_stage(stage2, "第二階段")
        if not ok:
            return None

        # 場數階段：第二階段整個目標鎖住，再從「一樣省」的排法裡挑總場數最少的。
        #
        # 第二階段有 0.5% 的 gap（數十個單位），積分目標被釘死的活動常常因此多花
        # 幾十點體力、用 CP 低的關卡湊同樣的分——實測某檔復刻排出
        # 關卡1 打十幾次，改用關卡4 可以少十幾場、還少幾十點體力。對求解器那是平手，對
        # 使用者卻是多打十幾場。鎖住再最小化場數，耗體只會更少、不會更多。
        # 鎖（lock_plays）一路留到第三階段之前，免得效期、偏好、提早階段把場數
        # 換回去；第三階段之後由各階段自己的 keep_total／tidy_plays 守住。
        total_plays = pulp.lpSum(day_plays[d][i] for d in range(n_days)
                                 for i in range(n_levels))
        plays_note["before"] = int(round(pulp.value(total_plays) or 0))
        saved = {v: v.varValue for v in prob.variables()}
        stage2_value = pulp.value(stage2) or 0.0
        prob += (stage2 <= stage2_value + max(0.01, abs(stage2_value) * 1e-7),
                 "lock_stage2")
        proven_2p, ok = run_stage(total_plays, "場數階段")
        _drop_constraint(prob, "lock_stage2")
        if ok:
            proven_2 = proven_2 and proven_2p
            plays_note["after"] = int(round(pulp.value(total_plays) or 0))
        else:
            for v, old in saved.items():
                v.varValue = old
            plays_note["failed"] = True
        prob.addConstraint(
            total_plays <= (pulp.value(total_plays) or 0.0) + 0.001, "lock_plays")

        # 效期階段（勾了「多的限時體力留在晚到期的」才跑）：同樣會過期的幾批之間，
        # 第二階段用哪一批都一樣，等於隨便挑，常常剩下最早到期的那批。這裡把第二
        # 階段整個目標鎖住，再挑「先用早到期的」那個排法——剩下的留在晚到期的，
        # 臨時有新關卡時手上還有。後面的階段（第三階段除外，加碼本來就會多用）
        # 各自在當下的值再鎖一次，免得把順序換回去。
        expiry_rank = {expire: k for k, expire in
                       enumerate(sorted({pool["expire"] for pool in pools}))}
        lateness = None
        if expire_late and len(expiry_rank) >= 2:
            # 信箱／任務獎勵的候選池反過來：同一批越晚領（到期越晚）權重越小，
            # 用得到時偏好晚一週領；權重都不低於那批最晚一週的名次，所以先用包包
            # 裡快過期的，信箱留著（照到期日排的話等於鼓勵提早領——實測曾把
            # 隔幾天才用的禮包排在週日領，晚一天到下週一再領，到期日就能晚一週）。
            last_rank = {}
            for p, pool in enumerate(pools):
                if "claim" in pool:
                    k = pool["claim"]
                    last_rank[k] = max(last_rank.get(k, 0), expiry_rank[pool["expire"]])

            def weight(p):
                rank = expiry_rank[pools[p]["expire"]]
                if "claim" in pools[p]:
                    return 2 * last_rank[pools[p]["claim"]] - rank
                return rank

            lateness = pulp.lpSum(weight(p) * pool_use[p][d]
                                  for p in range(len(pools)) for d in range(n_days)
                                  if weight(p))

            def leftover_by_expiry():
                left = {}
                for p, pool in enumerate(pools):
                    granted = (pool["total"] * int(round(pulp.value(claim_y[p]) or 0))
                               if p in claim_y else pool["total"])
                    used = sum(pulp.value(pool_use[p][d]) or 0 for d in range(n_days))
                    if granted - used > 0.5:
                        left[pool["expire"]] = (left.get(pool["expire"], 0)
                                                + int(round(granted - used)))
                return left

            expiry_note["before"] = leftover_by_expiry()
            saved = {v: v.varValue for v in prob.variables()}
            stage2_value = pulp.value(stage2) or 0.0
            prob += (stage2 <= stage2_value + max(0.01, abs(stage2_value) * 1e-7),
                     "lock_stage2")
            proven_2c, ok = run_stage(lateness, "效期階段")
            _drop_constraint(prob, "lock_stage2")
            if ok:
                proven_2 = proven_2 and proven_2c
                expiry_note["after"] = leftover_by_expiry()
            else:
                for v, old in saved.items():
                    v.varValue = old
                expiry_note["failed"] = True

        def expiry_locks(prefix):
            """後面的階段要守住效期階段挑的順序：在當下的值鎖一道，回傳名稱清單。"""
            if lateness is None or expiry_note.get("failed"):
                return []
            name = f"{prefix}_expiry"
            prob.addConstraint(lateness <= (pulp.value(lateness) or 0.0) + 0.001, name)
            return [name]

        # 偏好階段（只有排了關卡優先序才跑）：第二階段整個目標鎖在它算出來的值，
        # 再從「一樣好」的排法裡挑最偏向排前面關卡的那個。
        #
        # 為什麼另開一階段而不是在第二階段加一個小係數：0.5% 的 gap（數十個單位）
        # 會把任何「小到不影響耗體」的係數整個吞掉，求解器根本不會理它；而大到
        # 壓得過 gap 的係數又會開始跟耗體交換。鎖住再最大化，才保證一點都不多花。
        # 以體力加權（而不是次數），否則會偏好便宜的關卡刷次數。
        preferred = None
        if priority_weight:
            preferred = pulp.lpSum(w * costs[i] * day_plays[d][i]
                                   for i, w in priority_weight.items()
                                   for d in range(n_days))
            stage2_value = pulp.value(stage2) or 0.0
            # 容差只為了吸收浮點誤差：鎖的是剛剛那組解自己的值，它一定滿足
            prob += (stage2 <= stage2_value + max(0.01, abs(stage2_value) * 1e-7),
                     "lock_stage2")
            pref_locks = expiry_locks("pref")
            proven_2b, ok = run_stage(-preferred, "偏好階段")
            for name in pref_locks:
                _drop_constraint(prob, name)
            if not ok:
                # 理論上不會發生（第二階段的解本身就滿足鎖）。真的發生就退回沒有
                # 偏好的排程，不要因為一個平手偏好讓整份排程算不出來。
                _drop_constraint(prob, "lock_stage2")
                proven_2b, ok = run_stage(stage2, "第二階段")
                if not ok:
                    return None
                priority_note["failed"] = True
            else:
                # 這道鎖只屬於偏好階段。留著的話第三階段一關都加不了——它鎖住的
                # 式子裡有總耗體，任何加碼都會違反它。
                _drop_constraint(prob, "lock_stage2")
            proven_2 = proven_2 and proven_2b

        # 提早階段（見 EARLY_WEIGHT）。兩組活動共用下面這幾個小工具：
        #   * 開關開（early_first）——排在第三階段**之前**：日期前多餘的體力先被
        #     計分關卡吃掉，第三階段的加碼自然落到日期之後
        #   * 開關關（early_after）——排在第三階段**之後**：加碼照原樣打，只拿
        #     加碼吃不完的體力來挪
        def early_points(group):
            return pulp.lpSum(points_of[i] * day_plays[d][i]
                              for entry in group
                              for d in entry["days"] for i in entry["levels"])

        def lock_now(expr, name):
            """把一條式子鎖在目前這組解的值（只准更小）。回傳約束名稱。"""
            # addConstraint 而不是 `prob +=`：後者在巢狀函式裡會把 prob 變成區域變數
            prob.addConstraint(expr <= (pulp.value(expr) or 0.0) + 0.001, name)
            return name

        def run_early(group, locks, stage_name):
            """鎖住之後最大化日期前的積分。失敗就還原成進來時那組解。"""
            saved = {v: v.varValue for v in prob.variables()}
            proven, ok = run_stage(stage2 - EARLY_WEIGHT * early_points(group),
                                   stage_name)
            if not ok:
                for v, old in saved.items():
                    v.varValue = old
                early_note["failed"] = True
                proven = True
            for name in locks:
                _drop_constraint(prob, name)
            return proven

        proven_early = True
        if early_first:
            locks = [lock_now(pulp.lpSum(spend), "early_spend")]
            if savable:
                locks.append(lock_now(savable_use, "early_savable"))
            if cap_overshoot:
                locks.append(lock_now(pulp.lpSum(cap_overshoot), "early_cap"))
            locks += expiry_locks("early")
            # 解完三道鎖都要拿掉：留著總耗體那一道的話第三階段一關都加不了，
            # 另外兩道第三階段有自己的（keep_savable、積分天花板的罰則）。
            proven_early = run_early(early_first, locks, "提早階段")

        # 整理階段（見 LIGHT_WEEKDAYS）。排在**所有階段的最後**：加碼先定下來，
        # 整理只挪活動的關卡，其他關卡每一段的次數整個釘死。
        #
        # 為什麼不能排在第三階段之前：加碼靠「每天限打幾次」的常駐關卡吸收溢出的
        # 體力，底線排程一挪，溢出就集中到某幾天、那幾天的常駐關卡吸不完——實測
        # 加碼少回收了幾十點，等於多浪費。放在最後、把「浪費 − 已回收的限時體力」
        # 鎖住，就只能在不變差的範圍裡挪。
        # 「盡量提早」是使用者明確設的日期，所以日期前的積分也鎖住。
        def run_tidy():
            """平日減量＋打法簡化。失敗就還原成進來時那組解。回傳是否收斂。"""
            if (not light_days and not (simplify_days and event_level_idx)
                    and not order_weight):
                return True
            # 哪一週領、哪天達標在這裡都不動：貪婪法逐步驗證時要的是純 LP，
            # 留著 0/1 變數每一步都變成整數規劃。挪動讓達標日往後跑的話 LP 會擋下。
            claim_flags = list(claim_y.values()) + [v for flags in reached.values()
                                                    for v in flags]
            claim_bounds = {v: (v.lowBound, v.upBound) for v in claim_flags}
            for v in claim_flags:
                v.lowBound = v.upBound = int(round(v.varValue or 0))
            # 平日減量有開才放開常駐關卡；簡化與優先序只動活動關卡
            movable = set(light_level_idx if light_days else event_level_idx)
            for d in range(n_days):
                for s in range(len(segments[d])):
                    for i in range(n_levels):
                        var = plays[d][s][i]
                        if var is None:
                            continue
                        if i in movable and d not in pinned_idx:
                            # 第三階段的「只能加打」下界、提早階段釘死的上下界都要
                            # 放開，不然沒有東西可以挪
                            _drop_constraint(prob, f"keep_{d}_{s}_{i}", missing_ok=True)
                            _drop_constraint(prob, f"keep_total_{i}", missing_ok=True)
                            var.lowBound, var.upBound = 0, None
                        else:
                            var.lowBound = var.upBound = int(round(var.varValue or 0))
            # 加碼偏好階段的鎖裡有「計分關卡的次數」，理由同 early_after 那一段
            _drop_constraint(prob, "lock_stage3", missing_ok=True)
            locks = [lock_now(pulp.lpSum(spend), "tidy_spend"),
                     # 常駐關卡放開時也不准變少：它們是第三階段為了消化體力加打的，
                     # 少打一關省下的體力只會變成排程結束時的餘額（測試踩過：少 15）
                     *([lock_now(-pulp.lpSum(spend), "tidy_spend_floor"),
                        # 底下那道鎖准許「多浪費一點、多回收一點會過期的限時體力」，
                        # 挪常駐關卡時會拿這個換（實測：浪費從 0 變成個位數），所以另外鎖
                        lock_now(all_waste, "tidy_waste_raw")]
                       if movable != set(event_level_idx) else []),
                     lock_now(all_waste - pulp.lpSum(pool_use[p][d] for p in doomed
                                                     for d in range(n_days)),
                              "tidy_waste"),
                     lock_now(idle_spend, "tidy_idle")]
            if savable:
                locks.append(lock_now(savable_use, "tidy_savable"))
            if cap_overshoot:
                locks.append(lock_now(pulp.lpSum(cap_overshoot), "tidy_cap"))
            if preferred is not None:
                locks.append(lock_now(-preferred, "tidy_preferred"))
            # 場數階段挑好的場數不准變多（整理只挪 movable 的關卡，其他關卡已釘死）
            locks.append(lock_now(pulp.lpSum(day_plays[d][i]
                                             for d in range(n_days)
                                             for i in movable),
                                  "tidy_plays"))
            if early_first or early_after:
                locks.append(lock_now(-early_points(early_first + early_after),
                                      "tidy_early"))
            locks += expiry_locks("tidy")
            added_vars = []
            proven = True

            def current(d, i):
                return sum(int(round(pulp.value(plays[d][s][i]) or 0))
                           for s in range(len(segments[d]))
                           if plays[d][s][i] is not None)

            def over_now():
                return sum(max(0, sum(current(d, i) for i in light_level_idx)
                               - daily_clear_floor[d])
                           for d, w in light_days.items() if w == 1.0)

            def kinds_now():
                return sum(1 for d in range(n_days) for i in event_level_idx
                           if current(d, i))

            def attempt(objective, stage_name):
                """解一步；失敗就把變數值還原。回傳是否成功。"""
                nonlocal proven
                saved = {v: v.varValue for v in prob.variables()}
                ok_proven, ok = run_stage(objective, stage_name)
                if not ok:
                    for v, old in saved.items():
                        v.varValue = old
                    tidy_note["failed"] = True
                    return False
                proven = proven and ok_proven
                return True

            def attempt_in_slices(objective, stage_name, slice_seconds=8):
                """整數規劃，但一段一段跑：這一段沒有進展就停。

                簡化階段幾乎永遠證明不了最佳解，給多久就跑多久。貪婪法做完之後它
                常常已經沒有東西可以改善（實測曾白等滿整段時間），所以切成小段，
                有降才續跑，總時間仍不超過 time_limit。失敗就還原。
                """
                report(stage_name, f"最多 {time_limit} 秒")
                warm = os.access(os.getcwd(), os.W_OK)
                deadline = time.monotonic() + time_limit
                prob.setObjective(objective)
                best = pulp.value(objective)
                while time.monotonic() < deadline:
                    saved = {v: v.varValue for v in prob.variables()}
                    started = time.monotonic()
                    status = _solve(pulp, prob,
                                    msg=0, timeLimit=slice_seconds, gapRel=GAP_TOLERANCE,
                                    warmStart=warm, keepFiles=warm)
                    value = pulp.value(objective)
                    if status != "Optimal" or value is None or value > best - 0.5:
                        for v, old in saved.items():
                            v.varValue = old
                        return
                    best = value
                    if time.monotonic() - started < slice_seconds * 0.95:
                        return      # 提早收工＝這一段已經證明到 gap 以內

            def local_search(objective, propose, stage_name):
                """貪婪法的骨架：關卡次數全部釘死，一次試一組改動，用 LP 驗證。

                propose(day_count, try_changes) 負責出主意；try_changes 收
                [(第幾天, 關卡, 增減幾次), ...]，合法就留下並回傳 True，不合法就原樣
                退回。關卡次數釘死之後剩下的只有「體力怎麼付」，是一題純 LP。
                """
                report(stage_name, f"逐一試換法，最多 {time_limit} 秒")
                deadline = time.monotonic() + time_limit
                cells = {}
                for d in range(n_days):
                    for s in range(len(segments[d])):
                        for i in range(n_levels):
                            if plays[d][s][i] is not None:
                                cells.setdefault((d, i), []).append(plays[d][s][i])
                every = [var for group in cells.values() for var in group]
                bounds = {var: (var.lowBound, var.upBound) for var in every}
                counts = {var: int(round(var.varValue or 0)) for var in every}

                def pin(var):
                    var.lowBound = var.upBound = counts[var]

                def day_count(d, i):
                    return sum(counts[var] for var in cells.get((d, i), ()))

                def shift(d, i, delta, touched):
                    """那天那關加減幾次；減的時候從有次數的段落依序扣。"""
                    for var in cells[(d, i)]:
                        step = delta if delta > 0 else -min(-delta, counts[var])
                        if not step:
                            continue
                        touched.append((var, counts[var]))
                        counts[var] += step
                        pin(var)
                        delta -= step
                        if not delta:
                            return

                def try_changes(changes):
                    if time.monotonic() > deadline:
                        return False
                    if any((d, i) not in cells or day_count(d, i) + delta < 0
                           for d, i, delta in changes):
                        return False
                    touched = []
                    for d, i, delta in changes:
                        shift(d, i, delta, touched)
                    status = _solve(pulp, prob, msg=0, timeLimit=10)
                    if status == "Optimal":
                        good.update((v, v.varValue) for v in prob.variables())
                        return True
                    for var, old in reversed(touched):
                        counts[var] = old
                        pin(var)
                    return False

                for var in every:
                    pin(var)
                prob.setObjective(objective)
                good = {v: v.varValue for v in prob.variables()}
                propose(day_count, try_changes, lambda: time.monotonic() > deadline)
                # 還原成最後一組合法的解，並把上下界放回去給後面的階段
                for v, old in good.items():
                    v.varValue = old
                for var in every:
                    var.lowBound, var.upBound = bounds[var]

            def move_to_weekend(day_count, try_changes, out_of_time):
                """把平日多出來的活動／常駐關卡一批一批搬到週末。"""
                # 目的地：往後挪優先（能晚打就晚打，手上的體力留著比較保險），
                # 往前挪（例如挪到今天）最後才試；同方向裡星期日優先、再來星期六，
                # 離得近的先試（同一週的限時體力池最可能付得起）。手動鎖定的日子不能動。
                targets = [d for d in range(n_days)
                           if days[d].weekday() >= 5 and d not in pinned_idx]
                for d, weight in sorted(light_days.items()):
                    if weight != 1.0:
                        continue
                    left = (sum(day_count(d, i) for i in light_level_idx)
                            - daily_clear_floor[d])
                    order = sorted(targets, key=lambda t: (t < d,
                                                           days[t].weekday() != 6,
                                                           abs(t - d)))
                    for i in light_level_idx:
                        for t in order:
                            if left <= 0 or not day_count(d, i) or out_of_time():
                                break
                            # 先試整批，搬不動就減半，搬成功就同一天再試。
                            # 「整批不行就只搬一關、換下一天」的話，每個週末各搬
                            # 1 關就收工，平日還是留著幾十關。
                            count = min(left, day_count(d, i))
                            while count >= 1 and not out_of_time():
                                if try_changes([(d, i, -count), (t, i, count)]):
                                    left -= count
                                    count = min(count, left, day_count(d, i))
                                else:
                                    count //= 2

            def saturday_to_sunday(day_count, try_changes, out_of_time):
                """星期六多出來的，再往後挪到星期日（見 LIGHT_SATURDAY_WEIGHT）。

                跟平日那一輪分開跑、各有自己的時間：放在同一輪的話，平日搬完常常
                已經沒時間了（實測：同一份資料一次挪了、一次沒挪）。
                只往後挪：往前就是叫人提早打。
                """
                sundays = [t for t in range(n_days)
                           if days[t].weekday() == 6 and t not in pinned_idx]
                # 活動、常駐關卡先挪，限期關卡（多半是加碼）最後挪
                saturday_levels = light_level_idx + limited_level_idx
                for d, weight in sorted(light_days.items()):
                    if weight == 1.0:
                        continue
                    # 限期關卡不在 movable 裡，第三階段「加碼只能加不能減」的下界
                    # （keep_*）還留著，星期六那幾關就搬不走。這裡只放開星期六的；
                    # 總耗體、浪費、效期那幾道鎖照樣由 LP 把關
                    for s_ in range(len(segments[d])):
                        for i in limited_level_idx:
                            _drop_constraint(prob, f"keep_{d}_{s_}_{i}", missing_ok=True)
                    left = (sum(day_count(d, i) for i in saturday_levels)
                            - daily_clear_floor[d])
                    for i in saturday_levels:
                        for t in sorted((t for t in sundays if t > d),
                                        key=lambda t: t - d):
                            if left <= 0 or not day_count(d, i) or out_of_time():
                                break
                            count = min(left, day_count(d, i))
                            while count >= 1 and not out_of_time():
                                if try_changes([(d, i, -count), (t, i, count)]):
                                    left -= count
                                    count = min(count, left, day_count(d, i))
                                else:
                                    count //= 2

            def standing_to_weekend(day_count, try_changes, out_of_time):
                """平日的常駐關卡搬到週末；拿掉後湊不滿每日關數的話，同時從那個
                週末換同樣幾關活動關卡回來（兩天的關數不變，耗體由 LP 驗）。"""
                targets = [d for d in range(n_days)
                           if days[d].weekday() >= 5 and d not in pinned_idx]
                for d, weight in sorted(light_days.items()):
                    if weight != 1.0:
                        continue
                    order = sorted(targets, key=lambda t: (t < d,
                                                           days[t].weekday() != 6,
                                                           abs(t - d)))
                    for i in standing_level_idx:
                        for t in order:
                            if not day_count(d, i) or out_of_time():
                                break
                            # 跟 move_to_weekend 一樣：搬不動就減半，搬成功就同一天再試
                            k = day_count(d, i)
                            while k >= 1 and day_count(d, i) and not out_of_time():
                                move = [(d, i, -k), (t, i, k)]
                                if try_changes(move) or any(
                                        day_count(t, j) >= k
                                        and try_changes(move + [(t, j, -k), (d, j, k)])
                                        for j in event_level_idx):
                                    k = min(k, day_count(d, i))
                                else:
                                    k //= 2

            def merge_kinds(day_count, try_changes, out_of_time):
                """同一天打兩種以上的活動關卡時，跟別天對調，讓這天只剩一種。

                第 d 天的少數關卡 a（k 次）換成多數關卡 b，另外找一天 e 反過來換
                （b 少 k 次、a 多 k 次）。兩天的關數、每一關的總次數、總積分都不變，
                只有兩天的耗體互換一點——付不付得起由 LP 驗。e 必須本來就有 a，
                或 b 剛好換光，否則只是把「兩種」搬到另一天。
                """
                groups = {}
                for i in event_level_idx:
                    groups.setdefault(levels[i]["event_id"], []).append(i)
                free_days = [d for d in range(n_days) if d not in pinned_idx]
                improved = True
                while improved and not out_of_time():
                    improved = False
                    for idx in groups.values():
                        for d in free_days:
                            present = sorted((i for i in idx if day_count(d, i)),
                                             key=lambda i: day_count(d, i))
                            if len(present) < 2:
                                continue
                            major = present[-1]
                            for minor in present[:-1]:
                                k = day_count(d, minor)
                                for e in sorted(free_days, key=lambda e: abs(e - d)):
                                    if out_of_time():
                                        return
                                    if e == d or day_count(e, major) < k:
                                        continue
                                    if not (day_count(e, minor)
                                            or day_count(e, major) == k):
                                        continue
                                    if try_changes([(d, minor, -k), (d, major, k),
                                                    (e, major, -k), (e, minor, k)]):
                                        improved = True
                                        break

            def prioritise_events(day_count, try_changes, out_of_time):
                """排前面的活動往前、排後面的往後：兩天各換 k 關。

                跟 merge_kinds 同一種四格互換：第 d 天的低優先關卡 j 換成高優先
                關卡 i，較晚的第 e 天反過來換。兩天的關數、每一關的總次數、總積分
                都不變，只有兩天的耗體互換一點——付不付得起由 LP 驗。最晚的那天
                先試，挪得越遠越好。
                """
                pairs = [(i, j) for i in order_weight for j in order_weight
                         if order_weight[i] > order_weight[j]]
                free_days = [d for d in range(n_days) if d not in pinned_idx]
                improved = True
                while improved and not out_of_time():
                    improved = False
                    for d in free_days:
                        for i, j in pairs:
                            for e in reversed(free_days):
                                if e <= d:
                                    break
                                if out_of_time():
                                    return
                                k = min(day_count(d, j), day_count(e, i))
                                if not k:
                                    continue
                                for count in dict.fromkeys((k, 1)):
                                    if try_changes([(d, j, -count), (d, i, count),
                                                    (e, i, -count), (e, j, count)]):
                                        improved = True
                                        break

            if light_days:
                tidy_note.setdefault("over_before", over_now())
                overs = {}
                for d in light_days:
                    var = _new_var(prob, f"over_{d}", lowBound=0)
                    # 起點：warmStart 要每個變數都有值
                    var.varValue = max(0, sum(current(d, i) for i in light_level_idx)
                                       - daily_clear_floor[d])
                    prob.addConstraint(
                        var >= pulp.lpSum(day_plays[d][i] for i in light_level_idx)
                        - daily_clear_floor[d], f"tidy_over_{d}")
                    locks.append(f"tidy_over_{d}")
                    overs[d] = var
                    added_vars.append(var)
                excess = pulp.lpSum(w * overs[d] for d, w in light_days.items())
                # 先用「一次挪一批、用 LP 驗證」的貪婪法，剩下的才交給整數規劃。
                #
                # 為什麼不直接解：上面那幾道鎖把可行範圍壓得極窄，CBC 靠分支搜尋
                # 幾乎碰不到別的可行解——實測給了好幾分鐘還是原地不動，連改成硬
                # 限制都找不到解。但「把這幾關從週二搬到週日」合不合法很好驗：關卡
                # 次數全部釘死之後，剩下的只有體力怎麼付，是一題純 LP，零點幾秒。
                local_search(excess, move_to_weekend, "平日減量階段")
                if any(w != 1.0 for w in light_days.values()):
                    local_search(excess, saturday_to_sunday, "平日減量階段（星期六）")
                    # 限期關卡在整理階段是釘死的（不在 movable 裡）。上面挪過的話，
                    # 把它們釘在挪過之後的次數，後面的步驟才不會照舊的次數擋回去
                    for d in range(n_days):
                        for s_ in range(len(segments[d])):
                            for i in limited_level_idx:
                                var = plays[d][s_][i]
                                if var is not None and var.lowBound == var.upBound:
                                    var.lowBound = var.upBound = int(round(var.varValue or 0))
                if over_now():
                    attempt(excess, "平日減量階段")
                # 留給下面的簡化：不准為了少幾種關卡又把平日塞回去。
                # 平日那部分要**另外**鎖一道，不能只鎖加權總和——星期六的權重是
                # 0.1，只鎖總和的話，簡化階段讓星期六少 10 關就換得到平日多 1 關
                # （實測：某個平日被換回超過每日關數，回報的數字卻還是 0）。
                locks.append(lock_now(
                    pulp.lpSum(overs[d] for d, w in light_days.items() if w == 1.0),
                    "tidy_excess_weekday"))
                locks.append(lock_now(excess, "tidy_excess"))
                # 平日湊每日關數時先用活動關卡，常駐關卡留到週末：上面只管「總關數
                # 不超過」，常駐關卡照樣會拿來湊數、活動關卡反而被擠到週末（實測：
                # 平日活動關卡只打一部分、其餘拿常駐湊數，活動關卡全堆到週日）。
                standing_weekday = pulp.lpSum(
                    day_plays[d][i] for d, w in light_days.items() if w == 1.0
                    for i in standing_level_idx)
                if standing_level_idx and pulp.value(standing_weekday):
                    local_search(standing_weekday, standing_to_weekend,
                                 "平日減量階段（常駐關卡）")
                    locks.append(lock_now(standing_weekday, "tidy_standing_weekday"))

            # 活動優先序（見 order_weight）：平日減量鎖住之後才排，所以只會在不增加
            # 平日關數的範圍裡換；排完鎖住，打法簡化就不能再把順序換回去。
            if order_weight:
                def last_days():
                    result = {}
                    for i in order_weight:
                        eid = levels[i]["event_id"]
                        for d in range(n_days - 1, -1, -1):
                            if current(d, i):
                                result[eid] = max(result.get(eid, d), d)
                                break
                    return result

                tidy_note["order_before"] = last_days()
                lateness = pulp.lpSum(w * d * day_plays[d][i]
                                      for i, w in order_weight.items()
                                      for d in range(n_days))
                local_search(lateness, prioritise_events, "活動先後整理階段")
                attempt_in_slices(lateness, "活動先後整理階段")
                # 每檔各鎖一道：只鎖加權總和的話，簡化階段可以把排前面那檔往後
                # 挪幾關、再拿排後面那檔大量往前來抵（實測排後面那檔又被挪到前面幾天）。
                for eid in order_ids:
                    own = [i for i in order_weight if levels[i]["event_id"] == eid]
                    if own:
                        locks.append(lock_now(
                            pulp.lpSum(d * day_plays[d][i] for i in own
                                       for d in range(n_days)),
                            f"tidy_order_{eid}"))

            if simplify_days and event_level_idx:
                tidy_note.setdefault("kinds_before", kinds_now())
                total_spend = int(round(pulp.value(pulp.lpSum(spend)) or 0))
                used = []
                for d in range(n_days):
                    if d in pinned_idx:
                        continue
                    for i in event_level_idx:
                        if not any(plays[d][s][i] is not None
                                   for s in range(len(segments[d]))):
                            continue
                        # 總耗體已經鎖住，所以「總耗體 ÷ 這關的耗體」是有效的上界
                        bound = max(1, total_spend // costs[i])
                        limit = levels[i].get("max_total")
                        if limit is not None:
                            bound = max(1, min(bound, int(limit)))
                        var = _new_var(prob, f"used_{d}_{i}", cat="Binary")
                        var.varValue = 1 if current(d, i) else 0
                        prob.addConstraint(day_plays[d][i] <= bound * var,
                                           f"tidy_used_{d}_{i}")
                        locks.append(f"tidy_used_{d}_{i}")
                        used.append(var)
                        added_vars.append(var)
                if used:
                    # 同樣先貪婪、再交給整數規劃（理由見上面平日減量那一段）。
                    # used 是 0/1 變數，關卡次數釘死之後 LP 會自己把它壓到該有的值。
                    #
                    # 這裡的整數規劃不能省：對調不會改變每一關的總次數，而實測的
                    # 簡化大半來自「關卡2＋關卡4 換成 關卡3×2」這種同耗體同
                    # 積分的換法（打法種類少掉一到兩成，全是這一步做的）。
                    # 試過把這種換法做成貪婪動作（兩天各改寫成單一關卡）：幾份資料
                    # 各試了好幾百次，LP 一次都沒放行——單一關卡湊不滿每日關數。
                    local_search(pulp.lpSum(used), merge_kinds, "簡化打法階段")
                    attempt_in_slices(pulp.lpSum(used), "簡化打法階段")
                tidy_note["kinds_after"] = kinds_now()
            # 關卡次數都定了，最後在「體力怎麼付」上把溢出壓到最低：上面的鎖只保證
            # 「浪費 − 回收的限時體力」不變差，進來時的解若已經在溢出（實測：
            # 整理前某天溢出十幾點），挪完常駐關卡後可能還剩一點（剩個位數）。
            # 那幾點是挪動造成的（關卡次數釘死時 LP 壓不下來），所以交給整數規劃在
            # 前面所有鎖（平日關數、種類、總耗體……）之內重排；沒進展就原樣保留。
            if (pulp.value(all_waste) or 0) > 0.5:
                attempt_in_slices(all_waste, "整理階段（減少溢出）")
            # 等簡化也做完才量：回報的要是最終排程的數字
            if light_days:
                tidy_note["over_after"] = over_now()
            if order_weight:
                tidy_note["order_after"] = last_days()

            for name in locks:
                _drop_constraint(prob, name)
            for v, (low, up) in claim_bounds.items():
                v.lowBound, v.upBound = low, up
            # 輔助變數的約束都拿掉了，但 pulp 的變數清單只增不減：它們會變成模型裡
            # 一個係數都沒有的空欄位，CBC 回傳的解不含這種欄位，pulp 讀解時就炸在
            # KeyError（有第三階段時才會遇到）。所以釘成常數 0，再用一條恆成立的
            # 式子把它們留在矩陣裡——presolve 會整條消掉，不影響求解。
            # （這是最後一個階段，現在沒有人會再解這個模型；留著是為了以後有人在
            #   後面再加階段時不必重踩一次。）
            for var in added_vars:
                var.lowBound = var.upBound = 0
                var.varValue = 0
            if added_vars:
                prob.addConstraint(pulp.lpSum(added_vars) >= 0, "tidy_keepalive")
            # 挪過的活動關卡不是加碼（總耗體沒有變），併進底線——跟 early_after
            # 同一個作法，報表的「加碼」欄才只剩真正多打的那些。常駐關卡不併：
            # 它們本來就是加碼，挪到週末還是加碼。
            final = snapshot()
            for d in range(n_days):
                for s in range(len(segments[d])):
                    for i in event_level_idx:
                        base_counts[d][s][i] = final[d][s][i]
            return proven

        # 場數階段的鎖到這裡為止：第三階段本來就要加打
        _drop_constraint(prob, "lock_plays", missing_ok=True)

        # 第三階段：把「不用就永久消失」的體力拿去打不計分的關卡。
        # 前兩階段的目標是最省，所以會刻意少打；但頂到上限溢出的自然回復、
        # 到期沒用完的限時體力，留著也是蒸發，不如換成別的收益。
        # 買體力的量已經被鎖住，所以這一步不會讓你多花錢。
        def snapshot():
            return [[[int(round(pulp.value(plays[d][s][i]) or 0))
                      if plays[d][s][i] is not None else 0
                      for i in range(n_levels)]
                     for s in range(len(segments[d]))] for d in range(n_days)]

        base_counts = snapshot()
        base_waste = sum(int(round(pulp.value(w) or 0))
                         for day_w in waste for w in day_w)
        def granted_now(p):
            if p in claim_y:
                return pools[p]["total"] * int(round(pulp.value(claim_y[p]) or 0))
            return pools[p]["total"]

        doomed_left = sum(
            granted_now(p) - sum(int(round(pulp.value(pool_use[p][d]) or 0))
                                 for d in range(n_days))
            for p in doomed)
        reclaimable = base_waste + doomed_left

        proven_3 = True
        if reclaimable > 0 and reclaim_surplus:
            # 鎖住第二階段的排程當作底線：常駐、限期關卡與手動鎖定日只能「加打」，
            # 不能重排，「加碼」的數字才跟實際多花的體力對得起來。
            #
            # 活動（當期／復刻）關卡例外：只鎖整個排程的總次數，日子可以換。第二階段
            # 只求省耗體，把活動關卡平均排在每一天；那幾天的體力流向定死之後，會過期
            # 的那批常常找不到地方用（實測某天過期四百多點，強制那天打常駐、活動
            # 往前挪，損失從六百多降到二十左右，也不用多買）。每日關數、積分目標這些任務
            # 條件本來就是硬約束，換日子也一定守得住。
            #
            # 先照舊（全部逐格鎖）算一次，再從那組解出發放開活動關卡重排——直接
            # 放開的話題目變大，30 秒內常停在比原本還差的解（實測損失反而多了一成）。
            reshuffle = [i for i in event_level_idx]
            base_total = {i: sum(base_counts[d][s][i] for d in range(n_days)
                                 for s in range(len(segments[d])))
                          for i in reshuffle}
            movable_keeps = []
            for d in range(n_days):
                for s in range(len(segments[d])):
                    for i in range(n_levels):
                        if base_counts[d][s][i] and plays[d][s][i] is not None:
                            prob += (plays[d][s][i] >= base_counts[d][s][i],
                                     f"keep_{d}_{s}_{i}")
                            if i in base_total and d not in pinned_idx:
                                movable_keeps.append(f"keep_{d}_{s}_{i}")
            # 可留到下一檔的池子鎖在第二階段的用量，不准再多挖。
            # 這一階段的目標函數裡沒有 SAVE_FOR_NEXT，多用可留存體力來養「加碼」
            # 關卡是零成本的；只鎖住 buy 擋不住它（實測會被挖走一兩百點）。
            for p in savable:
                used = sum(int(round(pulp.value(pool_use[p][d]) or 0))
                           for d in range(n_days))
                prob += (pulp.lpSum(pool_use[p][d] for d in range(n_days))
                         <= used + 0.001), f"keep_savable_{p}"
            # 同理，留得住的信箱／任務獎勵不准為了加碼而改成提早領：這一階段
            # 獎勵的是「用掉 doomed 的池子」，提早領正好把它們變成 doomed。
            # 只准維持或取消第二階段的領法，不准多領。
            for k in savable_lots:
                for p in claim_lots[k]["pools"]:
                    prob += (claim_y[p] <= int(round(pulp.value(claim_y[p]) or 0)),
                             f"keep_claim_{p}")
            scoring_plays = pulp.lpSum(day_plays[d][i] for d in range(n_days)
                                       for i in range(n_levels)
                                       if levels[i]["scoring"])
            # 你指定的關卡優先——係數比「避開計分關卡」更強，所以多餘的體力
            # 會先塞滿指定關卡，再考慮其他。
            #
            # 只加總「那天真的有設上限」的組合，不是所有天數：獎勵的範圍必須跟
            # 上限一致，否則等於鼓勵求解器往你沒設限的日子灌（實際踩過）。
            designated = pulp.lpSum(day_plays[d][i] for (d, i) in level_cap)
            # 積分天花板的罰則必須跟著進來。這一階段鎖住了 buy、鎖住了第二階段的
            # 排法（keep_*）、也鎖住了可留存池的用量，但 cap_over 還是自由變數——
            # 少了這一項，「加碼」時把體力灌進計分關卡、衝破天花板在數學上是零成本
            # 的，只有很弱的 0.01 × scoring_plays 擋著。
            # （cap_idle_relief 不用加：那一項是逼求解器用最省體力的方式湊滿天花板，
            #   而這一階段本來就優先挑不計分的關卡。）
            if preferred is not None:
                # 下面的加碼偏好階段會讓「多打一關排前面的關卡」本身有價值，所以
                # 要明確限制加碼只能吃「本來就會浪費」的那些（溢出＋會過期的限時
                # 體力），不准把該留著的自然體力也拿去打——那是帶到下一檔的本錢。
                #
                # 直接鎖「收尾時的自然體力不准變少」（可留存的池子上面已經鎖了），
                # 不用「總耗體 ≤ 第二階段＋當時量到的浪費」：活動關卡重排之後，
                # 能回收的會比第二階段量到的多，那個額度會把更好的排法擋掉
                # （實測：額度用完、還剩好幾百點過期；放開後幾乎用光）。
                end_balance = balance[n_days - 1][len(segments[n_days - 1]) - 1]
                prob += (end_balance >= (pulp.value(end_balance) or 0.0) - 0.001,
                         "surplus_only")
            stage3 = (
                all_waste
                - pulp.lpSum(pool_use[p][d] for p in doomed for d in range(n_days))
                - 0.05 * designated
                + 0.01 * scoring_plays
                + (CAP_OVERSHOOT_PENALTY * pulp.lpSum(cap_overshoot)
                   if cap_overshoot else 0))
            proven_3, ok = run_stage(stage3, "第三階段")
            if not ok:
                return None
            def loss_now():
                """還有多少體力會白白損失：自然回復溢出＋會過期池子剩下的。"""
                return ((pulp.value(all_waste) or 0.0)
                        + sum(granted_now(p) - sum(pulp.value(pool_use[p][d]) or 0.0
                                                   for d in range(n_days))
                              for p in doomed))

            # stage3 的值含「用掉多少會過期的」整筆，是很大的負數，不能拿它判斷還有沒有剩
            if movable_keeps and loss_now() > 0.5:
                # 重排：活動關卡只鎖總次數，從剛才那組解（warmStart）出發，
                # 只收比它好的。「盡量提早」日期前的積分不准變少。
                saved = {v: v.varValue for v in prob.variables()}
                before = pulp.value(stage3) or 0.0
                for name in movable_keeps:
                    _drop_constraint(prob, name)
                for i, total in base_total.items():
                    prob += (pulp.lpSum(day_plays[d][i] for d in range(n_days))
                             >= total, f"keep_total_{i}")
                stage3_locks = []
                if early_first:
                    stage3_locks.append(lock_now(-early_points(early_first),
                                                 "stage3_early"))
                proven_r, ok = run_stage(stage3, "第三階段（重排）")
                for name in stage3_locks:
                    _drop_constraint(prob, name)
                if not ok or (pulp.value(stage3) or 0.0) > before - 0.5:
                    for v, old in saved.items():
                        v.varValue = old
                else:
                    proven_3 = proven_3 and proven_r
            if preferred is not None:
                # 加碼的偏好階段，理由同第二階段後的那一個：係數再小都會被 gap
                # 吞掉（實測 0.004／點的獎勵完全沒作用——求解器改用「拿會過期的
                # 限時體力付原本就要打的關卡」，一樣回收了體力，卻一關都沒加打）。
                # 鎖住第三階段的值，再從一樣好的加碼方式裡挑最偏向排前面關卡的。
                stage3_value = pulp.value(stage3) or 0.0
                prob += (stage3 <= stage3_value
                         + max(0.01, abs(stage3_value) * 1e-7), "lock_stage3")
                proven_3b, ok = run_stage(-preferred, "加碼偏好階段")
                if not ok:
                    _drop_constraint(prob, "lock_stage3")
                    proven_3b, ok = run_stage(stage3, "第三階段")
                    if not ok:
                        return None
                    priority_note["failed"] = True
                proven_3 = proven_3 and proven_3b
            # 活動關卡挪過日子的部分不是加碼（總次數沒變），併進底線——報表的
            # 「加碼」欄只留真正多打的。總次數真的變多的那幾次，從最後打的那天
            # 起算成加碼。
            final = snapshot()
            for i in reshuffle:
                extra = (sum(final[d][s][i] for d in range(n_days)
                             for s in range(len(segments[d]))) - base_total[i])
                for d in reversed(range(n_days)):
                    for s in reversed(range(len(segments[d]))):
                        count = final[d][s][i]
                        if d in pinned_idx:
                            continue
                        take = min(max(extra, 0), count)
                        base_counts[d][s][i] = count - take
                        extra -= take

        if early_after:
            # 加碼照打：其他關卡每一段的次數整個釘死，只有這幾檔的計分關卡能在
            # 日子之間挪。釘死用變數的上下界，比逐格加等式省一大片矩陣。
            movable = {i for entry in early_after for i in entry["levels"]}
            for d in range(n_days):
                for s in range(len(segments[d])):
                    for i in range(n_levels):
                        var = plays[d][s][i]
                        if var is None:
                            continue
                        if i in movable:
                            # 第三階段的「只能加打」下界要放開，不然沒有東西可以挪
                            _drop_constraint(prob, f"keep_{d}_{s}_{i}", missing_ok=True)
                            _drop_constraint(prob, f"keep_total_{i}", missing_ok=True)
                        else:
                            var.lowBound = var.upBound = int(round(var.varValue or 0))
            # 加碼偏好階段的鎖裡有「計分關卡的次數」，換關卡組合就會撞到它；
            # 這裡要守的只有「不准因此多浪費」，下面另外鎖。
            _drop_constraint(prob, "lock_stage3", missing_ok=True)
            locks = [
                lock_now(pulp.lpSum(spend), "early_spend"),
                lock_now(all_waste - pulp.lpSum(pool_use[p][d] for p in doomed
                                                for d in range(n_days)),
                         "early_waste"),
            ]
            if savable:
                locks.append(lock_now(savable_use, "early_savable"))
            if cap_overshoot:
                locks.append(lock_now(pulp.lpSum(cap_overshoot), "early_cap"))
            locks += expiry_locks("early_after")
            proven_early = (run_early(early_after, locks, "提早階段")
                            and proven_early)
            # 挪過來的計分關卡不是加碼（總耗體沒有變），併進底線，報表的「加碼」
            # 欄才只剩真正多打的那些。
            final = snapshot()
            for d in range(n_days):
                for s in range(len(segments[d])):
                    for i in movable:
                        base_counts[d][s][i] = final[d][s][i]
        proven_tidy = run_tidy()
        proven_3 = proven_3 and proven_early and proven_tidy

        # 最後一步：能晚一週領就晚一週領。第三階段以後「哪一週領」對求解器都一樣
        # （常常停在最早那週），但晚一週領到期日就晚一週——只要這批體力用到的
        # 日子全在後一週的候選池能用的範圍內，就把整筆搬過去。打法、耗體都不變，
        # 只換「哪一週領」（實測：隔幾天才用的禮包原本排在前一週的週日領，到期日也早了一週）。
        for lot in claim_lots:
            if lot.get("auto"):
                continue          # 自動領取沒得選，達標那週就進包包
            chain = lot["pools"]
            for _ in range(len(chain)):
                chosen = [p for p in chain if int(round(claim_y[p].varValue or 0))]
                if not chosen:
                    break
                p = chosen[0]
                used = [d for d in range(n_days) if (pool_use[p][d].varValue or 0) > 1e-6]
                if not used:
                    # 領了卻一點都沒用：對求解器「領不領」平手（看 CBC 版本隨手挑），
                    # 對人卻是白白把效期提早。一律改成不領，留到最晚再說。
                    claim_y[p].varValue = 0
                    break
                nxt = chain.index(p) + 1
                if nxt >= len(chain):
                    break
                q = chain[nxt]
                flags = reached.get(claim_lots.index(lot))
                ok = (not used
                      or (used[0] >= pools[q]["open_idx"]
                          and used[-1] <= pools[q]["last_idx"]))
                if flags is not None and ok:
                    # 任務獎勵：後一週那時也要已經達標
                    last = pools[q]["week_last_idx"]
                    ok = last >= 1 and int(round(flags[last - 1].varValue or 0)) == 1
                if not ok or not used:
                    break
                for d in range(n_days):
                    pool_use[q][d].varValue = pool_use[p][d].varValue
                    pool_use[p][d].varValue = 0
                claim_y[p].varValue, claim_y[q].varValue = 0, 1

        return {
            "plays": plays, "base_counts": base_counts, "use_nat": use_nat,
            "waste": waste,
            "pool_use": pool_use, "use_wk": use_wk, "buy": buy,
            "claim_y": claim_y, "reached": reached,
            "shorts": {i: pulp.value(v) or 0 for i, v in shorts.items()},
            "reclaimable": reclaimable,
            "proven": proven_0 and proven_1 and proven_2 and proven_3,
            "value": pulp.value,
            # PuLP 4.x 的變數值存在模型裡，模型被回收之後就讀不到了，要留著它
            "prob": prob,
        }

    # 先硬算；真的湊不出來才依優先序把活動的期限目標放寬
    order = [eid for eid in (profile.get("event_priority") or [])
             if eid in events_by_id]
    order += [ev["id"] for ev in events if ev["id"] not in order]
    relaxable = [eid for eid in reversed(order)
                 if any(c["event_id"] == eid and c["soft_ok"] for c in constraints)
                 or any(ch["event"]["id"] == eid and ch["soft_ok"] and ch["need"]
                        for ch in unlock_chains)]
    soft_events: set[str] = set()
    try:
        solution = build_and_solve(soft_events)
        while solution is None and relaxable:
            soft_events.add(relaxable.pop(0))
            names = "、".join(events_by_id[e]["name"] for e in soft_events)
            round_label["text"] = f"湊不齊全部目標，放寬「{names}」後重算：\n"
            solution = build_and_solve(set(soft_events))
            if solution is not None:
                warnings.append(
                    f"目前的資源湊不齊全部目標，已放寬「{names}」的活動目標，"
                    "下面會列出還差多少")
    finally:
        _remove_solver_files()
    if solution is None:
        round_label["text"] = "排不出來，正在找原因：\n"
        # 一般活動的解鎖鏈是硬約束、不會被上面的放寬機制軟化（可放寬的只有活動
        # 期限型任務與分組解鎖型活動的「至少一次」），所以它造成的無解一定會掉到
        # 這裡。不點名的話使用者會照著上面那段去調特殊日規則，怎麼調都沒用。
        unlock_hint = ""
        blocking = [levels[i]["label"] for chain in unlock_chains
                    if not chain["soft_ok"] for i in chain["need"]]
        if blocking:
            unlock_hint = (
                "\n\n也可能是「開場先打一次」的解鎖鏈排不進去："
                + "、".join(blocking)
                + " 一定要各先打過一次（硬條件，不會被放寬；"
                  "只有蜜意蒐羅、祕寶探尋這類分組活動的會被放寬）。\n"
                  "這幾關已經打過的話，到「每日紀錄」補記上 1 次就不會再排；"
                  "或到關卡結構取消它們的「開場先打一次」。")
        if level_target:
            # 拿掉指定次數再算一次：這樣就有解的話，擋住的就是指定次數本身，
            # 下面那些「調特殊日規則」的建議只會把人帶去錯的地方。
            kept = dict(level_target)
            level_target.clear()
            try:
                without = build_and_solve(set(soft_events))
            finally:
                _remove_solver_files()
                level_target.update(kept)
            if without is not None:
                listed = "\n".join(
                    f"　• {format_day(days[d])} {levels[i]['label']}"
                    f"{'至少' if mode == 'min' else ''}×{wanted}"
                    for (d, i), (mode, _remaining, wanted)
                    in sorted(level_target.items()))
                raise PlanError(
                    "照你指定的次數排不出來：\n\n" + listed + "\n\n"
                    "拿掉這些指定就排得出來，所以是它們跟體力或遊戲規則衝突——\n"
                    "・那幾天的體力（含可以買的量）撐不起這麼多次\n"
                    "・解鎖順序：便宜的那關還沒打過，貴的關卡不能打\n"
                    "・指定的次數把體力吃掉，其他一定要達成的目標補不回來\n"
                    "請到「排程設定」的「指定日期打指定次數」減少次數、換日期，"
                    "或把「剛好」改成「至少」。")
        active_stage = [rule for rule in stage_rules if rule["days"]]
        if active_stage:
            # 同上：拿掉難度規則再算一次，有解就是它們擋住的
            kept_days = [rule["days"] for rule in stage_rules]
            for rule in stage_rules:
                rule["days"] = []
            try:
                without = build_and_solve(set(soft_events))
            finally:
                _remove_solver_files()
                for rule, kept in zip(stage_rules, kept_days):
                    rule["days"] = kept
            if without is not None:
                raise PlanError(
                    "照難度規則排不出來：\n\n"
                    + "\n".join(f"　• {rule['text']}" for rule in active_stage)
                    + "\n\n拿掉這些規則就排得出來——多半是能打那幾關的日子太少，"
                    "一定要達成的目標（例如打滿總次數）來不及。\n"
                    "請到「排程設定」的「指定關卡次數限制」多勾幾個星期幾，"
                    "或刪掉其中幾條難度規則。")
        if pinned_idx:
            raise PlanError(
                "照你調整的打法排不出來（鎖定的日子："
                + "、".join(format_day(days[d]) for d in sorted(pinned_idx))
                + "）。\n"
                "每日／每週的要求與當日上限已經以你的調整為準，所以擋住的是"
                "遊戲規則：\n"
                "・解鎖順序——貴的關卡被搬到便宜的那關打過之前\n"
                "・關卡的「總共最多幾次」、限期關卡的上限\n"
                "・活動結束前一定要達成的目標，靠剩下的日子補不回來\n"
                "換一組日子對調，或還原之後再試。" + unlock_hint)
        raise PlanError(
            "在目前的條件下找不到可行解。\n"
            "常見原因：特殊日的體力使用上限太低、湊不滿當天的最低關卡數；"
            "或每日任務的要求超過當天能打的量。\n"
            "可以先把吃緊那幾天的「當日最低關卡數」「當日最低耗體」"
            "用特殊日規則調低看看；\n"
            "如果那個上限只是針對某一檔活動，改用「當日該活動體力上限」"
            "就不會卡到同一天的其他活動。" + unlock_hint)

    if plays_note.get("failed"):
        warnings.append("「場數最少」這次沒能套用（場數階段求解失敗），"
                        "耗體與補充量不受影響")
    elif plays_note.get("after") is not None and plays_note["after"] < plays_note["before"]:
        warnings.append(
            f"場數最少：同樣達標、不多花體力的打法裡挑場數最少的，"
            f"第二次計算前的總場數 {plays_note['before']} → {plays_note['after']}")

    if priority_note.get("failed"):
        warnings.append("關卡優先序這次沒能套用（偏好階段求解失敗），"
                        "以下是沒有偏好的排程——耗體與補充量不受影響")

    if expiry_note.get("failed"):
        warnings.append("「多的限時體力留在晚到期的」這次沒能套用（效期階段求解失敗），"
                        "耗體與補充量不受影響")
    elif "after" in expiry_note and expiry_note["after"] != expiry_note["before"]:
        def describe(left):
            return "、".join(f"{day:%m/%d} 到期的 {amount} 點"
                            for day, amount in sorted(left.items())) or "沒有"
        warnings.append(
            "多的限時體力改留在晚到期的：用不完的原本是"
            + describe(expiry_note["before"]) + "，改成"
            + describe(expiry_note["after"])
            + "（先用快過期的；總耗體與補充量不變，加碼之前的數字）")
    if early_note.get("failed"):
        warnings.append("「盡量提早」這次沒能套用（提早階段求解失敗），"
                        "以下是沒有提早的排程——耗體與補充量不受影響")

    if buy_retry:
        before = int(round(buy_retry["before"]))
        if buy_retry["after"] is None:
            warnings.append(
                f"補充量第一次 {time_limit} 秒內沒算完（{before} 點），已自動再算 "
                f"{buy_retry['seconds']} 秒，也沒有更少，維持 {before} 點")
        else:
            warnings.append(
                f"補充量第一次 {time_limit} 秒內沒算完（{before} 點），已自動再算 "
                f"{buy_retry['seconds']} 秒：→ {int(round(buy_retry['after']))} 點"
                + ("" if buy_retry["proven"]
                   else "（仍不保證是最少，實務上通常已經很接近）"))
    if not solution["proven"]:
        warnings.append(
            f"求解達到 {time_limit} 秒的時間上限，以下是這段時間內找到的最佳解，"
            "不保證是理論上最省的排程（實務上通常已經很接近）")
    if extended_stages:
        warnings.append(
            "、".join(extended_stages)
            + f"在 {time_limit} 秒內還沒找到任何可行的排法，"
            f"已自動延長到 {time_limit * TIMEOUT_RETRY_FACTOR} 秒重算，所以這次算得比較久")

    # ---- 取出結果 -------------------------------------------------------
    value = solution["value"]

    def val(v):
        return 0 if v is None else int(round(value(v) or 0))

    # 補充量是連續變數，每天各自四捨五入再加總會跟真正的總量差 1（73＋122＝195，
    # 實際是 194.4）。先決定總量，再用最大餘數法分回每一天，表格加起來才對得上。
    raw_buy = [max(0.0, value(b) or 0.0) for b in solution["buy"]]
    buy_rounded = [int(x) for x in raw_buy]
    short_by = int(round(sum(raw_buy))) - sum(buy_rounded)
    for d in sorted(range(len(raw_buy)), key=lambda k: raw_buy[k] - buy_rounded[k],
                    reverse=True)[:max(0, short_by)]:
        buy_rounded[d] += 1

    plays = solution["plays"]
    base_counts = solution["base_counts"]
    # 逐段的次數取一次就好：每天的總次數、以及任務達成度（只算活動開著那幾段）
    # 都從這一份推，不要各自再讀一次求解器的變數。
    seg_counts = [[[val(plays[d][s][i]) for i in range(n_levels)]
                   for s in range(len(segments[d]))] for d in range(n_days)]

    # 「盡量提早」的成果：日期前排了多少分、還有多少留在之後
    early_rows = []
    for entry in early_first + early_after:
        gained = [sum(points_of[i] * seg_counts[d][s][i]
                      for s in range(len(segments[d])) for i in entry["levels"])
                  for d in range(n_days)]
        row = {"event_id": entry["event"]["id"], "date": entry["date"],
               "takes_surplus": entry["event"]["early_takes_surplus"],
               "points_before": sum(gained[d] for d in entry["days"]),
               "points_after": sum(gained) - sum(gained[d] for d in entry["days"])}
        early_rows.append(row)
        if not early_note.get("failed"):
            warnings.append(
                f"「{entry['event']['name']}」盡量提早：{entry['date']:%m/%d} 前排了 "
                f"{row['points_before']} 分，剩下 {row['points_after']} 分排在之後"
                + ("（那天之前多餘的體力先打這檔的計分關卡，加碼排在之後）"
                   if row["takes_surplus"] else
                   "（常駐加碼照打，只挪加碼用不完的體力）")
                + "。總耗體與補充量跟不提早時一樣，計算會多跑一個階段")

    # 整理階段的成果（見 LIGHT_WEEKDAYS）
    if tidy_note.get("failed"):
        warnings.append("「平日減量／打法簡化」這次沒能完全套用（整理階段求解失敗），"
                        "耗體與補充量不受影響")
    if "order_after" in tidy_note:
        moved = [f"「{events_by_id[eid]['name']}」"
                 f"{format_day(days[tidy_note['order_before'][eid]])} → "
                 f"{format_day(days[last])}"
                 for eid in order_ids
                 if (last := tidy_note["order_after"].get(eid)) is not None
                 and tidy_note["order_before"].get(eid) not in (None, last)]
        if moved:
            warnings.append(
                "活動優先序：重疊期間先打排前面的活動，計分關卡最後一天 "
                + "、".join(moved) + "（總耗體與補充量不變；平日減量優先）")
    if "over_after" in tidy_note:
        before, after = tidy_note["over_before"], tidy_note["over_after"]
        warnings.append(
            f"平日減量：週一到週五超過每日關數的活動／常駐關卡 {before} 關 → {after} 關"
            "（多的挪到週末；總耗體與補充量不變）"
            + ("。還留在平日的是挪不動的：被「盡量提早」的日期、當日上限、"
               "限時體力的到期日、指定次數或體力上限卡住" if after else ""))
    if "kinds_after" in tidy_note:
        warnings.append(
            f"打法簡化：每天的活動關卡種類合計 {tidy_note['kinds_before']} → "
            f"{tidy_note['kinds_after']}（只算活動的關卡；總耗體與補充量不變）")

    # 餘額與浪費不直接讀求解器的變數：那些在 gap 容忍範圍內是「免費」的，
    # 求解器可能隨手把體力丟掉，害報表出現「餘額 0 卻還在浪費」的假數字。
    # 關卡怎麼打已經定了，餘額就是一路推下來的結果，重算才精確。
    exact_bed, exact_morning = [], []
    exact_waste_day, exact_waste_night = [], []
    balance_now = initial_stamina
    for d in range(n_days):
        bed_value = balance_now
        waste_day = waste_night = 0
        for s, seg in enumerate(segments[d]):
            raw = balance_now + seg["recovery"] - val(solution["use_nat"][d][s])
            spilled = max(0, raw - cap)
            balance_now = min(cap, max(0, raw))
            if seg["before_open"] and d > 0:
                # 重置到開工之間溢出的，是前一晚收工太高造成的，記回前一天
                exact_waste_night[d - 1] += spilled
            elif seg["before_bed"] and not seg["before_open"]:
                waste_day += spilled
            else:
                waste_night += spilled
            if bed_index[d] is not None and s == bed_index[d]:
                bed_value = balance_now
        exact_bed.append(bed_value)
        exact_morning.append(balance_now)
        exact_waste_day.append(waste_day)
        exact_waste_night.append(waste_night)

    # 每一關的「解鎖那一次」就是排程裡第一次打到它的那一天。LP 的閘門只保證
    # 「同一天或更早」，日內先後要在報表上講，所以先把那一天找出來。
    unlock_day: dict[int, int] = {}
    for chain in unlock_chains:
        for i in chain["need"]:
            running = 0
            for d in range(n_days):
                running += sum(seg_counts[d][s][i]
                               for s in range(len(segments[d])))
                if running >= 1:
                    unlock_day[i] = d
                    break

    schedule = []
    for d in range(n_days):
        counts = [sum(seg_counts[d][s][i] for s in range(len(segments[d])))
                  for i in range(n_levels)]
        base = [sum(base_counts[d][s][i] for s in range(len(segments[d])))
                for i in range(n_levels)]
        # 有活動在當天中途截止時，把「那個截止時刻之前要打完的」單獨列出來
        deadlines = []
        for event in events:
            if event["end_dt"].date() != days[d]:
                continue
            before = [0] * n_levels
            for s, seg in enumerate(segments[d]):
                if seg["hi"] > event["end_dt"]:
                    continue
                for i in range(n_levels):
                    if levels[i]["event_id"] == event["id"]:
                        before[i] += val(plays[d][s][i])
            if any(before):
                deadlines.append({
                    "event": event["name"], "moment": event["end_dt"],
                    "counts": before,
                    "spend": sum(costs[i] * before[i] for i in range(n_levels)),
                })
        # 「開場先打一次」的關卡，解鎖那一次落在這一天的就單獨列出來，照消耗
        # 體力由小到大排。跟 deadlines 一樣：有日內先後語意但不進 LP，只在報表
        # 上呈現（counts 是 list[int]，段落早就被加總掉了）。
        # 同一檔活動的好幾組（分組解鎖型）併成一則，各組用「；」隔開。
        unlocks = []
        for chain in unlock_chains:
            order = [i for i in chain["order"] if unlock_day.get(i) == d]
            if not order:
                continue
            # 顯示文字在這裡就排好（同耗體用「・」並列），報表照印即可
            text = chain_order_text(chain, order)
            if unlocks and unlocks[-1]["event_id"] == chain["event"]["id"]:
                unlocks[-1]["order"] += order
                unlocks[-1]["text"] += "；" + text
                unlocks[-1]["spend"] += sum(costs[i] for i in order)
                continue
            unlocks.append({
                "event": chain["event"]["name"],
                "event_id": chain["event"]["id"],
                "order": order,
                "text": text,
                "spend": sum(costs[i] for i in order),
            })
        schedule.append({
            "date": days[d],
            "week_index": week_of_day[d],
            "counts": counts,
            # 第三階段為了消化多餘體力而額外加的次數
            "extra_counts": [max(0, counts[i] - base[i]) for i in range(n_levels)],
            "clears": sum(counts),
            "scoring_clears": sum(c for i, c in enumerate(counts)
                                  if levels[i]["scoring"]),
            "enemies": sum(enemies_of[i] * c for i, c in enumerate(counts)),
            "enemy_floor": daily_enemy_floor.get(d) or None,
            "spend": sum(costs[i] * counts[i] for i in range(n_levels)),
            "points": sum(points_of[i] * counts[i] for i in range(n_levels)),
            "use_nat": sum(val(v) for v in solution["use_nat"][d]),
            "use_weekly": sum(val(solution["pool_use"][p][d])
                              for p in range(len(pools))),
            "buy": buy_rounded[d],
            "waste": exact_waste_day[d] + exact_waste_night[d],
            "waste_night": exact_waste_night[d],
            "bedtime_balance": exact_bed[d],
            "nat_balance": exact_morning[d],
            "usage_cap": usage_cap.get(d),
            "event_caps": [(events_by_id[eid]["name"] if eid in events_by_id
                            else eid, limit)
                           for (cap_day, eid), limit in sorted(event_cap.items())
                           if cap_day == d]
                          + ([("當天結束的活動（" + "、".join(
                                ev["name"] for ev in real_events
                                if ev["id"] in ending_cap[d][0]) + "）",
                               ending_cap[d][1])] if d in ending_cap else []),
            "daily_floor": daily_stamina_floor.get(d),
            # 活動當天才開的話，這個下限只算那個時段內的——不標出來會被拿去
            # 跟當天總耗體對帳，怎麼看怎麼不合
            "daily_floor_window": floor_window_text(d, "stamina"),
            "min_clears_override": min_clears_override.get(d),
            "min_stamina_override": min_stamina_override.get(d),
            "deadlines": deadlines,
            "unlocks": unlocks,
            "pinned": d in pinned_idx,
            # 這天有哪幾關是指定次數的：(關卡索引, 方式, 你指定的當天總數)
            "targets": [(i, mode, wanted)
                        for (day_idx, i), (mode, _remaining, wanted)
                        in sorted(level_target.items()) if day_idx == d],
        })

    # 閘門的 big-M 被頂到 ＝ 上面那個單日供給上界估太小，排出來的可能不是真正
    # 最省的解。這是最危險的失敗模式（默默變差、不會報錯），所以寧可講出來。
    # 實測實際資料的單日峰值約十次、M 在一兩百之間，離很遠；會撞到就是程式有問題。
    binding = [(days[d], levels[i]["label"], row["counts"][i], unlock_cap[i])
               for d, row in enumerate(schedule) for i in unlock_gated
               if row["counts"][i] >= unlock_cap[i]]
    if binding:
        warnings.append(
            "解鎖鏈的內部上限被頂到了："
            + "、".join(f"{day:%m/%d} {label}×{got}（內部上限 {limit}）"
                        for day, label, got, limit in binding)
            + "。這代表排出來的排程可能不是最省的（不是錯的，只是可能有更好的"
              "解）。請把這句話連同當時的設定回報，這是程式該修的地方")

    doomed = doomed_marker.get("doomed", [])
    claim_y = solution["claim_y"]

    def granted_of(p):
        if p in claim_y:
            return pools[p]["total"] * val(claim_y[p])
        return pools[p]["total"]

    weekly_usage = []
    for p, pool in enumerate(pools):
        granted = granted_of(p)
        if "claim" in pool and not granted:
            continue          # 沒選這一週領的候選池
        used = sum(val(solution["pool_use"][p][d]) for d in range(n_days))
        # 沒用完的部分要分清楚是「蒸發」還是「留到下一檔」
        left = granted - used
        carried = p not in doomed
        weekly_usage.append({
            "label": pool["label"], "granted": granted, "used": used,
            "expired": 0 if carried else left, "carried": left if carried else 0,
            "start": pool["start"], "end": pool["end"], "expire": pool["expire"],
            "sources": pool.get("sources") or [],
        })

    # 先放著、晚點再領的體力：哪天領、哪天到期
    claims = []
    for k, lot in enumerate(claim_lots):
        # 達標日照最終排程實際的進度算，不看求解器裡的 reached 旗標——手動領取時
        # 那個旗標「明明達標了卻記 0」也合法（等於晚點再領），後面的階段重排
        # 關卡之後它常常就留在 0，報表會誤寫成「沒有達標」。
        reach_day = None
        if lot["reach"] is not None:
            spec = lot["reach"]
            for d in range(n_days):
                upto = dict(spec, cells=[c for c in spec["cells"] if c[0] <= d])
                if _planned_metric(upto, seg_counts, levels, costs) >= spec["need"]:
                    reach_day = days[d]
                    break
        chosen = [p for p in lot["pools"] if val(claim_y[p])]
        row = {"label": lot["label"], "amount": lot["amount"],
               "received": lot["received"], "deadline": lot["deadline"],
               "needs_reach": lot["reach"] is not None, "reach_day": reach_day,
               "auto": bool(lot.get("auto")), "ref": lot["ref"]}
        if chosen:
            p = chosen[0]
            use_days = [d for d in range(n_days)
                        if val(solution["pool_use"][p][d])]
            use_day = days[use_days[0]] if use_days else None
            # 這一週裡能領的日子：選到的那一週（收到日／達標日以後）到這週的最後
            # 一個可領日（週日或領取期限，取早的）。同一週內哪天領到期日都一樣，
            # 但「第一次用」可能在下一週以後——那時信箱早就過期了，所以領取日
            # 不能直接拿第一次用的日子（月底才用的寫成月底才領，
            # 信箱可能早一週多就過期了）。
            window_start = pools[p]["start"]
            if reach_day is not None:
                window_start = max(window_start, reach_day)
            window_end = days[pools[p]["week_last_idx"]]
            claim_day = (use_day if use_day is not None and use_day <= window_end
                         else window_start)
            if lot.get("auto"):
                claim_day = reach_day or sched_start     # 一達標就進包包
            left = lot["amount"] - sum(val(solution["pool_use"][p][d])
                                       for d in range(n_days))
            row.update(claim_day=claim_day, expire=pools[p]["expire"],
                       claim_by=window_end, use_day=use_day,
                       carried=p not in doomed and left > 0, in_plan=True)
        elif lot["reach"] is not None and reach_day is None:
            # 排程裡沒有達標，領不到
            row.update(claim_day=None, expire=None, carried=False, in_plan=False)
        else:
            # 排程範圍內都不領：同一週內領到期日都一樣，最晚那一週的週一領就好
            earliest = max(lot["open"], sched_start,
                           (reach_day + timedelta(days=1)) if reach_day else sched_start)
            monday = lot["deadline"] - timedelta(days=lot["deadline"].weekday())
            claim_day = max(earliest, monday)
            row.update(claim_day=claim_day, expire=expiry_of(claim_day),
                       carried=True, in_plan=False)
        claims.append(row)

    # 任務達成狀況
    for index, spec in enumerate(constraints):
        got = _planned_metric(spec, seg_counts, levels, costs)
        spec["planned"] = got
        spec["short"] = max(0, spec["need"] - got)
        for win in spec["row"]["windows"]:
            if win["label"] == spec["label"] and win["need"] == spec["need"]:
                win["planned"] = got
                win["met"] = got >= spec["need"]
    shortfalls = []
    for index, spec in enumerate(constraints):
        gap = int(round(solution["shorts"].get(index, 0) or 0))
        if spec.get("pinned_soft"):
            # 以實際排出來的量為準：short 變數在 gap 容忍範圍內可能不精確
            gap = spec["short"]
        if gap > 0:
            shortfalls.append({
                "task": spec["row"]["name"],
                "event": spec["row"]["event_name"],
                "metric": spec["metric"], "need": spec["need"], "short": gap,
                "label": spec["label"],
                "pinned": bool(spec.get("pinned_soft")),
            })
    # 分組解鎖型活動被放寬的「至少打一次」：以實際排出來的次數為準（跟上面的
    # 任務一樣，short 變數在 gap 容忍範圍內可能不精確），整檔一則。
    missed_by_event: dict[str, list] = {}
    for chain in unlock_chains:
        if not chain["soft_ok"]:
            continue
        missed = [i for i in chain["need"]
                  if not any(row["counts"][i] for row in schedule)]
        if missed:
            missed_by_event.setdefault(chain["event"]["id"], []).append(
                (chain, missed))
    for event_id, parts in missed_by_event.items():
        count = sum(len(missed) for _chain, missed in parts)
        shortfalls.append({
            "task": "每關至少打一次",
            "event": events_by_id[event_id]["name"],
            "metric": "unlock",
            "need": sum(len(chain["need"]) for chain in unlock_chains
                        if chain["soft_ok"] and chain["event"]["id"] == event_id),
            "short": count,
            "label": "、".join(chain_order_text(chain, missed)
                              for chain, missed in parts) + " 還沒打",
        })

    # 各活動的小結
    event_rows = []
    for event in events:
        indices = [i for i, lv in enumerate(levels) if lv["event_id"] == event["id"]]
        data = (profile.get("events") or {}).get(event["id"]) or {}
        event_rows.append({
            "id": event["id"], "name": event["name"], "type": event["type"],
            "start_dt": event["start_dt"], "end_dt": event["end_dt"],
            "countdown": format_countdown(event["end_dt"], query_dt),
            "current_points": int(data.get("current_points") or 0),
            "current_clears": int(data.get("current_clears") or 0),
            "gained_points": sum(points_of[i] * row["counts"][i]
                                 for row in schedule for i in indices),
            "clears": sum(row["counts"][i] for row in schedule for i in indices),
            "spend": sum(costs[i] * row["counts"][i]
                         for row in schedule for i in indices),
            # 沒有自己的關卡（音像那種只有累計耗體任務的）——報表要講出來，
            # 不然看到一排 0 會以為算錯了
            "has_levels": bool(indices),
            # 積分上限（加成後）。報表要講出「這檔打完會不會頂到封頂、超出多少」，
            # 不然使用者只看到一個超標的數字，會以為排程算壞了。
            "points_cap": event.get("points_cap"),
            "tasks": [row for row in task_rows if row["event_id"] == event["id"]],
        })
        row = event_rows[-1]
        row["points_after"] = row["current_points"] + row["gained_points"]
        row["points_wasted"] = (0 if row["points_cap"] is None
                                else max(0, row["points_after"] - int(row["points_cap"])))

    # 積分上限相關的提醒。放在這裡是因為第 2、3 條要看排完的結果。
    for row in event_rows:
        # 變數名不能叫 cap——這個函式後面還要用它算收工體力上限
        limit = row["points_cap"]
        if limit is None:
            continue
        limit = int(limit)
        over_tasks = [t for t in row["tasks"]
                      if t["metric"] == "points" and t["amount"] > limit]
        for task in over_tasks:
            warnings.append(
                f"任務「{task['name']}」的目標 {task['amount']} 高於"
                f"「{row['name']}」的積分上限 {limit}，這個目標永遠達不到，請檢查哪一邊填錯了")
        if row["current_points"] >= limit:
            warnings.append(
                f"「{row['name']}」的積分已經到上限 {limit}（目前 {row['current_points']}），"
                "排程不會再為它安排計分關卡，體力都導去不計分的關卡了")
        elif row["points_wasted"]:
            warnings.append(
                f"「{row['name']}」的積分會打到上限 {limit}，超出的 {row['points_wasted']} 分"
                "拿不到獎勵——那是關卡積分跨不過去的零頭，多出來的體力已經改排不計分關卡")
        else:
            # 天花板由任務目標決定（比獎勵表封頂更嚴）時，排程會刻意不把獎勵表打滿。
            # 講出來，不然使用者只看到一個比上限低的數字，會以為排程漏打了。
            # 判斷條件跟 build_and_solve 的 ceiling 完全一致。
            targets = [c["need"] for c in constraints
                       if c.get("whole_event") and c["metric"] == "points"
                       and c["event_id"] == row["id"] and c["default_scope"]]
            headroom = limit - row["current_points"]
            if targets and max(targets) < headroom:
                warnings.append(
                    f"「{row['name']}」的積分停在任務目標（這次排程 +{max(targets)} 分，"
                    f"收工時 {row['points_after']}），沒有把獎勵表上限 {limit} 打滿——"
                    f"還差 {limit - row['points_after']} 分，那段體力已經改排不計分的關卡。"
                    "想打滿上限的話，把積分任務的目標調高")

    # 這段期間預計可以拿到的獎勵
    rewards = _expected_rewards(shared, task_rows, days)

    if done_counts:
        parts = []
        done_clears = sum(done_counts.values())
        done_spend = measure(today_entries, "stamina", None)
        done_enemies = measure(today_entries, "enemies", None)
        if done_clears:
            parts.append(f"{done_clears} 關")
        if done_enemies:
            parts.append(f"{done_enemies} 敵人")
        if done_spend:
            parts.append(f"{done_spend} 體力")
        warnings.append(
            f"{days[0]:%m/%d} 已經記錄了 {'、'.join(parts)}，"
            "當天的每日任務要求已經扣掉這些，排出來的是「從現在起還要再打的」")

    total_waste = sum(r["waste"] for r in schedule)
    if total_waste > 0:
        warnings.append(
            f"排程中有 {total_waste} 點自然回復會頂到體力上限而浪費，"
            "可考慮把耗體量拉平、每天多檢查幾次體力")
    expired_weekly = sum(w["expired"] for w in weekly_usage)
    if expired_weekly > 0:
        warnings.append(
            f"有 {expired_weekly} 點限時體力用不完會過期。"
            "排程刻意先花自然回復、把限時資源留到最後——因為自然回復頂到上限"
            "溢出是永久損失，而過期的限時體力還能拿去打不計分的關卡。"
            "記得在當週結束前把它用掉")
    carried_weekly = sum(w["carried"] for w in weekly_usage)
    if carried_weekly > 0:
        warnings.append(
            f"有 {carried_weekly} 點限時體力的到期日在排程結束之後，"
            "排程刻意不去動它，留給下一檔活動用（這不是浪費）")

    # 睡覺期間只回復不消耗，收工時體力太高的話隔天早上就滿了、白白溢出。
    night_waste = sum(r["waste_night"] for r in schedule)
    # 過夜＝當天收工後 ＋ 隔天重置到開工前。任務日在重置時刻換日，只算前半段的話
    # 會少算開工前那一小段（05:00 重置、06:00 開工就是少 12 點）。
    overnight = max((sum(seg["recovery"] for seg in day_segs
                         if not seg["before_bed"])
                     + sum(seg["recovery"]
                           for seg in segments_on(days[d] + timedelta(days=1))
                           if seg["before_open"])
                     for d, day_segs in enumerate(segments)), default=0)
    active_recovery_max = max(
        (sum(seg["recovery"] for seg in day_segs
             if seg["playable"] and not seg["overtime"])
         for day_segs in segments), default=0)
    bedtime_ceiling = max(0, cap - overnight)
    if overnight > 0:
        note = (f"收工（{act_end:%H:%M}）時體力要壓在 {bedtime_ceiling} 以下，"
                f"到隔天開工前會回復 {overnight} 點，超過 {cap} 的部分就浪費了")
        if night_waste > 0:
            note += f"。目前排程有 {night_waste} 點是這樣過夜浪費掉的"
        warnings.append(note)

    if active_recovery_max > cap:
        min_checkins = math.ceil(active_recovery_max / cap)
        active_hours = (minutes_of(act_end) - minutes_of(act_start)) / 60.0
        warnings.append(
            f"上線時段（{act_start:%H:%M}~{act_end:%H:%M}）內會回復 "
            f"{active_recovery_max} 點，但體力上限只有 {cap}，"
            f"代表這段時間裡至少要分 {min_checkins} 次使用體力"
            f"（約每 {active_hours / min_checkins:.1f} 小時一次），否則會頂到上限停止回復")

    base_spend = sum(costs[i] * c
                     for d in range(n_days)
                     for s in range(len(segments[d]))
                     for i, c in enumerate(base_counts[d][s]))
    return {
        "levels": levels,
        "points_of": points_of,
        "days": days,
        "events": event_rows,
        # 「盡量提早」的成果，每檔設了日期的活動一列（沒設就是空的）
        "early": early_rows,
        "tidy": {k: v for k, v in tidy_note.items() if k != "failed"},
        "schedule": schedule,
        # 今天已經記錄的打法。counts 只有在「排程首日就是今天」時才會有東西，
        # 所以下游可以直接往 schedule[0] 合併。
        "done_today": {"counts": done_counts, "label": done_label,
                       "date": days[0]},
        # 查詢時已經過了上線時段：首日只排補完今天任務需要的量（見加班階段）
        "overtime_today": bool(overtime_cells),
        # 手動鎖定的日子（對調日期）。再調整一次時要把這份一起帶回來。
        "pinned": {days[d]: {levels[i]["key"]: n
                             for i, n in enumerate(fixed) if n}
                   for d, fixed in pinned_idx.items()},
        # 指定日期打指定次數（這次真的套用的那幾條）。count 是當天總數。
        "targets": {
            days[d]: {levels[i]["key"]: {"mode": mode, "count": wanted}
                      for (day_idx, i), (mode, _remaining, wanted)
                      in level_target.items() if day_idx == d}
            for d in sorted({day_idx for day_idx, _i in level_target})},
        # 代幣關卡：排程首日（今天的話＝從現在起）手上有幾個
        "tokens": [{"label": rule["label"], "held": rule["start"],
                    "max": rule["max"], "per_day": rule["per_day"]}
                   for rule in token_rules],
        # [日][關卡] 那天那關打不打得到——對調日期前先擋掉不可行的
        "playable": playable_days,
        "weekly_usage": weekly_usage,
        "claims": claims,
        "tasks": task_rows,
        "shortfalls": shortfalls,
        "rewards": rewards,
        "warnings": warnings,
        "summary": {
            "event_start": sched_start,
            "event_end": last_end,
            "sched_start": sched_start,
            "n_days": n_days,
            "n_events": len(events),
            "current_stamina": current_stamina,
            "initial_stamina": initial_stamina,
            "held_corrected": bool(held_by_expiry),
            "used_natural": sum(r["use_nat"] for r in schedule),
            "used_weekly": sum(r["use_weekly"] for r in schedule),
            "granted_weekly": sum(w["granted"] for w in weekly_usage),
            "night_waste": night_waste,
            "bedtime_ceiling": bedtime_ceiling,
            "reset_time": reset,
            "active_start": act_start,
            "active_end": act_end,
            "active_recovery": active_recovery_max,
            "overnight_recovery": overnight,
            # 上線時段以外的回復（開工前 ＋ 收工後），也就是「睡覺期間回復多少」
            "sleep_recovery": max(
                (sum(seg["recovery"] for seg in day_segs
                     if not seg["playable"] or seg["overtime"])
                 for day_segs in segments), default=0),
            "query_dt": query_dt,
            "stamina_cap": cap,
            "per_day_recovery": per_day_recovery,
            "total_recovery": sum(recovery),
            "needed_points": sum(
                max(0, c["need"]) for c in constraints if c["metric"] == "points"),
            "gained_points": sum(r["points"] for r in schedule),
            "total_clears": sum(r["clears"] for r in schedule),
            "scoring_clears": sum(r["scoring_clears"] for r in schedule),
            "has_non_scoring": any(not lv["scoring"] for lv in levels),
            "base_spend": base_spend,
            "reclaimable": solution["reclaimable"],
            "extra_spend": sum(
                costs[i] * c
                for r in schedule for i, c in enumerate(r["extra_counts"])),
            "non_scoring_spend": sum(
                costs[i] * count
                for r in schedule for i, count in enumerate(r["counts"])
                if not levels[i]["scoring"]),
            "total_enemies": sum(r["enemies"] for r in schedule),
            # 下面四個是「彙總過的」方便值：任務化之後每一條要求各自獨立，
            # 但報表與測試常常只想知道「每天至少幾關」「總量還差幾關」。
            "daily_min": max(daily_clear_floor.values(), default=0),
            "daily_min_enemies": max(daily_enemy_floor.values(), default=0),
            "total_min": sum(int(spec["row"]["amount"]) for spec in constraints
                             if spec["metric"] == "clears" and spec["soft_ok"]),
            "needed_clears": sum(spec["need"] for spec in constraints
                                 if spec["metric"] == "clears" and spec["soft_ok"]),
            "current_clears": sum(
                int(((profile.get("events") or {}).get(ev["id"]) or {})
                    .get("current_clears") or 0) for ev in events),
            "tracks_enemies": bool(any(enemies_of)),
            "has_enemy_ranges": bool(daily_enemy_floor),
            "total_spend": sum(r["spend"] for r in schedule),
            "total_buy": sum(r["buy"] for r in schedule),
            "total_waste": total_waste,
            "final_balance": schedule[-1]["nat_balance"],
        },
    }


def _reset_windows(cycle: str, first: date, last: date,
                   weekly_weekday: int, monthly_day: int):
    """把一段日期切成一個個「重置窗」。

    每日／公會＝一天一個窗；每週＝從指定星期幾算起的七天；
    每月＝從指定幾號算起到下個月同一號的前一天。

    窗的**頭**不裁到 `first`：本期已經過掉的日子仍然要算進「已經做掉多少」。
    尾端照裁——排程結束之後的日子沒有紀錄可量，留著只會讓標籤承諾排不到的日子。
    """
    if cycle in ("daily", "guild"):
        day = first
        while day <= last:
            yield day, day
            day += timedelta(days=1)
        return
    if cycle == "weekly":
        day = first
        while day <= last:
            back = (day.weekday() - weekly_weekday) % 7
            win_first = day - timedelta(days=back)
            win_last = win_first + timedelta(days=6)
            yield win_first, min(win_last, last)
            day = win_last + timedelta(days=1)
        return
    if cycle == "monthly":
        day = first
        while day <= last:
            if day.day >= monthly_day:
                win_first = day.replace(day=monthly_day)
            else:
                prev = day.replace(day=1) - timedelta(days=1)
                win_first = prev.replace(day=monthly_day)
            nxt = win_first.replace(day=28) + timedelta(days=4)
            win_last = nxt.replace(day=monthly_day) - timedelta(days=1)
            yield win_first, min(win_last, last)
            day = win_last + timedelta(days=1)
        return
    yield first, last


def _metric_expr(pulp, spec, plays, seg_spend, enemies_of, points_of, drops_of):
    """把一條任務限制換成求解器看得懂的式子。

    逐「日×段」加總，段落由 `spec["cells"]` 指定——活動任務只算那檔活動
    還開著的段落，不是整天（見 `compute_plan.live_segments`）。
    """
    metric = spec["metric"]
    if metric == "stamina":
        return pulp.lpSum(seg_spend[d][s] for d, s in spec["cells"])
    weight = {"points": points_of, "enemies": enemies_of,
              "drops": drops_of}.get(metric)
    return pulp.lpSum((weight[i] if weight else 1) * plays[d][s][i]
                      for d, s in spec["cells"] for i in spec["levels"]
                      if plays[d][s][i] is not None)


def _planned_metric(spec, seg_counts, levels, costs) -> int:
    """這次排程在這條限制的範圍內實際排到多少。

    跟 `_metric_expr` 用同一份 `spec["cells"]`——兩邊的尺不一樣的話，
    報表會出現「排程明明照做了，任務卻顯示沒達成」這種鬼打牆。
    """
    metric = spec["metric"]
    if metric == "stamina":
        return sum(costs[i] * seg_counts[d][s][i]
                   for d, s in spec["cells"] for i in range(len(levels)))
    weight = ({i: levels[i]["points"] for i in spec["levels"]} if metric == "points"
              else {i: levels[i]["enemies"] for i in spec["levels"]}
              if metric == "enemies"
              else {i: int(levels[i].get("drops") or 0) for i in spec["levels"]}
              if metric == "drops" else None)
    return sum((weight[i] if weight else 1) * seg_counts[d][s][i]
               for d, s in spec["cells"] for i in spec["levels"])


def _expected_rewards(shared: dict, task_rows: list[dict],
                      days: list[date]) -> list[dict]:
    """剩餘期間如果把任務都做完，預計可以拿到的道具總計。"""
    items = {it.get("id"): it for it in (shared or {}).get("items") or []}
    totals: dict[str, int] = {}
    for row in task_rows:
        times = len(row["windows"]) or (1 if row["cycle"] == "event" else 0)
        if row["cycle"] in ("daily", "guild") and not row["windows"]:
            times = len(days)
        for reward in row["rewards"]:
            qty = int(reward.get("qty") or 0) * times
            if qty:
                totals[reward.get("item")] = totals.get(reward.get("item"), 0) + qty
    result = []
    for item_id, qty in sorted(totals.items(), key=lambda kv: -kv[1]):
        item = items.get(item_id) or {"name": item_id, "stamina": 0}
        result.append({"item": item_id, "name": item.get("name") or item_id,
                       "qty": qty,
                       "stamina": int(item.get("stamina") or 0) * qty})
    return result


def plan_snapshot(result: dict) -> dict:
    """把排程結果壓縮成可存檔的形式。

    `days` 只留「哪天打什麼」，體力來源、餘額那些推導資訊不存——重算就有了。
    `report` 存的是完整的分析文字，這樣關掉程式再開還看得到上次算出什麼，
    不必為了看結論重跑一次求解。

    **首日要把今天已經記錄的打法加回去**，存的是「今天總共要打的」而不是
    「還要打的」。「每日紀錄」把它跟「實際打法」並排顯示，兩欄必須同一個基準，
    否則相減會得到錯的數字；「照計畫記錄」按鈕也是直接覆蓋當天的紀錄，
    存成「還要打的」會把今天稍早已經記下的打法洗掉。
    """
    levels = result["levels"]
    days = {
        row["date"].isoformat(): {
            levels[i]["key"]: count
            for i, count in enumerate(row["counts"]) if count
        }
        for row in result["schedule"]
    }
    # counts 只在「排程首日就是今天」時才有東西，所以固定合併到首日。
    # 用關卡鍵相加，這次不列入計算、但真的打過的關卡也會併進來。
    done = result["done_today"]["counts"]
    if done:
        first = result["schedule"][0]["date"].isoformat()
        merged = dict(days.get(first) or {})
        for key, count in done.items():
            merged[key] = merged.get(key, 0) + count
        days[first] = merged
    return {
        "computed_at": datetime.now().astimezone().isoformat(timespec="seconds"),
        "days": days,
        "report": format_result(result),
        # 打法歸納與提醒另外存，計算分頁按按鈕才顯示
        "extras": format_extras(result),
        # 每日紀錄的領取提醒用（見 app.App.pending_claims）；自動領取的不用提醒
        "claims": [{"label": c["label"], "amount": c["amount"],
                    "claim_day": c["claim_day"].isoformat(),
                    "expire": c["expire"].isoformat() if c["expire"] else None,
                    "deadline": c["deadline"].isoformat(), "ref": c["ref"]}
                   for c in result.get("claims") or ()
                   if c["claim_day"] is not None and not c.get("auto")],
    }


# --------------------------------------------------------------------------
# 結果格式化
# --------------------------------------------------------------------------

def text_width(text: str) -> int:
    """字串在等寬字型下佔幾格。中文、全形標點都算兩格。"""
    return sum(2 if unicodedata.east_asian_width(ch) in "WF" else 1
               for ch in str(text))


def pad(text, width: int, align: str = "<") -> str:
    """依實際顯示寬度補空白。

    不能用 `str.format` 的寬度——它把中文算成 1 格，一排下來會整個歪掉。
    """
    text = str(text)
    space = max(0, width - text_width(text))
    return text + " " * space if align == "<" else " " * space + text


def render_table(columns, rows) -> list:
    """排版成「抬頭跟內容一定對得齊」的表格，回傳每一行的字串。

    columns：[(抬頭, 最小寬度, 對齊)]
    rows：   [(儲存格list, 尾註)]，尾註接在最後一欄後面，不佔欄寬

    欄寬取「抬頭與該欄所有內容的最大實際寬度」再加兩格間距。

    不寫死欄寬：寫死的話只要某格內容超出欄寬，後面整排就被往右推，
    跟抬頭差了一到兩欄——例如打法欄寫死 30 格，而
    「關卡1×1、關卡5×9、經商貿易×1、探索調查×1」佔 44 格，那一行的耗體
    數字就跑到「補充」欄的位置底下，整張表根本不能照欄位讀。

    **抬頭要用該欄自己的對齊方式**，否則右對齊的數字欄跟抬頭會差兩格。
    """
    widths = []
    for idx, (title, min_width, _align) in enumerate(columns):
        content = max([text_width(str(cells[idx])) for cells, _n in rows]
                      or [0])
        widths.append(max(min_width, text_width(title) + 2, content + 2))
    out = ["".join(pad(title, widths[idx], align)
                   for idx, (title, _w, align) in enumerate(columns)).rstrip()]
    for cells, note in rows:
        line = "".join(pad(cell, widths[idx], columns[idx][2])
                       for idx, cell in enumerate(cells))
        out.append((line + (note or "")).rstrip())
    return out


def format_result(result: dict) -> str:
    s = result["summary"]
    levels = result["levels"]
    lines = []

    lines.append("=" * 68)
    lines.append("排程結果")
    lines.append("=" * 68)
    lines.append(f"排程範圍　　：{s['sched_start']:%Y-%m-%d} 起，共 {s['n_days']} 天")
    lines.append(f"查詢時間　　：{s['query_dt']:%Y-%m-%d %H:%M}，"
                 f"當下體力 {s['current_stamina']}")
    if result.get("pinned"):
        lines.append("手動調整　　："
                     + "、".join(format_day(day) for day in sorted(result["pinned"]))
                     + "（照你對調的打法鎖住，其餘日子配合重排）")
    if result.get("targets"):
        names = {lv["key"]: lv["label"] for lv in levels}
        lines.append("指定次數　　：" + "、".join(
            f"{format_day(day)} {names.get(key, key)}"
            f"{'至少' if spec['mode'] == 'min' else ''}×{spec['count']}"
            for day, row in sorted(result["targets"].items())
            for key, spec in row.items()))
    if result.get("tokens"):
        lines.append("代幣　　　　：" + "、".join(
            f"{t['label']} 現有 {t['held']} 個" for t in result["tokens"])
            + "（每天發的會自動加上，頂多存到上限）")
    lines.append(f"體力上限　　：{s['stamina_cap']}　自然回復："
                 f"{s['per_day_recovery']} 點/天")
    lines.append(f"作息設定　　：每日 {s['reset_time']:%H:%M} 重置、"
                 f"上線時段 {s['active_start']:%H:%M}~{s['active_end']:%H:%M}"
                 f"（上線內回復 {s['active_recovery']}、"
                 f"收工到隔天開工回復 {s['overnight_recovery']}）")
    lines.append(f"　　　　　　　「收工」欄＝{s['active_end']:%H:%M} 當下的體力，"
                 f"建議壓在 {s['bedtime_ceiling']} 以下，否則過夜會頂到上限浪費")
    lines.append("")

    # ---- 各活動 --------------------------------------------------------
    lines.append("-" * 68)
    lines.append(f"活動（{s['n_events']} 檔同時進行）" if s["n_events"] > 1 else "活動")
    lines.append("-" * 68)
    for event in result["events"]:
        lines.append(
            f"◆ {event['name']}　"
            f"{event['start_dt']:%m/%d %H:%M} ~ {event['end_dt']:%m/%d %H:%M}"
            f"　剩 {event['countdown']}")
        if event.get("has_levels", True):
            cap_note = ""
            if event.get("points_cap") is not None:
                cap_note = f"　積分上限 {event['points_cap']}"
                if event["points_wasted"]:
                    cap_note += f"，超出 {event['points_wasted']} 分不計"
                elif event["points_after"] == event["points_cap"]:
                    cap_note += "，剛好打滿"
                else:
                    cap_note += (f"，本排程結束時 {event['points_after']}"
                                 f"（還差 {event['points_cap'] - event['points_after']}）")
            lines.append(
                f"　本排程：{event['clears']} 關、耗體 {event['spend']}、"
                f"積分 +{event['gained_points']}"
                f"（目前 {event['current_points']}）{cap_note}")
        else:
            lines.append("　（這檔沒有自己的關卡，任務靠其他活動的耗體累積）")
        for task in event["tasks"]:
            lines.append("　" + _task_line(task))
        lines.append("")

    routine = [t for t in result["tasks"] if t["event_id"] is None]
    if routine:
        lines.append("◆ 固定任務")
        for task in routine:
            lines.append("　" + _task_line(task))
        lines.append("")

    if result["shortfalls"]:
        lines.append("-" * 68)
        lines.append("★ 湊不齊的目標")
        lines.append("-" * 68)
        for gap in result["shortfalls"]:
            if gap["metric"] == "unlock":
                lines.append(f"　{gap['event']}：{gap['label']}"
                             f"（差 {gap['short']} 關，共 {gap['need']} 關要打過一次）")
                continue
            where = f"（{gap['event']}）" if gap["event"] else ""
            tag = "　← 因為手動調整" if gap.get("pinned") else ""
            lines.append(f"　{gap['task']}{where} {gap['label']}："
                         f"還差 {gap['short']}（需要 {gap['need']}）{tag}")
        if any(not gap.get("pinned") for gap in result["shortfalls"]):
            lines.append("　＝目前的體力與時間湊不到這些目標，"
                         "請考慮調低目標、買體力，或放掉其中一檔活動")
        if any(gap.get("pinned") for gap in result["shortfalls"]):
            lines.append("　＝標「因為手動調整」的是你對調日期之後那幾天達不到的要求，"
                         "排程照你的調整走；不想放掉就換一組日子對調")
        lines.append("")

    clears_note = ""
    if s["has_non_scoring"]:
        clears_note = f"（其中計分 {s['scoring_clears']} 關）"
    if s["total_min"]:
        # 「關卡次數」類的任務只算會進總量的關卡（計分 ＋ 只算次數），
        # 跟左邊那個「全部關卡」的總數不是同一回事，講清楚免得對不起來
        clears_note += (f"（關卡次數任務還差 {s['needed_clears']} 關，"
                        "只算會進總量的關卡）")
    spend_note = (f"（含不計分關 {s['non_scoring_spend']}）"
                  if s["non_scoring_spend"] else "")
    lines.append(f"總關卡數　　：{s['total_clears']} 關{clears_note}"
                 f"　　總消耗體力：{s['total_spend']}{spend_note}")
    if s["tracks_enemies"]:
        lines.append(f"總擊殺敵人　：{s['total_enemies']} 人")
    lines.append(f"期間自然回復：{s['total_recovery']}"
                 f"　　期末剩餘：{s['final_balance']}　　上限浪費：{s['total_waste']}")
    lines.append("")
    if s["total_buy"] > 0:
        lines.append(f"★ 需額外補充體力：{s['total_buy']} 點")
    else:
        lines.append("★ 不需額外補充體力，自然回復＋免費資源即可達成")
    lines.append("")

    # 把「需額外補充」是怎麼算出來的攤開來，免得要自己反推
    lines.append("-" * 68)
    lines.append("體力收支（★ 就是這張表湊不齊的差額）")
    lines.append("-" * 68)

    def money(label, value, suffix="", indent=2):
        return (" " * indent + pad(label, 26 - indent)
                + pad(value, 8, ">") + suffix)

    lines.append(money("總共要花掉", s["total_spend"]))
    lines.append("  由這些來源支付：")
    lines.append(money("自然回復池", s["used_natural"], indent=4))
    if s["granted_weekly"]:
        lines.append(money("限時體力", s["used_weekly"],
                           f"　（發放 {s['granted_weekly']}）", indent=4))
    lines.append(money("需額外補充", s["total_buy"], "　← ★", indent=4))
    lines.append("")
    lines.append("  自然回復池的內部帳：")
    lines.append(money("開始時手上的體力", s["initial_stamina"], indent=4))
    lines.append(money("期間自然回復", s["total_recovery"], indent=4))
    lines.append(money("頂到上限浪費掉", f"-{s['total_waste']}", indent=4))
    lines.append(money("期末沒用完剩下", f"-{s['final_balance']}", indent=4))
    lines.append(money("＝ 實際用掉", s["used_natural"], indent=4))
    lines.append("")

    if s["extra_spend"]:
        lines.append("-" * 68)
        lines.append("消化多餘體力（第二次計算加上去的）")
        lines.append("-" * 68)
        expired_now = sum(w["expired"] for w in result["weekly_usage"])
        lines.append(
            f"　只求達標的話會花 {s['base_spend']} 點，"
            f"但有 {s['reclaimable']} 點不用就永久消失")
        lines.append("　（頂到上限的自然回復 ＋ 到期沒用完的限時體力）")
        lines.append(
            f"　多打 {s['extra_spend']} 點之後，損失降到 "
            f"{s['total_waste'] + expired_now} 點，總消耗變成 {s['total_spend']}")
        extra_by_level = {}
        for row in result["schedule"]:
            for i, count in enumerate(row["extra_counts"]):
                if count:
                    extra_by_level[levels[i]["label"]] = (
                        extra_by_level.get(levels[i]["label"], 0) + count)
        if extra_by_level:
            lines.append("　多打的關卡：" + "、".join(
                f"{name}×{count}" for name, count in
                sorted(extra_by_level.items(), key=lambda kv: -kv[1])))
        lines.append("　（每日明細的「加碼」欄就是這部分；不打也不影響達標。"
                     "活動關卡可能跟著換日子，總次數不變）")
        lines.append("")

    if result["weekly_usage"]:
        lines.append("-" * 68)
        lines.append("限時體力")
        lines.append("-" * 68)
        # 同一天過期的池子對玩家來說可以互換，合併成一列比較好讀
        # （每週發的跟依發放日拿的常常會撞在同一個星期日）。
        merged = {}
        names_by_expiry = {}
        for w in result["weekly_usage"]:
            row = merged.setdefault(w["expire"],
                                    {"granted": 0, "used": 0,
                                     "expired": 0, "carried": 0})
            for key in row:
                row[key] += w[key]
            names = names_by_expiry.setdefault(w["expire"], [])
            names += [n for n in w.get("sources") or () if n not in names]
        columns = [("到期日", 10, "<"), ("發放", 8, ">"), ("用掉", 8, ">"),
                   ("過期", 8, ">"), ("留到下一檔", 12, ">")]
        rows = []
        for expire in sorted(merged):
            row = merged[expire]
            names = names_by_expiry.get(expire)
            rows.append(([f"{expire:%m/%d}", row["granted"], row["used"],
                          row["expired"] or "-", row["carried"] or "-"],
                         f"　{'、'.join(names)}" if names else ""))
        lines.extend(render_table(columns, rows))
        if any(w["carried"] for w in result["weekly_usage"]):
            lines.append("　「留到下一檔」＝到期日在排程結束之後，"
                         "排程刻意留著沒用，不是浪費")
        if s.get("held_corrected"):
            lines.append("　手上的限時體力以你在計算頁填的為準；"
                         "今天之後才發放的照排程算")
        lines.append("")

    if result.get("claims"):
        lines.append("-" * 68)
        lines.append("信箱與任務獎勵的領取時機（整筆一次領，效期從領出來那週算）")
        lines.append("-" * 68)
        lines.append("　「起用」＝排程第一次用到這批的日子；沒寫就是領的當天用")
        for c in result["claims"]:
            head = f"　{c['label']} {c['amount']}："
            if c["received"]:
                head += f"{c['received']:%m/%d} 收到，"
            if c["needs_reach"]:
                head += (f"預計 {c['reach_day']:%m/%d} 達標，" if c["reach_day"]
                         else "這次排程沒有達標，領不到")
            if c["claim_day"] is not None:
                by = c.get("claim_by")
                head += (f"{format_day(c['claim_day'])} "
                         + ("自動進包包" if c.get("auto") else "領")
                         + "（"
                         + (f"最晚 {by:%m/%d} 領；"
                            if by and not c.get("auto") and by > c["claim_day"] else "")
                         + f"{c['expire']:%m/%d} 到期"
                         + ("，留到下一檔" if c["carried"] else "") + "）")
                use = c.get("use_day")
                if use is not None and use > c["claim_day"]:
                    head += f"，{use:%m/%d} 起用"
                if not c["in_plan"] and not c.get("auto"):
                    head += f"——這次用不到；最晚 {c['deadline']:%m/%d} 要領"
            lines.append(head)
        lines.append("")

    if result["rewards"]:
        lines.append("-" * 68)
        lines.append("預計可拿到的獎勵（任務全做完的話）")
        lines.append("-" * 68)
        for item in result["rewards"]:
            extra = f"　＝體力 {item['stamina']}" if item["stamina"] else ""
            lines.append(f"　{item['name']}×{item['qty']}{extra}")
        lines.append("")

    lines.append("-" * 68)
    lines.append("每日明細")
    lines.append("-" * 68)
    columns = [("日期", 14, "<"), ("關卡打法", 30, "<"), ("關數", 6, ">")]
    if s["tracks_enemies"]:
        columns.append(("敵人", 7, ">"))
    columns += [("耗體", 7, ">"), ("補充", 7, ">"), ("收工", 7, ">"),
                ("隔早", 7, ">")]
    table_rows = []
    done_label = result["done_today"]["label"]
    for index, row in enumerate(result["schedule"]):
        plan = "、".join(f"{levels[i]['label']}×{c}"
                         for i, c in enumerate(row["counts"]) if c) or "（不打）"
        extra = "、".join(f"{levels[i]['label']}×{c}"
                          for i, c in enumerate(row["extra_counts"]) if c)
        note = "　[手動調整]" if row.get("pinned") else ""
        if row.get("targets"):
            note += "　[指定 " + "、".join(
                f"{levels[i]['label']}{'至少' if mode == 'min' else ''}×{wanted}"
                for i, mode, wanted in row["targets"]) + "]"
        if extra:
            note += f"　[加碼 {extra}]"
        # 這張表列的是「從現在起還要打的」——耗體、補充、收工那幾欄都是往前看的
        # 數字，關卡打法改成當天總量會讓整列自相矛盾。改成標註今天已經打了什麼。
        if index == 0 and result.get("overtime_today") and any(row["counts"]):
            note += "　[已過上線時段，只排補完今天任務的量]"
        if index == 0 and done_label:
            note += f"　[今天已打 {done_label}]"
        # 解鎖鏈：LP 的閘門只保證「同一天或更早」，真正的先後只能在這裡講。
        # 開場先打是當天第一件事，所以註記排在「今天已打」之後、截止之前。
        for unlock in row.get("unlocks") or ():
            who = f"「{unlock['event']}」" if len(result["events"]) > 1 else ""
            note += (f"　[{who}開場先打 {unlock['text']}"
                     f"（照體力由小到大，共 {unlock['spend']} 點）]")
        for deadline in row["deadlines"]:
            detail = "、".join(f"{levels[i]['label']}×{c}"
                               for i, c in enumerate(deadline["counts"]) if c)
            note += (f"　[{deadline['moment']:%H:%M} 前要打完 {detail}"
                     f"（{deadline['event']} 截止）]")
        if row["usage_cap"] is not None:
            note += f"　[當日上限 {row['usage_cap']}]"
        for event_name, limit in row["event_caps"]:
            note += f"　[「{event_name}」當日上限 {limit}]"
        if row["daily_floor"] is not None:
            note += f"　[當日至少 {row['daily_floor']}"
            note += (f"，{row['daily_floor_window']}]"
                     if row.get("daily_floor_window") else "]")
        if s["has_enemy_ranges"] and row["enemy_floor"]:
            note += f"　[當日至少 {row['enemy_floor']} 人]"
        if row["min_clears_override"] is not None:
            note += f"　[當日最低 {row['min_clears_override']} 關]"
        if row["min_stamina_override"] is not None:
            note += f"　[當日最低耗體 {row['min_stamina_override']}]"
        if row["use_weekly"]:
            note += f"　[限時體力 {row['use_weekly']}]"
        if row["waste_night"]:
            note += f"　[過夜浪費 {row['waste_night']}]"
        elif row["waste"]:
            note += f"　[浪費 {row['waste']}]"
        values = [format_day(row["date"]), plan, row["clears"]]
        if s["tracks_enemies"]:
            values.append(row["enemies"])
        values += [row["spend"], row["buy"], row["bedtime_balance"],
                   row["nat_balance"]]
        table_rows.append((values, note))
    lines.extend(render_table(columns, table_rows))

    return "\n".join(lines)


def format_extras(result: dict) -> str:
    """「打法歸納」與「提醒」：平常不用看，計算分頁按按鈕才另開視窗顯示。

    兩段都沒有就是空字串。
    """
    levels = result["levels"]
    lines = []
    # 把每日打法歸納成幾種固定模式，方便實際執行
    patterns = {}
    for row in result["schedule"]:
        key = tuple(row["counts"])
        patterns[key] = patterns.get(key, 0) + 1
    if len(patterns) > 1:
        lines.append("-" * 68)
        lines.append("打法歸納")
        lines.append("-" * 68)
        for key, count in sorted(patterns.items(), key=lambda kv: -kv[1]):
            plan = "、".join(f"{levels[i]['label']}×{c}"
                             for i, c in enumerate(key) if c) or "（不打）"
            lines.append(f"{count:>3} 天：{plan}")
        lines.append("")

    if result["warnings"]:
        lines.append("-" * 68)
        lines.append("提醒")
        lines.append("-" * 68)
        for w in result["warnings"]:
            lines.append(f"• {w}")

    return "\n".join(lines).strip("\n")



METRIC_UNITS = {"stamina": "體力", "clears": "關", "points": "分",
                "enemies": "人", "drops": "個", "manual": ""}
CYCLE_LABELS = {"daily": "每日", "weekly": "每週", "monthly": "每月",
                "event": "活動", "guild": "公會"}


def _task_line(task: dict) -> str:
    unit = METRIC_UNITS.get(task["metric"], "")
    head = f"[{CYCLE_LABELS.get(task['cycle'], task['cycle'])}] {task['name']}"
    if task["metric"] == "manual":
        return head + "（手動勾選）"
    if not task["windows"]:
        return head + f"　目標 {task['amount']} {unit}"
    if task["cycle"] in ("daily", "guild", "weekly", "monthly"):
        total = len(task["windows"])
        pending = [w for w in task["windows"] if not w.get("met")]
        status = (f"本排程已排滿 {total} 個週期" if not pending
                  else f"還有 {len(pending)}/{total} 個週期沒排滿")
        return head + f"　每次 {task['amount']} {unit}　{status}"
    win = task["windows"][0]
    status = "已達成" if win.get("met") else f"還差 {win['need']} {unit}"
    return (head + f"　{win['label']} 要 {task['amount']} {unit}"
            f"（已有 {win['done']}）　{status}")
