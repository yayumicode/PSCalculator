# PSCalculator 體力分配計算機

> **非官方粉絲工具**：玩家個人製作的《新世界狂歡》體力規劃小工具，
> 與官方及營運團隊無關，未經官方授權或認可，也不包含任何官方素材。
> 遊戲名稱與相關權利皆屬原權利人所有。本工具免費提供，不作任何商業用途。
>
> *Unofficial fan-made tool. Not affiliated with, endorsed by, or associated with NU: Carnival or its operators.*

盡量用最少的體力完成任務，另外配合活動預告和體力瓶時限，將達成每日任務以外的關卡放在星期日打。
系統需求：Windows 10 以上。
技術工具：使用 Python 搭配開源的 PuLP 與 CBC（PuLP 把目標寫成數學式，CBC 是求最佳解的求解器）。

## 快速開始

1. 安裝 Python 3.13（只要做一次）：到 [Python 官方網站](https://www.python.org/)，點上方的「Downloads」→「Windows」，在清單裡找「**Python 3.13**」開頭的版本，下載「Windows installer (64-bit)」。
   安裝畫面最下面的「**Add python.exe to PATH**」一定要勾起來，再按「Install Now」。
2. 到[最新版下載頁](https://github.com/yayumicode/PSCalculator/releases/latest)，
   在「Assets」底下點 **`PSCalculator-v版本號.zip`** 下載（不要點下面的「Source code」）。
   解壓縮到任何地方，會得到一個 `PSCalculator` 資料夾。
3. 打開 `PSCalculator` 資料夾，雙擊 **`PSCalculator.bat`**。
   第一次會跳出一個黑色視窗，顯示正在安裝計算元件（畫面是英文），等它自己跑完即可，**不要關掉**；
   這一步需要上網。程式視窗出現後，黑色視窗會自己消失，之後再開就不會再安裝。

詳細操作請看資料夾裡的操作手冊 **`PSCalculator_操作手冊.html`**（雙擊就會用瀏覽器打開），程式裡「說明 → 使用說明…」也能打開。

## 更新到新版本

目前的版本可以在程式裡的「說明 → 關於…」查看；每一版改了什麼，寫在
[發行版頁面](https://github.com/yayumicode/PSCalculator/releases)。

1. 先用程式裡的「設定 → 匯入/匯出 → 匯出…」備份一份資料，然後關掉程式。
2. 照「快速開始」第 2 步下載新版的 ZIP，解壓縮。
3. 把新的 `PSCalculator` 資料夾**裡面的檔案**全部複製到你原本的 `PSCalculator` 資料夾，
   遇到同名檔案選「取代」。

你的資料（`profiles`、`logs` 資料夾與 `shared_config.json`、`app_state.json`）不在 ZIP 裡，
覆蓋時不會被蓋掉。注意不要直接在新解壓縮的資料夾打開程式——那裡沒有你的資料，
看起來會像全部不見了。

## 致謝

活動積分的計算公式與基礎積分表，參考了[新世界狂歡活動計算機](https://linecross.github.io/nuCarnivalActivityCalculator/ActivityCalculator.html)。
感謝它幫我度過不曉得要打到哪一層的時期。

## 授權

本程式採用 PolyForm Noncommercial License 1.0.0 授權（全文見 [LICENSE](LICENSE) 檔）：
個人與非營利用途可以免費使用、修改、轉傳，**禁止任何商業用途**。
轉傳或改作時請一併附上 [LICENSE](LICENSE) 檔（含最上面那行 `Required Notice`）。
