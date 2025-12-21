@echo off
REM 設定腳本所在的目錄為當前工作目錄
cd /D "%~dp0"

REM 檢查 python.exe 是否存在於指定路徑
IF NOT EXIST "C:/Python313/python.exe" (
    echo ERROR: python.exe not found at "C:/Python313/python.exe"
    echo Please check your Python installation path.
    pause
    exit /b 1
)

REM 使用 start 命令來異步啟動 python.exe
REM "Minecraft Launcher" 是窗口標題，對於 python.exe 通常不可見，但 start 命令需要它
REM /B 參數確保在當前控制台環境中啟動，並且 start 命令立即返回
echo Starting Minecraft Python 3D Launcher (main.py)...
start "Minecraft Launcher" /B "C:/Python313/python.exe" "main.py"

REM 批次檔執行到這裡會立即退出，關閉 CMD 窗口
exit /b 0