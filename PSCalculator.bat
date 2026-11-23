@echo off
setlocal enabledelayedexpansion
cd /d "%~dp0"
title Stamina Scheduler

REM --------------------------------------------------------------
REM  NOTE: this file is deliberately pure ASCII, and deliberately
REM  contains no CHCP command.
REM    - cmd.exe parses batch files using the system ANSI codepage
REM      (CP950 here), so non-ASCII text gets shredded.
REM    - running CHCP mid-file desyncs cmd's byte offset into the
REM      file and corrupts parsing of even plain ASCII lines.
REM  Keep it ASCII.
REM --------------------------------------------------------------

REM  Locate a working Python. Windows App Execution Aliases put a
REM  0-byte python.exe on PATH that only opens the Microsoft Store,
REM  so each candidate must actually run - existence is not enough.
set "PY="
for %%C in (
  "%LOCALAPPDATA%\Programs\Python\Python313\python.exe"
  "%LOCALAPPDATA%\Programs\Python\Launcher\py.exe"
  "py"
  "python"
) do (
  if not defined PY (
    %%C -c "import sys" >nul 2>&1
    if !errorlevel! equ 0 set "PY=%%~C"
  )
)

if not defined PY (
  echo.
  echo   Python not found.
  echo.
  echo   Install it first:  winget install Python.Python.3.13
  echo   Tick "Add python.exe to PATH" during setup.
  echo.
  pause
  exit /b 1
)

REM  pulp + the CBC solver are the engine - nothing can be computed
REM  without them. PuLP 4.x no longer bundles CBC; the [cbc] extra in
REM  requirements.txt installs it. Older PuLP 3.x installs already work.
"%PY%" -c "import sys, scheduler; sys.exit(0 if scheduler.solver_available() else 1)" >nul 2>&1
if errorlevel 1 (
  echo.
  echo   Missing package 'pulp' or the CBC solver - installing it now...
  echo.
  "%PY%" -m pip install -r requirements.txt
  if errorlevel 1 (
    echo.
    echo   Install failed. Run this manually:  pip install -r requirements.txt
    echo.
    pause
    exit /b 1
  )
)

REM  Import once first, so syntax/import errors surface with a
REM  readable message instead of vanishing into a silent launch.
"%PY%" -c "import PSCalculator" 2>"%TEMP%\pscalculator_import_error.txt"
if errorlevel 1 (
  echo.
  echo   Failed to load the program:
  echo.
  type "%TEMP%\pscalculator_import_error.txt"
  echo.
  pause
  exit /b 1
)

REM  Launch with pythonw so no console window lingers behind the GUI.
REM  Ask the interpreter itself where it lives: PY may be just "py"
REM  or "python" (any version, any install location), so a text
REM  replace on PY cannot find pythonw.exe. Falls back to the console
REM  interpreter if pythonw.exe is missing. The Python code must not
REM  contain ! or %% - delayed expansion would eat them.
set "PYW="
"%PY%" -c "import sys, os; w = os.path.join(os.path.dirname(sys.executable), 'pythonw.exe'); print(w if os.path.isfile(w) else sys.executable)" >"%TEMP%\pscalculator_pythonw.txt" 2>nul
if not errorlevel 1 set /p PYW=<"%TEMP%\pscalculator_pythonw.txt"
del "%TEMP%\pscalculator_pythonw.txt" >nul 2>&1
if not defined PYW set "PYW=%PY%"

start "" "%PYW%" PSCalculator.py
exit /b 0
