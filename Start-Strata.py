@echo off
setlocal
title Strata Original IQ3_S for OpenCode
set "STRATA_PROJECT_DIR=%~dp0Strata-main\Strata-git"
powershell -NoProfile -Command "try { $r = Invoke-RestMethod 'http://127.0.0.1:8080/health' -TimeoutSec 2; if ($r.service -eq 'strata') { $listener = Get-NetTCPConnection -LocalPort 8080 -State Listen -ErrorAction Stop; $proc = Get-CimInstance Win32_Process -Filter ('ProcessId=' + $listener[0].OwningProcess); if ($r.model -eq 'qwen3.8-flash-next-iq3_s' -and $r.max_context -eq 262144 -and $r.loaded -and $proc.CommandLine.Contains($env:STRATA_PROJECT_DIR)) { exit 0 }; Write-Host ('A different Strata instance is running: ' + $r.model + ', context ' + $r.max_context); exit 2 } } catch {}; exit 1"
if errorlevel 2 (
  echo Close the running Strata server, then start this file again.
  pause
  exit /b 2
)
if not errorlevel 1 (
  echo Strata is already running at http://127.0.0.1:8080
  pause
  exit /b 0
)
cd /d "%STRATA_PROJECT_DIR%"
if errorlevel 1 exit /b 1
".venv\Scripts\python.exe" -u "%CD%\serve\server.py" --engine strata --config "%CD%\strata-iq3_s.json" --host 127.0.0.1 --port 8080
if errorlevel 1 pause
