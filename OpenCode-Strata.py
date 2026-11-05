@echo off
setlocal
title OpenCode - Strata - Houdini MCP
cd /d "%~dp0"
if errorlevel 1 goto folder_missing
set "OPENCODE_EXE=%~dp0.tools\opencode.exe"
if not exist "%OPENCODE_EXE%" goto executable_missing
if exist "%~dp0opencode.json" set "OPENCODE_CONFIG=%~dp0opencode.json"
if exist "%~dp0opencode.jsonc" set "OPENCODE_CONFIG=%~dp0opencode.jsonc"

"%OPENCODE_EXE%" %*
set "OPENCODE_EXIT=%ERRORLEVEL%"
if "%OPENCODE_EXIT%"=="0" exit /b 0
echo.
echo OpenCode exited with code %OPENCODE_EXIT%.
pause
exit /b %OPENCODE_EXIT%

:folder_missing
echo Cannot open the project folder: %~dp0
pause
exit /b 1

:executable_missing
echo OpenCode executable was not found:
echo %OPENCODE_EXE%
pause
exit /b 1
