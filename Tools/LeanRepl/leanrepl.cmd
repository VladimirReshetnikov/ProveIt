@echo off
python "%~dp0leanrepl.py" %*
if not "%errorlevel%"=="0" pause
