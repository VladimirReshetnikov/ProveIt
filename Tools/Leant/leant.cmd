@echo off
python "%~dp0leant.py" %*
if not "%errorlevel%"=="0" pause
