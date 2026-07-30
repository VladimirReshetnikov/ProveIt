@echo off
python "%~dp0Tools\Leant\leant.py" %*
if not "%errorlevel%"=="0" pause
