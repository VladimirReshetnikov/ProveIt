@echo off
python "%~dp0Tools\LeanRepl\leanrepl.py" %*
if not "%errorlevel%"=="0" pause
