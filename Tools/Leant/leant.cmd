@echo off
setlocal
set EXE=%~dp0dist-newstyle\build\x86_64-windows\ghc-9.12.4\leant-0.1.0\x\leant\build\leant\leant.exe
if not exist "%EXE%" (
  echo Building leant...
  pushd "%~dp0" && cabal build && popd
)
"%EXE%" %*
if not "%errorlevel%"=="0" pause
