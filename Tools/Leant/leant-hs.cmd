@echo off
setlocal
set EXE=%~dp0dist-newstyle\build\x86_64-windows\ghc-9.12.4\leant-hs-0.1.0\x\leant-hs\build\leant-hs\leant-hs.exe
if not exist "%EXE%" (
  echo Building leant-hs...
  pushd "%~dp0" && cabal build && popd
)
"%EXE%" %*
if not "%errorlevel%"=="0" pause
