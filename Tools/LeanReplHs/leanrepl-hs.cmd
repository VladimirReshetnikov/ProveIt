@echo off
setlocal
set EXE=%~dp0dist-newstyle\build\x86_64-windows\ghc-9.12.4\lean-repl-hs-0.1.0\x\leanrepl-hs\build\leanrepl-hs\leanrepl-hs.exe
if not exist "%EXE%" (
  echo Building leanrepl-hs...
  pushd "%~dp0" && cabal build && popd
)
"%EXE%" %*
if not "%errorlevel%"=="0" pause
