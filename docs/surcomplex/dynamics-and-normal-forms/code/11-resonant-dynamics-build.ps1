$ErrorActionPreference = 'Stop'
Set-Location $PSScriptRoot
python verify.py
if ($LASTEXITCODE -ne 0) { throw 'Finite verification failed.' }
foreach ($pass in 1..3) {
    pdflatex -interaction=nonstopmode -halt-on-error article.tex *> "build-pass-$pass.log"
    if ($LASTEXITCODE -ne 0) { throw "LaTeX build failed on pass $pass." }
}
Write-Host 'Built article.pdf; finite-check reports are verification.json and verification.txt.'
