$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    python verification.py
    if ($LASTEXITCODE -ne 0) { throw 'Supplementary checks failed.' }
    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
    if ($LASTEXITCODE -ne 0) { throw 'LaTeX compilation failed.' }
}
finally {
    Pop-Location
}
