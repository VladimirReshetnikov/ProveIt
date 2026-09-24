$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    & python verify.py
    if ($LASTEXITCODE -ne 0) { throw "Finite checks failed ($LASTEXITCODE)." }
    foreach ($pass in 1..3) {
        & pdflatex -interaction=nonstopmode -halt-on-error article.tex
        if ($LASTEXITCODE -ne 0) { throw "pdfLaTeX pass $pass failed ($LASTEXITCODE)." }
    }
}
finally {
    Pop-Location
}
