$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    for ($pass = 1; $pass -le 3; $pass++) {
        & pdflatex -interaction=nonstopmode -halt-on-error article.tex
        if ($LASTEXITCODE -ne 0) {
            throw "pdfLaTeX failed on pass $pass with exit code $LASTEXITCODE."
        }
    }
}
finally {
    Pop-Location
}
