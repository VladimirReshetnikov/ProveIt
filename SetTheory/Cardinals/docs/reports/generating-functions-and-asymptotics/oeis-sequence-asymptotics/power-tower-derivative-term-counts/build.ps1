$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    foreach ($pass in 1..3) {
        & pdflatex -interaction=nonstopmode -halt-on-error article.tex
        if ($LASTEXITCODE -ne 0) {
            throw "pdflatex failed on pass $pass with exit code $LASTEXITCODE"
        }
    }
}
finally {
    Pop-Location
}
