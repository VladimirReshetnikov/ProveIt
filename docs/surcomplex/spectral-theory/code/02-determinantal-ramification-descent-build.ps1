$ErrorActionPreference = 'Stop'
if (-not (Get-Command pdflatex -ErrorAction SilentlyContinue)) {
    throw 'pdflatex was not found. Install TeX Live or MiKTeX with the packages in article.tex.'
}
Push-Location $PSScriptRoot
try {
    for ($pass = 1; $pass -le 3; $pass++) {
        & pdflatex -interaction=nonstopmode -halt-on-error article.tex
        if ($LASTEXITCODE -ne 0) {
            throw "pdflatex failed on pass $pass with exit code $LASTEXITCODE."
        }
    }
    Write-Output "Built: $(Join-Path $PSScriptRoot 'article.pdf')"
}
finally {
    Pop-Location
}
