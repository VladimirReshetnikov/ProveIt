$ErrorActionPreference = 'Stop'
if (-not (Get-Command pdflatex -ErrorAction SilentlyContinue)) {
    throw 'pdflatex was not found. Install a TeX distribution first.'
}
Push-Location $PSScriptRoot
try {
    1..2 | ForEach-Object {
        & pdflatex -interaction=nonstopmode -halt-on-error article.tex
        if ($LASTEXITCODE -ne 0) {
            throw "LaTeX failed with exit code $LASTEXITCODE. See article.log."
        }
    }
    Write-Host 'Built article.pdf'
}
finally {
    Pop-Location
}
