$ErrorActionPreference = 'Stop'
if (-not (Get-Command pdflatex -ErrorAction SilentlyContinue)) {
    throw 'pdfLaTeX was not found. Install a TeX distribution and add it to PATH.'
}
Push-Location $PSScriptRoot
try {
    1..3 | ForEach-Object {
        & pdflatex -interaction=nonstopmode -halt-on-error article.tex
        if ($LASTEXITCODE -ne 0) {
            throw "pdfLaTeX failed on pass $_. See article.log."
        }
    }
    Write-Host "Built $(Join-Path $PSScriptRoot 'article.pdf')"
}
finally {
    Pop-Location
}
