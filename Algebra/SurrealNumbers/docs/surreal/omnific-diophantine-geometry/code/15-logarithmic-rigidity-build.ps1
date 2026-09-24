$ErrorActionPreference = 'Stop'
if (-not (Get-Command pdflatex -ErrorAction SilentlyContinue)) {
    throw 'pdfLaTeX was not found. Install TeX Live or MiKTeX and add it to PATH.'
}
Push-Location $PSScriptRoot
try {
    foreach ($pass in 1..3) {
        Write-Host "pdfLaTeX pass $pass"
        & pdflatex -interaction=nonstopmode -halt-on-error article.tex
        if ($LASTEXITCODE -ne 0) {
            throw "pdfLaTeX failed on pass $pass. See article.log."
        }
    }
    Write-Host 'Created article.pdf'
}
finally {
    Pop-Location
}
