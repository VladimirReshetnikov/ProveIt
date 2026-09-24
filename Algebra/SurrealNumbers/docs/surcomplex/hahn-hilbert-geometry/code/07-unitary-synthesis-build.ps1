$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    if (-not (Get-Command pdflatex -ErrorAction SilentlyContinue)) {
        throw 'pdfLaTeX is required. Install TeX Live or MiKTeX.'
    }
    foreach ($pass in 1..3) {
        & pdflatex -interaction=nonstopmode -halt-on-error article.tex
        if ($LASTEXITCODE -ne 0) { throw "pdfLaTeX failed on pass $pass." }
    }
    Write-Host 'Built article.pdf. Run python verify.py separately for exact diagnostics.'
} finally {
    Pop-Location
}
