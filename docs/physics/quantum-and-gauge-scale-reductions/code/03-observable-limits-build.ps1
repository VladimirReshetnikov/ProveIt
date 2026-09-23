# Build locally with installed TeX packages; no network access is requested.
$ErrorActionPreference = 'Stop'
if (-not (Get-Command pdflatex -ErrorAction SilentlyContinue)) {
    throw 'pdfLaTeX is required. Install TeX Live or MiKTeX and the packages in README.md.'
}
Push-Location $PSScriptRoot
try {
    for ($pass = 1; $pass -le 3; $pass++) {
        & pdflatex -interaction=nonstopmode -halt-on-error article.tex
        if ($LASTEXITCODE -ne 0) {
            throw "pdfLaTeX failed on pass $pass (exit $LASTEXITCODE)."
        }
    }
    Write-Host 'Built article.pdf'
}
finally {
    Pop-Location
}
