$ErrorActionPreference = 'Stop'
if (-not (Get-Command pdflatex -ErrorAction SilentlyContinue)) {
    throw 'pdfLaTeX is required; install a LaTeX distribution before building.'
}
Push-Location $PSScriptRoot
try {
    for ($pass = 1; $pass -le 3; $pass++) {
        & pdflatex '-interaction=nonstopmode' '-halt-on-error' 'article.tex'
        if ($LASTEXITCODE -ne 0) {
            throw "pdfLaTeX failed on pass $pass with exit code $LASTEXITCODE."
        }
    }
    Write-Host 'Built article.pdf. Run python verify.py separately for the exact finite checks.'
}
finally {
    Pop-Location
}
