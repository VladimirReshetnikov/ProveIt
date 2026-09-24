$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest
Push-Location $PSScriptRoot
try {
    if (-not (Get-Command pdflatex -ErrorAction SilentlyContinue)) {
        throw 'pdfLaTeX was not found. Install TeX Live or MiKTeX and add it to PATH.'
    }
    foreach ($pass in 1..3) {
        Write-Host "LaTeX pass $pass"
        & pdflatex -interaction=nonstopmode -halt-on-error article.tex
        if ($LASTEXITCODE -ne 0) {
            throw "pdfLaTeX failed during pass $pass. See article.log."
        }
    }
    Write-Host 'Built article.pdf. Run python ./code/verify.py for the finite sanity checks.'
}
finally {
    Pop-Location
}
