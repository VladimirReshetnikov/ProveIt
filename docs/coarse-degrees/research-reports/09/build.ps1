# Requires Python 3.9+ and pdflatex on PATH. Run from PowerShell.
$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    if (-not (Get-Command python -ErrorAction SilentlyContinue)) {
        throw 'Python 3.9 or later is required on PATH.'
    }
    if (-not (Get-Command pdflatex -ErrorAction SilentlyContinue)) {
        throw 'pdflatex is required on PATH (TeX Live or MiKTeX).'
    }
    & python checks/check_finite_lemmas.py --output checks/results.json
    if ($LASTEXITCODE -ne 0) { throw 'Finite checks failed.' }
    New-Item -ItemType Directory -Force -Path _build | Out-Null
    1..2 | ForEach-Object {
        & pdflatex -interaction=nonstopmode -halt-on-error `
            -output-directory=_build coarse_degree_attack.tex
        if ($LASTEXITCODE -ne 0) { throw 'LaTeX compilation failed.' }
    }
    Copy-Item _build/coarse_degree_attack.pdf coarse_degree_attack.pdf -Force
    Write-Host 'Built coarse_degree_attack.pdf'
}
finally {
    Pop-Location
}
