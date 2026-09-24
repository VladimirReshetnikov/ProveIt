$ErrorActionPreference = 'Stop'
if (-not (Get-Command latexmk -ErrorAction SilentlyContinue)) {
    throw 'latexmk is required. Install it with your TeX distribution.'
}
Push-Location $PSScriptRoot
try {
    & latexmk -pdf -interaction=nonstopmode -halt-on-error omnific_integers.tex
    if ($LASTEXITCODE -ne 0) {
        throw "LaTeX compilation failed with exit code $LASTEXITCODE."
    }
}
finally {
    Pop-Location
}
