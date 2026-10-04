# Requires a TeX distribution providing pdflatex.
$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    1..3 | ForEach-Object {
        & pdflatex -interaction=nonstopmode -halt-on-error unknot_speedup.tex
        if ($LASTEXITCODE -ne 0) { throw 'LaTeX compilation failed.' }
    }
} finally {
    Pop-Location
}
