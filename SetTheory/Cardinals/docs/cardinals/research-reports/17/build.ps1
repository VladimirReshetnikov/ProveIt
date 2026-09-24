# Requires a LaTeX distribution with pdflatex on PATH.
$ErrorActionPreference = 'Stop'
if (-not (Get-Command pdflatex -ErrorAction SilentlyContinue)) {
    throw 'pdflatex is not on PATH. Install a LaTeX distribution first.'
}
Push-Location $PSScriptRoot
try {
    foreach ($pass in 1..3) {
        Write-Host "`nLaTeX pass $pass of 3"
        & pdflatex -interaction=nonstopmode -halt-on-error Thin_Sections_and_Saturation.tex
        if ($LASTEXITCODE -ne 0) {
            throw "pdflatex failed with exit code $LASTEXITCODE. See the .log file."
        }
    }
    Write-Host "`nBuilt Thin_Sections_and_Saturation.pdf"
}
finally {
    Pop-Location
}
