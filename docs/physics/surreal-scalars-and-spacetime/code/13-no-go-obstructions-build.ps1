# Build the self-contained article; requires a LaTeX installation and latexmk.
$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    New-Item -ItemType Directory -Path 'build' -Force | Out-Null
    & latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build surreal_numbers_black_holes.tex
    if ($LASTEXITCODE -ne 0) {
        throw "LaTeX build failed with exit code $LASTEXITCODE."
    }
    Copy-Item 'build/surreal_numbers_black_holes.pdf' 'surreal_numbers_black_holes.pdf' -Force
    Write-Host 'Built surreal_numbers_black_holes.pdf'
}
finally {
    Pop-Location
}
