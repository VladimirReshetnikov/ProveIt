$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    python verify.py --out-dir data
    if ($LASTEXITCODE -ne 0) { throw 'Exact verification failed.' }
    python illustrate.py
    if ($LASTEXITCODE -ne 0) { throw 'Illustration generation failed.' }
    latexmk -pdf -interaction=nonstopmode -halt-on-error zigzag_spectral_research.tex
    if ($LASTEXITCODE -ne 0) { throw 'LaTeX compilation failed.' }
} finally {
    Pop-Location
}
