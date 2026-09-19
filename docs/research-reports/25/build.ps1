$ErrorActionPreference = 'Stop'
if (-not (Get-Command pdflatex -ErrorAction SilentlyContinue)) {
    throw 'pdfLaTeX was not found. Install TeX Live or MiKTeX with the packages listed in README.md.'
}
Push-Location $PSScriptRoot
try {
    foreach ($pass in 1..3) {
        & pdflatex -interaction=nonstopmode -halt-on-error Cofinal_Orbit_Consistency.tex
        if ($LASTEXITCODE -ne 0) {
            throw "pdfLaTeX failed on pass $pass. See Cofinal_Orbit_Consistency.log."
        }
    }
    Write-Output 'Built Cofinal_Orbit_Consistency.pdf'
}
finally {
    Pop-Location
}
