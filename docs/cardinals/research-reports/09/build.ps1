$ErrorActionPreference = 'Stop'
$engine = Get-Command pdflatex -ErrorAction SilentlyContinue
if (-not $engine) {
    throw 'pdfLaTeX is required. Install TeX Live or MiKTeX with the source packages.'
}
$name = 'Large_Cardinals_Research_Continuation'
Push-Location $PSScriptRoot
try {
    New-Item -ItemType Directory -Path 'build' -Force | Out-Null
    foreach ($pass in 1..3) {
        & $engine.Source '-file-line-error' '-interaction=nonstopmode' `
            '-halt-on-error' '-output-directory=build' "$name.tex"
        if ($LASTEXITCODE -ne 0) {
            throw "pdfLaTeX failed on pass $pass with exit code $LASTEXITCODE."
        }
    }
    Copy-Item -LiteralPath "build/$name.pdf" -Destination "$name.pdf" -Force
    Write-Host "Built $name.pdf"
}
finally {
    Pop-Location
}
