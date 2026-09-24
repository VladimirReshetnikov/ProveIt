param(
    [switch] $SkipChecks,
    [string] $Python = "python",
    [string] $Latexmk = "latexmk"
)

$ErrorActionPreference = "Stop"
Push-Location $PSScriptRoot
try {
    if (-not $SkipChecks) {
        foreach ($Script in @("counterexample.py", "verify.py", "certify_densities.py")) {
            & $Python $Script
            if ($LASTEXITCODE -ne 0) {
                throw "$Script failed with exit code $LASTEXITCODE."
            }
        }
    }
    & $Latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build article.tex
    if ($LASTEXITCODE -ne 0) {
        throw "The LaTeX build failed with exit code $LASTEXITCODE."
    }
    Copy-Item -LiteralPath "build/article.pdf" -Destination "article.pdf" -Force
    Write-Host "Created article.pdf."
}
finally {
    Pop-Location
}
