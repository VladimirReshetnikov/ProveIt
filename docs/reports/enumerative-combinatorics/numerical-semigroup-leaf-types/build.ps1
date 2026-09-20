$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    New-Item -ItemType Directory -Path '.build' -Force | Out-Null
    & latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=.build article.tex
    if ($LASTEXITCODE -ne 0) {
        throw "LaTeX build failed with exit code $LASTEXITCODE."
    }
    Copy-Item '.build/article.pdf' 'article.pdf' -Force
    Write-Host 'Built article.pdf'
}
finally {
    Pop-Location
}
