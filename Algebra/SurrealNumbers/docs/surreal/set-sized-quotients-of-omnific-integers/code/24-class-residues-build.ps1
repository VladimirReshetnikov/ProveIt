$ErrorActionPreference = 'Stop'
$Here = $PSScriptRoot
Push-Location $Here
try {
    if (-not (Get-Command pdflatex -ErrorAction SilentlyContinue)) {
        throw 'pdfLaTeX is required. Install TeX Live or MiKTeX with the packages in README.md.'
    }
    if (-not (Get-Command python -ErrorAction SilentlyContinue)) {
        throw 'Python 3.9 or later is required.'
    }
    New-Item -ItemType Directory -Path '.build' -Force | Out-Null
    foreach ($Pass in 1..3) {
        & pdflatex '-interaction=nonstopmode' '-halt-on-error' '-output-directory=.build' 'article.tex'
        if ($LASTEXITCODE -ne 0) { throw "pdfLaTeX pass $Pass failed." }
    }
    Copy-Item '.build/article.pdf' 'article.pdf' -Force
    & python 'code/verify.py'
    if ($LASTEXITCODE -ne 0) { throw 'Finite checks failed.' }
    Write-Output "Built: $(Join-Path $Here 'article.pdf')"
}
finally {
    Pop-Location
}
