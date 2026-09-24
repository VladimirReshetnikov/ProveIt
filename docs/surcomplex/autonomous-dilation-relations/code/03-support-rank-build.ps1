$ErrorActionPreference = 'Stop'
$previousLocation = Get-Location
try {
    Set-Location $PSScriptRoot
    if (-not (Get-Command python -ErrorAction SilentlyContinue)) {
        throw 'Python 3.9+ must be available as python on PATH.'
    }
    if (-not (Get-Command pdflatex -ErrorAction SilentlyContinue)) {
        throw 'A TeX installation with pdflatex is required on PATH.'
    }
    & python 'code/verify.py'
    if ($LASTEXITCODE -ne 0) { throw 'Exact verification failed.' }
    1..3 | ForEach-Object {
        & pdflatex '-interaction=nonstopmode' '-halt-on-error' 'article.tex'
        if ($LASTEXITCODE -ne 0) { throw "LaTeX pass $_ failed." }
    }
    Write-Host 'Built article.pdf and data/verification_results.json.'
}
finally {
    Set-Location $previousLocation
}
