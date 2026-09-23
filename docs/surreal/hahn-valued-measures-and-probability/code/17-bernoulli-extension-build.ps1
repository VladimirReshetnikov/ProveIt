# Build the article and run its finite verification suite.
$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    $python = Get-Command python -ErrorAction SilentlyContinue
    if (-not $python) { $python = Get-Command python3 -ErrorAction Stop }
    $latex = Get-Command pdflatex -ErrorAction Stop
    & $python.Source 'code/verify.py'
    if ($LASTEXITCODE -ne 0) { throw 'The finite verification suite failed.' }
    foreach ($pass in 1..3) {
        & $latex.Source '-interaction=nonstopmode' '-halt-on-error' 'article.tex'
        if ($LASTEXITCODE -ne 0) { throw "LaTeX pass $pass failed." }
    }
    Write-Host 'Built article.pdf. The Python checks cover finite identities only.'
}
finally {
    Pop-Location
}
