[CmdletBinding()]
param()
$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    if (-not (Get-Command python -ErrorAction SilentlyContinue)) {
        throw 'Python 3.10 or later must be available as python on PATH.'
    }
    if (-not (Get-Command latexmk -ErrorAction SilentlyContinue)) {
        throw 'latexmk must be available on PATH (TeX Live or MiKTeX).'
    }
    python verify.py
    if ($LASTEXITCODE -ne 0) { throw 'The main verifier failed.' }
    python minimal_check.py
    if ($LASTEXITCODE -ne 0) { throw 'The minimal verifier failed.' }
    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
    if ($LASTEXITCODE -ne 0) { throw 'LaTeX compilation failed.' }
}
finally {
    Pop-Location
}
