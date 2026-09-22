# Reproduce finite checks and build the PDF. Does not change execution policy.
[CmdletBinding()]
param()
$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    if (Get-Command py -ErrorAction SilentlyContinue) {
        & py -3 code/verify.py
    } elseif (Get-Command python -ErrorAction SilentlyContinue) {
        & python code/verify.py
    } elseif (Get-Command python3 -ErrorAction SilentlyContinue) {
        & python3 code/verify.py
    } else {
        throw 'Python 3.9 or later is required.'
    }
    if ($LASTEXITCODE -ne 0) { throw 'The verification program failed.' }

    if (Get-Command latexmk -ErrorAction SilentlyContinue) {
        & latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
        if ($LASTEXITCODE -ne 0) { throw 'The LaTeX build failed.' }
    } elseif (Get-Command pdflatex -ErrorAction SilentlyContinue) {
        for ($pass = 1; $pass -le 3; $pass++) {
            & pdflatex -interaction=nonstopmode -halt-on-error article.tex
            if ($LASTEXITCODE -ne 0) { throw "pdfLaTeX pass $pass failed." }
        }
    } else {
        throw 'A TeX installation with latexmk or pdflatex is required.'
    }
} finally {
    Pop-Location
}
