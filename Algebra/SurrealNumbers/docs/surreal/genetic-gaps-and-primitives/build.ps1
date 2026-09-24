# Rebuild the two papers and run exact finite checks. No network access needed.
[CmdletBinding()]
param()
Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    if (Get-Command py -ErrorAction SilentlyContinue) {
        $python = 'py'
        $pythonPrefix = @('-3')
    } elseif (Get-Command python -ErrorAction SilentlyContinue) {
        $python = 'python'
        $pythonPrefix = @()
    } elseif (Get-Command python3 -ErrorAction SilentlyContinue) {
        $python = 'python3'
        $pythonPrefix = @()
    } else {
        throw 'Python 3.9 or later is required.'
    }
    & $python @pythonPrefix -c 'import sys; sys.exit(int(sys.version_info < (3, 9)))'
    if ($LASTEXITCODE -ne 0) { throw 'The Python version check failed.' }
    & $python @pythonPrefix 'code/verify.py'
    if ($LASTEXITCODE -ne 0) { throw 'The exact finite verification failed.' }
    if (Get-Command latexmk -ErrorAction SilentlyContinue) {
        foreach ($file in @('article.tex', 'short_proof.tex')) {
            & latexmk -pdf -interaction=nonstopmode -halt-on-error $file
            if ($LASTEXITCODE -ne 0) { throw "LaTeX compilation failed: $file" }
        }
    } elseif (Get-Command pdflatex -ErrorAction SilentlyContinue) {
        foreach ($file in @('article.tex', 'short_proof.tex')) {
            foreach ($pass in 1..3) {
                & pdflatex -interaction=nonstopmode -halt-on-error $file
                if ($LASTEXITCODE -ne 0) { throw "LaTeX compilation failed: $file, pass $pass" }
            }
        }
    } else {
        throw 'Install a TeX distribution with pdfLaTeX to rebuild the PDFs.'
    }
    Write-Host 'Built article.pdf and short_proof.pdf; exact finite checks passed.'
} finally {
    Pop-Location
}
