# Compile the standalone report with pdfLaTeX. Works in Windows PowerShell 5.1+
# and PowerShell 7+. Requires pdflatex on PATH.
[CmdletBinding()]
param()
Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
if (-not (Get-Command pdflatex -ErrorAction SilentlyContinue)) {
    throw 'pdflatex is not on PATH. Install/configure TeX Live or MiKTeX.'
}
Push-Location $PSScriptRoot
try {
    $name = 'Large_Cardinals_Quotient_Continuation'
    New-Item -ItemType Directory -Path '.build' -Force | Out-Null
    foreach ($pass in 1..4) {
        Write-Host "Compiling pass $pass of 4..."
        & pdflatex '-interaction=nonstopmode' '-halt-on-error' '-file-line-error' `
            '-output-directory=.build' "$name.tex"
        if ($LASTEXITCODE -ne 0) {
            throw "pdfLaTeX failed on pass $pass. See .build/$name.log."
        }
    }
    Copy-Item ".build/$name.pdf" "$name.pdf" -Force
    $outputPdf = Join-Path $PSScriptRoot "$name.pdf"
    Write-Host "Created $outputPdf"
}
finally {
    Pop-Location
}
