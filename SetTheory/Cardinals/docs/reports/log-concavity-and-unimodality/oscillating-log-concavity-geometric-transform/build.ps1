[CmdletBinding()]
param(
    [string] $Python = 'python',
    [string] $TexEngine = 'pdflatex'
)
$ErrorActionPreference = 'Stop'
Get-Command $Python -ErrorAction Stop | Out-Null
Get-Command $TexEngine -ErrorAction Stop | Out-Null
Push-Location $PSScriptRoot
try {
    & $Python verify.py 2>&1 | Tee-Object -FilePath verification-output.txt
    if ($LASTEXITCODE -ne 0) { throw "Exact verification failed (exit $LASTEXITCODE)." }
    foreach ($Pass in 1..2) {
        & $TexEngine -interaction=nonstopmode -halt-on-error article.tex
        if ($LASTEXITCODE -ne 0) { throw "LaTeX pass $Pass failed (exit $LASTEXITCODE)." }
    }
    Write-Host 'Verification passed; article.pdf rebuilt.'
}
finally {
    Pop-Location
}
