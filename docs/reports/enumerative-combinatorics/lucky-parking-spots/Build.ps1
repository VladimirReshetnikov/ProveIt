$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    & python code/verify.py
    if ($LASTEXITCODE -ne 0) { throw 'Exact verification failed.' }
    for ($pass = 1; $pass -le 2; $pass++) {
        & pdflatex -interaction=nonstopmode -halt-on-error article.tex
        if ($LASTEXITCODE -ne 0) { throw "LaTeX pass $pass failed." }
    }
    Write-Output 'Verification passed; article.pdf was built.'
}
finally {
    Pop-Location
}
