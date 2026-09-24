$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    & python code/minimal_certificate.py
    if ($LASTEXITCODE -ne 0) { throw 'Minimal certificate failed.' }
    & python code/verify.py
    if ($LASTEXITCODE -ne 0) { throw 'Verification failed.' }
    for ($i = 1; $i -le 3; $i++) {
        & pdflatex -interaction=nonstopmode -halt-on-error delayed_digit_stabilization.tex
        if ($LASTEXITCODE -ne 0) { throw "LaTeX pass $i failed." }
    }
    Write-Host 'Built delayed_digit_stabilization.pdf'
} finally {
    Pop-Location
}
