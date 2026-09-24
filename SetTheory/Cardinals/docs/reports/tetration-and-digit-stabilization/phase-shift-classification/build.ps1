$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    if (-not (Get-Command pdflatex -ErrorAction SilentlyContinue)) {
        throw 'pdflatex is not on PATH.'
    }
    foreach ($pass in 1..2) {
        & pdflatex -interaction=nonstopmode -halt-on-error tetration_phase_classification.tex
        if ($LASTEXITCODE -ne 0) { throw "PDF build failed on pass $pass." }
    }
}
finally {
    Pop-Location
}
