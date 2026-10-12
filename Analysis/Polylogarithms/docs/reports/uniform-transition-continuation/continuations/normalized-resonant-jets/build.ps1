$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    if (-not (Get-Command pdflatex -ErrorAction SilentlyContinue)) {
        throw 'pdflatex is required and must be on PATH.'
    }
    foreach ($pass in 1..3) {
        & pdflatex '-interaction=nonstopmode' '-halt-on-error' 'resonant_polylog_transseries.tex'
        if ($LASTEXITCODE -ne 0) { throw "pdfLaTeX failed on pass $pass" }
    }
    if (Select-String -Path 'resonant_polylog_transseries.log' -Pattern 'LaTeX Warning:.*(undefined|multiply)|There were undefined references' -Quiet) {
        throw 'The PDF built, but reference warnings remain; inspect the LaTeX log.'
    }
} finally {
    Pop-Location
}
