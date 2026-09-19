$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    if (-not (Get-Command pdflatex -ErrorAction SilentlyContinue)) {
        throw 'pdflatex was not found. Install TeX Live or MiKTeX and retry.'
    }
    foreach ($pass in 1..2) {
        & pdflatex -interaction=nonstopmode -halt-on-error Prikry_Choice_Gap.tex
        if ($LASTEXITCODE -ne 0) {
            throw "LaTeX compilation failed on pass $pass (exit code $LASTEXITCODE)."
        }
    }
}
finally {
    Pop-Location
}
