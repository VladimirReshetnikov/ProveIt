$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    if (Get-Command latexmk -ErrorAction SilentlyContinue) {
        & latexmk -pdf -interaction=nonstopmode -halt-on-error omnific_fractions.tex
        if ($LASTEXITCODE -ne 0) { throw "latexmk failed with exit code $LASTEXITCODE" }
    } elseif (Get-Command pdflatex -ErrorAction SilentlyContinue) {
        1..3 | ForEach-Object {
            & pdflatex -interaction=nonstopmode -halt-on-error omnific_fractions.tex
            if ($LASTEXITCODE -ne 0) { throw "pdflatex failed with exit code $LASTEXITCODE" }
        }
    } else {
        throw 'Install TeX Live or MiKTeX with pdflatex and the packages listed in README.md.'
    }
} finally {
    Pop-Location
}
