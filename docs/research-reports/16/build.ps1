# Run with PowerShell from any directory. Requires TeX Live or MiKTeX.
Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    $source = 'Small_Fibres_Ultraexacting.tex'
    if (Get-Command latexmk -ErrorAction SilentlyContinue) {
        & latexmk -pdf -interaction=nonstopmode -halt-on-error $source
        if ($LASTEXITCODE -ne 0) { throw "latexmk failed with exit code $LASTEXITCODE." }
    }
    else {
        if (-not (Get-Command pdflatex -ErrorAction SilentlyContinue)) {
            throw 'pdfLaTeX was not found. Install TeX Live or MiKTeX and the packages listed in README.md.'
        }
        for ($pass = 1; $pass -le 3; $pass++) {
            & pdflatex -interaction=nonstopmode -halt-on-error $source
            if ($LASTEXITCODE -ne 0) { throw "pdfLaTeX pass $pass failed with exit code $LASTEXITCODE." }
        }
    }
}
finally {
    Pop-Location
}
