$ErrorActionPreference = 'Stop'
Get-Command latexmk -ErrorAction Stop | Out-Null
Push-Location $PSScriptRoot
try {
    & latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
    if ($LASTEXITCODE -ne 0) {
        throw "LaTeX build failed with exit code $LASTEXITCODE."
    }
}
finally {
    Pop-Location
}
