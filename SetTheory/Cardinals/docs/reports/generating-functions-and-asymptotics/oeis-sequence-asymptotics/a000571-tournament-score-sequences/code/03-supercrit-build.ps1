$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    foreach ($pass in 1..3) {
        & pdflatex -interaction=nonstopmode -halt-on-error article.tex
        if ($LASTEXITCODE -ne 0) { throw "pdfLaTeX failed on pass $pass" }
    }
    Write-Output "Built $PSScriptRoot/article.pdf"
} finally {
    Pop-Location
}
