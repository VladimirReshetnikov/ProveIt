$ErrorActionPreference = 'Stop'
Set-Location $PSScriptRoot
& python verify.py --output verification.json
if ($LASTEXITCODE -ne 0) { throw 'Finite verification failed.' }
if (Get-Command latexmk -ErrorAction SilentlyContinue) {
    & latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
    if ($LASTEXITCODE -ne 0) { throw 'LaTeX build failed.' }
} else {
    for ($i = 0; $i -lt 3; $i++) {
        & pdflatex -interaction=nonstopmode -halt-on-error article.tex
        if ($LASTEXITCODE -ne 0) { throw "LaTeX build failed on pass $($i + 1)." }
    }
}
