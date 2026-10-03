$ErrorActionPreference = "Stop"
Set-Location $PSScriptRoot
if (-not (Get-Command pdflatex -ErrorAction SilentlyContinue)) {
    throw "pdflatex is required; install TeX Live or MiKTeX."
}
New-Item -ItemType Directory -Force -Path build | Out-Null
foreach ($pass in 1..3) {
    & pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build article.tex *> "build/pass-$pass.txt"
    if ($LASTEXITCODE -ne 0) {
        Get-Content "build/pass-$pass.txt"
        throw "LaTeX compilation failed on pass $pass."
    }
}
Copy-Item build/article.pdf article.pdf -Force
Write-Output "Built article.pdf. Intermediate files are in build/."
