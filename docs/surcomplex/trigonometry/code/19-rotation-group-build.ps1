$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    & latexmk -pdf -interaction=nonstopmode -halt-on-error surreal_rotation_group.tex
    if ($LASTEXITCODE -ne 0) {
        throw "LaTeX build failed with exit code $LASTEXITCODE."
    }
}
finally {
    Pop-Location
}
