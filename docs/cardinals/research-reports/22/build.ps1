# Requires pdfLaTeX, with the packages listed in the source preamble.
$ErrorActionPreference = 'Stop'
$null = Get-Command pdflatex -ErrorAction Stop
Push-Location $PSScriptRoot
try {
    $null = New-Item -ItemType Directory -Path '_build' -Force
    for ($pass = 1; $pass -le 3; $pass++) {
        & pdflatex '-interaction=nonstopmode' '-halt-on-error' `
            '-output-directory=_build' 'Canonical_Tail_Measures.tex'
        if ($LASTEXITCODE -ne 0) {
            throw "pdfLaTeX failed on pass $pass. See _build/Canonical_Tail_Measures.log."
        }
    }
    Copy-Item '_build/Canonical_Tail_Measures.pdf' 'Canonical_Tail_Measures.pdf' -Force
    Write-Host 'Built Canonical_Tail_Measures.pdf'
}
finally {
    Pop-Location
}
