[CmdletBinding()]
param()
$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest

if (-not (Get-Command pdflatex -ErrorAction SilentlyContinue)) {
    throw 'pdfLaTeX was not found. Install a TeX distribution and add its executables to PATH.'
}

Push-Location $PSScriptRoot
try {
    $name = 'Large_Cardinals_Research_Continuation'
    $null = New-Item -ItemType Directory -Path '_build' -Force
    for ($pass = 1; $pass -le 3; $pass++) {
        Write-Host "pdfLaTeX pass $pass/3"
        $output = & pdflatex '-interaction=nonstopmode' '-halt-on-error' '-file-line-error' `
            '-output-directory=_build' "$name.tex" 2>&1
        $status = $LASTEXITCODE
        $output | Out-File "_build/pass-$pass.txt" -Encoding utf8
        if ($status -ne 0) {
            Get-Content "_build/pass-$pass.txt" -Tail 60 | Write-Host
            throw "pdfLaTeX failed on pass $pass. See _build/pass-$pass.txt."
        }
    }
    Copy-Item "_build/$name.pdf" "$name.pdf" -Force
    Write-Host "Created $name.pdf"
}
finally {
    Pop-Location
}
