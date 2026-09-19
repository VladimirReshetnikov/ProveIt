$ErrorActionPreference = 'Stop'
Set-Location $PSScriptRoot
function Invoke-Checked {
    param([string]$Command, [string[]]$CommandArguments)
    & $Command @CommandArguments
    if ($LASTEXITCODE -ne 0) {
        throw "$Command failed with exit code $LASTEXITCODE"
    }
}
Invoke-Checked -Command python -CommandArguments @('code/make_certificate.py')
Invoke-Checked -Command python -CommandArguments @('code/verify_certificate.py')
Invoke-Checked -Command python -CommandArguments @('code/test_certificate.py')
Invoke-Checked -Command python -CommandArguments @('code/export_tables.py')
for ($i = 0; $i -lt 3; $i++) {
    Invoke-Checked -Command pdflatex -CommandArguments @('-interaction=nonstopmode', '-halt-on-error', 'ordinal_chomp_counterexample.tex')
}
