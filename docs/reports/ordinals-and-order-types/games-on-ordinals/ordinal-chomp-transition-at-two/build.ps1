# Windows build path: verification first, then three pdfLaTeX passes.
# Ported from the ordinal-chomp-winner-stability report.  It is supplied for
# convenience and was not executed in the Linux environment in which the
# original poisoned-convention verification was recorded.
$ErrorActionPreference = 'Stop'
Set-Location $PSScriptRoot
function Invoke-Checked {
    param([string]$Command, [string[]]$CommandArguments)
    & $Command @CommandArguments
    if ($LASTEXITCODE -ne 0) {
        throw "$Command failed with exit code $LASTEXITCODE"
    }
}
Invoke-Checked -Command python -CommandArguments @('code/minimal_verifier.py')
Invoke-Checked -Command python -CommandArguments @('code/verify.py')
Invoke-Checked -Command python -CommandArguments @('code/independent_check.py')
Invoke-Checked -Command python -CommandArguments @('code/verify_poisoned_certificate.py')
Invoke-Checked -Command python -CommandArguments @('code/test_poisoned_certificate.py')
for ($i = 0; $i -lt 3; $i++) {
    Invoke-Checked -Command pdflatex -CommandArguments @('-interaction=nonstopmode', '-halt-on-error', 'ordinal_chomp_counterexample.tex')
}
