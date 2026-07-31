# Asserts that every Coq exhibit in this directory behaves as its header
# documents on the installed toolchain.
#
#   pwsh Shenanigans/Coq/verify.ps1
#
# Paradoxes must COMPILE (they are honest implications, axiom-free).
# Defect witnesses must be REJECTED -- each one is a proof of False on
# an affected toolchain, so acceptance here means a regression.

$ErrorActionPreference = 'Stop'
$root = $PSScriptRoot
$work = Join-Path ([System.IO.Path]::GetTempPath()) ("coq-shenanigans-" + [guid]::NewGuid().ToString('N').Substring(0,8))
New-Item -ItemType Directory -Path $work -Force | Out-Null

$version = (& coqc --version 2>&1 | Select-Object -First 1)
Write-Host "Toolchain: $version"
Write-Host ""

# name; relative path; expected 'accept' or 'reject'; substring required in output
$cases = @(
  @{ Name = 'Paradoxes/Hurkens';                 Path = 'Paradoxes/Hurkens.v';                 Expect = 'accept'; Needle = 'Closed under the global context' },
  @{ Name = 'GuardChecker/HigherOrderFixpoint';  Path = 'GuardChecker/HigherOrderFixpoint.v';  Expect = 'reject'; Needle = 'Recursive definition of russell is ill-formed' },
  @{ Name = 'GuardChecker/NestedMutualCrossCall';Path = 'GuardChecker/NestedMutualCrossCall.v';Expect = 'reject'; Needle = 'Recursive definition of F is ill-formed' },
  @{ Name = 'GuardChecker/UniformArgsLet';       Path = 'GuardChecker/UniformArgsLet.v';       Expect = 'reject'; Needle = 'Recursive definition of F_let is ill-formed' },
  @{ Name = 'ModuleSystem/AliasChainDeltaResolver'; Path = 'ModuleSystem/AliasChainDeltaResolver.v'; Expect = 'reject'; Needle = 'Unable to unify' }
)

$failures = 0
foreach ($c in $cases) {
  $src = Join-Path $root $c.Path
  $dst = Join-Path $work ([System.IO.Path]::GetFileName($c.Path))
  Copy-Item $src $dst -Force

  Push-Location $work
  $output = & coqc ([System.IO.Path]::GetFileName($c.Path)) 2>&1 | Out-String
  $code = $LASTEXITCODE
  Pop-Location

  $accepted = ($code -eq 0)
  $wantAccept = ($c.Expect -eq 'accept')
  $verdictOk = ($accepted -eq $wantAccept)
  $needleOk = $output -match [regex]::Escape($c.Needle)

  if ($verdictOk -and $needleOk) {
    Write-Host ("  OK    {0,-38} {1} (exit {2})" -f $c.Name, $c.Expect, $code)
  } else {
    $failures++
    Write-Host ("  FAIL  {0,-38} expected {1}, exit {2}" -f $c.Name, $c.Expect, $code) -ForegroundColor Red
    if (-not $needleOk) { Write-Host ("        missing expected text: " + $c.Needle) -ForegroundColor Red }
    Write-Host ($output.Trim() -split "`n" | Select-Object -First 6 | Out-String)
  }
}

Remove-Item $work -Recurse -Force -ErrorAction SilentlyContinue

Write-Host ""
if ($failures -eq 0) {
  Write-Host ("All {0} Coq exhibits behaved as documented." -f $cases.Count)
  exit 0
} else {
  Write-Host ("{0} of {1} exhibits did NOT behave as documented." -f $failures, $cases.Count) -ForegroundColor Red
  exit 1
}
