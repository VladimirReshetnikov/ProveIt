# Asserts that every paradox exhibit behaves as its header documents.
#
#   pwsh Shenanigans/Paradoxes/verify.ps1
#
# Everything here must COMPILE: these are honest implications, and every one
# carries an audit showing it assumes nothing.  The Lean modules assert their
# own `#print axioms` output and every expected error message via `#guard_msgs`,
# so "lean exits 0" already means all of that matched.

$ErrorActionPreference = 'Continue'
$root = $PSScriptRoot
$work = Join-Path ([System.IO.Path]::GetTempPath()) ("paradoxes-" + [guid]::NewGuid().ToString('N').Substring(0, 8))
New-Item -ItemType Directory -Path (Join-Path $work 'TypeTheoryParadoxes') -Force | Out-Null

Write-Host ("Lean:  " + ((& lean --version 2>&1) | Select-Object -First 1))
Write-Host ("Rocq:  " + ((& coqc --version 2>&1) | Select-Object -First 1))
Write-Host ""

$failures = 0
$env:LEAN_PATH = $work

# --- Lean: build the library in dependency order, then check the root module --
$leanModules = @('Girard', 'CoquandPaulin', 'LargeElimination', 'Blockers')
foreach ($m in $leanModules) {
  Copy-Item (Join-Path $root "Lean/TypeTheoryParadoxes/$m.lean") (Join-Path $work 'TypeTheoryParadoxes') -Force
}
Copy-Item (Join-Path $root 'Lean/TypeTheoryParadoxes.lean') $work -Force

Push-Location $work
foreach ($m in $leanModules) {
  $out = & lean -o "TypeTheoryParadoxes/$m.olean" "TypeTheoryParadoxes/$m.lean" 2>&1 | Out-String
  $code = $LASTEXITCODE
  if ($code -eq 0) {
    Write-Host ("  OK    Lean/TypeTheoryParadoxes/{0,-22} accept (exit 0)" -f $m)
  } else {
    $failures++
    Write-Host ("  FAIL  Lean/TypeTheoryParadoxes/{0,-22} exit {1}" -f $m, $code) -ForegroundColor Red
    Write-Host (($out.Trim() -split "`n" | Select-Object -First 8) -join "`n")
  }
}
$out = & lean 'TypeTheoryParadoxes.lean' 2>&1 | Out-String
$code = $LASTEXITCODE
if ($code -eq 0) {
  Write-Host ("  OK    Lean/{0,-38} accept (exit 0)" -f 'TypeTheoryParadoxes (root)')
} else {
  $failures++
  Write-Host ("  FAIL  Lean/{0,-38} exit {1}" -f 'TypeTheoryParadoxes (root)', $code) -ForegroundColor Red
  Write-Host (($out.Trim() -split "`n" | Select-Object -First 8) -join "`n")
}
Pop-Location

# --- Rocq -------------------------------------------------------------------
$coqCases = @(
  @{ Name = 'Coq/Hurkens'; File = 'Hurkens.v';
     Needles = @('Closed under the global context') }
)
foreach ($c in $coqCases) {
  Copy-Item (Join-Path $root "Coq/$($c.File)") $work -Force
  Push-Location $work
  $out = & coqc $c.File 2>&1 | Out-String
  $code = $LASTEXITCODE
  Pop-Location
  $missing = @($c.Needles | Where-Object { $out -notmatch [regex]::Escape($_) })
  if ($code -eq 0 -and $missing.Count -eq 0) {
    Write-Host ("  OK    {0,-44} accept (exit 0)" -f $c.Name)
  } else {
    $failures++
    Write-Host ("  FAIL  {0,-44} exit {1}" -f $c.Name, $code) -ForegroundColor Red
    foreach ($m in $missing) { Write-Host ("        missing expected text: " + $m) -ForegroundColor Red }
    Write-Host (($out.Trim() -split "`n" | Select-Object -First 8) -join "`n")
  }
}

Remove-Item $work -Recurse -Force -ErrorAction SilentlyContinue

$total = $leanModules.Count + 1 + $coqCases.Count
Write-Host ""
if ($failures -eq 0) {
  Write-Host ("All {0} paradox exhibits behaved as documented." -f $total)
  exit 0
} else {
  Write-Host ("{0} of {1} exhibits did NOT behave as documented." -f $failures, $total) -ForegroundColor Red
  exit 1
}
