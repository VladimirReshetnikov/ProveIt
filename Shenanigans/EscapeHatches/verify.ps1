# Asserts that every escape-hatch exhibit behaves as its header documents.
#
#   pwsh Shenanigans/EscapeHatches/verify.ps1
#
# Unlike ../KernelDefects/, these files are SUPPOSED to work: each one is a
# sanctioned route to `False`, and the claim being checked is that the route is
# still open and that the audit reports what the file says it reports.
#
# Every Lean file carries its own `#guard_msgs` assertions, including the exact
# `#print axioms` output, so "lean exits 0" already means every documented
# message matched.  For Coq there is no `#guard_msgs`, so expected substrings
# are asserted here.
#
# Everything is compiled in a scratch directory outside the repository.

$ErrorActionPreference = 'Continue'
$root = $PSScriptRoot
$work = Join-Path ([System.IO.Path]::GetTempPath()) ("escape-hatches-" + [guid]::NewGuid().ToString('N').Substring(0, 8))
New-Item -ItemType Directory -Path $work -Force | Out-Null

Write-Host ("Lean:  " + ((& lean --version 2>&1) | Select-Object -First 1))
Write-Host ("Rocq:  " + ((& coqc --version 2>&1) | Select-Object -First 1))
Write-Host ""

$failures = 0

function Test-Case {
  param($Name, $Command, $Arguments, $Expect, $Needles)
  Push-Location $work
  $output = & $Command @Arguments 2>&1 | Out-String
  $code = $LASTEXITCODE
  Pop-Location

  $accepted = ($code -eq 0)
  $verdictOk = ($accepted -eq ($Expect -eq 'accept'))
  $missing = @($Needles | Where-Object { $output -notmatch [regex]::Escape($_) })

  if ($verdictOk -and $missing.Count -eq 0) {
    Write-Host ("  OK    {0,-34} {1} (exit {2})" -f $Name, $Expect, $code)
  } else {
    $script:failures++
    Write-Host ("  FAIL  {0,-34} expected {1}, exit {2}" -f $Name, $Expect, $code) -ForegroundColor Red
    foreach ($m in $missing) { Write-Host ("        missing expected text: " + $m) -ForegroundColor Red }
    Write-Host (($output.Trim() -split "`n" | Select-Object -First 8) -join "`n")
  }
}

# --- Lean -------------------------------------------------------------------
# Each file's own `#guard_msgs` blocks assert the messages; exit 0 is the verdict.
$leanAccept = @(
  'Sorry', 'Axioms', 'Unsafe', 'NativeDecide', 'Metaprogramming', 'Spoofing'
)
foreach ($m in $leanAccept) {
  Copy-Item (Join-Path $root "Lean/$m.lean") $work -Force
  Test-Case -Name "Lean/$m" -Command 'lean' -Arguments @("$m.lean") -Expect 'accept' -Needles @()
}

# The one Lean check that cannot live in a `#guard_msgs` block: a *parse* error.
Copy-Item (Join-Path $root 'Lean/Spoofing.BareCyrillic.lean') $work -Force
Test-Case -Name 'Lean/Spoofing.BareCyrillic' -Command 'lean' `
  -Arguments @('Spoofing.BareCyrillic.lean') -Expect 'reject' -Needles @('expected token')

# --- Rocq -------------------------------------------------------------------
$coqCases = @(
  @{ Name = 'Coq/Assumptions'; File = 'Assumptions.v'; Flags = @();
     Needles = @('admitted_false : False',
                 'everything_inhabited : forall A : Type, A',
                 'strictly_bigger_obligation_1') },
  @{ Name = 'Coq/TypingFlags'; File = 'TypingFlags.v'; Flags = @();
     Needles = @('loop is assumed to be guarded.',
                 'Curry is assumed to be positive.',
                 'universe_false relies on an unsafe hierarchy.',
                 'check_guarded: true') },
  @{ Name = 'Coq/RewriteRules'; File = 'RewriteRules.v'; Flags = @('-allow-rewrite-rules');
     Needles = @('raise : forall A : Type, A',
                 'Rewrite rules are allowed (subject reduction might be broken)') },
  @{ Name = 'Coq/ImpredicativeSet'; File = 'ImpredicativeSet.v'; Flags = @('-impredicative-set');
     Needles = @('Set is impredicative', 'classic : forall P : Prop, P \/ ~ P') },
  @{ Name = 'Coq/Spoofing'; File = 'Spoofing.v'; Flags = @();
     Needles = @('Closed under the global context',
                 'Relation.zero_is_one', 'Notated.looks_absurd') }
)
foreach ($c in $coqCases) {
  Copy-Item (Join-Path $root "Coq/$($c.File)") $work -Force
  Test-Case -Name $c.Name -Command 'coqc' -Arguments ($c.Flags + @($c.File)) `
    -Expect 'accept' -Needles $c.Needles
}

# Controls: the two flag-gated files must FAIL without their flag.
Test-Case -Name 'Coq/RewriteRules (no flag)' -Command 'coqc' -Arguments @('RewriteRules.v') `
  -Expect 'reject' -Needles @('requires passing the flag "-allow-rewrite-rules"')
Test-Case -Name 'Coq/ImpredicativeSet (no flag)' -Command 'coqc' -Arguments @('ImpredicativeSet.v') `
  -Expect 'reject' -Needles @('Cannot enforce Set+1 <= Set')

Remove-Item $work -Recurse -Force -ErrorAction SilentlyContinue

$total = $leanAccept.Count + 1 + $coqCases.Count + 2
Write-Host ""
if ($failures -eq 0) {
  Write-Host ("All {0} escape-hatch exhibits behaved as documented." -f $total)
  exit 0
} else {
  Write-Host ("{0} of {1} exhibits did NOT behave as documented." -f $failures, $total) -ForegroundColor Red
  exit 1
}
