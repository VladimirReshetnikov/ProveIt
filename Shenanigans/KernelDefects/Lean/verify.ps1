# Reproduce and verify the kernel-soundness artifacts in this directory.
#
#   pwsh Shenanigans/KernelDefects/Lean/verify.ps1
#
# Builds each module into a scratch directory (deliberately *outside* the Lake
# workspace: these are `prelude` modules and must not join the mathlib build),
# then re-checks each .olean with `leanchecker`.
#
# Expected outcomes are asserted below.  Note that they differ per module:
# the three kernel-accelerator exhibits are accepted by `leanchecker`, the
# native-hook exhibit is NOT (it is an axiom-*tracking* hole, not a kernel hole),
# and the negative control must be rejected — that last one is what proves
# `leanchecker` is actually doing something.

$ErrorActionPreference = 'Continue'
$env:LEAN_NUM_THREADS = '0'

$src  = $PSScriptRoot
$work = Join-Path ([System.IO.Path]::GetTempPath()) ("proveit-kernel-soundness-" + [System.Guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Force -Path $work | Out-Null
Copy-Item (Join-Path $PSScriptRoot 'lean-toolchain') $work
$env:LEAN_PATH = $work

# module name -> expected `leanchecker` verdict
# module name -> subdirectory it lives in
$where = [ordered]@{
  'NatAddAccelerator'    = 'Accelerators'
  'NatBeqAccelerator'    = 'Accelerators'
  'NatGcdFreeName'       = 'Accelerators'
  'StringLitFabrication' = 'Accelerators'
  'ReduceBoolFreeName'   = 'Accelerators'
  'NegativeControl'      = 'Controls'
}

$expected = [ordered]@{
  'NatAddAccelerator'  = 'accept'   # own `Nat`, own `Nat.add`
  'NatBeqAccelerator'  = 'accept'   # own `Nat`, own `Nat.beq`
  'NatGcdFreeName'     = 'accept'   # real core `Nat`; only *defines* the free name `Nat.gcd`
  'StringLitFabrication' = 'accept' # kernel fabricates an inhabitant of `Empty` from a string literal
  'ReduceBoolFreeName' = 'reject'   # `lean` accepts it, but the native hook cannot be replayed
  'NegativeControl'    = 'reject'   # control: built with debug.skipKernelTC
}

foreach ($m in $expected.Keys) { Copy-Item (Join-Path $src (Join-Path $where[$m] "$m.lean")) $work }

$failures = 0
Push-Location $work
try {
  foreach ($m in $expected.Keys) {
    Write-Output ""
    Write-Output "=============== $m  (expect leanchecker to $($expected[$m])) ==============="
    lean -o "$m.olean" "$m.lean" 2>&1 | ForEach-Object { "  [lean] $_" }
    $leanExit = $LASTEXITCODE
    Write-Output "  lean exit = $leanExit"
    if ($leanExit -ne 0) { Write-Output "  !! UNEXPECTED: lean failed to build $m"; $failures++; continue }

    leanchecker --fresh $m 2>&1 | ForEach-Object { "  [leanchecker] $_" }
    $verdict = if ($LASTEXITCODE -eq 0) { 'accept' } else { 'reject' }
    Write-Output "  leanchecker -> $verdict"
    if ($verdict -ne $expected[$m]) {
      Write-Output "  !! UNEXPECTED: expected $($expected[$m])"
      $failures++
    }
  }
} finally {
  Pop-Location
  Remove-Item -Recurse -Force $work -ErrorAction SilentlyContinue
}

Write-Output ""
if ($failures -eq 0) { Write-Output "All $($expected.Count) modules behaved as documented." }
else { Write-Output "$failures module(s) deviated from the documented behaviour." }
