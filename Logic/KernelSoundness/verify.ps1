# Reproduce and verify the kernel-soundness artifacts in this directory.
#
#   pwsh Logic/KernelSoundness/verify.ps1
#
# Builds each module into a scratch directory (deliberately *outside* the Lake
# workspace: these are `prelude` modules and must not join the mathlib build),
# then re-checks each .olean with `leanchecker`.
#
# Expected outcome:
#   NatAddAccelerator   builds, no axioms, leanchecker ACCEPTS  (the hole)
#   NatBeqAccelerator   builds, no axioms, leanchecker ACCEPTS  (the hole)
#   NegativeControl     builds, no axioms, leanchecker REJECTS  (control)

$ErrorActionPreference = 'Continue'
$env:LEAN_NUM_THREADS = '0'

$src = Join-Path $PSScriptRoot 'Lean'
$work = Join-Path ([System.IO.Path]::GetTempPath()) ("proveit-kernel-soundness-" + [System.Guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Force -Path $work | Out-Null
Copy-Item (Join-Path $PSScriptRoot 'lean-toolchain') $work
$env:LEAN_PATH = $work

$modules = @('NatAddAccelerator', 'NatBeqAccelerator', 'NegativeControl')
foreach ($m in $modules) {
  Copy-Item (Join-Path $src "$m.lean") $work
}

Push-Location $work
try {
  foreach ($m in $modules) {
    Write-Output ""
    Write-Output "=============== $m ==============="
    lean -o "$m.olean" "$m.lean" 2>&1 | ForEach-Object { "  [lean] $_" }
    Write-Output "  lean exit = $LASTEXITCODE"
    leanchecker --fresh $m 2>&1 | ForEach-Object { "  [leanchecker] $_" }
    if ($LASTEXITCODE -eq 0) {
      Write-Output "  leanchecker ACCEPTED $m"
    } else {
      Write-Output "  leanchecker REJECTED $m  (exit $LASTEXITCODE)"
    }
  }
} finally {
  Pop-Location
  Remove-Item -Recurse -Force $work -ErrorAction SilentlyContinue
}
