[CmdletBinding()]
param()

$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest

$repoRoot = (Resolve-Path (Join-Path $PSScriptRoot '..\..\..')).Path
$dependencyRoot = Join-Path $repoRoot 'lib\Coq-Synthetic-Computability\theories'
$sourceRoot = Join-Path $repoRoot 'Computability\TuringDegrees\Coq'
$projectFile = Join-Path $sourceRoot '_CoqProject'

if (-not (Test-Path (Join-Path $dependencyRoot 'PostsTheorem\TuringJump.vo'))) {
  throw 'Synthetic Computability is not built. Run BuildSyntheticComputability.ps1 first.'
}

Push-Location $repoRoot
try {
  $files = @(Get-Content $projectFile |
    Where-Object { $_ -match '\.v$' } |
    ForEach-Object { $_.Trim() })
  $uniqueFiles = @($files | Sort-Object -Unique)
  if ($files.Count -ne 10 -or $uniqueFiles.Count -ne 10) {
    throw "Expected exactly ten distinct wrapper sources in $projectFile; found $($files.Count) entries and $($uniqueFiles.Count) distinct paths."
  }

  $ordered = @(((& rocq dep -sort `
      -Q 'lib/Coq-Synthetic-Computability/theories' SyntheticComputability `
      -Q 'Computability/TuringDegrees/Coq' TuringDegrees `
      @files) -split '\s+') | Where-Object { $_ -like '*.v' })
  if ($LASTEXITCODE) { throw 'rocq dep failed for the Turing-degree wrappers.' }
  # [rocq dep -sort] also prints transitive source dependencies.  They are
  # built (with the compatibility patch) by the dedicated upstream helper;
  # this focused command must compile only this project's own source list.
  $ordered = @($ordered |
    Where-Object { $_ -like 'Computability/TuringDegrees/Coq/*.v' })

  $uniqueOrdered = @($ordered | Sort-Object -Unique)
  $sourceDelta = @(Compare-Object -CaseSensitive `
    -ReferenceObject $uniqueFiles -DifferenceObject $uniqueOrdered)
  if ($ordered.Count -ne 10 -or $uniqueOrdered.Count -ne 10 -or
      $sourceDelta.Count -ne 0) {
    $details = ($sourceDelta | Out-String).Trim()
    throw "Filtered rocq dependency order did not contain exactly the ten _CoqProject wrapper sources. Difference: $details"
  }

  foreach ($file in $ordered) {
    Write-Host "[TuringDegrees] $file"
    & rocq c `
      -Q 'lib/Coq-Synthetic-Computability/theories' SyntheticComputability `
      -Q 'Computability/TuringDegrees/Coq' TuringDegrees `
      $file
    if ($LASTEXITCODE) { throw "rocq c failed: $file" }
  }
}
finally {
  Pop-Location
}
