[CmdletBinding()]
param(
    [switch]$ApplyOnly
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$expectedCommit = "8fc0014f1b35f832e78d98f72dfef525aa39861f"
$repositoryRoot = (Resolve-Path (Join-Path $PSScriptRoot "../../..")).Path
$submoduleRoot = Join-Path $repositoryRoot "lib/Coq-Synthetic-Computability"
$theoriesRoot = Join-Path $submoduleRoot "theories"
$patchPath = Join-Path $PSScriptRoot "patches/coq-synthetic-computability-8fc0014-rocq-9.2-stdpp-1.13.patch"

if (-not (Test-Path -LiteralPath (Join-Path $submoduleRoot ".git"))) {
    throw "The coq-synthetic-computability submodule is not initialized. Run: git submodule update --init lib/Coq-Synthetic-Computability"
}

$actualCommit = (& git -C $submoduleRoot rev-parse HEAD).Trim()
if ($LASTEXITCODE -ne 0 -or $actualCommit -ne $expectedCommit) {
    throw "Expected coq-synthetic-computability $expectedCommit, found $actualCommit."
}

# stdpp 1.13 consistently renamed the old elem_of_list_* lemmas to
# list_elem_of_* and stopped exposing Forall2 lemmas through the
# list_relations module qualifier. Apply the repository-owned compatibility
# patch once; accept an already-patched checkout so this helper is idempotent.
$appliedPatch = $false
& git -C $submoduleRoot diff --cached --quiet --
if ($LASTEXITCODE -ne 0) {
    throw "The submodule has staged tracked changes; restore them before running this helper."
}
& git -C $submoduleRoot diff --quiet --
$isPristine = $LASTEXITCODE -eq 0

if ($isPristine) {
    & git -C $submoduleRoot apply --unidiff-zero --check -- $patchPath
    if ($LASTEXITCODE -ne 0) {
        throw "The compatibility patch does not apply to the pristine pinned submodule."
    }
    & git -C $submoduleRoot apply --unidiff-zero --whitespace=nowarn -- $patchPath
    if ($LASTEXITCODE -ne 0) {
        throw "Failed to apply $patchPath."
    }
    $appliedPatch = $true
    Write-Host "Applied the Rocq 9.2 / stdpp 1.13 compatibility patch."
} else {
    # A dirty tracked worktree is accepted only when its complete diff is this
    # patch. Reverse it temporarily, demand that no residual diff remains, and
    # then put it back before continuing.
    & git -C $submoduleRoot apply --reverse --unidiff-zero --check -- $patchPath 2>$null
    if ($LASTEXITCODE -ne 0) {
        throw "The submodule has tracked changes other than the exact compatibility patch; restore it to $expectedCommit and retry."
    }
    & git -C $submoduleRoot apply --reverse --unidiff-zero --whitespace=nowarn -- $patchPath
    if ($LASTEXITCODE -ne 0) {
        throw "Could not verify the already-applied compatibility patch."
    }
    & git -C $submoduleRoot diff --quiet --
    $hasResidualDiff = $LASTEXITCODE -ne 0
    & git -C $submoduleRoot apply --unidiff-zero --whitespace=nowarn -- $patchPath
    if ($LASTEXITCODE -ne 0) {
        throw "Could not restore the compatibility patch after verifying it."
    }
    if ($hasResidualDiff) {
        throw "The submodule contains unrelated tracked changes in addition to the compatibility patch."
    }
    # An ordinary build promises to leave the pinned checkout pristine even
    # when a preceding [-ApplyOnly] invocation supplied the exact patch.
    $appliedPatch = $true
    Write-Host "The Rocq 9.2 / stdpp 1.13 compatibility patch is already applied."
}

if ($ApplyOnly) {
    return
}

try {
    $rocq = Get-Command rocq -ErrorAction Stop
    $rocqVersion = (& $rocq.Source --version | Out-String).Trim()
    if ($rocqVersion -notmatch "version 9\.2(?:\D|$)") {
        throw "This compatibility build is tested with Rocq 9.2; found: $rocqVersion"
    }

    Push-Location $theoriesRoot
    try {
        # This is exactly upstream's default target: all tracked .v files except
        # the optional Models/ and ArithmeticHierarchy/ trees. rocq dep supplies
        # a topological order, avoiding the generated GNU Makefile's dependence
        # on POSIX utilities that are unavailable in a native Windows shell.
        $sources = & git ls-files "*.v" |
            Where-Object { $_ -notmatch "^Models/" -and $_ -notmatch "^ArithmeticHierarchy/" }
        if ($LASTEXITCODE -ne 0 -or $sources.Count -eq 0) {
            throw "Could not enumerate the upstream Rocq sources."
        }

        $dependencyOrder = & $rocq.Source dep -sort -Q . SyntheticComputability @sources
        if ($LASTEXITCODE -ne 0) {
            throw "rocq dep failed for coq-synthetic-computability."
        }
        $orderedSources = (($dependencyOrder | Out-String) -split "\s+") |
            Where-Object { $_ -like "*.v" }

        $index = 0
        foreach ($source in $orderedSources) {
            $index++
            Write-Host "[$index/$($orderedSources.Count)] $source"
            & $rocq.Source c -Q . SyntheticComputability -w -notation-overridden $source
            if ($LASTEXITCODE -ne 0) {
                throw "rocq c failed for $source."
            }
        }

        Write-Host "Built $($orderedSources.Count) coq-synthetic-computability modules."
    } finally {
        Pop-Location
    }
} finally {
    if ($appliedPatch) {
        & git -C $submoduleRoot apply --reverse --unidiff-zero --check -- $patchPath
        if ($LASTEXITCODE -ne 0) {
            throw "The compatibility patch could not be reversed after the build."
        }
        & git -C $submoduleRoot apply --reverse --unidiff-zero --whitespace=nowarn -- $patchPath
        if ($LASTEXITCODE -ne 0) {
            throw "Failed to restore the pristine pinned submodule after the build."
        }
        Write-Host "Restored the pristine pinned coq-synthetic-computability sources."
    }
}
