param(
    [string] $Switch = "rocq-9.2",
    [string] $Opam = "C:\Tools\opam-2.5.2\opam.exe"
)

$ErrorActionPreference = "Stop"
$compatRoot = $PSScriptRoot
$rocqElpiRevision = "36c7e0ec8fe5ab4bd87cefd9829986d9c941cffe"
$rocqElpiSource = "git+https://github.com/VladimirReshetnikov/coq-elpi.git#$rocqElpiRevision"
$mathCompRevision = "ee97c32faaf5d10532cb7e41e513e75007025db1"
$mathCompSource = "git+https://github.com/math-comp/math-comp.git#$mathCompRevision"

# Never let an older Rocq Platform redirect installation into its library tree.
Remove-Item Env:ROCQLIB -ErrorAction SilentlyContinue

function Invoke-Opam {
    & $Opam @args
    if ($LASTEXITCODE -ne 0) {
        throw "opam failed with exit code $LASTEXITCODE"
    }
}

# Rocq 9.2 renamed its implementation packages, while some released ecosystem
# metadata still asks for the historical package names.  These two empty local
# pins bridge only the names; Rocq supplies all binaries and libraries.
Invoke-Opam pin add coq-core (Join-Path $compatRoot "coq-core") --switch=$Switch --no-action -y
Invoke-Opam pin add coq-stdlib (Join-Path $compatRoot "coq-stdlib") --switch=$Switch --no-action -y

# Elpi 3.4.0 advertises Rocq 9.2 support but still refers to two APIs removed in
# 9.2.  The synchronized upstream revision contains the compatibility repair.
Invoke-Opam pin add rocq-elpi $rocqElpiSource --switch=$Switch --no-action -y

# MathComp 2.5 predates Rocq 9.2 and carries an upper version bound.  The pinned
# official revision has removed that bound and is used by all four packages so
# their versions and compiled interfaces stay synchronized.
foreach ($package in @(
    "rocq-mathcomp-boot",
    "rocq-mathcomp-order",
    "rocq-mathcomp-ssreflect",
    "coq-mathcomp-ssreflect"
)) {
    Invoke-Opam pin add $package $mathCompSource --switch=$Switch --no-action -y
}

Invoke-Opam install --switch=$Switch --jobs=2 -y `
    rocq-runtime.9.2.0 `
    rocq-core.9.2.0 `
    rocq-stdlib.9.1.0 `
    coq-core.9.2.0 `
    coq-stdlib.9.2.0

$prefix = (& $Opam var prefix --switch=$Switch).Trim()
if ($LASTEXITCODE -ne 0) {
    throw "opam var prefix failed with exit code $LASTEXITCODE"
}
$bin = Join-Path $prefix "bin"

# Dune on Windows resolves .exe files directly and otherwise falls through to
# the old Rocq Platform before it considers .cmd wrappers.  Compile one tiny
# launcher that inserts the appropriate Rocq 9.2 subcommand, then expose it
# under every historical executable name by hard link.
$opamRoot = (& $Opam var root).Trim()
if ($LASTEXITCODE -ne 0) {
    throw "opam var root failed with exit code $LASTEXITCODE"
}
$cygwinSetup = Join-Path $opamRoot ".cygwin\setup-x86_64.exe"
$cygwinRoot = Join-Path $opamRoot ".cygwin\root"
$cygwinCache = Join-Path $opamRoot ".cygwin\cache"
$cygwinBin = Join-Path $opamRoot ".cygwin\root\bin"
$cygwinPatch = Join-Path $cygwinBin "patch.exe"

# MetaRocq's generated-plugin refresh applies two bundled extraction patches.
# Opam's minimal internal Cygwin installation does not include GNU patch, and
# the upstream script historically continued after `patch` was not found,
# leaving a misleading OCaml weak-type error much later in the build.
& $cygwinSetup -q -B -R $cygwinRoot -l $cygwinCache `
    -s "https://cygwin.mirror.constant.com/" -P patch
if (-not (Test-Path -LiteralPath $cygwinPatch)) {
    throw "Cygwin patch installation did not produce $cygwinPatch"
}
& $cygwinPatch --version | Out-Null
if ($LASTEXITCODE -ne 0) {
    throw "Cygwin patch validation failed with exit code $LASTEXITCODE"
}

$compiler = Join-Path $cygwinBin "x86_64-w64-mingw32-gcc.exe"
$env:PATH = "$cygwinBin;$env:PATH"

# Several configure scripts request unprefixed compiler names.  Without these
# aliases they find an unrelated WinLibs compiler, while opam prepends its own
# MinGW runtime DLLs, producing binaries that fail at loader startup.
foreach ($compilerAlias in @(
    @("gcc.exe", "x86_64-w64-mingw32-gcc.exe"),
    @("g++.exe", "x86_64-w64-mingw32-g++.exe")
)) {
    $alias = Join-Path $cygwinBin $compilerAlias[0]
    Remove-Item -LiteralPath $alias -Force -ErrorAction SilentlyContinue
    New-Item -ItemType HardLink -Path $alias `
        -Target (Join-Path $cygwinBin $compilerAlias[1]) | Out-Null
}
$shim = Join-Path $bin "rocq-legacy-shim.exe"
Remove-Item -LiteralPath $shim -Force -ErrorAction SilentlyContinue
& $compiler -O2 (Join-Path $compatRoot "LegacyShim.c") -o $shim
if ($LASTEXITCODE -ne 0) {
    throw "compatibility launcher compilation failed with exit code $LASTEXITCODE"
}

foreach ($name in @(
    "coqc", "coqchk", "coqdep", "coq_makefile", "coqtop", "coqdoc",
    "coqpp", "coqnative", "coqwc", "coqtex"
)) {
    $entryPoint = Join-Path $bin "$name.exe"
    Remove-Item -LiteralPath $entryPoint -Force -ErrorAction SilentlyContinue
    New-Item -ItemType HardLink -Path $entryPoint -Target $shim | Out-Null
}

$env:PATH = "$bin;$cygwinBin;$env:PATH"

# Give the compatibility repository highest priority.  It applies the audited
# Coquelicot proof patch and builds that package with Rocq's generated makefile;
# its native Windows remake database is not self-readable.  The Flocq and
# Interval recipes use `./remake.exe` on win32.  Official release archives and
# checksums remain unchanged.
$localRepository = Join-Path $compatRoot "repository"
$repositories = @(& $Opam repository list --switch=$Switch --short)
if ($repositories -contains "proofs-rocq92") {
    Invoke-Opam repository set-url proofs-rocq92 $localRepository --switch=$Switch
} else {
    Invoke-Opam repository add proofs-rocq92 $localRepository --switch=$Switch
}

Invoke-Opam install --switch=$Switch --jobs=2 -y `
    coq-coquelicot.3.4.4 `
    coq-interval.4.11.4 `
    rocq-equations.1.3.2+9.2 `
    rocq-stdpp.1.13.0 `
    rocq-metarocq-template.1.5.1+9.2

$userPath = [Environment]::GetEnvironmentVariable("PATH", "User")
if (($userPath -split ";") -notcontains $bin) {
    [Environment]::SetEnvironmentVariable("PATH", "$bin;$userPath", "User")
}
