# Report274: reproducible companion and build

This distribution contains the article, its source, a bounded exact-arithmetic
companion, and offline regression/build tools. See `article.pdf` for the
mathematical statements and `SOURCES.md` for bibliographic provenance. The
companion's finite checks are diagnostics and regression tests; they do not
replace the article's proofs or certify an asymptotic threshold.

## Requirements

- Linux with POSIX directory descriptors, `O_NOFOLLOW`, and `/proc/self/fd`
- Python 3.11 or newer; only the standard library is used
- An already installed TeX toolchain at `/usr/bin/pdftex` and
  `/usr/bin/pdflatex`, with the packages used by `article.tex`

No installation, dependency download, network request, or shell escape is
performed by the build. The reference environment uses Python 3.12.14 and
pdfTeX 1.40.26 (TeX Live 2025/dev/Debian). Byte-for-byte PDF reproduction assumes
matching TeX engines, formats, packages, fonts, and compression libraries.
Archive byte identity additionally assumes the same Python/DEFLATE toolchain.
The mathematics does not depend on PDF or ZIP byte identity.

## Run the exact checks

From the directory containing `build.py`:

```sh
python3 -I -B -X int_max_str_digits=640 tests/test_companion.py
python3 -I -B -X int_max_str_digits=640 companion/exact_checks.py
python3 -I -B -X int_max_str_digits=640 -O tests/test_companion.py
python3 -I -B -X int_max_str_digits=640 -O companion/exact_checks.py
python3 -I -B -X int_max_str_digits=640 tests/test_build.py
python3 -I -B -X int_max_str_digits=640 -O tests/test_build.py
```

`-I` isolates Python from user-site modules, inherited Python settings, and
ambient import paths. `-B` suppresses bytecode writes. The explicit `-X` option
sets the child process's integer-to/from-decimal digit limit to 640, including
under `-I`, which ignores the corresponding environment variable. The code does
not disable that protection or alter the caller's global integer digit limit.
The companion uses integers and exact fractions, with no floating-point or
shared decimal context.

The full build runs these three programs normally and with `-O`, and requires
identical stdout for each normal/optimized pair. Unit-test progress and elapsed
time are written to stderr and retained in logs, but are not compared as
reproducible mathematical output. All substantive checks use explicit exceptions
or unittest methods; they remain active when Python removes `assert` statements.

The companion defaults are maximum word length 12, boundary order 10, graph
order 8, allocation size 6, and standardization length 12. Public input ceilings
are length 12, boundary order 10, graph order 9, allocation size 8, and structural
size 256. Exact activities must be positive, at most 16, and have numerator and
denominator of at most 128 bits. Decimal CLI tokens must contain only ASCII
digits, occupy at most 640 characters, and fit the parameter-specific range;
magnitude is checked before integer conversion. Public integer parameters reject
booleans, floats, strings, negative values, and values above their individual caps.
Allocation size alone permits zero. These are deliberately finite diagnostics.

### Default-run coverage

The deterministic JSON report records the actual bounds and counts. With the
default parameters, the checked finite instances are:

- Boundary polynomial identities for orders 1 through 10; length/genus and
  renewal identities for lengths 1 through 12; complete genus coefficients
  through genus 14
- 30 general-activity transform identities using three exact rational activity
  triples
- 7,056 eligibility allocations and 1,470 optimum-budget checks
- 502 cyclic graphs, including 476 looped graphs, and 4,330 independent sets
- 41,878 dense-block images for block parameters 2 and 3, checking structural
  properties only; this does not verify the full dense-block probability theorem
- 11,358 early-mark instances, including 872 overwritten marks; 9,123 retained
  relations and 7,768 selected relations
- 54 forbidden-block marginal checks and three four-block independence checks
- 13 companion regression tests and 33 builder regression tests, each run
  normally and under `-O`

These finite coverage counts are reproducibility records, not asymptotic
certificates. In particular, observed examples and structural checks do not
supply uniform probabilistic estimates or a numerical onset guarantee.

Graph/container cases with degrees below four are structural diagnostics only;
the theorem uses its entropy estimate for degrees at least four. Likewise,
the dense-image tests with parameters two and three exercise the finite
construction, not the asymptotic choice of a large fixed parameter.

## Verify and reproduce

```sh
python3 -I -B -X int_max_str_digits=640 build.py verify
python3 -I -B -X int_max_str_digits=640 build.py reproduce \
  --output /tmp/report274-build-1
```

Choose a new, absolute output directory outside the source directory. The builder
creates it if absent; an existing directory must be empty. It refuses relative
paths, traversal components, symlink ancestors, the source tree or its ancestors,
system-directory destinations, and existing output files. It never overwrites a
previous build. For a second reproduction, choose another fresh directory.

There are two exact permitted source layouts:

1. An authoring tree with the seven source files listed below. `verify` checks
   this exact bounded inventory; no previously published content hash is implied
2. An extracted distribution with those seven files, `article.pdf`, and
   `MANIFEST.sha256`. `verify` also checks every manifest digest. `reproduce`
   additionally requires the rebuilt PDF hash to equal the distributed PDF hash

The seven source files are:

```text
README.md
SOURCES.md
article.tex
build.py
companion/exact_checks.py
tests/test_build.py
tests/test_companion.py
```

Unexpected files, empty extra directories, bytecode caches, and generated files
inside the source tree are rejected. Do not place a ZIP or its detached pin in
the extracted `Report274` directory.

A successful reproduction writes these deliverables outside the source tree:

- `article.pdf`
- `MANIFEST.sha256`
- `report274_stressed_amplitude.zip`
- `report274_stressed_amplitude.zip.sha256`
- `reproduction_receipt.json`

The output also retains normal/optimized test and companion logs, a copied
`check-work` source snapshot, and the private `tex-work` directory and TeX logs.
They are not archive members. The receipt records the actual PDF, manifest, and
ZIP digests, Python version, digit limit, stdout equality, and source-preservation
result. A failed build leaves its partial output for inspection; use a fresh
output directory when retrying.

TeX builds a local format, then runs two PDF passes, with shell escape disabled,
restricted TeX input/output options, and automatic font/format generators
disabled. The final log must contain no overfull boxes, unresolved references,
undefined citations, multiply defined labels, or pending cross-reference rerun.

## Archive and pins

The ZIP contains exactly nine regular files under `Report274/`: the seven source
files above, `article.pdf`, and `MANIFEST.sha256`. Members are sorted, use a fixed
2026-10-06 00:00:00 timestamp, Unix regular-file mode 0644, DEFLATE level 9, and no
encryption, extra fields, comments, directory entries, or private build logs.
The builder reopens the ZIP, verifies metadata, CRCs, member names, and every
member's bytes, and only then writes the detached actual ZIP pin.

`MANIFEST.sha256` hashes the eight public files other than itself. The detached
`report274_stressed_amplitude.zip.sha256` hashes the completed archive. The ZIP
pin is deliberately outside the ZIP to avoid a self-referential hash. A hash
verifies byte consistency; authenticity requires a trusted, independently
obtained copy of the pin.

From the build-output directory, check the actual archive pin with:

```sh
sha256sum -c report274_stressed_amplitude.zip.sha256
```

To repackage a verified extracted distribution without running TeX:

```sh
python3 -I -B -X int_max_str_digits=640 build.py package \
  --output /tmp/report274-package-1
```

`package` requires the manifest-pinned distribution layout. It preserves and
repackages the existing PDF; it does not claim that TeX or the companion checks
were rerun. Its output is the ZIP and detached ZIP pin.

## Safety and resource boundaries

Python-side reads traverse no-follow directory descriptors and check ordinary
single-link files before and after reading. A file's identity, size, timestamps,
and link count must remain stable. Source snapshots are bounded to 64 entries,
12 MiB per file, and 32 MiB overall, and must match the exact source/distribution
allowlist. All Python-side destination writes use descriptor-relative exclusive
creation; existing regular files, symlinks, dangling links, and hard-link aliases
are refused. Output reads reject aliases and nonregular files as well.

Tests and companion checks run from a byte snapshot copied into the external
build directory. Final inventory comparisons detect source-content changes.
Output-parent rename regressions verify that an already opened directory handle
continues to refer to the original directory; pre-open symlink swaps are
rejected. Subprocess working directories use a pinned descriptor through
`/proc/self/fd`. Unsupported platforms fail closed rather than substituting a
path-based fallback.

The subprocess environment is constructed from a small allowlist, with a fixed
PATH and deterministic time/locale settings. Isolated Python ignores the
environment hash seed; reproducible output uses explicit sorting and stable
serialization instead. The integer-digit cap is set explicitly with `-X`. The
environment does not inherit `PYTHONPATH`, `PYTHONHOME`, loader overrides, or TeX search-path
variables. Each child has a 900-second timeout and a streaming 4 MiB combined
stdout/stderr limit. Timeout and output-limit arguments reject booleans,
fractional values, strings, nonpositive values, and values above their caps.
Failure terminates the child process group. Standard input is closed.

These are integrity and bounded-execution safeguards for trusted source and an
installed toolchain, not an operating-system sandbox. Python test scripts and
the TeX engine still execute with the caller's privileges. TeX's own file access
and output creation are explicitly outside the Python no-follow/race-safety
boundary. The flags reduce accidental or unwanted operations; they do not make
untrusted TeX safe. Concurrent hostile same-user processes, compromised tools,
malicious Python source, mounts, and kernel-level attacks are outside the claim.
Use an independently isolated environment before building untrusted material.
