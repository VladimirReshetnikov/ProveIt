# Report172: distinct sums of square roots

This package accompanies Report172 on OEIS [A397045](https://oeis.org/A397045).
The mathematical proof is in `Report172.tex` and `Report172.pdf`. The executable
companion checks the exact canonical counting model, endpoint conventions,
and a small numerical sample of the exact-product saddle approximation.

## Contents

- `Report172.tex`, `Report172.pdf`: self-contained report and compiled PDF
- `sources/`: bibliographic references and source provenance; no source papers
- `fixtures/oeis_35_historical.json`: preserved, previously verified 35-term
  fixture, including the auxiliary value a(0)=1
- `fixtures/provenance.json`: historical computation versus fresh build coverage
- `code/companion.py`: exact Python checks, optional C++ driver, and diagnostics
- `code/enumerate_roots.cpp`: independent C++ enclosure enumerator
- `code/test_companion.py`, `code/test_build.py`: explicit-exception tests
- `generated/`: fresh output and normal/optimized test records from this build
- `BUILD-INFO.json`: toolchain and reproducibility scope
- `SHA256SUMS.json`: SHA-256 of every packaged file except the manifest itself

## Dependencies

Python 3.10 or newer and its standard library; no pip dependencies. A complete
build also needs `g++` supporting C++17 and `__uint128_t`, and pdfLaTeX with the
packages used by the TeX source. Poppler is useful for separate visual review.
The build can initialize a missing pdfLaTeX format from an already installed
TeX distribution inside its temporary directory. It does not install packages
or alter the global TeX configuration.

## Rebuild safely

From the extracted package directory:

```sh
python build.py --output /existing/directory/Report172-new.zip \
  --pdf-output /existing/directory/Report172-new.pdf
```

Choose new output names in an existing directory. Existing regular files,
directories, symlinks, and broken symlinks are rejected. ZIP and PDF destinations
must be distinct even after path normalization. Sources and archive input
symlinks are rejected. Builds use temporary working directories and compile
with shell escape disabled. A failed test, failed compilation, unresolved
reference or citation, missing glyph, or overfull box stops publication.

The builder creates every generated artifact afresh. It runs all tests both
normally and under `python -O`, then compiles until the auxiliary references
stabilize, with at least two and at most six passes. Output creation is exclusive
and no-clobber. If a requested PDF is successfully published but a later ZIP
publication fails, the new PDF can remain; pre-existing files are never replaced.
Initial imports and subprocesses suppress bytecode generation, so the build
does not create Python cache files in the source tree.

With identical source files and toolchain, builds have byte-identical PDFs and
ZIPs. ZIP member order, timestamp, permissions, and platform metadata are fixed;
ZIP entries are stored without compression. Toolchain differences, particularly
TeX versions or platform math libraries, can change bytes. The manifest checks
integrity, not authenticity or mathematical correctness.

## Fast exact verification

```sh
python code/companion.py exact --output exact-new.json
python code/companion.py cpp --n 20 --output cpp-new.json
python code/test_companion.py --output tests-new.json
python -O code/test_companion.py --output tests-optimized-new.json
python code/test_build.py --output build-tests-new.json
python -O code/test_build.py --output build-tests-optimized-new.json
```

The default fresh cumulative calculation covers n=0,...,20: 458,000 canonical
nonunit vectors and 268 generators. It uses trial-division squarefreeness,
arbitrary-precision integers, and denominator 2^96 root enclosures. A separate
direct-shell enumeration includes the unit generator and covers n=0,...,12:
14,155 vectors. C++ independently uses a squarefree sieve and denominator 2^48
enclosures to reproduce n=0,...,20. No floating-point number decides membership.
Every unresolved comparison aborts without emitting a successful result.

Strict and weak counts are tested at 0, 1, sqrt(2), 2sqrt(2), sqrt(2)+sqrt(3),
sqrt(2)+sqrt(5), 3, and 6. Equality is decided using canonical coefficient
vectors. At a nonunit atom the weak count exceeds the strict count by one;
at a positive integer they agree. The zero vector is included in the cumulative
model; a(0)=1 is an auxiliary convention. Validation uses explicit exceptions,
so optimized Python cannot silently remove it.

Tests also cover invalid bounds and argument types, low-precision ambiguity
aborts, fixture and checksum mutation, malformed C++ arguments, exclusive
writes, malicious/aliased output paths, archive symlinks, deterministic ZIP
metadata and hashes, compiler failures, reference warnings, and layout defects.
The integer-weight relaxation used in the tests proves a conservative upper
bound of 2,878,677,965 vectors at the largest admitted C++ bound without doing
the large exact enumeration. The C++ code also aborts on counter overflow.
These are regression tests for the stated cases, not a claim of exhaustive
security verification.

## Optional full historical-prefix rerun

**This is intentionally not part of the default build.** The preserved fixture
records a previous exact n=35 calculation with 788 generators and 428,363,342
visited vectors, with no ambiguous comparisons. The current default reruns
only through n=20. Values n=21,...,35 are supplied as historical verified data;
no fresh full rerun is claimed.

To request the large computation explicitly:

```sh
python code/companion.py cpp --n 35 --allow-full --output full-n35-new.json
```

The driver compiles in a temporary directory, checks the complete prefix
against the pinned fixture, and refuses n>20 without `--allow-full`. The
standalone C++ program requires an explicit maximum n and rejects n>35.
The existing fixture is never overwritten. Allow for hundreds of millions
of vector visits; execution time depends on the machine. The wrapper permits
up to one hour before aborting. No b-file values beyond the displayed OEIS
prefix are claimed to have been checked.

## Optional noncertified numerical diagnostics

```sh
python code/companion.py diagnostics --output saddle-new.json
python code/companion.py diagnostics --n 5 10 20 35 100 --output saddle-more-new.json
```

The small default sample uses n=5,10,20,35. It evaluates the positive truncated
product, solves its mean equation by numerical bisection, and prints the
saddle approximation and comparison with the historical fixture where
available. Numerical diagnostics do not enumerate vectors at n=35.

For an integer cutoff D>=1, the omitted log-product has the analytic bound

    0 < F(t)-F_D(t)
      <= 2 exp(-t sqrt(D)) (sqrt(D)/t + 1/t^2) / (1-exp(-t sqrt(D))).

It follows by replacing the omitted squarefree radicands by all integers and
integrating the decreasing exponential. Its printed floating-point evaluation
is not a rigorous enclosure. Neither binary64 rounding, the derivatives, nor
the numerical root solve is interval-certified. The output is diagnostic, not
a finite-n error certificate. No formal correction term is included or claimed.

## Scope and rights

The report proves an exact-product saddle approximation with relative error
O(x^-1/3) and an implicit inverse with bounded additive O(1) error. These are
asymptotic statements, not exact integer rounding rules or finite-index
interval certificates. The leading logarithmic law and qualitative saddle
framework have classical precedents; consult the report and references for
the precise scope. The
package contains reproducibility code, mathematical data, the report, and
bibliographic links. It does not redistribute third-party papers. The exact
fixture is pinned by SHA-256 in both the companion and fixture manifest;
changing data requires a deliberate reviewed update to the companion.
