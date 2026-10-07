REPORT 197: DISTINCT POSITIVE MULTIPLICITY VALUES IN INTEGER PARTITIONS
Reproducibility package for OEIS A373271, 4 October 2026

Definition and scope
--------------------
For an integer partition lambda, M_j is the number of copies of the part size
j, and D(lambda) is the number of DIFFERENT POSITIVE VALUES among the M_j.
Then a_n=sum_{lambda partition of n} D(lambda), with a_0=0 and p_0=1.
For example, the partition 5+5+3+3+3+1 has positive multiplicities 2,3,1 and
D=3; the partition 4+4+2+2 has positive multiplicities 2,2 and D=1. This is
neither the number of occupied sizes nor a count of partitions satisfying a
restriction on multiplicities.

Report197.tex contains the proof of the displayed three-term mean expansion,
the resulting total-count expansion, and its shrinking-width two-ceiling
inverse envelope. Exact finite computations check definitions, coefficient
algebra, and reproducibility; they do not replace the analytic proof. No
central limit theorem, proved variance asymptotic, all-fixed-orders theorem,
effective onset/error constant, exact single-ceiling inverse, or exhaustive
worldwide novelty claim is made by this package.

Requirements and commands
-------------------------
Python 3.9+ with only its standard library suffices for counting, symbolic
checks, and unit guards. Building a PDF additionally needs an installed
pdfLaTeX stack, kpsewhich, and the packages/fonts used by Report197.tex.
No network connection, third-party Python package, or downloaded executable
is needed. From the package directory, run:

  python3 -I -S -B symbolic_checks.py
  python3 -I -S -B verify.py
  python3 -I -S -B -O verify.py
  python3 -I -S -B guard_tests.py --unit-only
  python3 -I -S -B build.py --check
  python3 -I -S -B build.py /absolute/path/to/new-output
  python3 -I -S -B guard_tests.py
  python3 -I -S -B -O guard_tests.py

All verification and build commands recompute every n=0,...,2000 term by
default. There is no reduced-count build mode. They also perform the positive
forbidden-multiplicity DP through 400, Ferrers-gap enumeration through 45,
Euler's independent partition recurrence through 2000, and exact Fraction
checks. Execution time depends on hardware; the independent checks are
intentionally substantial. There are no run-time or timestamp fields in the
mathematical verification receipts.

verify.py accepts --output NEW_FILE and --terms-output NEW_FILE to save its
JSON receipt and all 2,001 exact rows. These two paths must be distinct and
outside the source package. guard_tests.py accepts --output NEW_FILE. The
parent of every output must already exist and have no symlink ancestor.
Outputs must be absent, including dangling links. Never put extra files,
working notes, caches, or receipts in the source package: its inventory is
closed and extra entries make validation fail.

Counting algorithms
-------------------
Let P(q)=product_{j>=1}(1-q^j)^(-1), and define
  Q_m(q)=product_{j>=1}(1-q^(mj)+q^((m+1)j)).
Then the exact generating function is
  sum_{n>=0} a_n q^n = P(q) sum_{m>=1}(1-Q_m(q)).
The mth complement starts in degree m. To compute through n=N, it therefore
suffices to use 1<=m<=N and 1<=j<=floor(N/m). verify.py multiplies these
Q-polynomials by descending in-place coefficient updates, sums complements,
and performs one convolution with P. Intermediate Q coefficients can be
negative, but final counts are nonnegative. All operations use arbitrary-
precision Python integers; no fixed-width overflow or floating-point fit is
involved.

The independent positive DP directly forms, separately for each m,
  P_m(q)=product_j ((1-q^j)^(-1)-q^(mj)),
which counts partitions having no part size with multiplicity m. At each
part size it first allows all multiplicities and then subtracts the old-row
contribution having exactly m copies. Every resulting coefficient remains
nonnegative and is checked to be so. Summing p(n)-[q^n]P_m gives a_n. This
check does not construct Q_m or use the final convolution of the first
algorithm. It checks all 401 terms through n=400.

The Ferrers-gap check enumerates descending partitions through n=45. It
counts distinct positive adjacent gaps, including the final part minus zero.
Conjugation turns those gaps into the positive multiplicity values of the
conjugate partition. This tests the same total using a different combinatorial
representation. Its count of all enumerated partitions is checked separately
against p(n). Euler's pentagonal recurrence verifies all 2,001 product-DP
partition numbers independently.

symbolic_checks.py uses exact Fraction arithmetic for finite coefficient
identities: the matched radial constant and square-root correction, the S2
cancellation, the Gaussian saddle correction, and the forward/logarithmic
normalizations and inverse coefficients. It checks algebraic consequences of
the proved expansions, not asymptotic remainders by numerical tolerance.

Pinned data and provenance
--------------------------
data/exact_A373271.txt has exactly 2,001 rows with columns n, a_n, p_n and no
header. Its SHA-256 is:
  0654b0fea149748897d72efd56bda9f5f65ef448e3a30776ee947f86e4c80e56
This is a locally computed exact reference, not a downloaded OEIS b-file.
All rows are regenerated from the combinatorial definition by verify.py.
The first 45 positive-index values were compared with the displayed terms at
https://oeis.org/A373271 during source review on 4 October 2026, and that
finite displayed-term comparison is preserved explicitly in the verifier.
No comparison with the linked OEIS b-file is claimed.

The sequence is attributed to the OEIS Foundation and the contributors
credited at https://oeis.org/A373271. For OEIS data terms see
https://oeis.org/wiki/The_OEIS_End-User_License_Agreement and
https://creativecommons.org/licenses/by-sa/4.0/ . The report provides the
bibliographic context and limits of its source review. The verification code
was prepared for this report. The general isolated-build, manifest, guard,
and deterministic-ZIP structure follows the preceding reproducibility
package; no theorem or sequence-specific counting code for that different
statistic is reused.

Manifests and deterministic builds
---------------------------------
SOURCE_MANIFEST.json hashes all seven source files, including the exact data,
and explicitly excludes itself. The complete package's MANIFEST.json hashes
every source, SOURCE_MANIFEST.json, the PDF, computed exact terms, and all
verification/build/guard receipts, excluding only itself. The ZIP contains
that complete package, including both manifests; it cannot contain itself.
The outer ARTIFACTS.json hashes every delivered file, the ZIP, and every file
in package/, including both manifests; it explicitly excludes itself.
Manifests are integrity records, not signatures or proofs of authenticity.
Someone able to replace both content and its manifest can replace the hashes.

For authors only, after all seven source files are final and with no existing
source manifest or other files present:
  python3 -I -S -B build.py --freeze-source
This creates SOURCE_MANIFEST.json exclusively. Ordinary builds require it,
check all file/directory names and sizes, verify hashes, recheck the actual
in-memory bytes, and copy the verified bytes to isolated staging storage.
Only the staged verified code is executed. A source-only package or a complete
built package can be used as input; partial built packages are refused.

The build destination must be new and disjoint from the source. Source or
destination symlinks, symlink ancestors, path traversal, special files,
existing outputs, unlisted files/directories, and malformed or mismatched
manifests are refused. No source or existing output is overwritten. The
builder checks that the entire source tree remains unchanged. These are
fail-closed guards for ordinary isolated builds, not a claim of sandboxing
arbitrary hostile Python/TeX source or resisting an adversarial process that
mutates directory ancestors concurrently.

Each build runs guards AND the full mathematical verifier under normal
Python and python -O, requiring byte-identical receipts. No correctness or
security check relies on Python assert. TeX runs with shell escape disabled
and restrictive file access, fixed PDF metadata, a fixed epoch, locale and
private cache/home directories. Cross-references must stabilize within four
passes; overfull boxes, missing characters, and unresolved or multiply-defined
references cause failure. ZIP order, timestamps, permissions, and compression
are fixed; entries are stored without compression.

BUILD_INFO.json records actual Python, pdfTeX and kpathsea versions, relevant
integer representation, fixed build settings, and the number of TeX passes.
It deliberately excludes executable locations, absolute working paths,
wall-clock times, run durations, and optimization-mode flags. Byte identity
is promised only for identical source bytes and the same installed Python/
TeX/font toolchain and controlled build environment. Different toolchain
versions can change BUILD_INFO.json and PDF bytes; no cross-version identity
is promised. Mathematical receipts themselves use only exact deterministic
integer/Fraction arithmetic.

Build outputs are Report197.tex, Report197.pdf, Report197_code.zip,
ARTIFACTS.json, and package/ containing the complete rebuildable release.

Guard tests and genuine extracted rebuilds
-----------------------------------------
guard_tests.py --unit-only checks source and output collisions, malformed
manifests, tampering, unlisted entries, unsafe names, symlinks, path traversal,
complete-manifest coverage, safe ZIP extraction and metadata, changed bytes
between validation and copying, and absence of assert-based guards. All
builds run this same suite under normal and optimized Python.

The default guard_tests.py additionally performs four actual complete builds:
original source under normal Python and python -O, then two separately
validated ZIP extractions rebuilt under normal Python and python -O. It
compares every file in all four output trees and verifies preservation of
all source trees. These are actual extracted-ZIP builds, not merely digest
comparisons or repeat executions of the verifier. Each of the four builds
itself runs the complete normal/optimized verifier and unit guards. The
--unit-only option prevents recursive build testing inside those builds.
