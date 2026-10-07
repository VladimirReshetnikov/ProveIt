REPORT 196: DISTINCT PART SIZES EQUAL TO MAXIMUM MULTIPLICITY
Reproducibility package for OEIS A239964, 4 October 2026

Scope
-----
a(n) counts nonempty integer partitions with D=M, where D is the number of
occupied part sizes and M their maximum multiplicity; a(0)=0. Report196.tex
contains the mathematical argument. Finite exact computations are checks,
not a substitute for its analytic proof. No convergence of the infinite
Poincare expansion, exhaustive novelty search, or exact finite-threshold
inverse based solely on an asymptotic truncation is claimed.

Requirements and commands
-------------------------
Python 3.9+ and its standard library suffice for all counting and guard tests.
Building the PDF additionally requires an installed pdfLaTeX stack, kpsewhich,
and the packages/fonts used by Report196.tex. No network access is needed.

From an extracted package, run:
  python3 -I -S -B verify.py
  python3 -I -S -B verify.py --full1000
  python3 -I -S -B build.py --check
  python3 -I -S -B build.py /absolute/path/to/new-output --full1000
  python3 -I -S -B guard_tests.py
  python3 -I -S -B -O guard_tests.py

The destination's parent must already exist. The destination itself must be
absent, disjoint from the source tree, and have no symlink ancestor. Existing
files/directories, dangling links, parent traversals, symlinks in the source,
extra files, and mismatched/partial manifests are errors. Commands never
replace an existing output. Keep result files outside the source package.

verify.py's default capped DP checks n=0,...,250 (251 exact terms). The
--full1000 mode recomputes all n=0,...,1000 (1,001 exact terms). On the build
machine these took approximately 1 second and 47 seconds respectively;
performance is machine-dependent. Both modes additionally run independent
multiplicity-vector enumeration through 45, the independent positive B_S
subset-product identity through 55, exact rational low-order algebra, independent fourth-radial/second-forward
Fraction jets, and
saddle-polynomial recurrence checks. --output NEW_FILE and --terms-output
NEW_FILE save deterministic results and the computed terms, respectively.

Algorithm and arithmetic
------------------------
For each multiplicity cap c, a bivariate occupancy DP multiplies the local
factors 1 + u(q^j + ... + q^(cj)). Descending occupancy rows preserve the old
row for each new size. A sliding sum in each residue class modulo j includes
exactly multiplicities 1,...,c. Row c contributes positively to the diagonal;
row c+1 contributes negatively. Reusing these adjacent rows implements the
sum over m of [u^m](cap m minus cap m-1). The exact minimum total size for
D=M=m is (m*m+3*m-2)/2, giving the finite cap limit. Every counting operation
uses arbitrary-precision Python integers; there is no fixed-width overflow
assumption or platform-dependent integer extension.

The second check directly enumerates increasing-size multiplicity vectors
through 45 and separately verifies their total counts against p(n). The
third check literally multiplies the nonnegative product
  B_S(q)=q^(|S|s) product_{j in S}(1-q^j)^(-1)
         product_{j not in S}(1+q^(s+j)/(1-q^j)),  s=sum(S),
and sums (-1)^(|S|+1)(1-q^s)B_S. It includes all 333 subsets with |S|s<=55.
It is independent of the capped DP. Fraction arithmetic checks the first
normalized logarithmic coefficients, including the deleted-site -s^2 term,
and the probability-series division. An integer polynomial recurrence checks
the exact saddle amplitude through m=13 (the monomials r=0,...,12). symbolic_checks.py independently
derives the cubic normalized logarithm and c4 integrand by formal exp/log
jets, including the marked shape statistic sum(j*j), and verifies the d2
normalization coefficient. It can also be run standalone.

Pinned data and attribution
--------------------------
The included data/b239964.txt is the complete OEIS b-file downloaded on
4 October 2026 from https://oeis.org/A239964/b239964.txt, linked at
https://oeis.org/A239964. It contains exactly 1,001 rows, indexed 0 through
1000. Its SHA-256 is:
  e215b0baba64bf4afb2df72a642ed4c1e93ba16f87ea0f01ab50d58d87a2814b
OEIS data is attributed to the OEIS Foundation and the sequence's credited
contributors; see https://oeis.org/wiki/The_OEIS_End-User_License_Agreement
and https://creativecommons.org/licenses/by-sa/4.0/ for data licensing.
The sequence page credits Seiichi Manyama's 13 March 2026 coefficient-product
formula. The report gives its own derivation and identifies related published
work and the limits of the source review. The Python verification was written
for this report. The generic packaging design follows the preceding report's
isolated-build, closed-inventory, and deterministic-ZIP pattern; no theorem or
counting code for that different sequence is reused.

Manifests and reproducibility
-----------------------------
SOURCE_MANIFEST.json hashes every source, including data and all programs;
it excludes itself, explicitly. MANIFEST.json in a built package additionally
hashes the source manifest, PDF, exact results, and build/guard records; it
excludes itself, explicitly. The deterministic ZIP contains exactly that
complete package including both manifests, but cannot contain itself. The
outer ARTIFACTS.json covers every deliverable and every file in package/,
including the ZIP and both manifests; it excludes only itself, explicitly.
These are integrity checks, not signatures. Replacing both content and its
manifest is not authenticated by a hash manifest.

For authors only, with exactly the seven source files and no existing source
manifest: python3 -I -S -B build.py --freeze-source writes a new manifest.
Ordinary builds require that manifest, validate every file and directory, and
preserve the entire source tree. They recheck the exact in-memory bytes, copy them to private
staging storage, revalidate that copy before executing it, run normal and optimized guard tests, run exact verification,
compile TeX with shell escape disabled and restrictive file access, wait for
stable cross-references, reject overfull boxes/missing glyphs/unresolved
references, and publish only to an exclusively created fresh destination.

Build output consists of Report196.tex, Report196.pdf, Report196_code.zip,
ARTIFACTS.json, and package/ (the complete rebuildable package). Results record
whether --full1000 was requested; the default build never claims to have
recomputed terms beyond 250. Generated JSON deliberately excludes timestamps,
absolute paths, and run times. TeX metadata, locale, environment, cache paths,
and ZIP timestamps/order/permissions are controlled. ZIP uses stored entries.
Identical source, mode, and installed Python/TeX stack should yield byte-identical
outputs. There is no promise of identical PDFs across different TeX versions.

Guard tests
-----------
guard_tests.py --unit-only tests malformed manifests, tampering, unlisted
files, symlinks, traversal, destination collisions, and optimized-mode safety.
No correctness or security condition uses Python assert. Every build runs
these tests under both ordinary Python and python -O and compares their bytes.

The default guard_tests.py additionally performs four actual builds: original
source under normal Python and python -O, followed by two separate safe ZIP
extractions and actual builds under normal Python and python -O. It compares
all files in all four complete output trees and checks preservation of every
source tree. This is a genuine extracted rebuild, not only a hash comparison
or a second verification run. Add --full1000 to recompute all 1,001 terms in
each build (several minutes total). --output NEW_FILE saves its JSON evidence.
The unit-only option exists to avoid recursive rebuild testing inside a build.
