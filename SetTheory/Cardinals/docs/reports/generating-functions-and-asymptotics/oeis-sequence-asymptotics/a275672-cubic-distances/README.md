# Distinct distances in a cubic lattice — A275672

Research report and reproducibility package, 8 October 2026.

The problem is to maximize the number of points in `{0,...,n-1}^3` when
every unordered pair has a different Euclidean distance. Adding one to
each coordinate gives the convention in the original question.

## Results

The completed exhaustive computations and matching coordinate sets give

```text
n:    0 1 2 3 4 5 6  7  8
a(n): 0 1 3 4 6 7 9 10 12
```

The new exact terms are **a(7)=10 and a(8)=12**. The package also contains
verified constructions at every side length from 7 through 30, including
13 points at n=9, 14 at n=10, and at least n+4 points for every n=8,...,14.
See `data/finite_results.csv` for the complete final bounds and their
status. A lower bound is not an exact sequence term.

The article proves

```text
limsup a(n)/n <= sqrt(1/(6*kappa)) = 1.848895345708975...
kappa = 48755553510102913673137 / 10^24.
```

The proof uses exact rational exponential enclosures, a global
interpolation bound, Gaussian positivity, and the arithmetic density of
integers that are not of the form 4^a(8b+7). An independent rational
implementation checks the same certificate. A separate analytic
certificate gives the slightly weaker coefficient 1.8712786400....
The article includes an elementary lower-bound proof, the established
Lefmann–Thiele lower bound, structural properties, and research questions.
It does not determine the growth exponent or strict monotonicity.

## Read the article

- `a275672.pdf`: complete article, with proofs, tables, figures, and references.
- `a275672.tex`: main editable LaTeX source.
- `article/`: included LaTeX sections and generated result tables.
- `figures/`: included vector PDF figures and PNG previews.

## Verify the supplied results

Python 3.10 or later is required. The mathematical verification and
bound scripts use only the Python standard library.

```sh
python3 src/verify_results.py
python3 src/verify_gaussian_certificate.py
python3 computations/constructions/scripts/verify_bundle.py
python3 src/finite_bounds.py 50 100 200 500 1000
```

The main verifier checks every point list using integer squared
distances; independently regenerates the palette; checks complete
diameter-orbit coverage and the source hashes of the exact runs;
checks the rational Gaussian certificate with different interval
parameters; and recomputes the reported finite upper bounds.

**The distinction between two types of verification matters.** A point
list is a compact lower-bound certificate and can be checked directly.
The impossibility runs are reproducible exhaustive computations, backed
by a completeness proof, source audit, full outer case logs, and source
snapshots. Checking their case coverage alone does not independently
prove that every inner search is UNSAT. They are not formal SAT proof
traces or theorem-prover-kernel certificates.

## Reproduce the exhaustive searches

The completed sources require GCC or Clang with C++17. Their fixed masks
support 1 <= n <= 10; the underlying method is not restricted to this
range. A time limit or interruption produces no global impossibility
conclusion. Allow additional time on a slower machine.

The convenient entry point validates all arguments and compiles a
source-hash-specific executable automatically:

```sh
python3 src/run_exact.py 8 13 --mode top6 --seconds 3600
```

For new searches, `--variant prefix-filtered` uses the separately audited
implementation that moves arithmetic filters earlier in the edge-prefix
recursion. The original proof sources remain byte-for-byte preserved.

```sh
mkdir -p build
g++ -O3 -std=c++17 computations/exact/rainbow_exact_v5.cpp -o build/rainbow_exact_v5
g++ -O3 -std=c++17 computations/exact/rainbow_edge_prefix.cpp -o build/rainbow_edge_prefix

# Original proof that eleven points are impossible at n=7.
build/rainbow_exact_v5 7 11 3600 diameters

# Proof that thirteen points are impossible at n=8.
build/rainbow_edge_prefix 8 13 3600 top6

# Corroborating, differently refined n=7 computation.
build/rainbow_edge_prefix 7 11 3600 top4
```

These commands write a structured result to standard output and the
per-case record to standard error. The original retained logs and JSON
summaries are in `computations/exact/`. See its `EXACT_SEARCH.md` and
`MANIFEST.json` for exact source provenance. Recorded times came from
shared hardware and are not controlled performance benchmarks. In the
prefix version, the node counter counts inner clique calls; it excludes
outer edge-prefix calls.

## Inspect independent validation

`validation/` includes a manual source audit, immutable source snapshots,
and recorded comparisons against a deliberately simple independent
subset enumerator. The original audit covered 1,500 random induced
instances and 256 small-grid diameter-case runs. The README there states
precisely which versions were tested and which extensions were checked
by source comparison and the general correctness argument.

A second independent review is in `validation/fresh_audit/`. For each of
three implementations it compared 1,902 kernel states and 927 diameter
cases with a plain enumerator; both prefix implementations also passed
4,635 prefix comparisons. Its original runs used address and undefined
behavior sanitizers. The complete report and portable replay runner
are included.

This stronger audit can be rerun separately. It is not needed merely to
read or verify the supplied constructive witnesses.

```sh
python3 validation/run_audit.py --help
```

## Reproduce the constructive walks

`computations/constructions/` is a self-contained constructive package
with five C++ programs, immutable starting configurations, all final
coordinate certificates, and a reproduction manifest.

```sh
make -C computations/constructions
python3 computations/constructions/scripts/reproduce.py --n 10
python3 computations/constructions/scripts/reproduce.py --n 12
```

These runs were reproduced point-for-point with the packaged iteration
budgets. Exact random trajectories can depend on the standard library's
implementation of `std::shuffle`; validity of the final coordinates
does not depend on reproducing the trajectory. Failed bounded searches
are inconclusive.

## Rebuild the article and tables

A standard LaTeX installation with `latexmk` and the packages named in
the preamble suffices. The figures are already included; no network
access or numerical optimization package is needed.

```sh
python3 src/make_result_tables.py
latexmk -pdf -interaction=nonstopmode -halt-on-error a275672.tex
```

`make verify`, `make pdf`, and `make exact-binaries` provide shortcuts.
Regenerating the figures additionally requires matplotlib and NumPy;
see `src/plot_bounds.py` and the constructive package's figure script.

## Data and provenance

- `data/witnesses.json`: unified coordinate catalogue for n=0,...,30.
- `data/finite_results.json` and `.csv`: final lower and upper bounds,
  exactness status, palette counts, and evidence categories.
- `data/n*_exact_certificate.json`: source-linked records for complete
  impossibility runs that match a verified lower bound.
- `data/n*_upper_certificate.json`, if present: complete impossibility
  runs giving upper bounds without settling the exact term.
- `data/verification_report.json`: retained result of the main verifier.
- `data/gaussian_certificate_verified.json`: rational potential certificate.
- `data/large_n_upper_bounds.json`: rigorously computed finite bounds.
- `oeis/b275672.txt`: proposed b-file extension, containing exact terms only.
- `oeis/proposed_update.txt`: draft update text. It has not been submitted.
- `SHA256SUMS`: hashes of all packaged deliverables except the manifest itself.

The historical terms and published lower bound are attributed in the
article. The Gaussian upper bounds are proved within the report; no
exhaustive publication-priority claim is made. Larger-grid constructions
are certified here without a claim of global record status.

## Original question and literature

- https://math.stackexchange.com/questions/1879760/
- https://oeis.org/A275672
- Lefmann and Thiele, *Point sets with distinct distances*, Combinatorica
  15 (1995), 379–408, https://doi.org/10.1007/BF01299744
- Official preceding report abstract:
  https://www.inf.fu-berlin.de/inst/pubs/tr-b-94-16.abstract.html
- Croot, Mao, Pohoata, Sheffer, and Yip, *A combinatorial large sieve for
  Sidon sets, distances, and norm forms*, https://arxiv.org/abs/2606.17487
  (the relevant upper bound is planar; it does not establish a sublinear
  bound for the present cubic problem).
