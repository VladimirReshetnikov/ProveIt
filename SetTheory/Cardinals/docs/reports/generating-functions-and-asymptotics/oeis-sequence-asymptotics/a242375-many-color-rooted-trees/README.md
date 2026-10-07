# Report 222 — Many color rooted trees and their symmetries

This self-contained report treats OEIS A242249/A255517 and diagonals A242375/A255523. It includes:

- A common complex domain and all fixed-order uniform asymptotics for both signs
- Analytic palette coefficients and rounding-sensitive asymmetry crossover corrections
- Leaf-pair Poisson limits, all fixed-order signed-Poisson expansions, and the sharp moving-parameter total-variation constant
- The asymptotic elementary-abelian automorphism-group law and a sharp recursive-class defect
- A separately proved labeled-Cayley contrast and explicit failure of positive exponential-moment convergence
- Diagonal and real-palette inversion, with exact integer-threshold safeguards
- Offline exact code, independent finite checks, exact rational domain certificates, and optional numerical diagnostics

## Read first

Open Report222.pdf. Its complete source is article.tex; tables.tex is generated from verified exact results.

The probability model is uniform over colored rooted isomorphism classes. N counts all vertices; diagonal n counts nonroot vertices. Only positive integer q is a counting probability. The all-order expansion depths are fixed. The core q≥40 range is distinct from the marked q≥200 range and from existential monotonicity/onset constants.

The comparison Poisson parameter is λ_N=e^(-2)/(q/N). A rate against a fixed limiting parameter requires a rate for q/N. The sharp group-defect coefficient concerns the recursive class B; the total-variation bound for the whole automorphism group is only an upper bound. No positive exponential-moment convergence is claimed.

Enumeration and general transfer/inversion machinery are prior; the leading diagonal constants are already posted on OEIS. The 1992 Labelle full text was not accessible in the source review. No worldwide novelty claim or effective numerical onset is made.

## Portable exact code

Python 3.10+; no third-party dependencies for this section.

    python3 code/test_exact.py
    python3 -O code/test_exact.py
    python3 code/certify_bounds.py
    python3 code/colored_trees.py count 640 640
    python3 code/colored_trees.py count 20 20 --kind identity
    python3 code/colored_trees.py marked 6 3
    python3 code/colored_trees.py marked 6 3 --kind B
    python3 code/colored_trees.py diagonal 35 --kind identity
    python3 code/colored_trees.py inverse 1000000 --max-n 100
    python3 code/colored_trees.py palette 10 9 10 --max-q 100

The count kinds are all, identity, zero (J=0), and B. The marked command prints a JSON map from the marking exponent to its exact coefficient as a decimal string. The exact inverse returns the least index within the specified bound, or null if none occurs there. Palette search exhaustively checks all smaller positive palettes; it does not assume finite-size monotonicity.

### Input and serialization safeguards

- Exact counts: 1≤N≤2000, 1≤q≤1,000,000
- Diagonals: 0≤n≤1999
- Full marked polynomials: 1≤N≤12, 1≤q≤100
- Exact marked prefixes: N≤640, degree K≤32, N(K+1)≤12000
- Palette scan: N·max_q≤20000
- User threshold input: positive ASCII decimal, at most 600 digits
- Computed integers are printed in base-10^9 chunks, without changing Python's global decimal conversion setting
- Explicit exception checks remain active under python -O
- No global recursion or precision setting is changed; mpmath diagnostics use a temporary precision context

The regression suite actually computes and prints the 2067-digit A_+(640,640) under PYTHONINTMAXSTRDIGITS=640 in normal and optimized subprocesses. It tests the input guard separately. Bounds are intentional implementation safeguards and can be reviewed in the source; they are not mathematical theorem restrictions.

## Optional symbolic and numerical checks

Recorded versions: SymPy 1.14.0 and mpmath 1.3.0. These are unnecessary for the exact core.

    python3 code/palette_jets.py --order 4
    python3 code/diagnostics.py --tv

requirements-optional.txt records those versions. Palette generation is bounded to orders 1..6. The symbolic output contains exact expressions with a=e^(-1), and exact verification of the first fixed-size palette coefficient and the Poisson correction algebra.

The numerical program uses exact integer counts, then 80-digit arithmetic. It records crossover/gap/class-B checks through N=640, diagonal inverse checks through n=320, and TV checks through N=320. Marked-prefix coefficients through degree 16 and the omitted actual probability mass are exact. Numerical TV brackets use explicit Poisson tails summed through degree 159; these are high-precision diagnostics, not directed-rounding interval certificates. No optional diagnostic was omitted because of the validation environment.

results/analytic_bounds.json is different: it certifies the stated elementary analytic-domain inequalities using rational arithmetic only. It does not certify the implicit asymptotic constants or onsets.

## Rebuild the PDF and deterministic ZIP

A TeX Live installation with pdfTeX, the standard LaTeX/AMS packages, Latin Modern, microtype, hyperref, geometry, enumitem, and fancyhdr is required. The build never downloads or installs software. It initializes a fresh format from the installed TeX sources and uses only local writable caches, including on machines whose default TeX cache is read-only.

    python3 build.py
    python3 build.py --checks
    python3 build.py --optional
    python3 -O build.py --optional

--checks regenerates portable results; --optional also regenerates symbolic/numerical results. --pdf-only and --zip-only are available separately. The small article table is regenerated from the exact result file during checked builds.

The PDF is date-free with a fixed source epoch; ZIP members have fixed timestamps and permissions and use stored bytes rather than implementation-dependent compression. Rebuilds with the same TeX/font and optional-library versions are byte reproducible. Different toolchain versions can change PDF or symbolic formatting; mathematical counts do not depend on them.

SHA256SUMS covers every public file except itself and the ZIP that contains it. The builder verifies the archive membership, CRCs, and all manifest hashes. It excludes caches and build intermediates. No source-paper PDFs or working notes are included.

## Recorded validation

- Entire marked polynomials and four scalar classes independently checked by Prüfer enumeration through N=6, q=1,2,3
- Orbit-stabilizer, class-B group order, and labeled expectation checked exactly
- Independent Euler products through N=11 for q=1,2,3,5,40
- Both OEIS diagonal prefixes checked at n=0..35
- Exact threshold, invalid-input, and large-output regressions
- Exact rational analytic-domain certificates
- Optional symbolic and numerical outputs replayed in ordinary and optimized modes
- PDF rendered and visually checked; deterministic rebuild and archive checks recorded with the release
