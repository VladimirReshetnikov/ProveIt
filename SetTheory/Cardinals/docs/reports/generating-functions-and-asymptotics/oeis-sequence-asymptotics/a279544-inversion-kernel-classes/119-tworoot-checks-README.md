# Exact reproducibility checks for report119

Requires Python 3.10 or newer; only the Python standard library is used. No
network access, third-party packages, research files, or private files are needed.

From the package root:

    python3 -B checks/run_checks.py
    python3 -B -O checks/run_checks.py
    python3 -B checks/mutation_tests.py --output /tmp/report119-check-results.json

The first command verifies the closed inventory, the strict fixture schema,
exact algebra, counting sequences, the core N=256 certificate, and the N=400
correction certificate. The last command is the aggregate bounded campaign: it
runs normal and optimized baselines, repeats both in a fresh directory, and
requires every named mutation to fail with its expected diagnostic in both
modes. It also verifies that the supplied files remain byte-for-byte unchanged.
Output must be outside this checks directory. A nonzero exit status is failure.
The supplied MANIFEST.json seals all seven other files and admits no extra file,
subdirectory, symlink, or special file. Bytecode creation is disabled.

## Mathematical reconstruction

- `exact_math.py` implements independent sparse rational identities, formal
  series, aggregated tree counts, exhaustive inversion-sequence enumeration,
  integer-directed intervals, explicit differentiated canceled orbits, and
  gamma/inverse algebra
- `jet_certificate.py` reconstructs the two critical root jets by solving their
  cubic coefficient equations over Q(sqrt(3)), then propagates rectangular
  complex intervals and degree-five interval jets independently
- `fixtures.json` records source provenance and exact expected results. All 26
  displayed OEIS terms n=0..25 are externally checked. Terms n=26..60 are only
  internally generated: the tree and two-root formal orbit independently agree
  through n=60. The OEIS b-file was not used
- The source equation (3.39) and derived scalar equation are checked through
  degree 16 at two rational catalytic choices. Brute-force avoidance is checked
  through n=8. Exact finite threshold cases test equality and adjacent integers
- The core infinite value tail is 2^244 (7/25)^256, with 1000 times that tail for
  the upper-seed derivative. The correction tail is E=2^342 (7/25)^400; Cauchy
  coefficient errors are 16 E 10^(5j), j=1,3,5. All finite arithmetic and the
  rational constants in these analytic bounds are checked
- Machin's identity and exact alternating arctangent bounds enclose pi. Integer
  square roots give outward square-root bounds. No binary float enters the
  certificate. The 80-place correction enclosures strictly contain the exact
  computed intervals
- Gamma-ratio terms through order six at four half-integers are independently
  obtained from both the gamma functional equation and Bernoulli exponentiation.
  Exact Laurent-polynomial residuals verify three Lambert-W inverse corrections,
  the relative-to-logarithmic conversion, and the first log-log correction

## Scope

Finite checks do not prove the tree interpretation, formal identification,
normal convergence, Pringsheim theorem, boundary removability, or transfer.
Those arguments are in report119. Interval enclosures use the analytic tail and
Cauchy proofs there. Fixed-order remainder constants and threshold cutoffs are
existential. The inverse must retain its error inside the ceiling/rounding
bracket. No claim of novelty, nonalgebraicity, non-D-finiteness, or a complete
exponentially improved transseries is made.

## Provenance

Nathan Britt and Nicholas Beaton, *Completing the enumeration of inversion
sequences avoiding triples of relations*, arXiv:2512.21943v3 (29 September 2026),
Section 3.7, equations (3.38)-(3.39), and Section 4.2, equation (4.11):
https://arxiv.org/html/2512.21943v3

OEIS A279569, displayed prefix n=0..25, checked 2 October 2026:
https://oeis.org/A279569

The paper explicitly describes its Section 4.2 asymptotics as numerical and
non-rigorous. Those numerical estimates are not proof inputs. Infrastructure
conventions are adapted from report118; the class-1953A computations above are
independently reconstructed, rather than importing its mathematics or the
original research certificate.
