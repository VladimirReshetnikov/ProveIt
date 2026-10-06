# Report 166: bounded computational companion

This standalone Python standard-library companion checks the run-refined
exponential generating function for **distinct pop-stacked image permutations**.
For size `n`, entry `rows[n][k]` counts images with `k` maximal ascending runs.
The empty permutation has zero runs, so `rows[0] == [1]`. Trailing zero
coefficients are omitted. Uniformly sampling these distinct images is different
from applying the pop-stack map to a uniformly sampled input.

## Run

Use Python 3.9 or later. No third-party packages, installation, source downloads,
network access, or data files are required. Run from this directory, or use an
absolute path to the scripts. The scripts are import-safe and do no calculations
until their functions or command-line entry points are called.

```sh
# Fast default: full rows through n=12, literal images through n=7,
# published fixed-k formulas for k=1,...,5, and exact slope certificates.
python -B run_checks.py

# Full bounded audit, with the optional filtered-series examples and all data.
python -B run_checks.py all --n 40 --literal 9 --filtration 12 --include-data

# Run the independently scoped checks separately.
python -B run_checks.py coefficients --n 40 --literal 9 --include-data
python -B run_checks.py filtration --n 40 --filtration 12 --include-data
python -B run_checks.py slopes

# Regression suite, including deliberately failing checks and bad-input cases.
python -B run_tests.py
python -B -O run_tests.py

# Repeat the full audit with optimization enabled.
python -B -O run_checks.py all --n 40 --literal 9 --filtration 12 --include-data
```

Each CLI entry point prints exactly one deterministic JSON object to stdout. The programs
contain no file/network APIs, and no result is saved automatically. The caller
may redirect stdout to a chosen file. `-B` also prevents Python bytecode cache
creation; both entry-point scripts independently disable bytecode writes before
importing the local modules. Imported APIs should likewise be run with `-B` if
no bytecode-cache files are desired. Core tests capture CLI output in memory and
do not spawn processes or create files.

Bounds are enforced with ordinary `if` statements, not Python `assert`:

- Complete EGF and endpoint rows: `0 <= n <= 40`
- Literal image enumeration: `0 <= literal <= min(n, 9)`
- Optional filtered-series examples: `1 <= k <= 12`
- CLI defaults: `n=12`, `literal=7`; filtration is off for `all` unless selected,
  and defaults to `k=5` for the `filtration` command

For small `n`, set `--literal` accordingly, e.g.
`python -B run_checks.py coefficients --n 0 --literal 0`.
The `slopes` command has a fixed certificate and ignores numeric/data options,
although numeric bounds are still validated. The `filtration` command ignores
`--literal`. `--filtration` is rejected for `coefficients` or `slopes`.
`--help` returns JSON describing the interface. Exit status is 0 on success/help,
1 on a failed mathematical check, and 2 on invalid input. All check failures
remain active under `python -O`.

The maximum settings are intentionally modest. The literal check enumerates all
`9!` inputs and deduplicates their outputs. The exact bivariate computations use
large rational numbers and the endpoint recurrence keeps a finite array; runtime
and memory depend on the interpreter and machine. No improved refined-count
complexity bound is claimed.

## What is checked

1. **Branch-free EGF extraction.** In `Q[u][[z]]`, set
   `Q=4u+4u^2(exp(z)-1)-1`, `B=2u exp(z/2)+2u-1`, and
   `h=1+u(exp(z)-1)`. The entire series
   `H=sum_j (-1)^j z^(2j)Q^j/(16^j(2j)!)` and
   `J=sum_j (-1)^j z^(2j+1)Q^j/(4*16^j(2j+1)!)` give
   `P=Q(H+BJ)/(h(BH-QJ))`. No square root is evaluated. Formal division is by
   the polynomial `4u-1`, with its zero remainder explicitly verified at each
   `z` coefficient. Multiplication by `n!` yields complete integral, nonnegative
   polynomials of degree at most `n`.
2. **Published endpoint recurrence.** An integer prefix-sum implementation of
   Claesson–Guðmundsson–Pantone, Eq. (3), computes the whole run-refined triangle
   independently of the EGF, fixture formulas, and pop-stack simulation. Every
   complete row is compared, including zero coefficients implicit in padding.
3. **Literal image enumeration.** Every input is processed by stack push/flush
   operations; outputs are deduplicated. Runs are then counted by descents plus
   one. This path does not use the overlap characterization.
4. **Published fixed-run formulas.** For each `k=1,...,5`, the fixture equation
   `D_k(x) F_k(x)=N_k(x)` is checked coefficientwise through the requested `n`.
   Fixtures are transcribed from Asinowski–Banderier–Hackl, printed p.10. See
   `PROVENANCE.md` for precise sources and numerators.
5. **Optional filtered-series examples.** A separate formal expansion in `u`
   keeps `q,z` independent. It checks the square-root identity, degree bound
   `j+ell<=k`, and `q`-constant part `-1`. Substitution `q=exp(z)` is checked
   against every complete EGF row. It constructs integer numerators over
   `D_k=product_{j=1}^k(1-j*x)^(k-j+1)` and verifies degree `k(k+1)/2` and
   leading coefficient equal to that of `-D_k`. These are denominator
   representations; reduction or minimality is not asserted.
6. **Exact slope certificates.** Rational interval arithmetic certifies opposite
   denominator signs at the displayed root-bracket endpoints, the mean-slope
   and strictly positive variance-slope brackets, and
   `rho_upper < 6/5` together with `exp(6/5) < 4`. Exponentials use a Taylor
   polynomial and geometric tail bound; square roots use integer arithmetic;
   sine/cosine use alternating-series bounds on `[0,1]`. Decimal endpoints are
   rounded outwards. No floating-point arithmetic is used.

The certificate checks arithmetic consequences of formulas proved in the report.
Finite computation does **not** prove the EGF for every `n`, a central/local
limit theorem, uniform complex transfer, root uniqueness or dominance, an
all-`k` denominator theorem, global bivariate-pole classification, or an effective
asymptotic error constant. Analytic results and prior-art qualifications remain
in Report 166. The optional denominator application is separate from the
run-distribution argument.

## In-memory API

The modules expose the following bounded entry points. Invalid arguments raise
`ValueError`; a mathematical check failure raises `run_polynomials.CheckFailure`.
There is no hidden global triangle or dependence on a working-directory data file.

```python
from run_polynomials import (
    egf_run_polynomials, endpoint_run_polynomials, literal_run_polynomials,
    pop_stack_image, fixed_run_numerator, fixed_run_denominator,
    check_published_fixed_runs, check_run_polynomials,
)
from run_filtration import filtered_run_coefficients, check_filtration
from run_slopes import certify_slopes

rows = egf_run_polynomials(12)          # lists of integer coefficients
independent = endpoint_run_polynomials(12)
literal = literal_run_polynomials(7)
image = pop_stack_image([3, 1, 2])      # (1, 3, 2); list/tuple input only
summary = check_run_polynomials(12, 7, include_data=True)
examples = check_filtration(5, 12, rows=rows, include_data=True)
certificate = certify_slopes()         # JSON-ready exact enclosure report
```

`filtered_run_coefficients(k)` returns a list whose entry `r` is a dictionary
mapping `(j,ell)` to a `Fraction`, representing `[u^r]P` as a polynomial in
independent `q,z`. Its coefficient at `r=1` is `-1+q`. The JSON version uses
sorted triples `[j,ell,"rational coefficient"]`. `fixed_run_numerator(k)` is
available for the five published fixtures; `fixed_run_denominator(k)` is bounded
to `k<=12`. Returned fixture lists are fresh copies. Underscore-prefixed helpers
are implementation details, not a general-purpose symbolic or interval library.

## Files and evidence

- `run_polynomials.py`: EGF, endpoint recurrence, literal enumeration, fixtures
- `run_filtration.py`: optional filtered-series examples
- `run_slopes.py`: rational root/slope certificates
- `run_checks.py`: JSON CLI
- `run_tests.py`: nine regression groups, including optimization-safe failures
- `PROVENANCE.md`: mathematical and adaptation provenance

The Report 166 source archive also includes caller-captured evidence at
`../data/full_verification.json` and `../data/companion_tests.json`. The full
normal and optimized checks produced identical JSON: 41 complete EGF/endpoint
rows (`n=0,...,40`), 10 literal-image rows (`n=0,...,9`), 205 fixed-run fixture
coefficient equations, 492 filtered-series coefficient comparisons, 12 checked
numerator degrees, and all exact slope/bridge inequalities passed. All nine
regression groups passed in normal and optimized Python; their stdout also
matched byte for byte. The commands above reproduce these checks without using
the captured evidence as an input.

These authored scripts and generated outputs are sufficient for reproduction.
Third-party PDFs, HTML, repository code, private notes, and source snapshots are
not included in this companion.
