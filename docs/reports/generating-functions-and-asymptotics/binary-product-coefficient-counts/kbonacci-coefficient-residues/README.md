# Coefficient residues in generalized Fibonacci products

**Research manuscript — complete proposed proofs, not independently refereed.**
Prepared September 20, 2026, in response to a request to attempt a documented
open mathematical problem.

The main targets are Conjectures 6.2 and 6.3 of Richard P. Stanley,
*Theorems and Conjectures on Some Rational Generating Functions*,
arXiv:2101.02131v3, pp. 23–24. A targeted literature search did not identify
a later resolution, but this is not a certified novelty or priority review.
See `LITERATURE.md` and `RESEARCH_STATUS.md` for the exact scope of that
claim; the two audits are complementary and neither contains the other.

## What this archive is

It is the merger of two previously separate research packages that attacked
the same conjecture page by completely disjoint methods:

- **`stanley-kbonacci-residues`** (the spine): a finite-state proof of
  Conjecture 6.2 for *every* modulus and residue, and of Conjecture 6.3, via
  unique canonical words avoiding `1^k 0`, a proved canonical-fiber
  factorization into carry blocks, a `k+1`-coordinate exact counter, a
  uniform `4k+2`-state parity automaton, and a symbolic elimination.
- **`quasifibonacci-odd-coefficient-counts`** (the donor): a
  signed-cancellation proof of Conjecture 6.3 — a coherent periodic signing
  makes every coefficient of the signed product lie in `{-1,0,1}`, parity
  becomes a squared norm, and an exact overlap identity closes the
  recurrence. It proves the count for *every* superincreasing seed list, not
  only Stanley's initialization.

Neither package contains a single lemma of the other, and neither result
contains the other: the finite-state route is strictly more general in the
**modulus**, the signed route is strictly more general in the **seeds**.
The merged article proves the shared core theorem twice and keeps the
duplication wherever it carries information; the article's section
"What this article deliberately keeps twice" lists the thirteen such items
and says in one sentence what each buys.

## Read the result

`article.pdf` is the 34-page article; `article.tex` is its editable source.
For k >= 2 and F_1^(k) = ... = F_k^(k) = 1, the product is

    P_n(x) = product(1 + x^(F_(i+k)^(k)), i = 0,...,n-1).

The manuscript proves rationality of coefficient-residue counts for every
modulus, and derives the odd-coefficient formula

    sum(odd_count(k,n)*z^n, n >= 0)
      = (1 + 2*z^k)/(1 - 2*z + 2*z^k - 2*z^(k+1)),

equivalently `a_k(n) = 2^n` for `0 <= n <= k` and
`a_k(n) = 2a_k(n-1) - 2a_k(n-k) + 2a_k(n-k-1)` for `n >= k+1`.
It also proves rationality for fixed exact multiplicities, handles internal
zero coefficients explicitly, and proves *two different* exponential sparsity
statements: one whose denominator is the number of nonzero coefficients, and
one whose denominator is every position from 0 to the degree, zeros included.
These are not the same theorem and the article keeps them apart.

General claims do not depend on finite experimental fitting. The special
modulo-three identities are additionally proved with finite Cayley–Hamilton
certificates.

## Reproduce the checks

Python 3.10 or newer is required. Everything except one optional symbolic
check uses only the standard library. The two original packages recorded
their runs under Python 3.13.5; the JSON records now in `data/` were
regenerated under Python 3.14.4.

    python code/verify.py            # finite-state suite (safe under -O)
    python code/verify_signed.py     # signed suite (needs assertions)
    python code/test_api.py          # boundary and validation tests
    python code/cross_check.py       # comparisons BETWEEN the two proofs
    python code/check_certificates.py
    python code/growth_constants.py
    python code/make_tex_tables.py

Put `code` on the import path first (`PYTHONPATH=code`, or run via `make`).

An optional symbolic check uses SymPy 1.14.0:

    python -m pip install -r requirements-optional.txt
    python code/verify.py --symbolic

`verify.py`, `check_certificates.py` and `cross_check.py` use explicit error
checks rather than removable Python assertions, so they still validate under
`python -O`. `verify_signed.py` refuses to run under `-O`, so do not use `-O`
for it. `test_api.py` is unaffected: its checks are `unittest` assertion
methods, which `-O` does not remove.

`check_certificates.py` does not import the main implementation. It validates
state-space closure and every transition, reconstructs the integer sequence,
and checks the finite recurrence conditions for both modulo-three formulas.

### Recorded coverage

The two suites test disjoint objects and are reported separately, on purpose.

*Finite-state suite* (`data/verification_summary.json`): 476 full
residue-histogram comparisons covering 1,666 individual residue counts, every
one including the zero-position correction; 28,665 exhaustive binary-word
normalizations and pair factorizations; 22,582 coefficient fibers; 208
exact-multiplicity checks; 6,024 parity-sequence entries; 3,384
quotient-transition checks. Direct expansion reached degree 227,138.

*Signed suite* (`data/verification_signed.json`): 519 direct bitset prefix
comparisons for 2 <= k <= 25 under an 8,000,000-degree cap; 144 signed dense
products with 19,338 coefficient-oracle comparisons; all 2^k initial signings
for 2 <= k <= 6 over two seed families (248 cases); 96 random superincreasing
seed/sign cases; 5,821 exact pointwise-overlap identity checks; 28,101
positive-recurrence comparisons; fast-versus-linear counts at eight indices
per k for 2 <= k <= 30, exact and modulo 1000000007.

*Cross-verification* (`data/cross_check.json`), which neither original
package could run: 53,876 coefficient positions where the signed value's
absolute value is compared with the exact coefficient mod 2, and 27,747 of
them where the fiber counter is compared with the exact coefficient; 707
comparisons of polynomial powering against the uniform parity automaton; the
707 common entries of the two count tables; 21 growth-constant values across
the two numerical tables (worst relative difference 3.0e-16); and the weight
conventions of the two modules for 2 <= k <= 12.

## Use the implementations

Finite-state module:

    python code/kbonacci_residues.py 3 5 20

This prints all residue counts modulo 5 for k=3 and n=0,...,20. By default,
zero positions through the degree are included; use `--exclude-holes` to
count nonzero terms only. Never count the infinitely many implicit zeros
beyond the polynomial's degree.

    from kbonacci_residues import build_machine, coefficient_for_canonical
    from kbonacci_residues import normalize, residue_counts, odd_counts

    assert coefficient_for_canonical((0,0,0,0,1), k=2) == 3
    assert normalize((1,1,0), k=2) == (0,0,1)
    print(odd_counts(3, 12))
    print(residue_counts(3, 5, 20))

    # Number of coefficients equal to exactly 4:
    machine = build_machine(3, cap=5)
    exact_four = [row[4] for row in machine.distributions(20)]

Signed module:

    python code/kbonacci_parity.py 3 20 --prefix
    python code/kbonacci_parity.py 3 10000
    python code/kbonacci_parity.py 3 1000000000000 --modulus 1000000007
    python code/kbonacci_parity.py 3 8 --coefficient 105

The last two return `699562826` and
`{"parity": 1, "signed_coefficient": -1}`. The signed coefficient refers to
the canonical coherent signing, not to the all-plus product's integer
coefficient.

    from kbonacci_parity import count_fast, count_prefix, CoefficientOracle

    assert count_fast(3, 20) == 76576
    assert count_fast(3, 10**12, modulus=1000000007) == 699562826

    # Nonstandard superincreasing seeds, and a noncanonical initial sign block.
    oracle = CoefficientOracle(3, 50, seeds=[2, 7, 15], initial_signs=[-1, 1, -1])
    parity = oracle.parity(1000)        # 0 or 1
    signed_value = oracle.signed(1000)  # -1, 0, or 1
    assert parity == abs(signed_value)

**All words are in low-to-high weight order.** The leftmost bit has weight 1.
For k=3, the weights are 1,3,5,9,17,..., NOT 1,2,4,7,... .
`kbonacci_residues.weights` and `kbonacci_parity.weights` return the same
sequence; the article's section on notation records that `kbonacci_parity`
stores an extra leading slot internally, matching its original one-based
indexing, and `cross_check.py` asserts the agreement.

The k=1 case is excluded and is genuinely false there. The residue API
accepts moduli at least 2; modulus 1 is mathematically trivial and handled in
the article. `count_fast` takes O(k^2 log(n+1)) ring operations, including for
composite moduli — this is not a bit-complexity claim, since an exact result
has Theta(n) bits for fixed k. The coefficient oracle uses at most O(n)
arithmetic steps per query after O(n+k)-entry preprocessing. `parity_bitset`
has a default degree cap of 8,000,000; the sparse checker is intended only
for small products and can require exponential memory. A state limit guards
`build_machine` against uncontrolled memory use: finite-state existence does
not mean that very large parameters are cheap.

The two oracles do different things and neither subsumes the other.
`CoefficientOracle.signed` works for arbitrary superincreasing seeds and
arbitrary initial sign blocks and returns a value in {-1,0,1};
`coefficient_for_canonical` returns the exact nonnegative integer
coefficient, for Stanley's seeds only.

## Build the article

    make pdf

or

    latexmk -pdf -interaction=nonstopmode article.tex
    latexmk -c

Standard TeX packages are listed at the top of the source. No external
graphics or proprietary fonts are required. The article `\input`s three
generated fragments — `data/initial_table.tex`, `data/growth_table.tex` and
`data/large_table.tex` — which must exist; `python code/make_tex_tables.py`
regenerates them from `data/growth.csv` and `data/large_values.json`.

`make all` runs both suites, the cross-check, the certificates, the tables
and the PDF. `make clean` removes only TeX build intermediates and Python
bytecode.

## Files

- `article.tex`, `article.pdf`: the merged manuscript.
- `code/kbonacci_residues.py`, `code/verify.py`, `code/check_certificates.py`,
  `code/growth_constants.py`: the finite-state route.
- `code/kbonacci_parity.py`, `code/verify_signed.py`, `code/test_api.py`,
  `code/make_tex_tables.py`: the signed-cancellation route.
- `code/cross_check.py`: comparisons between the two routes. New in the
  merged archive; neither original package could run it.
- `certificates/`: two complete modulo-three certificates and the parity
  automata for k=2,...,8.
- `data/`: exact checked coefficient tables (`coefficient_counts.csv`),
  two independent odd-count tables (`odd_counts.csv`, `counts.csv`),
  two independent growth tables (`growth_constants.csv`, `growth.csv`),
  state counts, large values, two-column index/value files `b_k*.txt`
  (not assigned OEIS b-files), the three verification records, and the
  generated TeX fragments.
- `LITERATURE.md`, `RESEARCH_STATUS.md`: the two source and status audits.
- `Makefile`, `requirements-optional.txt`: reproduction conveniences.

The archive contains no third-party research PDFs, font files, compiled
Python caches, or LaTeX build intermediates.

## Verification is not the proof

The article's arguments prove all indices, all orders, and (for the residue
theorem) all moduli. Direct polynomial multiplication checks only finite
instances. Agreement between two algorithms that descend from the *same*
recurrence — `count_prefix` versus `count_fast` — checks their
implementation, not the combinatorial theorem. Agreement between algorithms
that descend from *different proofs* — `count_fast` versus the parity
automaton, or the signed oracle versus the fiber counter — is a real check,
and `cross_check.py` exists to record exactly those.

The degree cap in the bitset sweep means that at the largest tested orders
the sweep reaches only the nonoverlapping seed block; those runs are not
evidence of long-run behaviour. The numerical growth constants are
high-precision approximations, not certified interval enclosures, and every
inequality in the article is proved without numerical root finding.
