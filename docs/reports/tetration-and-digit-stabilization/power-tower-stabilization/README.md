# Stabilization of integer power towers

Research package — September 19, 2026. Merged edition, version 2.0.

Subtitle: *Exact decimal transients, a counterexample to a congruence-speed conjecture, and a complete resolution of OEIS A324017 — onset laws, sharp radix congruences, higher arrows, and the local p-adic limit.*

## Provenance

This package merges two independently produced research reports on the same topic:

- `delayed-stabilization-of-towers` — the Ripà height-2 conjecture, the decimal transient formula, the minimal prime counterexample 2749, the CRT prime families, the density theorem, and the general-radix extension;
- `one-stable-digit-per-height` — the three OEIS A324017 comments, the gap-general local distances, the inverse-limit description, the higher-arrow saturation criterion, and the local Lambert W formula.

Both reports independently proved the same shared core theorem — the one-digit law `T(h+r) - T(h) == -2*B^h (mod B^(h+1))` — by the same route: a binomial precision estimate followed by induction on the height. It is proved **once** in the merged article, as Theorem "Exact leading unstable difference", in its gap-general form.

At four places the two reports reached a common conclusion by **genuinely different arguments**, and both are preserved and marked in the text:

1. Gap-general local distances: a direct induction at fixed gap, beside the telescoping-plus-unique-minimum route.
2. Uniqueness of the modular fixed point: a contraction bootstrap from `B^0` upward, beside the strictly stronger dynamical theorem (orbit bounds, sharpness, no other cycles).
3. Higher-arrow saturation: a tower-height representation with the practical bound `n + r - 2 >= m`, beside the exact threshold recursion for `sigma_r(m)`.
4. The local Lambert W formula: uniqueness of the small inverse branch, beside a direct verification by substitution.

The software likewise keeps **both** independent oracles — a restricted Euler chain on {2,5}-supported moduli and a general totient chain with a capped exponent lift — and cross-checks them against each other and against literal integer towers.

## Main results

### The decimal transient and the height-2 conjecture

A published conjecture asserts that every prime base ending in 9 has reached its permanent decimal congruence speed by height 2. With the source's height convention, 2749 is the smallest prime counterexample:

- Stable counts C(h), starting at h=0: 0, 3, 6, 8, 10, 12, ...
- Speeds V(a,h), starting at h=1: 3, 3, 2, 2, 2, ...
- Permanent speed: 2. First permanent-speed height: H(2749)=3.

For every integer a ending in 9, put s=v_2(a-1), t=v_2(a+1), u=s+t-1, e=v_5(a+1). The article proves

    C_a(h) = min(s + h*u, h*e),
    V(a)   = min(u, e),
    H(a)   = 1                         if e <= u,
             1 + ceil(s / (e-u))       if e > u.

There are infinitely many prime examples with each prescribed onset H>=3 (Chinese remainder theorem plus Dirichlet), and the relative natural density of integers ending in 9 with H>K is exactly 4/(9*(5*10^(K-1)-1)) for K>=2.

### The diagonal family and OEIS A324017

Let B >= 4 be even, a = B-1, T_0 = 1, T_(h+1) = a^(T_h). For every h >= 0 and every gap r >= 1,

    T_(h+r) - T_h == -2*B^h  (mod B^(h+1)),
    (T_(h+r) - T_h) / B^h == B - 2  (mod B).

So exactly one further stable base-B digit is acquired at each height, and the article also proves:

- the exact prime-adic distance between any two heights, for every gap, by a direct induction;
- the exact base-B precision order `ord_B` of every such difference, with the composite/power-of-two case split;
- the sharp threshold: the residue mod B^m becomes permanent exactly at height m, with no earlier accidental visit;
- uniqueness of the modular fixed point of a^x == x (mod B^m), its compatibility across precisions, and the full dynamics of x -> a^x;
- a factorization-free digit-lifting recurrence with an explicit per-digit formula;
- the inverse limit xi_B and the exact distance from it at every height;
- modular saturation across arbitrarily high Knuth arrow ranks, with `n + r - 2 >= m` as a checkable sufficient condition;
- a sign-sensitive local p-adic Lambert W description of each component of the limit.

The three conjectural comments in the retrieved A324017 entry are resolved: **C1 true** (in a stronger form, without the source's m,k>1 restrictions), **C2 true** (in the stronger form T_h == B^2-B-1 mod B^2 for h>=2), **C3 false** for every n>1 and m>1. The smallest witness is

    3 ^^ 2 = 27       (mod 64),
    3 ^^ 3 = 59       (mod 64),

checkable by hand: 3^8 == 33, 3^16 == 1, 3^27 == 1*33*9*3 == 59 (mod 64).

The correct replacement for C3 is `A(m+1,n) == T_m - 2*B^m (mod B^(m+1))`.

## Status and attribution

This is an unrefereed research note, with complete English proofs and supplementary exact computations. It is not a proof-assistant formalization and does not claim verified priority.

The eventual-speed formula and delayed transients were already studied in prior literature. General modular stabilization of power towers, lifting-the-exponent arguments, and the p-adic Lambert W function are established background, not claimed discoveries here. No claim is made to resolve general analytic tetration, arbitrary Conway chains, unrestricted fast-growing hierarchies, or general modular-tetration complexity.

Both selected sources still labeled their statements as conjectures in the versions examined; no explicit prior resolution was located in the targeted searches, but those searches do not certify worldwide open status.

- The Ripà claim is **Conjecture 2 on journal page 57** of *The congruence speed formula* (2021), and **Conjecture 4.1 on page 14** of arXiv:2208.02622v1 (2022).
- The A324017 entry was retrieved on 19 September 2026; the internal record showed revision `#91, Feb 16 2025` and retained all three conjectural comments.

**Nothing has been submitted to OEIS by this work.** Appendix C of the article proposes replacement text; it has not been sent anywhere.

See `sources.md` for exact references, version distinctions, and the limits of the search.

## Files

- `article.pdf` — the complete merged article.
- `article.tex` — self-contained LaTeX source with inline bibliography.
- `code/tetration.py` — reusable exact arithmetic routines, plus a command-line interface.
- `code/verify.py` — the merged verification suite and data generator.
- `verification.txt` — human-readable record of the successful merged test run.
- `data/verification_report.json` — structured per-suite, per-family test counts and limitations.
- `data/2749_primality_certificate.json` — complete trial-division certificate and optional Pocklington data.
- `data/oeis_a324017_counterexample.json` — exact certificate for the C3 disproof, including the hand-check chain.
- `data/decimal_tower_traces.csv` — counts, speeds, local valuations, and compact residue traces.
- `data/prime_counterexamples_below_100000.csv` — all 23 prime counterexamples below 100000.
- `data/arbitrarily_delayed_prime_progressions.csv` — explicit CRT classes for s=2 through 12, with trial-certified prime examples for s<=6.
- `data/integer_delay_density_counts.csv` — integer counts and exact limiting-density fractions.
- `data/oeis_a324017_values.csv` — stable residues R_m for even B from 4 to 20 and m=1..10, with the previous-height residue and the new digit in each row.
- `data/local_lambert.csv` — the 60 exact local Lambert-series checks.
- `counterexample_certificate.md` — compact proof of the 2749 disproof and its minimality.
- `proof_audit.md` — logical dependencies and important boundary conditions.
- `sources.md` — source locations, version distinctions, and search limitations.
- `Makefile` — optional build/test convenience, with both pdflatex and latexmk paths.

## Reproduce the computations

Python 3.10+ is required; only the standard library is used. The module uses modern built-in generic types, which is the binding constraint. The recorded run used Python 3.14.4.

From this directory:

```sh
python code/verify.py
```

This regenerates the CSV/JSON data and `verification.txt`. The recorded result is
**PASS: 183204 exact assertions** in the merged suite — **118813** from the decimal
families and **64391** from the diagonal families, plus **51414** residue classes
examined inside exhaustive fixed-point searches and not counted as assertions.

Those two subtotals count assertions *executed*, not distinct mathematical facts:
the grids overlap on even radices 4..100 at heights 0..10. **Do not add them**, and
do not quote either of the two originally published totals (118271 and 62649) as the
merged suite's total.

No floating-point arithmetic is used. No high power tower is constructed.

The suite validates in three layers so that no test reuses the routine it checks:
literal constructed integer towers at manageable sizes; two independent modular
oracles (a restricted Euler chain on {2,5}-supported moduli, and a general totient
chain with a capped exponent lift proved valid even for nonunit bases); and only
then the specialized evaluators. All primality claims made for displayed finite
examples are checked deterministically, by trial division or by a sieve.

## Command-line interface

```sh
python code/tetration.py 4 3 --height 2                    # 27
python code/tetration.py 4 3 --height 3                    # 59
python code/tetration.py 10 60 --rank 1000000 --argument 2
python code/tetration.py 10 20                             # the stable residue
```

The third command computes 9 with one million Knuth arrows and right argument 2,
modulo 10^60, and prints

```text
864868894914047889985007525482726503475610748087597392745289
```

The enormous integer is never constructed.

Here `B` is always the **radix**, and the tower base is **B - 1**. Precision is
measured in radix-B digits — not in bits, and not in digits of the tower base.
The one exception is `local_lambert_residue(B, q, K)`, whose precision `K` is
measured in q-adic digits; its docstring states this.

## Build the article

A standard TeX installation with pdfLaTeX, Latin Modern, AMS packages, geometry, microtype, booktabs, longtable, array, xcolor, enumitem, fancyhdr, titlesec, listings, hyperref, and bookmark is sufficient.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, run `make pdf`, or `make pdf-latexmk` for the `latexmk` path. `make test` is an alias for `make verify`. No external images, bibliography processor, shell escape, or downloaded fonts are required.

## Reuse the Python routines

```python
import sys
sys.path.insert(0, "code")
from tetration import DecimalProfile, stable_radix_residue

p = DecimalProfile.for_base(2749)
print([p.speed(h) for h in range(1, 7)])  # [3, 3, 2, 2, 2, 2]
print(p.onset)                            # 3
print(stable_radix_residue(12, 4))        # 16115
```

The diagonal-family routines:

```python
from tetration import (
    stable_residue, tetration_mod, knuth_mod,
    difference_residue, predicted_prime_distance,
    local_lambert_residue, capped_hyper,
)

assert tetration_mod(4, 2, 3) == 27
assert tetration_mod(4, 3, 3) == 59
assert stable_residue(4, 3) == 59            # alias of stable_radix_residue
assert difference_residue(4, 2, 1) == 2      # = B - 2
assert predicted_prime_distance(4, 2, 2) == 5
assert knuth_mod(10, 10**100, 2, 20) == stable_residue(10, 20)
assert local_lambert_residue(6, 2, 9) == stable_residue(6, 9) % 512
```

`stable_radix_residue` is the documented public name; `stable_residue` is an alias
kept so that the second source package's API keeps working.

Factorization is used only by diagnostic and verification helpers
(`factor_trial`, `local_lines`, `predicted_prime_distance`,
`local_lambert_residue`, and the test oracle), never by the production tetration
or higher-arrow evaluators.

## Important domain and precision restrictions

`DecimalProfile.for_base` is for positive integer bases ending in 9, not for arbitrary integer bases. `stable_radix_residue`, `tetration_mod`, `difference_residue`, `predicted_prime_distance` and `knuth_mod` all require an even radix B>=4 and use tower base B-1; the excluded B=2 is the trivial constant base-1 tower. General-radix formulas require every prime divisor of the radix to divide a*a-1.

`capped_hyper` has the separate domain a >= 3. The rank bound must not be extended to base 2, because 2 ↑^r 2 = 4 for every positive rank r.

`residue_towers` is deliberately not a generic modular-tetration solver: it checks the sufficient condition pow(a, modulus, modulus)==1 and rejects unsupported inputs. Reducing a tower exponent modulo its output modulus without a suitable period is generally wrong — for instance 2^3 is not congruent to 2^(3+3) modulo 3.

`valuation(0,p)` is rejected: a zero residue can indicate insufficient working precision. The compact 16-digit display columns in `decimal_tower_traces.csv` are not used to infer large valuations; those valuations were checked at 100-digit precision.

The restriction a = B-1 is precisely why none of this is an unrestricted fast modular-tetration algorithm. Hittmeir reduces the computation of squarefree parts of integers to general modular tetration in deterministic polynomial time; nothing here provides a general fast evaluator.

Finite tests do not prove the universal, infinitude, or density results. Those proofs are in the article. The density formula is for integers ending in 9, not for primes.
