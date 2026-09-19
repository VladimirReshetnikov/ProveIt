# Delayed stabilization of power towers

Research package — September 19, 2026, version 1.0.

## Main result

A published conjecture asserts that every prime base ending in 9 has reached its permanent decimal congruence speed by height 2. With the source's height convention, 2749 is the smallest prime counterexample:

- Stable counts C(h), starting at h=0: 0, 3, 6, 8, 10, 12, ...
- Speeds V(a,h), starting at h=1: 3, 3, 2, 2, 2, ...
- Permanent speed: 2. First permanent-speed height: H(2749)=3.

For every integer a ending in 9, put s=v_2(a-1), t=v_2(a+1), u=s+t-1, e=v_5(a+1). The article proves

    C_a(h) = min(s + h*u, h*e),
    V(a)   = min(u, e),
    H(a)   = 1                         if e <= u,
             1 + ceil(s / (e-u))       if e > u.

There are infinitely many prime examples with each prescribed onset H>=3. The proof uses the Chinese remainder theorem and Dirichlet's theorem. The article also proves an integer-density theorem and a sharp radix congruence resolving the three conjectural comments in OEIS A324017.

## Status and attribution

This is an unrefereed research note, with complete English proofs and supplementary exact computations. It is not a proof-assistant formalization and does not claim verified priority. The eventual-speed formula and delayed transients were already studied in prior literature. The selected conjecture remains labeled as a conjecture in the source version examined; no explicit prior resolution was located in the targeted search, but the search does not certify worldwide open status.

The conjecture is **Conjecture 2 on journal page 57** of Marco Ripà's *The congruence speed formula* (2021), and **Conjecture 4.1 on page 14** of arXiv:2208.02622v1 (2022). See `sources.md` for exact references and the later paper considered in the literature audit.

## Files

- `article.pdf` — the complete article.
- `article.tex` — self-contained LaTeX source with inline bibliography.
- `code/tetration.py` — reusable exact arithmetic routines.
- `code/verify.py` — verification suite and data generator.
- `verification.txt` — human-readable record of the successful test run.
- `data/verification_report.json` — structured test counts and limitations.
- `data/2749_primality_certificate.json` — complete trial-division certificate and optional Pocklington data.
- `data/decimal_tower_traces.csv` — counts, speeds, local valuations, and compact residue traces.
- `data/prime_counterexamples_below_100000.csv` — all 23 prime counterexamples below 100000.
- `data/arbitrarily_delayed_prime_progressions.csv` — explicit CRT classes for s=2 through 12, with trial-certified prime examples for s<=6.
- `data/integer_delay_density_counts.csv` — integer counts and exact limiting-density fractions.
- `data/oeis_a324017_values.csv` — computed array values for n=2 through 10 and heights 1 through 8.
- `counterexample_certificate.md` — compact proof of the disproof and minimality.
- `proof_audit.md` — logical dependencies and important boundary conditions.
- `sources.md` — source locations, version distinctions, and search limitations.
- `Makefile` — optional build/test convenience.

## Reproduce the computations

Python 3.10+ is sufficient; only the standard library is used. The recorded run used Python 3.13.5.

From this directory:

```sh
python code/verify.py
```

This regenerates the CSV/JSON data and `verification.txt`. The recorded result is **PASS: 118271 exact assertions**. No floating-point arithmetic is used. No high power tower is constructed.

The verification suite includes an Euler-totient-chain reference evaluator independent of the guarded fixed-modulus residue iterator. All primality claims made for the displayed finite examples are checked deterministically, by trial division or by a sieve.

## Build the article

A standard TeX installation with pdfLaTeX, Latin Modern, AMS packages, geometry, microtype, booktabs, longtable, xcolor, enumitem, fancyhdr, titlesec, listings, hyperref, and bookmark is sufficient.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, run `make pdf`. No external images, bibliography processor, shell escape, or downloaded fonts are required.

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

## Important domain and precision restrictions

`DecimalProfile.for_base` is for positive integer bases ending in 9, not for arbitrary integer bases. `stable_radix_residue` requires an even radix B>=4 and uses tower base B-1. General-radix formulas require every prime divisor of the radix to divide a*a-1.

`residue_towers` is deliberately not a generic modular-tetration solver: it checks the sufficient condition pow(a, modulus, modulus)==1 and rejects unsupported inputs. Reducing a tower exponent modulo its output modulus without a suitable period is generally wrong.

`valuation(0,p)` is rejected: a zero residue can indicate insufficient working precision. The compact 16-digit display columns in `decimal_tower_traces.csv` are not used to infer large valuations; those valuations were checked at 100-digit precision.

Finite tests do not prove the universal, infinitude, or density results. Those proofs are in the article. The density formula is for integers ending in 9, not for primes.
