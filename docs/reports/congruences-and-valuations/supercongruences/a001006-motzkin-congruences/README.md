# Four Motzkin Congruences

A self-contained mathematical treatment of the four conjectures in Peter
Bala's 10 February 2022 comment in OEIS A001006, with sharp ranges and
reproducible computation. Prepared for Vladimir Reshetnikov, 20 September 2026.

## Read the article

`article.pdf` is the compiled article. `article.tex` is its complete editable
LaTeX source, including references; no external bibliography database or
external graphics are required.

All four targeted formulas are proved. The article also gives:

* the exact first failures beyond the two initial-block ranges;
* a block-transfer theorem at arbitrary prime-power precision;
* arbitrary-multiplier and all-prime-power boundary extensions;
* a prime-modulus digit algorithm, and examples showing why unweighted
  repetition modulo a prime cube is generally false.

The statements are still labeled conjectures in the OEIS comment consulted.
This does not establish their novelty: the article discusses Burns's comment,
Kohen's related mod-p results, and Pan–Sun's stronger central-trinomial theorem.
No assertion of publication priority is made. Nothing has been submitted to
or edited in OEIS.

## Reproduce the computations

Python 3.9 or later is sufficient. There are no third-party dependencies.
The recorded run used Python 3.13.5.

Run these commands from this directory in a terminal (including PowerShell):

```text
python code/verify.py
python code/motzkin.py exact 28
python code/motzkin.py mod 12345678901234567890 97
python code/motzkin.py block 1 3 0 5 3
```

The exact command returns `208023278209`. The final block command returns
`51`, the residue of M_125 modulo 125.

The default verification command is equivalent to:

```text
python code/verify.py --max-index 20000 --prime-limit 97
```

It checks 276,814 equalities or congruences, then recreates the three files
in `data/`. It prints its report to standard output. The included report is
`data/verification.json`. An optional `--output PATH` places newly generated
data elsewhere. The exact oracle deliberately stores large integers, so
raising `--max-index` increases memory consumption substantially.

The checked identities are not used to generate their own expected values.
The main oracle uses exact integer recurrences with checked divisions;
small values are cross-checked against binomial sums and path enumeration.
This is finite verification, not a proof-assistant formalization. The
mathematical proofs are in the article.

## Module interface

Add `code` to the Python import path, or run a script from that directory.

```python
from motzkin import motzkin_mod_prime, trinomial_prime_table

p = 97
table = trinomial_prime_table(p)
n = 10**100 + 123456789
assert motzkin_mod_prime(n, p, table) == 28
```

A supplied table must be the output of `trinomial_prime_table(p)` for the
same prime. Reusing it avoids rebuilding the O(p)-size table for every
query. The evaluator accepts odd primes only; the exact recurrence can of
course be reduced modulo any integer after exact division.

`block_mod_prime_power(m, k, offset, p, precision)` evaluates
M_(m*p**k+offset) modulo p**precision in the block covered by Theorem 3.3.
It requires an odd prime p, m >= 0, 1 <= precision <= k, and
0 <= offset < p**(k-precision+1). It uses smaller exact coefficients,
not a universal prime-power digit algorithm. Its cost still grows with
the local offset and m*p**(precision-1).

## Build the PDF

A current TeX Live or MiKTeX installation with the packages named in the
preamble is sufficient. In a terminal:

```text
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively run `latexmk -pdf article.tex`. The included `Makefile`
provides `make pdf`, `make verify`, and `make clean` where make is available.
Several passes settle the table of contents and theorem references.

## Contents

| Path | Contents |
| --- | --- |
| `article.tex`, `article.pdf` | Complete source and compiled article |
| `code/motzkin.py` | Exact arithmetic, modular algorithms, and CLI |
| `code/verify.py` | Independent finite verification program |
| `data/verification.json` | Recorded successful verification counts |
| `data/sharp_boundaries.csv` | All 36 checked prime-square boundary errors |
| `data/initial_values.csv` | M_n, T_n, U_n, D_n for 0 <= n <= 200 |
| `notes/source_provenance.md` | Target provenance and literature overlap |
| `notes/proof_map.md` | Proof dependencies and theorem-to-conjecture map |
| `notes/proposed_oeis_update.txt` | Draft mathematical update; not submitted |

The U sequence is extended to index zero by U_0=0. D_0=1 is included
separately; for n >= 1, D_n=T_(n-1)+U_(n-1).
