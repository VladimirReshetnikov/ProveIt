# Natural densities of the three additive complexities of the Tribonacci word

**Proposed solution to Remark 19 of Popoli–Shallit–Stipulanti, _Additive word complexity and Walnut_, arXiv:2410.02409v1.**

Prepared on 20 September 2026. This is an AI-assisted research draft, not an independently refereed or proof-assistant-formalized result. See `STATUS.md` for the precise claim boundaries.

## Result

Let `t` be the fixed point of `0 -> 01, 1 -> 02, 2 -> 0`. For `n >= 1`, let `a(n)` be the number of different sums of its contiguous length-`n` factors. Set `a(0)=1`.

Let beta be the real root greater than 1 of `beta^3 = beta^2 + beta + 1`. For `j=3,4,5`, define `C_j(N) = #{0 <= n < N: a(n)=j}`. The article proves, subject to the disclosed verification status,

```
C_j(N) = d_j N + O(N^theta),
theta = log(7/5)/log(beta) = 0.552156973218551343...

d_3 = (21 beta^2 - 38 beta + 5)/22 = 0.2795270194496756518...
d_4 = (-55 beta^2 + 72 beta + 67)/22 = 0.6074990518443881530...
d_5 = (17 beta^2 - 17 beta - 25)/11 = 0.1129739287059361952...
```

These are ordinary natural densities over **all integer cutoffs**, not only the Tribonacci-number subsequence. The average additive complexity tends to `(13 beta^2 + 4 beta + 33)/22 = 3.833446909256260543...`.

The known possible values `{3,4,5}`, the existence of a 76-state automaton, and the co-decomposition method are **not** claimed as new. The proposed contribution is the explicit density evaluation, the uniform all-cutoff proof, and the error estimate.

## Start here

- Read `article.pdf`; editable source is `article.tex`.
- The main proof is in Sections 2–5.
- Full transition and eigenvector tables are printed in the appendices.
- Source provenance is in `notes/sources.md`.
- Random selection and manifest exclusions are documented in `notes/manifest_audit.md`.

## Run the exact verifier

Python 3.10 or later is intended; the recorded run used Python 3.13.5. The main verifier and counting program require **only the standard library**. They do not require network access, Walnut, NumPy, or SymPy.

From this directory:

```sh
python3 code/verify.py
```

The script regenerates the co-decomposition closure and the quotient automaton, compares them with the stored data, verifies graph structure and algebraic identities, checks every entry of the matrix annihilator, and performs the independent factor and counting cross-checks. It writes `data/verification_results.json` and prints the same report. The archived standard run is also in `data/verification_log.txt`.

All checks remain active under `python3 -O`. An optimized-mode run is recorded separately in `data/verification_optimized_results.json` and `data/verification_optimized_log.txt`.

For a shorter diagnostic run (not the archived full cross-check scope):

```sh
python3 code/verify.py --factor-limit 100 --count-limit 1000 --output /tmp/tribonacci-quick-check.json
```

## Compute values and exact interval counts

```sh
python3 code/tribonacci.py --value 123456789
python3 code/tribonacci.py --count 1000000000000000000
```

The `--count N` command returns counts over the half-open interval `[0,N)`, including the one length with value `1` when `N>0`. The output counts sum to `N`. Integers are arbitrary precision.

As a Python module:

```python
import sys
sys.path.insert(0, "code")
from tribonacci import complexity, prefix_counts

print(complexity(123456789))
print(prefix_counts(10**100))
```

## Optional symbolic derivation

The independent exact verifier does not need this step. To reproduce the discovery-side symbolic calculation, install/use SymPy (tested version 1.14.0) and run:

```sh
python3 code/derive_spectrum.py --output /tmp/tribonacci-derived.json
```

This computes the characteristic polynomial factorization, solves for the left eigenvector in the cubic field, and derives the rational cutoff generating functions. The archived symbolic output is `data/derivation_results.json`.

The proof only needs the exact integer identity `p(A)=0`; it does not rely on trusting the symbolic characteristic-polynomial routine.

## Rebuild tables and PDF

```sh
python3 code/make_tables.py
pdflatex -halt-on-error article.tex
pdflatex -halt-on-error article.tex
```

The PDF uses ordinary TeX Live packages and Latin Modern fonts. No font files are distributed. Tables are generated from the same JSON certificates that the verifier checks. `make pdf`, `make verify`, and `make tables` are alternatives; the Makefile puts TeX intermediates in `build/`.

## Data layout

`data/co_decomposition.json` holds 56 word pairs, 277 sets, both raw transitions, relative sum sets, the 296 valid-language product states and their quotient map. Words use the literal alphabet `0,1,2`.

`data/automaton.json` holds 76 live states with two transition columns, outputs, and initial state 0. A target `-1` means invalid. Leading zeros are allowed. The machine is independently reconstructed, not copied from a source's original automaton file.

`data/eigenvector.json` uses denominator 44; each triple `[u,w,z]` represents `(u+w*beta+z*beta^2)/44`.

`data/generating_functions.json` stores coefficient arrays in **ascending powers**, constant coefficient first. The output-1 generating function is `1/(1-z)`; the other three share the denominator printed in the article.

`data/prefix_counts.csv`, `data/large_prefix_counts.json`, and `data/tribonacci_cutoff_counts.csv` contain exact counts, not estimates. `data/constants.json` contains presentation-only decimal approximations.

`data/selection.json` preserves the original single random area selection: item 68 of 120, **Combinatorics on words**. `python3 code/area_selection.py` audits that record without drawing again. `--draw --output NEW_PATH` makes a separate new random record, refuses to overwrite an existing file, and does not change the historical selection.

## What verification does and does not establish

The finite closure, quotient diagram, eigenvector equations and matrix annihilator are proof certificates. The article gives the infinite-word interpretation and the uniform asymptotic argument connecting them to natural densities.

The independent all-factor check covers every length 1–2048 through a proved five-pair-image covering lemma and examines 93,070,336 windows. It is additional testing, not the source of the all-index claim.

No claim is made that the error exponent is optimal, that the literature search proves global priority, or that the argument settles general additive-complexity regularity questions.
