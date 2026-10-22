# Twelve positive unknowns for Con(ZFC)

**Research contribution, 22 October 2026.** This package combines the current
ProveIt blank-machine compiler with new root-combination, signed-domain, and
finite-alphabet reductions. It contains an ordinary mathematical proof that
ZFC proves the equivalence

\[
\bigl(\nexists\mathbf x\in\mathbb Z_{>0}^{12}:P_{12}(\mathbf x)=0\bigr)
\quad\longleftrightarrow\quad\operatorname{Con}(\mathrm{ZFC}).
\]

It also supplies an explicit equation in **26 unrestricted integers**, and
several smaller-degree alternatives in **27 unrestricted integers**, with
the same absence-of-solutions equivalence.

Read **[report.pdf](report.pdf)** for the complete article, including the
literal norm formula and the exact coefficient recipe. Its editable source
is **[report.tex](report.tex)** with four files in `sections/`.

## Results and tradeoffs

| New construction | Domain / unknowns | Equations | Exact total degree | Binary arithmetic operations |
|---|---|---:|---:|---:|
| Separating-root product | 12 positive integers | 1 | 1369 | 144 |
| Separating-root system | 12 positive integers | 3 | 1360 | 140 |
| Separating-root sum of squares | 12 positive integers | 1 | 2720 | 147 |
| Robust separating-root product | 26 integers | 1 | 3560 | 199 |
| Robust separating-root system | 26 integers | 3 | 3544 | 195 |
| Robust separating-root sum of squares | 26 integers | 1 | 7088 | 202 |
| Ordinary signed-scale product | 27 integers | 1 | 172 | 116 |
| Ordinary signed-scale system | 27 integers | 6 | 46 | 107 |
| Ordinary signed-scale sum of squares | 27 integers | 1 | 92 | 124 |
| Normalized signed-scale product | 27 integers | 1 | 274 | 114 |
| Reduced normalized signed-scale product | 27 integers | 1 | 216 | 115 |

For systems, the degree is the largest residual degree. Operations count all
binary additions, subtractions and multiplications, including multiplication
by numerals. Final comparisons are free, as in the source catalogue. The
explicit residual systems cost 142 operations for 12 positive unknowns and
197 operations for 26 unrestricted integers.

The source comparison is pinned to
[`f0ae4e0991ca44a7bb4e5671d42e33d775e48035`](https://github.com/VladimirReshetnikov/ProveIt/tree/f0ae4e0991ca44a7bb4e5671d42e33d775e48035).
Its reviewed explicit frontier has 13-positive-variable products, a
29-integer ordinary product, and a 67-operation product in 15 positive
variables. The new 12-variable result improves coordinate count while
increasing degree and arithmetic size. The new 27-integer ordinary product
improves all three displayed numerical measures over the existing
29-integer ordinary product (degree 188, 121 operations). The 26-integer
variant saves another coordinate at a substantial degree cost.

**No global minimality is claimed.** Classical universal constructions over
nonnegative integers already use nine variables, with different degree and
coefficient tradeoffs. The present theorem concerns these explicitly bound
K215 polynomials; it does not assert a new universal pair.

## The mathematical reduction

The actual twelve positive coordinates are

\[
J,F,\alpha,z,h,i,T,s,w,\eta,\zeta,t.
\]

All other symbols in the article are polynomial abbreviations. The single
equation has the form

\[
P_{12}=N_kN_t(1+\mathcal R_{12})-1=0,
\]

where the retained index and transport factors are

\[
N_k=k-hXY-R,\qquad
N_t=(\kappa+w)C+q-F-z(q-1).
\]

The literal degree-16 norm in the last variable `t` is expanded using two
successive quadratic norms in the article and in `data/polynomial12.json`.
Its conceptual factorization is

\[
\mathcal R_{12}=d^8H^{16}
\prod(t-y-M\tau-N\gamma),
\]

over sixteen algebraic branches. The explicit positive weights separate all
those branches. If the product vanishes at an integer `t`, Galois invariance
and separation force the reconstructed auxiliary witnesses to be rational.
The special strong multiplier `H*i` ensures `gcd(H,d)=1`; together with
`N = 1 mod H`, this upgrades the rational witnesses to integers. The
inherited signed Pell compiler then applies. Conversely, a suitable period
of the Pell matrix modulo `H*c^2` supplies the required multiplier for every
canonical accepting tableau. The norm is a square modulo four, which makes
the single product equivalent to the three retained equations.

The 27-integer construction proves that a negative odd half-binomial scale
cannot satisfy the equations. Canonical solutions have odd positive scale
because the packed rank obeys `popcount(R) = 3*log2(q) + 2`. Only six source
ports then need the positive surjection

\[
\operatorname{Pos}(u,v,r)=1+u^2+v^2+r(r+1).
\]

The 26-integer construction combines that result with the root norm, using
larger weights that work for signed `T`, `H`, and `s`. Its proof separately
handles the `T=0` and `X=0` cases. Seven source ports remain positive;
`i` is not required to be odd in this version.

## Fixed coefficients

`coefficients/T5263_CONSTANTS.json` specifies four exact fixed integers,
derived from the literal 215-state, 430-transition machine. The refined
alphabet has **5263 tiles**, versus 37075 in the reviewed T4 package, and
uses

\[
B=2^{5^{16}},\qquad\beta=B-1.
\]

Thus `beta` has **152,587,890,625 bits**, exactly one twenty-fifth of the
previous `2^(5^18)-1` bit length. The coefficients remain enormous; their
expanded numerals are intentionally not materialized. These finite recipes
specify constants, not exponentials involving an unknown.

**Bind the whole coefficient tuple.** `COEFFICIENT_BINDING.json` maps the
different port names in the circuit families to this one recipe. In
particular, the circuit port `MF` is the **shifted** mask
`MF_native + B - 1`. The native mask is used in the population proofs.
Do not substitute only `B` or combine masks from different backends.

The refined compiler proof checks the changed rank-tuning unit, the actual
packed rank, carry bounds, all cyclic alignments, the origin marker, and
arbitrarily large powers-of-five padding. The coefficient adapter is
therefore part of the proof, not merely a smaller tile count.

## Reproduce

From this directory:

```sh
python3 reproduce.py
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

The Python code requires Python 3.10 or later and no third-party packages.
It regenerates the arithmetic circuits and compiler data into a temporary
directory, compares the results byte for byte with the bundled files,
checks source hashes and the literal transition list, and runs an
independently implemented quotient-algebra check of the 26-integer norm.
The result is written to `verification/REPRODUCTION.json`. Do not use
`python -O`, because some independent checkers use assertions.
The distribution manifest covers the static artifacts; the reproduction
receipt is regenerated and is therefore excluded from that manifest.

`make verify` and `make pdf` provide the corresponding targets. The PDF
requires standard LaTeX packages; no network access or repository checkout
is needed for these finite checks or the report build.

## Archive map

| Path | Contents |
|---|---|
| `report.tex`, `sections/`, `report.pdf` | Complete article and compiled PDF |
| `code/build_twelve.py` | Fully substituted positive-variable circuits |
| `code/build_integer26.py` | Fully substituted 26-integer circuits |
| `code/build_integer27.py`, `code/inputs/` | 27-integer circuits and their pinned source arithmetic |
| `code/audit_integer26.py` | Independent generic quotient-algebra norm check |
| `data/` | JSON circuits, exact operation ledgers and arithmetic receipts |
| `coefficients/` | Exact recipe, finite alphabet, verifier and literal machine |
| `proofs/` | New proofs and independent mathematical audit notes |
| `upstream/` | Selected unchanged inherited proofs and source packets |
| `comparison.csv` | Machine-readable numerical comparison |
| `SOURCE_MANIFEST.json` | Source paths and verified Git/SHA identities |
| `MANIFEST.sha256` | Distribution checksums |
| `NOTICE.md`, `licenses/` | Provenance, scope and retained licenses |

## Verification boundary

The new work consists of ordinary mathematical proofs formalizable in ZFC,
supported by finite executable checks and independent reviews. It is **not
a new end-to-end Lean or Rocq formalization**. The copied Lean/Rocq endpoint
logs are inherited upstream records; neither kernel was freshly rebuilt for
this package. The complete upstream development remains the source for
those formal endpoint theorems.

The consistency predicate means absence of a finite syntactic ZFC
refutation. The `B` in the endpoint's `BProv` refers to background axioms,
not a bound on proof length. The proof of the equivalence does not assume
or prove Con(ZFC), and the synthetic arithmetic fixtures do not claim an
actual solution for the K215 coefficients.

This package is ready to review as a further contribution alongside the
wave-2 packages 09–15. It does not modify or replace those source packages.
