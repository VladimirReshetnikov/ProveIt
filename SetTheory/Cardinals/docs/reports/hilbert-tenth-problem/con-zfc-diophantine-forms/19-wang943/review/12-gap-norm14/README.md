# Smaller Diophantine forms of ZFC consistency

Research synthesis prepared for Vladimir Reshetnikov's ProveIt repository,
22 October 2026. The inspected repository snapshot is
`3b201cdea32d2c816f5f3d20734051f25fd3ef14`.

## Main result

This contribution gives explicit fixed polynomials and systems whose
unsolvability, in the specified domain, is equivalent to `Con(ZFC)` by an
ordinary mathematical proof formalizable in ZFC. It combines the eight
existing fixed-instance packages with several further simplifications.

The recommended compact system has **15 positive unknowns, 6 equations,
maximum degree 22, and 61 arithmetic operations**. If the number of unknowns
is the priority, the new auxiliary-gap norm gives **one degree-219 equation
in 14 positive unknowns with 75 operations**. A lower-degree presentation
uses **32 positive unknowns and 23 quadratic equations**, or their single
quartic sum of squares. All use the same four fixed coefficients.

The coefficient compiler removes the four unused corners of its local
windows. Its exact selector count is `38,256,607,897`; the bit length of
`B-1` is `5^36`, compared with `5^67` in the raw blank-input source package.
This is an exact reduction by a factor `5^31`. The coefficients are given
by closed finite recipes and remain far too large to expand.

There is no global minimality claim. The known nine-natural-variable and
eleven-integer-variable general representations are different constructions
with substantially different degree and coefficient tradeoffs. The gains
here concern the literal short-circuit family in the supplied repository.

## Read first

- `report.pdf`: the article, including equations, proofs, comparison tables,
  exact coefficient definitions, and verification scope.
- `report.tex`, `root_elimination.tex`, `gap_auxiliary.tex`, and
  `gap_root_elimination.tex`, together with `coefficient_recipe.tex`: editable
  article sources. Keep all five TeX files together.
- `verification.json`: the fresh finite-audit receipt and a machine-readable
  census of all emitted arithmetic presentations.
- `provenance.json`: pinned source paths, exact Git blob identities, SHA-256
  hashes, coefficient-port binding, and inherited proof dependencies.

## Main positive-domain tradeoffs

An operation is one binary `+`, `-`, or `*`, including multiplication by a
fixed numeral. Reuse and system comparisons are free. These are arithmetic
circuit sizes, not bit-complexity bounds.

| Presentation | Unknowns | Equations | Exact degree | Operations | Packet |
|---|---:|---:|---:|---:|---|
| Gap root norm | 14 | 1 | 219 | 75 | `arithmetic/blank14_gap_norm75.json` |
| Outer root norm | 14 | 1 | 342 | 73 | `arithmetic/blank14_outer73.json` |
| Ordinary system | 15 | 6 | 28 maximum | 60 | `arithmetic/ordinary_blank_system60.json` |
| Gap system | 15 | 6 | 22 maximum | 61 | `arithmetic/ordinary_gap_system61.json` |
| Ordinary product | 15 | 1 | 99 | 69 | `arithmetic/ordinary_blank69.json` |
| Gap product | 15 | 1 | 93 | 70 | `arithmetic/ordinary_gap70.json` |
| Ordinary sum of squares | 15 | 1 | 56 | 77 | `arithmetic/ordinary_blank_sos77.json` |
| Gap sum of squares | 15 | 1 | 44 | 78 | `arithmetic/ordinary_gap_sos78.json` |
| Quadratic system | 32 | 23 | 2 maximum | not optimized | `quadratic/quartic32.json` |
| Its sum of squares | 32 | 1 | 4 | not optimized | same packet |

The earlier local root norm, degree 293 at 75 operations, and the direct
gap outer norm, degree 268 at 75 operations, are retained as reproducible
intermediate comparisons. The degree-219 gap norm dominates both on these
metrics. It does not dominate the 73-operation outer norm.

The source package's 67-operation degree-155 polynomial remains useful if
operation count alone is the objective. The present contribution does not
claim a lower count than 67 for a single positive-domain equation.

## Unrestricted integer domains

The signed proof leaves only nine original coordinates requiring
positivity. Replace each independently by

`Pos(u,v,t) = 1 + u*u + v*v + t*(t+1)`.

This is positive on integers and represents every positive integer; the
article gives the three-square proof of surjectivity. It leads to the
following explicit alternatives:

| Presentation | Integer unknowns | Equations | Exact degree | Operations |
|---|---:|---:|---:|---:|
| Gap root norm | 32 | 1 | 434 | 138 |
| Outer root norm | 32 | 1 | 680 | 136 |
| Gap system | 33 | 6 | 44 maximum | 124 |
| Gap product | 33 | 1 | 179 | 133 |
| Gap sum of squares | 33 | 1 | 88 | 141 |
| Lifted quadratic system | 50 | 23 | 4 maximum | not optimized |
| Its sum of squares | 50 | 1 | 8 | not optimized |

The corresponding arithmetic packets have suffix `_over_Z32` or
`_over_Z33`. The 50-integer residuals are in `quadratic/quartic32.json`.
Nonnegative-domain versions instead follow by replacing every positive
unknown by `n+1`, without changing the number of unknowns or degree.

## Four fixed coefficients, with no hidden input

`compiler/cross_constants.json` defines the default coefficient quartet:

| Arithmetic port | Meaning |
|---|---|
| `Bm1` | `B-1` |
| `Kconstant` | `DC+B*DR` |
| `MC` | native word mask |
| `MF` | `MF_native+B-1`, the **shifted** source port |

The main article uses the symbols `beta`, `K`, `M_C`, and `M_F^src` for
these four ports. `quadratic/quartic32.json` calls the first two `beta` and
`K0`. All four must be bound together. The original coherent package-06
quartet is an alternative for the arithmetic theorems; mixing old and new
coefficients is not justified.

The recipe includes the literal 430-transition K215 table, its complete
439-symbol local predicate, a fixed enumeration of valid five-cell crosses,
and finite sums with fixed bounds. Exponentiation occurs only in the
definition of fixed integer coefficients. Every unknown enters polynomially.
No universal-program parameter, proof-search input, or unevaluated truth
value is supplied as an additional coefficient.

The canonical machine table's SHA-256 is
`fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.

## Reproduce

Python 3.10 or later and its standard library suffice for the finite checks.
No network, proof assistant, computer algebra package, or giant-integer
coefficient allocation is needed.

```bash
python3 reproduce.py
```

Run without `-O`, because some exact symbolic checks use assertions.
The script authenticates 24 retained source files, regenerates all 20
arithmetic presentations and the quadratic packet, and runs seven audit
stages. Individual logs are placed in `verification/`.

To compile the article, install a normal TeX Live setup containing pdfLaTeX,
AMS packages, Latin Modern, geometry, booktabs, hyperref, microtype,
enumitem, and listings, then run:

```bash
make report
```

`make all` runs both the finite verification and the three-pass PDF build.
`make clean` removes only TeX auxiliary files. `SHA256SUMS.txt` authenticates
the delivered files; regenerated PDFs may differ in timestamps or metadata.

## What is proved and what is checked

The mathematical route is:

1. The existing calibrated K215 machine halts on blank tape exactly when
   the specified ZFC proof presentation has a finite refutation.
2. A marked valid periodic cross tableau is equivalent to a finite blank
   halting computation. Removing unused corners preserves the local rule.
3. The revised native compiler and Pell equations are equivalent to that
   tableau problem. The proof includes arbitrary-bit synchronization and
   dummy tuning of the actual packed index.
4. Ordinary strong norms, root elimination, the auxiliary gap, quadratic
   lifting, and positivity substitutions preserve the stated solvability
   equivalences. Nonzero-denominator and signed-root cases are addressed.

Negating the resulting existence equivalence gives the requested theorem
in ZFC. It does not require an assumption that ZFC is consistent.

The finite checks cover live circuit counts, exact integer/rational formula
evaluations, symbolic quadratic identities, nonzero leading-form
certificates and degree diagnostics, source-table identity, all thirteen
center categories, 32 helical control presentations, 26,106 cyclic lift
checks, 100,384 small cross-word candidates, and 16,224 sparse convolution
tests. A separately derived interval audit covers all 38,256,610,097 actual
native positions with 396 interval intersection checks. These quantities
are reproduced in the receipts.

The unbounded Pell/compiler arguments are ordinary mathematical proofs
with explicitly retained or pinned dependencies. This contribution does
not contain a new Lean/Rocq proof of the Diophantine equivalence and does
not rerun the repository's full K215 proof-assistant builds. No accepting
computation of actual K215 is exhibited, no consistency result is inferred
from finite tests, and no impossibly large coefficient is expanded.

## Repository integration and attribution

The folder can be incorporated as a new report package beside the eight
source packages. Its scripts use paths relative to themselves or the
package root. Retain the TeX sections, `arithmetic/baseline67.json`, the
three inherited compiler support modules, and `compiler/k215.tm` when
moving it. The complete finite-check package is intentionally offline.

See `NOTICE.md`, `LICENSE`, `licenses/LICENSE.Wade`, and
`upstream/K215_NOTICE.md` for attribution and inherited terms. Exact
upstream files are preserved as source evidence. Relative links within
those retained notes refer to their original repository context, whose
pinned URLs are in `provenance.json`.
