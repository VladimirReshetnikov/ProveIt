# Completion audit: corrected and full Fabius asymptotics

This document records the evidence used to close the small-argument
asymptotic formalization.  It distinguishes the formula printed by Wikipedia,
the necessary periodic correction, and the complete exact-Lambert expansion.

## Printed formula and correction

`Fabius.fabiusWikipediaElementaryMain` is the literal elementary expression
from the Wikipedia *Asymptotic* section: every `log x`, `log (-log x)`, Euler
constant, first Stieltjes constant, and `1 / log x` term is represented with
the printed sign and normalization.

The printed `O(1 / log x)` remainder is not correct without an oscillatory
term.  The formalization defines

```text
lambda(x) = -W_{-1} (-(log 2) x) / log 2
correctedMain(x) = wikipediaMain(x) + negativeLaplacePsi(lambda(x)),
```

where `negativeLaplacePsi` is continuous, one-periodic, centered, and
nonconstant.  Its nonzero-frequency Fourier coefficients are proved to be

```text
-Gamma(-chi_k) * zeta(1-chi_k) / log 2,
chi_k = 2 pi i k / log 2.
```

The source-facing completion theorems are:

- `Fabius.log_fabius_sub_explicitCorrectedWikipediaMain_isBigO`;
- `Fabius.log_fabius_sub_WikipediaElementaryMain_not_isBigO`;
- `Fabius.fabius_isEquivalent_exp_explicitCorrectedWikipediaMain`.

Thus the corrected logarithmic formula has error `O(1 / (-log x))`, while the
same assertion for the elementary formula with the periodic term deleted is
formally false.

## Full expansion

Let `lambda = Fabius.fabiusLambertPhase x`.  For every natural number `N`,
the finite form proved by
`Fabius.log_fabius_sub_sharpLambertExpansion_isBigO` is

```text
log F(x) = fabiusSharpLambertMain(x)
  + sum (j < N), lambda^(-j) * fabiusSaddleLogCoefficient(j, lambda)
  + O(lambda^(-N)).
```

The stronger bundled statement is
`Fabius.log_fabius_sub_sharpLambertMain_hasAsymptoticExpansion`.  Every
coefficient family is continuous, one-periodic, and bounded.  The zeroth
logarithmic coefficient is identically zero.  At `N = 2`, the next coefficient
is identified explicitly by `Fabius.fabiusSharpLambertExpansion_two` as

```text
fabiusFirstSaddleCorrection(lambda) / lambda.
```

This identifies the first explicit correction; no separate claim that this
coefficient function is nonzero is needed for the expansion.

`Fabius.fabiusLambertPhase_sub_literalApproximation_isBigO` independently
expands the exact lower-Lambert phase to every order using `-log x` and
`log (-log x)`.  The full Fabius theorem deliberately retains the exact phase
inside its periodic coefficients.  It does not claim an unproved all-orders
composition obtained by substituting a truncated phase into every oscillatory
coefficient.

## Machine-checked gates

The completion audit uses the following gates from the repository root:

```sh
lake build FabiusFunction
lake env lean Analysis/FabiusFunction/Lean/FabiusFunction/FabiusSharpAsymptotic.lean
lake env lean Analysis/FabiusFunction/Lean/FabiusFunction/FabiusFullAsymptoticExpansion.lean
lake env lean Analysis/FabiusFunction/Lean/FabiusFunction/FabiusLambertAllOrderSmallArgument.lean
```

The public aggregate build completes successfully.  A `Lean.collectAxioms`
scan of every declaration originating in a `FabiusFunction.*` module reported,
at the 141-file snapshot at which that scan was last run, 4,632 constants
including 4,139 theorems, with zero declared axioms, zero `sorryAx`
dependencies, and no unexpected axioms; the union of dependencies was exactly
`propext`, `Classical.choice`, and `Quot.sound`.

The tree has since grown and the axiom scan has not been re-run, so those two
figures are historical.  The current source-level counts, which do not require
a build, are:

| Measure | Count |
| --- | --- |
| Lean files (174 modules plus the root aggregate) | 175 |
| Lines of Lean | 62,411 |
| Top-level `theorem` / `lemma` declarations | 2,967 |
| of which `private` | 537 |
| Public `theorem` / `lemma` declarations | 2,430 |
| Top-level `def` / `abbrev` declarations | 536 |
| Occurrences of `sorry`, `admit`, `axiom`, `opaque` | 0 |

The last row is the one that matters for the completion claim, and it is
re-verified by a source scan of all 175 files.  Re-running `Lean.collectAxioms`
to refresh the first two figures is the outstanding item in this audit.

The complete source-to-theorem mapping remains in
[`PAPER_COVERAGE.md`](PAPER_COVERAGE.md).
