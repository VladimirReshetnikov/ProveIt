# Lean sources

## Standalone proofs

The directory's toolchain is Lean 4.32.0. From this directory run

```sh
./check.sh
```

The script builds `FiniteInversion.lean` and checks `FormalSeries.lean` using that build. Both sources use only bundled libraries and were checked under both 4.32.0 and 4.19.0. Set `LEAN` to a compiler executable to select an installation explicitly.

`FiniteInversion.lean` proves generic triangular inversion, pointwise uniqueness, finite chain expansion and vanishing above the row length, divisor cancellation and a separate exponent-vector sum. The signed function on positive integers is defined by the divisor recurrence. Relating that function in Lean to ProveIt's prime-valuation terms requires the object-theory comparison described in the paper. The example at the end of the divisor specialization reduces a finite table by kernel conversion.

`FormalSeries.lean` proves the coefficient identity for the geometric ray, the universal Möbius Lambert coefficient identity, the scaled logarithmic coefficient formula, and the characterization of the factorial-scaled formal exponential by its recurrence.

## Existing embedded iPRA proofs

`ProveItAudit.lean` displays the types of the relevant embedded-theory declarations and prints the axiom dependencies of selected declarations. Its names and imports were checked against the pinned sources. The external package build was not rerun for this packet.

Use a checkout of https://github.com/VladimirReshetnikov/ProveIt at `65b76a5b8aa87ecad4103c2d287eff5660d3c84c`. In the checkout root, after configuring its declared dependencies, run

```sh
lake build IPRADerivations.AnalyticNumberTheory.MobiusInversion \
  IPRADerivations.AnalyticNumberTheory.SummatoryPhi \
  IPRADerivations.AnalyticNumberTheory.MuLambda \
  IPRADerivations.AnalyticNumberTheory.PsiModulus \
  IPRADerivations.AnalyticNumberTheory.FinalPNT
lake env lean /path/to/packet/lean/ProveItAudit.lean
```

Replace the absolute path in the last command with the location of the extracted file. The document explains how to specialize the declarations at concrete terms, compile a bounded induction invariant, and construct the additional deductions.
