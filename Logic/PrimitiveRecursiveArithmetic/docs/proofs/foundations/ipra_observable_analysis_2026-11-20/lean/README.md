# Checked finite kernels and explicit formalization specifications

This directory builds with **Lean 4.32.0**, without Mathlib or any other
external Lean package:

```sh
lake build
```

The toolchain is pinned in `lean-toolchain`. The completed build is recorded
in `build.log`; the exact compiler version and source-audit results are in
`verification.json`.

## What is proved

| Module | Kernel-checked result |
| --- | --- |
| `ObservableAnalysis/Neumann.lean` | For every possibly noncommutative ring and every finite `n`, both `(1-R) S_n = 1-R^n` and `S_n (1-R) = 1-R^n`. |
| `ObservableAnalysis/Neumann.lean` | If `D*D=0`, then `D` commutes with `R=1-D*h-h*D`, and the finite corrected contraction `H_n=h*S_n(R)` obeys `D*H_n+H_n*D=1-R^n`. |
| `ObservableAnalysis/Budget.lean` | Finite rational sums commute; pointwise inequalities pass to the finite sum. |
| `ObservableAnalysis/Budget.lean` | Nonnegative weights satisfying `W=b+transpose(L)*W` certify the final bound `b·e ≤ W·delta` from `e ≤ delta+L*e`. |
| `ObservableAnalysis/Budget.lean` | The same bound follows from the supersolution `b+transpose(L)*W ≤ W`, provided `e` is also nonnegative. This verifier does not require acyclicity. |
| `ObservableAnalysis/FiniteMinimum.lean` | The explicit bounded rational argmin returns an index within the table and an actual minimum. Uniform two-sided rational error in the table gives the same error in its minimum. |
| `ObservableAnalysis/Blueprint.lean` | The `BudgetCertificate.sound` bridge instantiates the proved supersolution verifier. |

There are **no `sorry` proof terms, no admitted theorems, and no new axiom
declarations**. Structure fields expressing laws are explicit hypotheses;
the blueprint supplies no global instances satisfying unproved laws.

## What is not claimed

The complete analytic framework is **not fully Lean-formalized**, and this
is **not a formal proof that the Lean developments are interpretable in
iPRA**. In particular, the completion, L1, effective Vitali, functional
calculus and continuous-model theorems need the remaining work listed in
`ProofRoadmap.md`. Construction and verification of an iPRA proof compiler
also remain unimplemented.

`PRCode` gives ordinary primitive-recursive syntax, indexed by arity.
Its Lean interpreter `PRCode.eval` is a **metatheoretic** evaluator over
arbitrary syntax. It is **not a primitive-recursive universal evaluator**.
An iPRA instance must expand one externally fixed recipe into its own
primitive-recursive definition. Quantification over Lean functions and
types in schematic theorems is likewise not internal higher-order
quantification in iPRA.

`FiniteNetData.cover` is a specification about a supplied finite net. The
finite bound permits a bounded scan only after its decidable comparison
predicate has been implemented as a fixed PR recipe. It is not a compactness
or choice axiom.

## Foundational dependencies

The source explicitly runs `#print axioms` on the main checked kernels.

* The abstract ring/Neumann development reports only `propext` and, for
  some results, `Quot.sound`. It does not depend on `Classical.choice`.
* The concrete rational budget and minimum results report `propext`,
  `Classical.choice`, and `Quot.sound`. `Classical.choice` is inherited from
  Lean 4.32.0's `Rat` arithmetic lemmas themselves, including
  `Rat.add_assoc` and `Rat.le_trans`. It is not concealed or claimed absent.
* The PR interpreter reports `propext` only.

These are Lean metatheory dependencies. The human iPRA argument instead
uses natural-number encodings, cross-multiplied rational inequalities, and
quantifier-free finite invariants. Replacing the rational convenience layer
by a verified constructive coding layer, and checking the resulting
object-theory derivations, are distinct remaining tasks.

## Main exact definitions

`geometricSum R 0=0` and
`geometricSum R (n+1)=geometricSum R n+R^n`.

`sumQ f 0=0` and `sumQ f (n+1)=sumQ f n+f n`.

`argminQ f n` minimizes the nonempty table `f 0,...,f n`; ties choose the
earlier recursive candidate. The formal theorem proves optimality and a
bound, but does not separately assert least-index minimality.

In `weighted_budget`, all summation bounds are exclusive. The reverse
weight producer for a triangular graph belongs to the paper's algorithm;
the checked theorem verifies any supplied weight solution. For the
supersolution theorem it verifies any supplied inequality certificate.

## Files to retain

The `.lean` sources, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`,
this README, `ProofRoadmap.md`, `build.log`, and `verification.json` suffice.
Generated `.lake` build caches need not be included in the research archive.
