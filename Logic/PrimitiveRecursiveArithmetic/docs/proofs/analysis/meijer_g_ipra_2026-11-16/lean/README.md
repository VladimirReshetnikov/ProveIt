# Lean roadmap

This directory is an **outline**, not a completed formalization.

- `FiniteCore.lean` makes the proposed finite data structures and evaluator
  interfaces concrete. It contains `sorry` placeholders and has not been
  compiled in this artifact environment.
- `AnalyticContracts.lean` packages Gamma, logarithm, contour, Mellin, Fubini,
  and transform hypotheses as data. These structures must eventually be
  inhabited by bounded checkers with object-iPRA soundness proofs.
- `ObjectLanguageTargets.lean` names the exact ProveIt imports and records the
  final theorem shapes. It intentionally declares no analytic theorem.
- `ROADMAP.md` gives the module order and trust audit.

The final endpoint is not a theorem about host `Nat`/`Rat`/`Complex`. It is a
closed derivation of type

```lean
[] ⊢[PRAAx] phi
```

in `LeanProofs.ConciseIPRA`, followed only then by `pra_iff_native` if a native
calculus theorem is desired.

Pinned repository commit:
`85afffc93b2abbc1972fdfc98244052cbfbda1b3`.
