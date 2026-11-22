# Checked rational kernel for quantitative integration

This project builds with **Lean 4.32.0** and has no Mathlib dependency. The four
`.lean` files contain **35 named theorem declarations and 8 checked examples**.
There is no `sorry`, `admit`, or new axiom declaration in them.

These are ordinary Lean theorems about rational finite calculations. They are
**not new derivations in `Prf PRAAx`**, and do not by themselves formalize an
infinite measure space, the L1 completion, or a Radon–Nikodym theorem. The
report and `OBJECT_LANGUAGE_PLAN.md` give the separate route to those endpoints.

## Reproduce

With the pinned toolchain selected by Elan, run `bash replay.sh`. With a standalone
Lean distribution, set `LEAN_LAKE_BIN` to its absolute `bin/lake` path.
The successful build and axiom audit are recorded in `verification.log`.

## Main declarations

All declarations are in namespace `IPRAIntegration`.

| File | Main checked content |
|---|---|
| `Truncation.lean` | Rational clipping, exact clipping residual, 1-Lipschitz clipping/excess, bounded metric `rho`, its triangle inequality, stable Vitali pointwise and finite weighted bounds, sharp L2 excess-tail inequality, and a threshold variant |
| `Energy.lean` | Binary conditional-average energy and residual identities, finite simultaneous version, weighted orthogonal energy identity, telescoping, and the executable bounded energy-window search with soundness and existence proof |
| `Examples.lean` | Counterexample to the invalid independent-tail shortcut; eight small exact examples |
| `Audit.lean` | `#print axioms` receipts for the principal results |

The two central statements are, for rational `K ≥ 1`,

```
|x-y| ≤ 2K min(1, |x-y|) + (|x|-K)^+ + (|y|-K)^+,
4K (|x|-K)^+ ≤ x².
```

`truncation_rho_integrated` proves the first inequality for **every finite
number of nonnegative rational weights**, not only for the small examples.
No normalization of the weights is assumed in that theorem.

`energy_window` returns a successful value of `smallWindow`, not just a
nonconstructive claim that a window exists. For a rational energy sequence
`E` with `E(0) ≥ 0`, `E(n) ≤ B`, and `B < n δ`, it produces `j < n` with
`E(j+1) ≤ E(j)+δ`. Applying this to the sequence at iterated endpoints gives
the finite energy argument used for metastability in the report.

## Axiom boundary

The standard Lean rational library and arithmetic tactics used here report
`propext`, `Classical.choice`, and `Quot.sound` in the axiom audit. Thus the
host proofs must not be called axiom-free, choice-free, or automatically
intuitionistic object proofs. The finite algorithms themselves use rational
comparisons and bounded primitive recursion; an iPRA derivation requires the
separate reification detailed in `OBJECT_LANGUAGE_PLAN.md`.

`ObjectAdapter.lean.txt` is an **uncompiled integration candidate** showing
exact existing repository interfaces. It is not part of the Lake targets.
The canonical repository's Mathlib dependency was not installed or rebuilt
in this run. Source paths, blob hashes and the pinned repository revision are
recorded in `source_manifest.json`.
