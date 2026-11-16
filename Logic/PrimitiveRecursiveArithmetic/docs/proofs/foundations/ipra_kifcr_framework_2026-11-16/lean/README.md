# KIFC-R Lean formalization outline

These files target ProveIt commit
`31784f0710fa04ccd8ee863ce9bad91fb1d8cf88` and the current
`IPRADerivations` API.

They are **source-oriented outlines**, not a claimed clean Lean build. Lean is
not installed in the artifact environment. No theorem-specific axiom or
`sorry` is used; unfinished results are represented as structures with proof
fields and explicit implementation notes.

## Files

- `KIFCR/KernelCore.lean` — local `Prf PRAAx` rules, proof schedules,
  residualized conditional theorems, and QF loop certificates.
- `KIFCR/BooleanBlueprint.lean` — fixed-formula reflection and bounded-fold
  interfaces.
- `KIFCR/SearchAdapterBlueprint.lean` — adapter plan for the **already checked**
  `IPRADerivations.Core.Search`; no duplicate search recurrence.
- `KIFCR/ResidualBlueprint.lean` — metalevel residual reachability and
  conditional theorem generation.
- `KIFCR/DemandClosureBlueprint.lean` — capped cyclic demand closure endpoint.
- `KIFCR/TraceBlueprint.lean` — one-loop packed trace endpoint.
- `KIFCR/RelationalBlueprint.lean` — finite viability and selected-path
  interfaces.
- `KIFCR/ObserverBlueprint.lean` — exact/diameter observers and tail budgets.
- `KIFCR/GraphBlueprint.lean` — seven node kinds and conditional compiled
  graph endpoint.
- `KIFCR/CubicBisectionBlueprint.lean` — complete definition/proof roadmap for
  the stable cubic benchmark.
- `KIFCR/Examples.lean` — adapters for inherited checked algebraic derivations.
- `KIFCR/Checks.lean` — intended axiom audit after integration.

## Recommended repository placement

Place the completed modules under:

```text
Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/
  IPRADerivations/Framework/
```

Rename the namespace from `LeanProofs.KIFCR` to
`LeanProofs.IPRA.Framework` during integration, then add a root import
`IPRADerivations/Framework.lean`.

See `FORMALIZATION_PLAN.md` for dependency order and exact completion gates.
