# PA axiom branches for conditional PAeq proof transport

In every IΣ₁ arithmetic model, `pa_axiom_cases` classifies the actual current
Foundation internal PA axiom predicate as either the code of one of the
standard finite PeanoMinus axioms or an arbitrary internal induction-schema
code satisfying `InductionUnivR`. This explicitly covers nonstandard codes.

For any Δ₁ PAeq target theory `U`, `refutation_transport` uses that
classification and the ten-rule LK transport to derive internal
`Provable U falsum` from internal `Provable PA falsum`, given two explicit
assumptions: translated provability of each finite PeanoMinus axiom, and
translated provability of every internal induction-schema axiom. Neither
assumption is supplied here. The target theory and its relation to the PA194
numerical calculus and literal machine also remain to be established.

From the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-paeq-pa-supplier/check.sh
```

The complete standalone script passed against the audited project and
Foundation overlays, rebuilding the local chain and checking the upstream
pins. The exported theorems' axiom audits contained no `sorryAx`.
