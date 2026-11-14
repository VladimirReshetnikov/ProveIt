# Arithmetic-to-PAeq term-translation graph witnesses

`PA194PAeqTermCodeWitness` proves `WB M` for the exact current-Foundation
arithmetic-to-PAeq term-translation graph and its term-vector graph in every
candidate-PRA model. The theorems require no extra IΣ₁ model premise. The
bounds are model-level monotone witness bounds, not extracted finite PRA codes
or a proof of numeric output growth.

The proof constructs an identity rank for the actual translation recursor and
bounds all six positive/negative blueprint clauses. The rank proof treats the
zero-arity source case separately: its recursive output vector is empty, while
the nonzero-arity result retains that vector in the encoded function node.
The negative function clause uses an explicit polynomial and a fixed constant
to bound all four source-tag cases. The existing arithmetic term-recursion
witness framework then gives both graph bounds.

The formula-translation graph and its output growth remain unbounded here.
This package does not prove substitution compatibility, PA proof transport,
or machine/consistency calibration.

Run from the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-paeq-translation-rank/check.sh
```

The three final modules passed ordered suffix checks against the retained
PAeq formula and arithmetic-recursion prerequisites plus audited
project/Foundation objects. Printed dependencies contain no `sorryAx`. The
generated wrapper syntax and source pins were checked; the full PA196
prerequisite-prefix replay remains pending.
