# Independent source review of the Pell-history majorant proposal

The candidate `BoundTerm` has the intended source-level context `[result,time,parameter]`: `#1` selects time, `#2` selects the sole Pell parameter, and the `Fin 1` parameter projection `e j.succ.succ` selects that same third coordinate. Its proposed paired-value bound and the generic raw-history formula match the inspected interfaces. No concrete arithmetic or interface mismatch was found. The majorization predicate is **unproved**, and the `.lean.src` has not been elaborated or compiled.

For `B=2*(a+2)`, the inspected `x_le` and `y_le` declarations give both coordinates at i at most `B^i`. In ordinary naturals, `B≤2^B` and `i≤u` imply `B^i≤2^(B*u)=F`. The source's `pair_polybound` then bounds the paired state by `(x+y+1)²≤(2F+1)²=H`. The candidate uses `exp2 A 0`, whose inspected valuation is `2^(A*2^0)=2^A`, and squares `2F+1`; this agrees with H. The all-model power, exponential, pair/projection and term-valuation rewrites needed to turn this calculation into `PellValueMajorant` remain to be proved and checked in Lean.

The raw `history_bound` theorem additionally requires an already valid recursion sequence containing the requested result and a bound on all previous paired values. Under those hypotheses it supplies another history with code strictly below `2^((u+H+3)²)`. The separate `wb_resultDef` interface also requires witness-bounded zero and successor formulas and the all-`IΣ₁` majorant. The packet correctly leaves both those inputs and the pair/projection graph assembly open.

This raw history-code estimate is not a complete bound for `bnd periodDef`: nested existential witnesses for sequence membership, pairing, projections and the outer period formula must also be accounted for. In particular, the inspected `WB M` definition merely asserts existence of a monotone **model function** for a given model; it does not by itself provide one uniform primitive-recursive code across models. A candidate horizon for the specific period inputs and the small outer-witness estimates do not close that gap or the separate classical/intuitionistic transfer.

The independent checker pins the draft and interfaces, inspects the exact `BoundTerm`, `histT`, `history_bound` and `WB` clauses, and checks the coordinate/pair inequality chain and small horizon controls without materializing a history bound. The finite controls do not prove these claims for arbitrary models, authenticate providers, or verify Lean syntax or tactics.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-pell-period-history-majorant-independent/check.py | cmp - reviews/ordinary13-pell-period-history-majorant-independent/receipt.json
```

No Lean, build, staging, axiom report, full witness bound or iPRA proof was produced.
