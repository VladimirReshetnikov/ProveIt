# A candidate primitive-recursive majorant for Pell recursion histories

Existing source provides a concrete **raw history-code bound**, but no checked theorem was found in the inspected route giving a uniform primitive-recursive bound for **all** witnesses of the proposed bounded period formula. The gap is narrower than merely “Pell coordinates grow too fast”: `PRAWitnessPR.history_bound` explicitly bounds a chosen computation history once all prior **paired recursion values** are bounded, and `wb_resultDef` packages it with additional zero/successor witness-bound hypotheses. This packet proposes the missing paired-value majorant as an inert `BoundTerm`; its correctness and all Lean elaboration remain unproved.

## Exact generic interfaces

`ArithmeticPellRecurrence.blueprint` is a one-parameter recursion, and `construction.result ![a] i` is the paired state whose projections are `xcoord i a` and `ycoord i a`. Its `runDef` is `blueprint.resultDef`, with outer context `(result,time,parameter)`. `PRAWitnessPR.history_bound` says that, from a valid recursion history containing the requested result and an upper bound F on every paired result through time u, another valid history exists below

```text
2^((u + F + 3)^2).
```

This is a bound on the **history code**, not automatically on every witness used to certify membership, pairing, the sequence predicate, or the outer period formula.

`PRAWitnessPR.wb_resultDef` is a further candidate-PRA-model interface. Its exact premises include `WB M p.zero.val`, `WB M p.succ.val`, a `BoundTerm (k+2)` H, and an all-`IΣ₁`-model majorant on each result through the requested time. Its `histT H` is the explicit term above. Existing `wb_pairDef`, `wb_pi₁Def`, `wb_pi₂Def`, the compositional `WB` calculus, and the quoted `PRAWitnessRepeatVec` use of `pair_polybound` are plausible ingredients for the two Pell clauses and coordinate projections; this packet does not establish their assembly.

Crucially, `WB M φ` itself existentially quantifies a monotone **model function** bounding witnesses. Its type does not state that this function is a single primitive-recursive code uniform across all models. A proof of `WB` or a coordinate bound must therefore not be described as the requested full uniform primitive-recursive `bnd periodDef` bound without further code and correctness work.

## Concrete paired-value candidate

For nonnegative u and a, write

```text
B = 2*(a+2),  F = 2^(B*u),  H = (2*F+1)^2.
```

`ArithmeticConstructionBoundPell.x_le` and `.y_le` bound each coordinate at time i by `B^i`. For `i≤u`, elementary power monotonicity and `B≤2^B` give `B^i≤F`. Since `run i a` is the pair of its projections, the source's `pair_polybound` gives `run i a≤H`. The required model proof of those inequalities, the pair/projection rewrite and the `BoundTerm.vval` normalization are **not yet written or checked**. The source-only `PellValueMajorant` predicate states exactly the resulting `hH` premise for `wb_resultDef`, using context `e=[result,u,a]`; `pairValueBound` represents H through the existing primitive-recursive `BoundTerm.exp2` constructor, and `rawHistoryBound` applies its existing `histT` constructor. The proposed source has no theorem claiming that majorization.

For the period input `(m,a)`, one possible outer horizon is

```text
C = 2^(B*m),  U = 2*m*C.
```

The same coordinate estimate gives `c=ycoord m a≤C` and hence both m and `h=2mc` are ≤U. Substituting U for u in H and `2^((U+H+3)^2)` gives a concrete primitive-recursive **candidate raw-history bound** for the three Pell evaluations at m and h, without constructing a Pell iterate. With m>0, the equations `x_h=1+c²r` and `y_h=t*c²`, together with c≥1, also bound the chosen r and t by the corresponding coordinate bound; m=0 can use r=t=0. These are mathematical estimates and a proof plan, not a verified bound for `bnd periodDef`.

To complete the desired interface, prove `PellValueMajorant` in all intended `IΣ₁` models and elaborate `pairValueBound`; establish the Pell zero/successor `WB` inputs and coordinate-graph rewriting; account explicitly for every **nested** existential introduced by the pairing, sequence/history and graph formulas; construct a single suitable candidate-PRA code/bound for the full `(m,a)` period assertion and prove its correctness/dominance. The generic `WB` existence result may help with the intermediate graph but does not by itself supply that last uniform code. Then the previously documented open-goal/Parsons and intuitionistic witness-transfer obligations still apply.

The bounded checker pins the exact source interfaces, checks the candidate context and term text, and tests 63 small paired-state majorants. It intentionally never computes the astronomical history bound. These finite controls and signature matches are not a Lean proof, a general resource bound, or a primitive-recursive correctness theorem. The `.lean.src` file is an inert proposed source provider, not a built module. Reproduce from `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-pell-period-history-majorant-draft/check.py | cmp - research/ordinary13-pell-period-history-majorant-draft/receipt.json
```

No Lean, build, staging, axiom report or iPRA proof was performed.
