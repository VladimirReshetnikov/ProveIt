# PAeq formula-substitution graph witness bound

`PA194PAeqSubstWitnessComplete.wb_substsGraph` proves `WB M` for the exact
current-Foundation PAeq formula-substitution graph in every candidate-PRA
model. It has no extra IΣ₁ model premise. This is a model-level monotone bound
on the graph's existential witnesses; the theorem does not extract a fixed
finite PRA code for choosing that bound.

The checked chain establishes the target qVec graph bound, all substitution
constructor-clause bounds, and both polarities of the actual recursion core.
It then proves the PAeq substitution fixpoint stage bound in arbitrary IΣ₁
models, including nonstandard codes. The final all-candidate-PRA theorem uses
the already established classical-PRA tower domination and target-independent
monotonicity. The conditional intermediate theorem keeps these premises
explicit before the final module discharges them.

The separate PAeq formula-translation graph is total and Σ₁, but its output
size and graph-witness bounds have not yet been established. This result does
not prove that translation commutes with substitution, translate PA proof
codes, or establish either machine/consistency implication.

Run from the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-paeq-subst-witness/check.sh
```

The final modules passed ordered Lean suffix checks against the individually
checked target syntax, term/formula recognizer, and substitution-growth
modules plus retained PA196 and audited project/Foundation prerequisites. All
printed theorem dependencies omit `sorryAx`. The wrapper checks input pins
and rebuilds the PA196 prerequisite prefix followed by the complete target
chain in a private directory; its generated shell syntax has been checked,
but the full prefix replay remains pending. The target atomic-growth module
alone required several minutes and roughly 2.5 GiB RAM in the suffix run.
