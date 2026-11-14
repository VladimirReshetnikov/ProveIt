# Modeled halt endpoint with the distinct-label premise

`PA194DistinctGateEndpoint.all_tail_from_distinct` uses the checked exact
numerical equal-label gate proof to show that fresh-label separation tails
for all distinct `a` and `b` suffice for *all* guarded separation tails. This
works for arbitrary, potentially nonstandard parameters in every candidate-PRA
model whose arithmetic reduct satisfies IΣ₁.

`modeled_halt_refutes_PA_of_distinct_tail` composes that reduction with the
fixed coded modeled scheduler: if its halt bit is set after a model number of
steps, then the model has a PA refutation, provided the explicit distinct-label
separation-tail premise holds. The equal-label case is discharged.

The distinct-label premise remains unproved, and the modeled scheduler is not
identified with the literal PA194 machine on nonstandard runs. Consequently
this is not yet a PA194/Con(PA) implication in iPRA.

From the repository root, with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-distinct-gate-endpoint/check.sh
```

A fresh suffix check passed against separately rebuilt equal-gate and scheduler
objects with retained deeper prerequisites and no `sorryAx`. A full nested
replay has not yet been completed.
