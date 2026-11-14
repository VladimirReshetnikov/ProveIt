# Conditional modeled-scheduler halt endpoint

`PA194SchedulerHalt.halt_implies_provable` proves that, in every candidate-PRA
model with IΣ₁ arithmetic, a modeled scheduler state satisfying `SoundStore`
and having halt bit 1 supplies a proof of numerical contradiction code 1 in
the independent `TargetProvable` encoding. The proof covers nonstandard model
values and handles both ways that the SHIFT test can have top + cache = 1.

The theorem assumes the store invariant at the halting state. It does not yet
prove that a model-length scheduler run maintains that invariant, connect the
modeled scheduler to the literal PA194 machine, or translate `TargetProvable`
into internal PA provability. It therefore proves neither consistency
implication in iPRA.

From the repository root, run with the matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-scheduler-halt/check.sh
```

The final module passed a fresh suffix check against a separately checked
scheduler object and retained deeper prerequisites, without `sorryAx`.
The nested full replay has not yet been completed.
