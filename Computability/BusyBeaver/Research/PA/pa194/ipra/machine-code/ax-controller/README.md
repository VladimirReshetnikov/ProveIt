# Literal PA194 and its modeled scheduler

`PA194LiteralSchedulerCorrectness.endpoint` identifies the exact sentence
`PA194ExplicitEndpoint.haltClassical` with halting of the scheduler from its
initial state in every PRA model with a classical IΣ₁ arithmetic reduct.
The theorem has no command or table coverage premises.

The Lean kernel checks the 251 AX body blocks in `PA194ModelAXBatch*`.
The aggregate binds those blocks to the exact symbolic plan in
`PA194AXSymbolic.core`. The symbolic evaluator interprets that plan in the
same arithmetic model as the controller, and the certified output gives
the scheduler's top, stack and remaining command fields. The literal gate
then reaches the next scheduler frame. This AX transition supplies the last
return case of the controller/scheduler induction, alongside MP and SHIFT.

The complete model-level endpoint passed Lean checking and reported
`propext`, `Classical.choice`, and `Quot.sound`. The staged checker
rebuilds this directory from source and checks the recorded inputs and
axiom reports. Its lower Foundation and previously checked machine
objects come from the ordered stages in `ax-controller-stages.txt`.

```sh
dir=Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/ax-controller
ulimit -s 65536
python3 "$dir/check-ax-controller.py" "$PWD" "$dir" /dev/shm/pa194-ax-controller-new "$dir/ax-controller-stages.txt"
```
