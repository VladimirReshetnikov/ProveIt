# Fixed code for modeled scheduler halting

`PA194SchedulerHaltCode.lean` defines a fixed unary finite candidate-PRA code
`haltAfter`: on an input `k`, it evaluates the halt bit of the modeled
scheduler after `k` iterations from its fixed initial state. The equation
`haltAfter_model` holds in every candidate-PRA model whose arithmetic reduct
satisfies IΣ₁, including for nonstandard `k`. `haltAfter_graph` gives its
parameter-free Σ₁ graph in those models. The code uses the previously fixed,
certified projection codes; its full concrete syntax has not been extracted.

`modeled_halt_provable` shows that a modeled halt supplies a proof of the
numerical target formula `1`. `modeled_halt_refutes_PA` then yields an
internal PA refutation, assuming that all oldBundle instances satisfying the
two guards translate to internally PA-provable formulas. That guard premise
remains open. `modeled_halt_refutes_PA_of_tail` instead assumes the more
specific fresh-label negated separation-tail proof, which the gate reduction
shows is sufficient.

The scheduler is matched to the source scheduler on standard natural inputs;
its nonstandard iterations have not been identified with a literal PA194
controller or machine trace. Thus these results do not establish an
implication between PA194 halting and Con(PA).

Run from the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-scheduler-halt-code/check.sh
```

The final module was checked against the freshly built scheduler-to-PA object
and retained prerequisite overlays. Its printed axiom dependencies contain no
`sorryAx`. The wrapper's syntax has been checked, but a full nested replay has
not yet been completed.

An independent suffix replay rebuilt the modeled halt-code module against
separately checked scheduler-to-PA and iteration objects and retained deeper
prerequisite overlays. It passed without `sorryAx`; this was not a full nested
replay.

A fresh ordered suffix replay rebuilt the scheduler-to-PA and halt-code
modules after adding the separation-tail variants; it passed without `sorryAx`,
using retained checked prerequisite overlays.
