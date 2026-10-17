# Exact numeric simulation of the actual 252-state table

[ArithmeticMachinePerm252.lean](../../Lean/BusyBeaver/ZFC/ArithmeticMachinePerm252.lean)
represents the actual machine's tape by two natural numbers and proves agreement
with its complete blank run at every natural time. This is the finite-data
bridge needed before representing the binary run in first-order arithmetic.
The subsequent [arithmetic extension](arithmetic_machine252.md) supplies that
fixed run formula. A PA proof of the machine/consistency equivalence remains
open.

A numeric configuration contains `(state, left, right)`. The low bit of `right`
is the scanned cell; the low bit of `left` is the cell immediately to its left.
Successive bits move away from the head. State zero means halted, and working
state `i` is coded by `i+1`. Codes beyond the machine's state range are explicitly
absorbing active states. The blank initial configuration for this table is
`(1,0,0)`.

For write bit `w`, the update is:

| Move | New left half | New right half |
| --- | --- | --- |
| Right | `2*left + w` | `right/2` |
| Left | `left/2` | `left%2 + 2*w + 4*(right/2)` |

The write and move occur even when the transition enters the halt state.
Already halted configurations remain unchanged. The absolute head position is
tracked by a separate integer witness. `Represents` uses the existing whole-tape
`FiniteZipper.ZipRep` relation, which constrains every cell on both sides;
there is no finite-window or unspecified-exterior premise.

`encodeZip_step` proves the exact numeric update for any machine, and
`step_sound` transports the whole-tape relation through one actual `Core.step`.
Induction yields `numericRun_sound` at every natural time and the exact
per-time equivalence:

```text
(numericRun machinePerm252 t).state = 0
  ↔ (machinePerm252.run t).state = none.
```

`perm252_halts_iff` existentially closes this same statement for the frozen
canonical table. Its inputs are the actual `TablePerm252` transition data.
Concrete callers also check the first transition and the sole halting edge:
working state 75 reading one writes one and moves right, for arbitrary tape
halves. The original Mira-Cult/Jeff/Wade attribution is retained through the
[frozen candidate](candidate-permutation252/README.md).

This module uses only the Std dependency closure of `FiniteZipper` and
`TablePerm252`. It is the 168th unit in the opt-in core verification. The
[integration record](results/arithmetic-machine-perm252-integration-verification.json)
freshly checks the new module and umbrella, reuses 166 modules with matching
source and object hashes, and runs the stored 19-probe/27-caller audit. The
[independent review](results/arithmetic-machine-perm252-review.json) checks tape
orientation, final halting movement, invalid states and actual table binding.

The subsequent [arithmetic extension](arithmetic_machine252.md) compiles all504
transition rows into a fixed lookup formula, encodes the numeric configuration
and represents iteration at every internal time. It uses the separate
Foundation arithmetic lane of the [PA-total checker](arithmetic_history254.md).
Proof translations relating the represented run and checker to ZFC refutations
remain further obligations.
