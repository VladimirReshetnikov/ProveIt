# Standard PA194 SHIFT and MP code binding

`PA194MachineShiftMPStandard.lean` proves that the selected finite
machine-Cantor projection codes evaluate on natural numbers to the exact
components of `M6.Source.Cantor.decode`. It then proves `shift_code_command`
and `mp_code_command`: for arbitrary finite input codes and standard natural
arguments, the modeled SHIFT and MP effect codes reproduce
`PA194CommandTransfer.step` exactly, including SHIFT's halting branch, both MP
branches, the register updates, and the triangular work stack. The proofs
use the candidate-PRA model equations without an additional Nat IΣ₁ reduct
assumption.

These are standard-input equalities. They do not establish a correspondence
between a model scheduler trace and the PA194 controller, identify target
provability with internal PA provability, or prove a PA194/Con(PA) implication.
The AX command's separate standard binding is in
`../pa194-machine-ax-standard`.

Run from the repository root with the matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-machine-shift-mp-standard/check.sh
```

The final module was rebuilt against the freshly generalized SHIFT/MP code
module and previously checked prerequisites. A full nested replay of this
wrapper has not yet been completed. Its printed axiom dependencies contain no
`sorryAx`.
