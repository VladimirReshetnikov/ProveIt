# Dense-7 return to dense 24

`PA194SevenToRootControl.sevenTo24` proves the following physical-machine
contract in every candidate PRA model, including nonstandard model values and
clocks. Starting at dense control 7, its left half has the increment-box
controller shape defined in the theorem; its right half is twice a first
block whose length is `k+1`, followed by an even encoded remaining file
`file = r+r`. It reaches dense control 24 with exact halves

```
h = 2*g+1,  g = zeros(2, zeros(6, u)),
z = zeros(2, zeros(k, 1+2*file)),
w = ones(5, 1+4*z),
right = 1+4*w.
```

Here `ones` and `zeros` are the model interpretations of the respective
finite-code functions. The exact clock is in the theorem. The first block must
be positive; the zero case is not covered. This theorem can be used on the
increment output when the `k+1` first-block and even-file layout are supplied.
`PA194IncrementOutputEven.outputEven` proves the concrete returned file is
even, and `PA194ContinueIncrementTo24.continueIncrement` composes any prior
run with the exact increment output and positive first block to the dense-24
endpoint. These results do not themselves assert reachability from the blank
tape or instantiate the complete marker-entry theorem.

The table-label metadata externally identifies dense 24 with the native root
control, but the theorem does **not** prove the full native-to-dense map, a
source-frame correspondence, or any source-instruction simulation. In
particular, the left half is the canonical root-frame left half 1 when `u=0`;
the established marker-entry contract leaves `u` arbitrary and does not
establish that condition. Even with that condition, the right-hand header and
its relationship to the source path and complete physical file require a
separate correspondence proof. From its displayed bit expression, the right
half starts with the fixed eight bits `10111111` (head first), then `k+3`
zeros, then a one and the complete even `file`. For standard natural values,
`u=0` and `k≥27` make this layout match the concrete source root-frame shape
with path `10111111` and padding parameter `k-27`. This observation is a
manual comparison, not yet a Lean-checked frame correspondence or a proof
that those conditions hold on a run from the blank tape.

The prior standard-source calculation that a decrease of register 2 from
`k+7` to `k` requires at least seven source steps is conditional on source
configurations matching both physical endpoints; this package proves no such
matching and makes no `Con(PA)`/halting implication.

All six new modules were rebuilt together in a fresh author suffix overlay
against the previously checked controller prerequisites. They reported only
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. A full
prerequisite rebuild is available via `check-seven-to-root-control.sh` and has
not yet been run for this package.

An independent ordered suffix replay rebuilt all six new modules using the
separately checked increment, slot-eight and rewind objects and retained deeper
prerequisite overlays. It passed without `sorryAx`; this was not a full nested
replay.
