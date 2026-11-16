# PA194 model-valued modus ponens

`PA194ModelMPDrain` consumes a finite certificate for a decrement, a sequence
of increments and the return jump. It follows the literal source controller
for arbitrary register lengths. Each positive decrement lowers the counter
and adds the certified increment tallies to the other registers.

`PA194ModelCantorWalker.walk` binds the eight-row decoder at any certified
source ordinal and input register. It uses the same Cantor projections as the
model scheduler. The reader supplied by `PA194ModelAXReader` composes this
walker with two drains. At site 3554 the decoded head adds to D and the tail
replaces L. The two push routines and implication construction use the exact
ten-row pairing loop in `PA194ModelMPPair`. The guard compares T with H and
clears both values and its scratch register on each branch.

`PA194ModelMPFields.nextFields` unfolds the modeled MP tag into its operand,
success or failure store values, suffix and zero halt flag. The endpoint
`PA194ModelMPSchedule.commandMatches` aligns these values at the actual
controller return to source site 25, given the already fetched operand at
site 3554. It includes the positive model-valued source clock and retains the
dispatch register and the clean scratch registers.

`PA194ModelMPFromFrame.advance` includes the literal fetch and decode. For
a scheduler state whose fetched tag is one, the source controller runs
from the exact packed scheduler frame to the exact next packed scheduler
frame after a positive model-valued clock. The checked theorem requires
the usual PRA model and IΣ₁ reduct instances.

`PA194ShiftModelReturn.fromSchedulerFrame` supplies the corresponding
nonhalting SHIFT transition. The source prefix transfers the old cache to
the top, computes the halt guard and takes its ordinary exit. The shared
reader at site 11 then replaces the stack and cache with the appropriate
Cantor projections and returns to site 25. The proof aligns the six
scheduler fields and the cleared scratch registers.

The generalized reader also supplies the field readers at AX source sites
131 and 224. The rest of AX is needed for the full returning-command
contract.

```sh
dir=Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code
ulimit -s 65536
python3 "$dir/check-model-returning-commands.py" "$PWD" "$dir" /dev/shm/pa194-returning-commands-new "$dir/model-mp-command-stages.txt"
```

The aligned MP and SHIFT endpoints passed Lean checking against the staged
shared-model and reader proofs. The checker rebuilds this suffix, records
the selected direct imports and source hashes, and audits the reported
axioms. Lower imports in the ordered stages remain prebuilt.
