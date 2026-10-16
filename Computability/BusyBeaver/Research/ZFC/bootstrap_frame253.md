# Joining the finite binary and register endpoints

16 October 2026. [`BootstrapFrame253.lean`](../../Lean/BusyBeaver/ZFC/BootstrapFrame253.lean)
proves that the actual Core configuration after 312,975 blank-tape steps
represents the actual public register configuration after 330 RM steps.
It combines [the boot certificate](finite253_lean.md) and
[the register certificate](rm330_lean.md); it does not execute the boot again.

`dispatchZip` constructs the complete dispatch layout for any state type:
a marker immediately left of the head, the logical PC, a zero gap, a one
header, then unary blocks for the nine permuted logical registers and an
arbitrary finite spare suffix. Each block is `0 1^(value+1)`. Explicit
left and right exterior zero padding preserves the exact stored zipper
while `ZipRep` specifies every tape cell, including the blank exterior.
`DispatchFrame` also requires PC length plus gap at least 40, and separately
requires every logical register at index 9 or higher to be zero.

That separation is essential: the first nine physical blocks encode the
logical vector under `[2,4,3,7,6,8,0,1,5]`. The remaining blocks are spare
data, with no identification between spare indices and logical registers.
The concrete suffix has length 158, nonzero values exactly at indices 2
and 8, and values 1 at those positions. All 158 blocks are retained.

`target_zip` checks equality of the finite constructed zipper and the
existing `Boot253.bootTarget253`. `boot_exact_dispatch_zip` then imports
the already proved whole-tape Core representation. The parameters are:

| Component | Value |
|---|---|
| Compact dispatch state | 33 |
| Absolute head | −17 |
| PC | `000` |
| Additional gap zeros | 37 |
| Total PC-plus-gap cells | 40 |
| PC marker | −18 |
| Register header | 23 |
| First register separator | 24 |
| Physical primary values | `[0,2,0,0,0,0,5,0,0]` |
| Exterior stored zero padding | 10 left, 1 right |

The actual marker and header reads have separate theorems.
`bootstrap_matches_rm330` pairs the actual RM execution equality with
`DispatchFrame` for the actual Core execution. This proves a spatial
endpoint relation; preservation of that relation by instructions is still
unproved. It makes no first-arrival or consistency claim.

The representation follows Jeff's verification of Mira-Cult's machine,
using Wade's framework, `ZF/m254/coq/tm/Sim.v:81–85`. The concrete 253-state
frame is attributed to mira-emmy's public PR20 head
`0d544f2a2e3c18f12278441a74b7879f31cbe856`, especially
`ZF/m253/coq/tm/{Sim,Boot253,Check253}.v`. The original `Sim.Inv` already
permits an arbitrary spare suffix; a positive decrement can append another
zero spare. No all-zero-spares condition is added here.

In the pinned source state map, old proof label 96 maps to compact 33,
old start label 5 maps to compact 0, and deleted old label 8 maps to the
compact halt target 253. The current theorem uses literal compact states,
so it needs no assumed machine renaming. Reusing the old symbolic execution
proofs later requires their full state-map/transition correspondence;
the modified 253-state machine is not a mere renaming of the 254-state one.

`WadeMachine.lean` supplies reusable generic tape/scan utilities, but its
literal instruction theorems are about `machine252`. Its selected-register
convention also differs from the old `Box.sepsM` erasure convention. This
module therefore reuses `FiniteZipper` and the exact boot block encoding,
without applying those instruction theorems to the 253-state table.

The [verification evidence](results/bootstrap-frame253-verification.json)
records the explicit absolute Lean 4.32.0 compiler, source identities,
dependency headers, scoped checks, axiom audits, and a checked caller.
There are no admissions, custom axioms, native evaluation oracles, or
upstream Coq builds. The dependency cache is reused; this is a scoped
module check, not another fresh build of the complete source closure.
