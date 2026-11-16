# PA194 selected-zero decision and preceding-register rollback

`PA194TwoPassesTo4.twoPassesTo4` extends the two-pass scan through an
arbitrary-length preceding physical register, reaching state 4 with the
selected register's code under the head. It places no restriction on any
source register or suffix. `PA194TwoPassesZeroTo5.twoPassesZeroTo5` assumes
only logical register 8 is zero, proves that state 4 takes its zero row, and
reaches state 5, with an exact named residual file and clock.

`PA194RollbackEvenTail.rollbackEven` generalizes the state-11 rollback to an
arbitrary even tape prefix, arbitrary suffix and arbitrary model-valued scan
length. `PA194ZeroToRollback.zeroToRollback` composes the zero route through
state 5 with that rollback. Finally
`PA194TwoPassesZeroRollback.twoPassesZeroRollback` composes all steps from the
original source header, assuming only `args 8 = 0`, and returns the preceding
register to the right tape at state 11. Its definitions retain all other
logical registers, all physical spare blocks, and the entire suffix; its
clock and endpoint are exact, and no blank suffix is assumed.

`check-two-passes-zero.sh` rebuilds these six modules plus the nine two-pass
and scan-prefix modules with the same five overlay variables described in
`TWO-HEADER-PASSES.md`; it additionally pins the direct rollback and
zero-cell objects. Its checks are a suffix replay. As with the earlier
checkers, the supplied overlays must have an independently audited coherent
transitive import closure. `PA194_TWO_PASSES_SOURCE_DIR` can point at scratch
sources.

The theorems do not yet identify the final site-27 frame, establish the full
source-machine simulation, or prove either consistency direction in iPRA.
