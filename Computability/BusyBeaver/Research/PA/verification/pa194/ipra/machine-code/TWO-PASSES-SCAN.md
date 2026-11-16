# PA194 third-pass entry and header scan

`PA194ThirdHeaderTo1.twelveSteps` gives the exact model-uniform state-24 to
state-1 transition for an odd header word. `PA194TwoPassesTo1.twoPassesTo1`
composes that entry with the two completed root passes. The further theorem
`PA194TwoPassesScan.twoPassesScan` scans the resulting unary header in state 1
for its model-valued length. It gives an exact named clock and exact tape
halves, preserving every input register and the entire arbitrary suffix. The
proof uses the previously established open-induction scan theorem, so the
header length can be nonstandard.

The [selected-zero continuation](TWO-PASSES-ZERO.md) continues through the
register decision and rollback when logical register 8 is zero, preserving the
other registers and arbitrary suffix.

`check-two-passes-scan.sh` rebuilds these three modules together with the six
two-pass modules. It accepts the same five overlay variables documented in
`TWO-HEADER-PASSES.md`, additionally pins `PA194ScanInvariant.olean`, and
checks the axioms of the new theorems. The input overlays must still have an
independently audited coherent transitive closure; direct hash checks alone do
not provide one. The script can use `PA194_TWO_PASSES_SOURCE_DIR` to point at
uninstalled sources.

This is an intermediate physical execution result, not an exact site-27
source-frame result, an all-model source-machine simulation, or either
consistency implication in iPRA.
