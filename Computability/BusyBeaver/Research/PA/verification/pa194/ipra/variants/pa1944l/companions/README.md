# PA1944L companion tables

Lean proves `iPRA ⊢ Con(PA) ↔ ¬Halt(M)` for these seven literal
194-state tables. The declarations in
[PA1944LCompanionFinals.lean](PA1944LCompanionFinals.lean) apply the model
comparisons to the checked [PA1944L theorem](../PA1944LFinal.lean).

| Companion | Native SHA-256 |
| --- | --- |
| Timing | `481796e5f6b88cb73c35cf2c7cde543a1d9afa4b87c5b1e6f267ffd21cdc2f90` |
| Selector | `59b64faa9b5a0cd2facfc8676aeca9d2ecb87f50cdc8445a2c7b64d84072e5d3` |
| Timing and selector | `2f02da57c72d820825a7b86e656d7c11ad86219ac0bdb3e46b5e4458e3962acc` |
| b4l | `0ccf69e31825f78b3be1769f9227f2ffcd81dedc8072f5edbbbcbab3170e8bbd` |
| b4l timing | `c591bfe12a6a650ead6efa3b589bacd6476a90fd4a90d90cf8cf864cf16eaca8` |
| b4l selector | `b3ea2ac01a206d4f82daa959d3d05b44b47185e1c591dbbecf4d94fd445b7a04` |
| b4l timing and selector | `5bbf9c34d11beaeadc31a1a2e5c5332e513b4c1d7cf9553b6374ace05a42e5ad` |

The [PA1944L packet](../../../../../../docs/pa1944l_research_2026-11-14/README.txt)
specifies a blank tape, native start 74, and native halt 254. Its authoritative
dense table has SHA-256
`c5787c6f2350e77183ca0d3ff25d2733ba87e8bb52cd54092d7fa26fcf4d5253`.
The label map has SHA-256
`2890771c2db5c598d5f3f833feecf2903e01d69bdf626782e34196c34bfcb13b`.
Re-encoding with that map gives the native parent SHA-256
`0867349f173d1a98287e5727114e0f210ed36e47f9e927cdf845b978c2ec72b5`.

The [local b4l packet](../../../../../../docs/pa194_ax11qh4_research_2026-11-14/research/local/README.txt)
specifies native start 74 for its
[exact input table](../../../../../../docs/pa194_ax11qh4_research_2026-11-14/research/local/b4l.native.tm).
The other six literals are
[retained under their native digests](../../../../../../docs/pa194_comparison_and_new_designs_2026-11-15/research/physical/inputs/corpus/).
Their transition files inherit the blank start from the exact parent tables
identified in the [provenance receipt](../../../../../../docs/pa194_comparison_and_new_designs_2026-11-15/research/physical/receipts/corpus_meta.json).
The generators check the bytes, the parent and overlay pins, and the common
dense translation with start 0 and halt 194.

The timing and selector variants use the shared guarded timing and selector
proofs. For b4l, native 88 and 301 map to 88 at corresponding configurations.
The original incoming transitions determine the left-neighbor bit, with
bit 1 at 88 and bit 0 at 301. The candidate reuses 301 as a helper
and uses that bit to return to the corresponding configuration in three
or five steps when the current bit is zero. Reading one takes a single step.
[PA194GuardedHistory.lean](PA194GuardedHistory.lean) proves the guarded
segments over arbitrary model tape halves and lifts them to halting
equivalence with model-valued clocks.

## Replay

Use the [covered PA1944L model and final stages](../README.md) and the
existing outputs exposing `PA194GuardedShortcuts.olean`,
`PA194GuardedSelectors.olean`, and `ConPAMachineRelative.olean`.
The coverage stage supplies the ordered model dependency paths in
`leanpath.txt`. Each other provider may also supply a path receipt.

```sh
dir=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa1944l/companions
bash "$dir/check.sh" "$PWD" "$four_l_final" "$four_l_coverage" \
  "$timing_stage" "$selector_stage" "$relative_stage" "$fresh_output"
```

The checker regenerates the seven finite certificates from the archive.
It builds `PA194GuardedHistory`, then `PA1944LFastRows`,
`PA1944LSELRows`, `PA1944LFastSELRows`, `PA1944LHistoryRows`,
`PA1944LFastHistoryRows`, `PA1944LSELHistoryRows`, and
`PA1944LFastSELHistoryRows`. The final `PA1944LCompanionFinals` stage
checks the seven unconditional endpoints together and audits their axioms.
The output records the selected module paths and SHA-256 checksums.
