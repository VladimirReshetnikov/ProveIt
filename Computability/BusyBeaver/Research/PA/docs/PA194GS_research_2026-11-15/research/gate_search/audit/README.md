# Rejected binding and price-model correction

The old search's source leaf `node69` means the remainder of `copyH`, namely `(node68,node34)`. The raw parent implements this at 179. Its enclosing copyH selector 166 has literal rows `0 R 19` and `1 R 179`. The inherited expanded search instead mapped that source leaf to 30 and treated `(19,30)` as the free copyH pair.

The correction is physically determined, not a renaming preference. Entry 30 is the reader `(0 R 45, 1 R 46)` and has a different source role. Entries 114, 20, and 179 are the three inspected copy remainders. The independent `../macro_audit.md` describes their pair identities and context restrictions.

The three rejected nominees all have 193 non-halting controls and pass source instruction-list identity and local fold checks. They fail the full symbolic tape contracts:

| Nominee | Reachable raw controls | Folds | Failed source site | Branch | Completed outcomes |
|---|---:|---:|---:|---|---:|
| orphan_h11 | 200 | 7 | 389 | Physical register 4 is zero | 513 |
| orphan_h14 | 200 | 7 | 389 | Physical register 4 is zero | 513 |
| orphan_gdh0 | 202 | 9 | 95 | Physical register 4 is zero | 129 |

For H11, the failing source instruction is `dec 3`, with successors 393 and 390. The literal witness uses nine zero physical registers, one spare value equal to one, and zero extra gap. After 120 ordinary transitions, it returns to control 84 at the correct head position but with a different code tape than the required zero-branch target. The retained trace prefix makes this particular contract failure concrete. The longer bounded diagnostic did not reach the required target within 10,000 steps; that observation is not used as a non-halting proof.

`replay_bad_copyH_failure.py` reruns the symbolic and bounded literal diagnostics using only this package's construction checker and the H11 snapshot. It rewrites the two trace files and emits the full 10,000-step literal diagnostic, so its output can be larger than the compact retained trace. It is a rejection reproducer, not a proof validator.

The corrected scorer also removes syntactically unreachable fixed controls before finding fold opportunities. Thus it does not continue charging control 12 or 166 when all calls to them have disappeared. The unified diff in `scorer_correction.patch` records both the binding correction and the reachability adjustment. All 900 previously saved grammars were then repriced with the corrected model; every corrected nominal count is 194.
