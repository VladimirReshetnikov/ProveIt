# Optional MP tails: two 195-state physical experiments

These are unsuccessful attempts to reach the requested size. They are kept
as reproducible research and are **not** additional Con(PA)-equivalence theorems.

Both replace the successful-MP tail while retaining the primary coefficient-four
axiom grammar and original Shift. At entry to the tail, the implication test has
succeeded, `D=b`, and `T=H=X=0`; the carried encoded stack is `w`.

| Variant | Source tail | Result `(T,W,D,H)` | Working states | Source sites | Universal outcomes |
|---|---|---|---:|---:|---:|
| `D_to_T` | `(dec4, node38)` | `(b,w,0,0)` | 195 | 3,650 | 4,750 |
| `D_to_T_H` | `(node51, node19)` | `(b,w,0,b)` | 195 | 3,654 | 4,755 |

For the first tail, one loop decrements D and increments T. For the second,
`node51` empties D into T and X, and `node19` then empties X into H. The loop
identities are elementary, but a complete new proof-word compiler and logical
calibration are not supplied for either controller.

The implementation changes `node163` to `(node6, tail)`, creates one reader at
native label 900, and redirects native row `(164,1)` to it. The count is
`135 fixed controls + 67 AX readers - 7 inherited folds = 195`. The entire
literal blank startup is unchanged and reaches the complete source frame in
58,154 transitions. The inherited universal symbolic checker passes every
source outcome for arbitrary natural registers, arbitrary affine header gap,
and a nonempty finite spare list. The arithmetic-box rows are unchanged.
Both outcomes of every decrement are checked.

No separate independent literal-tape replay or new Lean/Rocq theorem is claimed
for these two experiments. Their physical correctness checks do not, by
themselves, prove the Con(PA) equivalence.

## Reproduce

Python 3.10+ and the enclosing package suffice; no external checkout or network
is needed. Keep assertions enabled. From any directory:

```sh
python3 /path/to/package/research/mp_tails/replay.py \
  --package /path/to/package --output /new/replay-directory --merge-screen
```

Omitting `--merge-screen` still rebuilds both tables, checks every symbolic
source contract, all simultaneous fold cases, complete blank initialization,
and the finite helper-opportunity count. It omits only the final row-synthesis
screens. `recorded/` contains fresh replay results from the supplied package.

## Exact negative-search scope

The three-step helper template was checked on all 129 controls whose incoming
rows rigorously establish a single previous bit. It finds only the seven
inherited opportunities, a maximum matching of seven, and none involving the
new reader. This excludes that fold template for these fixed raw tables.

The extra synthesis screens redirect reader 900 to reader 130 (`D_to_T`) or
114 (`D_to_T_H`) and allow one conflicting row to take every combination of
write bit, direction, and existing working target. Each screen tries 776
actions and retains no passing candidate. Symbolic execution is bounded at
1,024 operations per contract. The screens do not exclude different grammars,
other survivors, several changed rows, more general contextual folds, or
smaller machines by other methods.

Source/runtime code and the seven-fold primary grammar are inherited from the
attributed PA194 research. The new work here is the pair of tail transformations,
their literal physical bindings, and the explicitly bounded cost screens.
