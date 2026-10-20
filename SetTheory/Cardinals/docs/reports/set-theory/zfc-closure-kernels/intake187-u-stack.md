# Batch 187: exact zero-terminal source combinations

The all-natural open identity `((CD6,CC2),CB1) = ((CD6,CC2),CD6)` applies to the shared-cancellation, Direct09 and Direct13 equality routines without a reachability assumption. Replacing every occurrence gives the following exact source census:

| Source | U replacements | DAG / interior | Leaves | Guarded cases | Right-child decrements |
| --- | ---: | ---: | ---: | ---: | ---: |
| Shared cancellation | 4 | 206 / 183 | 4,752 | 6,183 | 4 |
| Direct09 | 8 | 206 / 183 | 4,748 | 6,179 | 12 |
| Direct13 | 12 | 207 / 184 | 4,760 | 6,199 | 12 |

All U occurrences are inside the four equality macros, so equality-only and whole-source replacement agree. Each source also admits the same 81 retagged four-increment rotations; their complete ordered control-flow graphs agree before and after retagging, and the table above is unchanged. Depth is38 throughout. Every unchanged primitive has its complete original successor list, while each new decrement's zero successor equals the replaced break successor.

This is a source construction and exact data comparison, not a binary allocation, runtime or startup check. The source DAG does not shrink; no physical state reduction follows. The new positive decrement guards remain obligations of any future binary runtime proof. The all-natural open-fragment theorem, together with the separately reviewed equality contracts, supplies the semantic justification; no finite input sampling is used here.

[Own reader](code/intake187-u-stack-census.py), [actual census](data/intake187-u-stack-census.json), and [six exact generated sources](data/intake187-u-stack-sources.json.gz). Source inputs are recovered from Source143 as described in [the intake reproduction](intake-187-reproduction.md). To reproduce in a new directory:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake187-u-stack-census.py --packet /tmp/zfc187-packets/research218_encoding_supplement_latex --output /tmp/zfc187-u-stack
```

No delivered executable, compiler, proof assistant or machine simulator is invoked by this reader. Original source histories remain unchanged.
