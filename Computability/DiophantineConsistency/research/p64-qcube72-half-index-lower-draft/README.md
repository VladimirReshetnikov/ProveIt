# Main Pell index is less than twice the first index

`FreeMainHalfIndexLower.main_lt_twice_first` proves `m<2n` in any IΣ₁
model from the two coordinate identities

```
2*ycoord n (2*(X*Y²−1)+1) = eta+zeta
 ycoord m (X*Y+Y) = (eta+zeta)*Y+eta
```

and `0<zeta`. It uses model nonnegativity and no early congruence, rank
window, or graph-specific premise. The checked Pell composition theorem
rewrites the ordinate at `2n` using a doubled base; base monotonicity and
`eta<eta+zeta` give the contradiction if `2n≤m`. This generic comparison
alone does not extract graph coordinates, prove `2n=R+1`, or establish the
72-operation reverse implication.

Attempt04 passed with Lean exit 0, stable direct guards, no warnings or
`sorryAx`, and the expected `[propext, Classical.choice, Quot.sound]` axiom
report. The source's historical unchecked-draft header predates this check.
Direct provider objects are `ArithmeticAdaptiveIndexComparison2011` and
`ArithmeticPellCommonUnit`; transitive and dynamic ancestry and sampled
resource monitoring are inherited, so this is not a source-only rebuild.

| Artifact | SHA-256 |
| --- | --- |
| `FreeMainHalfIndexLower.lean` | `de70b6754ba9e28615f565d545b9eed0031f40e38fd12e0c4724bf8356298874` |
| `check04.py` | `2c4c5b794b3d32ac5637b7657796c882f24d7c1e77c03bff885a0c677341cb5e` |
| `observations/attempt04/compile.log` | `04f147e9114c924bdeff1cc074ba52d341f85f98a48b5feac09861aba112093b` |
| `observations/attempt04/result.json` | `7700a73f610d45a221ff8fa135b14af2fa5b6328fe0f19755ffb6b028a976c38` |
| `/tmp/p64-qcube72-half-index-lower-priority-check04/FreeMainHalfIndexLower.olean` | `efd15c9bbd3394fbf085518e4f7374a0e0d75013a771872d6700a542c8ad5839` |

The run used a 2,400 MiB Lean limit, 120-second timeout, sampled 3.5 GiB
process-group RSS limit, minimum 10 GiB host available memory, and low
CPU/I/O priority. Attempt01 failed on six model-semiring arithmetic goals;
attempts02–03 failed on calc layout. Their exact source snapshots, runners,
logs and receipts are retained under `observations/attempt01`–`attempt03`.
Each failure's report contains `sorryAx`; none produced an object.
