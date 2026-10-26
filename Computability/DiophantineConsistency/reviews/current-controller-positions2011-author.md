# Current controller positions: author verification

This is an author receipt, not an independent review. Both complete new
sources were read before execution. Only the frozen finite-data module
`CurrentControllerData2011` is imported. No accepted dependency was edited.

For `T=auxiliary^k` and `N=auxiliary^(k+1)`, the literal position is
`2+(auxiliary-1)*j.val`, with j in `ZMod T`. The proof establishes the
subtraction-free budget `position+T+auxiliary ≤ N+3`, the requested
upper bound `position ≤ N-T-auxiliary+3`, injectivity, and disjointness
from optional cell3. The cast into `ZMod N` has exactly that natural
value and is injective. Natural subtraction is truncated at k=0; the
bound remains valid there, and the sole orbit position is exactly2.

The actual finite natural support is the image of a supplied finite
orbit-index subset, with cell3 inserted iff ε is nonzero. If ε≤1, its
cardinality is `s.card+ε`. The image in `ZMod N` preserves that cardinality.
For any `rw<k`, every support member has positive value and satisfies
both ordinary inequalities `j.val+1<N` and `j.val+auxiliary^rw<N`.
Thus neither successor wraps. These geometric inequalities do not need
the stronger `T>d*auxiliary` hypothesis used by the subset-existence
construction. Insertion is geometric only: the file does not assume or
prove old dummy values, rank variation, modular target selection, or Γ
invertibility.

Frozen sources and fresh objects:

| File | Lines | SHA-256 |
|---|---:|---|
| `CurrentControllerPositions2011.lean` |178| `aab00b74d13e24bb78dda62c5c5a5fa55990f414821fef7b56d02c8fee675acf` |
| `CurrentControllerPositions2011Checks.lean` |48| `7723e5c1bd82e7711aa47930c219ff967ae3e0de8e9b180db85aa431c55f84ea` |
| main `.olean` |—| `fb7b49a7b537aa728eed0f9654fd509d9b1efa3eda45d9ae46c94286db9885f6` |
| checks `.olean` |—| `d7b503222a725e5536572f3bee3532e86b30959d53d41ce4a6ff707c4df183d7` |

Both final fresh replays used `lake env lean -M 6000 -j 1 -o` with the
corresponding object under `.lake/build/lib/lean/DiophantineConsistency`
and source under `Computability/DiophantineConsistency/Lean/DiophantineConsistency`.
Both files set `Elab.async false`. Main passed in5.66seconds, peak RSS
3,267,036KiB, empty log; checks passed in3.52seconds, peak RSS
3,233,304KiB. All13 axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. No new axiom, `sorry`,
`native_decide`, or incoming execution was used.

The initial main attempt selected the ordered-monoid strict-power lemma,
whose typeclass excludes zero; the correction uses the actual natural
strict-power lemma. The first focused checks used overly broad `simp`
on dependent k=0 expressions; explicit value rewriting and `simp only`
fixed those elaboration checks. No mathematical statement was weakened.
Final logs are `/tmp/current-controller-positions-main-final.log` and
`/tmp/current-controller-positions-checks-final.log`, with corresponding
`*-time.log` files. No Git operation was performed.
