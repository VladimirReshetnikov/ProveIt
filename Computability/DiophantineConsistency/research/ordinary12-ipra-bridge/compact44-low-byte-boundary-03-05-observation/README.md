# MC boundary windows 03–05

Three bounded mixed-provider author checks proved that the generated closed
Lean recipe's `byteAt j` equals `(lowNat / 256^j) % 256` in the following
half-open intervals:

| Module | Interval | Source SHA-256 | Object SHA-256 |
| --- | --- | --- | --- |
| `CompactLowByteBoundary03` | `[8225,8233)` | `a00748f6179fff08351111c190d34e78c25996556a4cd50fb38571a8a0b02cef` | `a2fcd0dbe2d690de142fc2158cff6f8938648365884cb192a4dc3251b3aae107` |
| `CompactLowByteBoundary04` | `[8308,8317)` | `e34244fc7685c6bca8603a49e8d2b4e8d6f1a9c253519c8b989382474525588f` | `63ca172c85d6d446d582194f795b269861a07ba2caa5d2eb8cf36c927d86c8b2` |
| `CompactLowByteBoundary05` | `[8392,8401)` | `97a8e6536ee83f7c55ddcedbae6513373117005fb45403eadd0d3f044592d0c1` | `e4bbd93962c15da5786094d3bfdad7e5d35eff60af899650b2181c8655224fa3` |

All three compilers and wrappers exited 0 without warnings or `sorryAx`;
their exact source copies, direct dependency and companion guards, generic
provider inventories, logs and receipts are retained. The recorded guards
were unchanged at the checked points. Lean reports `[propext,
Classical.choice, Quot.sound]` for each theorem as metatheory dependencies,
not iPRA axioms.

These are exploratory author-side results, not paired replays or a full
symbolic/package/dynamic ancestry audit. With the earlier accepted boundary
02 and separately corrected boundary 01, five of the twelve finite boundary
modules have now passed; the remaining seven and global reconstruction are
still open. None of these theorems asserts filesystem/gzip, supplement, PDF
or iPRA correspondence.
