# MC boundary windows 06–12

Seven individually bounded, sequential author checks proved equality
between the generated closed recipe's `byteAt` and the symbolic `lowNat`
byte window on these half-open intervals:

| Module | Interval | Object SHA-256 |
| --- | --- | --- |
| 06 | `[8468,8484)` | `aeeed3c1628d1f8e61ff99d8fbd81d96caf918376fee857208b8cd55d3abc69b` |
| 07 | `[8635,8643)` | `32fd5cd47746fec5fe3b0942d55719c2bbcba1d2bb2d4b85211f1753a1719fb8` |
| 08 | `[8895,8920)` | `c346da1cbef3418141befcf69622b9baa02e8dc623de7884ee5bd57a3ab056b8` |
| 09 | `[9163,9179)` | `fa1f6d0f30a73a354b04e61866729aa2dd552e8c0e8700ed4a308625419feeed` |
| 10 | `[18375,18392)` | `bd1036cadeba16b7ebedc29da17786dcc45ad8b1899d01e09031a92e8d1b873b` |
| 11 | `[27596,27613)` | `8e60b2809bd3d106fb984d717c469576155e829cc2504c9073daa9cec1fc8f29` |
| 12 | `[73751,73759)` | `bd5ea2afb2da3eaea61749b8b38d5bf737b405540fc2ffed0c1b6591666d4b37` |

All seven compilers and the sequential batch wrapper exited 0 without
warnings or `sorryAx`. Each module's exact source, direct dependency and
companion guards, separately inventoried generic provider, compiler log
and terminal receipt are retained under `observations/module-details`;
the batch commands and per-module exit reports are under
`observations/attempt01`. The per-module recorded guards and the batch's
input source/runner hashes remained unchanged. The named Lean axiom reports
are `[propext, Classical.choice, Quot.sound]`, metatheory dependencies
rather than iPRA axioms.

Together with the separately checked corrected boundary 01 and boundary
02–05, all 142 boundary positions now have individual author-side symbolic
window certificates. The all-index Lean assembly and reconstruction still
need a coherent build. These checks do not prove filesystem/gzip, parent-
to-supplement, PDF or iPRA correspondence, and are not paired replays or a
full symbolic/package/dynamic ancestry audit; checks are point-in-time.
