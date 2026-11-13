# Independent audit of the printed-port extension source plan

On 2026-11-04 the read-only [`audit.py`](audit.py) independently followed
current workspace import declarations from `CurrentKernel2011` and
`CurrentMaskRecipes2011`, stripping nested comments and strings. It exited 0
and produced [`receipt.json`](receipt.json). It rehashed each source and
compared its explicit imports with the two frozen manifests, then validated
the proposed 61-module order against the active endpoint snapshot. The
union contains **84 project sources**, **23 shared** with the 1,000-module
endpoint snapshot and **61 additional** sources. All shared source hashes
and explicit imports matched. The existing printed-port assembly source is
hash-matched and explicitly imports these two roots.

The independently derived set difference in direct external names is exactly
`Mathlib.Analysis.SpecialFunctions.Pow.Real`, `Mathlib.NumberTheory.Wilson`
and `Mathlib.Tactic`. Each corresponding `.olean` was present in the
captured package overlay and hashed at the observation time, with real paths
and hashes in the receipt. **None of their `.olean` module paths appears in
the Foundation receipt's declared external guard.** Any later extension
must therefore separately guard the selected direct objects, companions,
namespace resolution and shadows; present bytes do not authenticate their
transitive package or dynamic ancestry. This observation does not establish
that the three files were absent from every other guard or check.

This is source-declared, point-in-time planning evidence, not Lean's
`--deps`, a successful 61-module extension, an authenticated provider union,
or a printed-port/iPRA join. The active endpoint build must finish successfully
and its resulting sources and objects must be reauthenticated before any
extension. The assembly and syntax client are additional modules. The
[`receipt-preliminary.json`](receipt-preliminary.json) is retained from the
earlier check before adding the assembly and provider-guard observations.
No Lean process was run during this review.

Reproduce while the captured provider paths remain available:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/current14-printed-port-extension-independent/audit.py
```

SHA-256: `audit.py`
`b5b5e2d57529159c1fe0cfefa21013dd1ae213634f084f1b4d579e05dd216c34`;
`receipt.json` `be8eb4524360155102657d0d9b9e9a56eb43d5f528652a173236acdccf2e1e64`.
