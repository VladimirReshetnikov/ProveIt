# Attribution and source provenance

This delivery combines inherited mathematical and implementation work with new transfer constructions, executable audits and a research report. It does not change the attribution or license scope of the included upstream files.

## K230

`vendor/k230-rocq/` preserves the non-hidden tracked source files from Elliot Glazer's `k230-rocq` repository, commit `3142e4dd980f0be12f4abb636c4ae2528afc17eb`. All 103 files covered by that repository's local proof manifest are present and byte-checked. Git metadata and hidden workflow/configuration files are not needed for the local reconstruction and are omitted. The original `THIRD_PARTY.md` and `LICENSES/` are retained unchanged.

The compact K theory, its axiom encoding, its 230-state machine and its formal calibration are inherited from that development. Its reference dependency is `jeff87654/busy-beaver` at `c132d7eae8158cd3a9850ea3eb7251158c3dd821`. That dependency is pinned in the retained manifest but its 115 upstream proof sources are not bundled here. The upstream fetch/build scripts explain how to obtain and recheck them.

The original downloaded successful Linux CI artifact is `evidence/upstream-ci-original.zip`, SHA-256 `60702d530e637fd343eda4d370b73d71924ca5c3f581444196acdf5da344f15f`. It is the `k230-linux-verification` artifact (ID 12192455062) of workflow run 39258562285. Extracted bytes are checked against the original ZIP.

## ProveIt verification and reductions

The requested 235-state reference was added in ProveIt commit `0128d662fd46f72dc84505176ae8ec28affb2d9d` as `docs/incoming/ZFC235_Construction_2026-10-19.zip`.

These files are copied unchanged from that delivery and its included 236/237 dependencies:

| Retained file | SHA-256 | Original role |
|---|---|---|
| `vendor/proveit/build_zfc235.py` | `3184f98cb7d86a6688165aa19b5e715db5fa3facf4eabd6d0ecd88d54df9a75a` | Source/tree utilities and historical 235 construction |
| `vendor/proveit/verify_state_fold.py` | `43c89550f165972cefa619993084b53e10e5d31165d152749ecc3a2144c4044e` | Inductive tape-bit invariant and open-tape fold checker |
| `vendor/proveit/symbolic_runtime.py` | `c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145` | Generic unary/list induction runtime engine |
| `vendor/proveit/independent_runtime.py` | `0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346` | Physical register map and tape/path helper |

The latter two originate in the included `zfc237/verification` directory. Their historical CLI entry points refer to different source/input packages. The new adapter invokes the generic checked functions and independently validates the K-specific source. No behavior of those retained engines was edited.

The predecessor-bit folds, transfer-loop rewrite, boundary sharing, delayed erasure and source-rotation/context-fold search ideas retain the attributions of their ProveIt incoming contributions. The principal new work here is their compatible K230 composition, the constrained 49-atom layout and helper repairs, the final concrete rotation/fold, and the complete new table/source/runtime verification.

`licenses/ProveIt-MIT-0.txt` retains the repository's MIT No Attribution notice. The two C++ discovery programs in `discovery/` are copied from the included 237-stage discovery materials; they are not proof dependencies. The E662 companion preserves its own baseline attribution and license notice.

## Earlier contributors and scope

The underlying calculus and proof-search program are credited to Mira-Cult; the formal busy-beaver reference to Jeff Ketchersid; and the compiler framework to Andrew James Wade's Turing Machine Explorer. ProveIt contributors retain their existing credits. The K230 notices additionally identify BusyCoq (Maja Kądziołka), LibTactics (Arthur Charguéraud), the Coq Library of Undecidability, and their respective MIT, MIT X11, MIT No Attribution and MPL 2.0 scope.

The retained K230 notice expressly identifies custom upstream and adapted sources without a specified repository-wide license. Source availability and inclusion of neighboring license notices do not relicense those sources. This delivery preserves that distinction and assigns no new blanket license to them.

The research report and new Python reconstruction/audit files were prepared in this collaboration for incorporation into ProveIt. No additional personal author or priority claim is invented. The reported optimization optimum is restricted to the fixed 49 atoms, their order, the stated feasibility masks and weighted-depth objective; it is not a global Turing-machine state optimum.
