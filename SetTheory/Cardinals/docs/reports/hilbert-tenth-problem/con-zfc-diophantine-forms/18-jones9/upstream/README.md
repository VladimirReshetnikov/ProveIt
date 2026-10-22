# Selected upstream sources for offline review

This directory preserves selected sources from
`VladimirReshetnikov/ProveIt` at commit
`f0ae4e0991ca44a7bb4e5671d42e33d775e48035`. The original repository path,
size, and SHA-256 of every selected file are recorded in `SOURCES.json`.
Sources are copied without editorial changes. Internal historical pins,
references, and coefficient choices in those documents remain their
original authors' statements; the main report defines this package's
actual construction and coefficient binding.

The collection is intended for **offline mathematical review and replay
of the two T4 finite checks**. It is not the full transitive proof closure,
not a standalone Lean project, and not a runnable distribution of every
historical script or linked example.

## Organization

| Directory or file | Contents |
|---|---|
| `t4/bridge/` | Original T4 coefficient recipe, mathematical bridge audit, literal transition data, and exhaustive checker. |
| `t4/review/` | Original independent successor-generation checker and its replayed receipt. |
| `reports/09-combined13/` | Weighted-root elimination and audit, ordinary low-degree lift, frozen quartic32, and blank-helical proof. |
| `reports/12-gap-norm14/` | Ordinary-strong and gap proofs, inherited blank67 and Pell audit notes. |
| `reports/14-integer29/` | Signed-domain argument, independent review, ordinary Pell interface, and ordinary-strong proof. |
| `reports/COMPARISON_README.md` | Pinned repository comparison and the original authors' stated scope. |
| `math/1980/` and `math/research-wip/` | The 27 selected Pell and compiler dependencies named by the preserved T4 dependency manifest. |
| `lean/Diophantine/` | Selected Jones nine-variable, coding, and relation-combining formal sources. |
| `lean/BusyBeaver/ZFC/KEndpoint215.lean` | Exact-machine Lean endpoint source. |
| `machine/` | Literal `k215.tm`, ordinary machine proof, original notices, source attribution, and inherited licenses. |
| `K215_README.md` | Pinned repository record of the existing formal verification lanes. |
| `licenses/` | ProveIt's root license; machine-specific notices and licenses also remain under `machine/`. |

## Replay the T4 checks

From the unpacked package root:

```sh
python3 upstream/t4/bridge/check_t4.py
python3 upstream/t4/review/independent_t4_checks.py
```

The original directory layout is preserved, so the scripts also work when
invoked by absolute path from another working directory. They use Python's
standard library and the supplied local data. Run them in the displayed
order. They write the canonical tile list and two receipts beneath `t4/`.

Both unchanged scripts were replayed for this delivery. They checked all
20,624,220 filtered quadruple candidates, obtained exactly 37,075 T4 tiles,
and agreed on the ordered tile list. The geometric checks cover 1,319
field targets; the helical controls cover 927 local windows. The independent
checker generates successors separately rather than importing the first
checker's predicate.

The canonical tile-list SHA-256 is
`9c2e473b5dbc5b3dc1468a31aefdbec6a901d6ba1e6b1ec9212698d41e1d84b1`.

The three generated files are explicitly marked `freshly_replayed` in
`SOURCES.json`:

- `t4/bridge/t4_windows.json`
- `t4/bridge/t4_verification.json`
- `t4/review/INDEPENDENT_T4_CHECKS.json`

Their repository-path fields identify the corresponding historical
artifact locations; the status makes clear that these copies are the
outputs of the present replay. Their hashes are computed after the replay.

## Evidence boundaries

The finite T4 checks establish the stated table, local alphabet, support,
population, carry-bound, and geometric facts. They do not replace the
unbounded native-compiler theorem, prove K215 halts or fails to halt, or
prove Con(ZFC). The mathematical reductions and their dependency boundaries
are described in the main report and the preserved proof notes.

The selected Lean source files retain their original imports. The full
project, pinned Lean toolchain, Mathlib, and remaining imports are not
bundled here. No new Lean or Rocq build is asserted by this source collection.
The existing machine endpoint's formal status does not automatically
extend to the new Diophantine reductions.

All 27 downloaded mathematical dependencies match the SHA-256 values in
the inherited historical dependency manifest; that fact is recorded per
file. It verifies the identity of this selected dependency set, not a full
transitive closure. The manifest itself retains its original earlier pin.

## Attribution and reuse

Preserve `machine/NOTICE.md`, its `provenance/` attribution notes, and all
files in `machine/licenses/` when redistributing the inherited machine
material. They credit the contributing machine, compact-theory, compiler,
and formalization work and retain its original terms. The root project
license in `licenses/LICENSE.ProveIt` does not relicense inherited
third-party components. No new discovery-priority claim is made by bundling
these sources.
