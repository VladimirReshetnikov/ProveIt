# U211: decoder reassociation and a guarded state deletion

Research prepared for Vladimir Reshetnikov, 28 October 2026.

This archive supplies an explicit **211-working-state, two-symbol, one-tape
Turing-machine candidate** for Con(PA), including its entire blank initialization.
It reduces the common supplied U212 machine by eleven closed source-tree
reassociations followed by the deletion of native state 218.

Read `report.pdf` for the complete argument, comparison of all eight proposals,
proof boundaries, exact patch, and all 422 dense transition rows. `report.tex`
and `source_transport.tex` are the editable source. The three other TeX files
contain the generated table fragments; their contents are also inlined in the
main report to make the long-table environments robust across TeX installations.

## Machine conventions

`machine/u211.tm` is the primary executable table:

- Working states: 0 through 210; separate halting label: 211.
- Alphabet: 0 and 1. One head on a two-way infinite tape.
- Start: working state 0, head coordinate 0, all tape cells zero.
- Only left and right moves; all 422 working-state/symbol pairs are defined.
- A row `q b w D r` means: in state q scanning b, write w, move in direction
  D (L or R), and enter state r. A transition into 211 halts after its write/move.
- `#! start 0` is a header, not a transition.

`machine/u211.native.tm` retains sparse inherited state labels for auditing;
its separate halting label is 254. Those label values are not a state count.
`machine/state_map.json` supplies the checked bijection to the dense table.
All 211 working states are reachable in the transition graph; no claim is made
that every state is visited in the particular blank run.

| Artifact | SHA-256 |
| --- | --- |
| Dense table | `b7cd1359872334097d7a17c533c52c0aca46e05b0b901136d1b3e0f30fdf2304` |
| Native table | `72234980bd604524d5cd39e16f0e7f40c8547161334d65045fba5743e26db1c1` |
| Final source | `3f74267c84fc31cb7e9c596548dc698e17212a097ebf2f6f0e75c7a67992ec08` |

## What is proved, and at what level

Let A be the frozen incoming U212, R the rotated 212-state intermediate, and C
the delivered U211. The new ordinary mathematical argument is formalizable in
PA and gives

    PA proves Halt(C, blank) <-> Halt(A, blank).

The source transformation preserves every ordered primitive and its complete
ordinal control-flow graph. A full symbolic runtime derivation verifies the
final interpreter for arbitrary natural registers and arbitrary finite spare
lists in the specified frame. The complete literal blank-start prefix and its
source bridge are checked exactly. The separate local fold R -> C preserves
halting from state 0 on every common initial tape; that stronger arbitrary-tape
claim is not asserted for the entire source reassociation A -> C.

Composing the new reduction with the supplied numerical-calculus and U/PA
interpretation arguments yields the inherited endpoint

    PA proves not Halt(C, blank) <-> Con(U) <-> Con(PA).

This is an ordinary PA-formalizable proof with executable finite and symbolic
evidence. It is **not** a newly exported formal PA proof object or a newly
compiled Lean, Rocq, or MM0 theorem. The inherited theory and proof-search
calibration remain explicit dependencies. Python is not a proof-assistant
kernel. No unconditional nonhalting, global minimality, or priority claim is
made.

The source implemented by the machine uses the inherited numerical calculus
for unrestricted weak cover plus global irreflexivity. Its consistency is
calibrated to the unary Theory U. The machine does not newly implement the
separate positive-reference emitter in the theory packet.

## Offline reproduction

Requirements: Python 3.10 or later, with its standard library. No network,
optimizer, external solver, or proof-assistant installation is needed.
From this archive's top-level directory run:

```sh
python3 checks/check_manifest.py
python3 checks/verify.py
python3 checks/verify.py --full
```

The first command verifies every delivered payload file against `MANIFEST.json`.
The second reconstructs both machine tables and the new source from the frozen
parent and short recipe, checks both source-successor algorithms at all eleven
stages, runs independently written construction and startup checks, and verifies
the inherited runtime engine's provenance. It also checks two deliberately
invalid local replacements. This command normally takes a few seconds.

The `--full` command additionally regenerates all 5,084 symbolic runtime cases
on the exact candidate and checks them against the delivered case records as
data. The fresh full replay used about 114 seconds in the preparation environment;
runtime depends on the machine. Its summary is in `evidence/verification.json`.
Assertions must remain enabled for the full symbolic replay; the wrapper rejects
optimized Python for `--full`. The independent finite checker also passes under
`python3 -O` and performs its checks with explicit exceptions.

All regenerated data goes under `build/`, which is created on demand. The
delivered evidence is not overwritten. The parent ZIP is hash-checked before
safe extraction. To run the independent checker directly, first run
`python3 checks/rebuild.py`, then `python3 checks/independent_check.py`.

To compile the PDF from the archive root, use a standard TeX installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

Alternatively use `latexmk -pdf report.tex`. Recompiling can change PDF metadata
and therefore its manifest hash; verify the delivered manifest before rebuilding
the PDF, or keep the rebuilt PDF separately.

## Fresh verification results

| Check | Result |
| --- | --- |
| Literal machine | 211 working states, 422 total binary rows |
| Closed source rotations | All eleven; all 33 factors closed |
| Ordered source occurrences | 3,909, all preserved |
| Guarded source/runtime cases | 5,084 / 5,084 passed |
| Literal rows covered by runtime derivations | 422 / 422 |
| Symbolic inference applications | 1,245,944 |
| Exact blank prefix | 48,140 transitions; identical whole tape |
| Retained native rows changed | 19; two outgoing rows of 218 removed |
| Repeat runtime derivations | Exact data equality with discovery cases |
| Negative controls | Wrong helper write and false predecessor premise rejected |

The universal runtime cases use arbitrary natural register variables and finite
list induction; these are not bounded numerical test samples. The exact proof
rules and their trust boundary are explained in Sections 5-7 of the report.

## Provenance and proposal comparison

The comparison is pinned to ProveIt commit
`9d50bf3df8c9e14941b549945c4f8400172d81f4`:

<https://github.com/VladimirReshetnikov/ProveIt/tree/9d50bf3df8c9e14941b549945c4f8400172d81f4/docs/incoming>

Seven complete U212 proposals have byte-identical final native tables, dense
tables, and sources. Numbered Stacked (5) is a genuinely truncated repository
blob: 50 complete local ZIP members verify, but final machine members and the
central directory are absent. Its recoverable metadata identifies the common
U212; it is not counted as an eighth byte-verified table. Historical controls
reported by the packets are distinguished from the fresh checks performed here.

The exact original `u212_combined_2026-10-29.zip` is included under `inputs/`
(SHA-256 `993a97dd787144f7c9fcc7303f33032a392e866ba66ad15eb2aa2ebb1e48f56b`).
It preserves the earlier U212/U213 source and mathematical proof dependencies,
including the unchanged `pa_unary_power_cover.zip` at
`u212_combined_2026-10-29/baseline/primary_u213/inputs/pa_unary_power_cover.zip`.
The four unchanged native runtime-checker files were selected from the identical
parent in the ConU packet; `checks/native56/PROVENANCE.json` records their exact
archive/member provenance and hashes. `checks/check_engine.py` compares its
inference core with the retained parent engine under the explicit state mapping
and 56+g header convention. The old standalone startup decoder in the vendored
`check_startup.py` is not used; runtime imports only its literal-table loader.

## Archive map

| Path | Contents |
| --- | --- |
| `report.pdf`, `report.tex`, `source_transport.tex` | Complete 13-page report and editable proof source |
| `machine/` | Dense and native U211, rotated U212 intermediate, state bijection |
| `source/sites.json` | Final source, with 3,909 primitive occurrences |
| `construction/` | Short deterministic recipe and detailed rotation certificate |
| `checks/` | Rebuilder, independent checks, full symbolic replay, manifest check |
| `comparison/` | Eight-proposal comparison, Git inventory, archive census |
| `evidence/` | Fresh receipts, full compressed runtime cases, semantic reviews |
| `inputs/` | Unchanged original compact U212 dependency archive |
| `MANIFEST.json` | SHA-256 and size of each payload file |

The release excludes generated `build/`, Python bytecode, and TeX auxiliary
files. Exploratory unsuccessful tables are not included as candidates.
