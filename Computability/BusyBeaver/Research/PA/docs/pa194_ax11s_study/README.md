# PA194AX11S: comparison, construction and proof audit

## Result

This packet does **not** establish a machine with fewer than 194 states or
the requested absolute iPRA theorem. It provides a new, materially different
194-state physical/source composition, PA194AX11S, and an explicit relative
iPRA source-equivalence proof. The machine-specific iPRA calibration remains
open. The current ProveIt PA README also leaves that calibration open for
the primary PA194 machine.

Start with **`report/main.pdf`**. Its complete LaTeX sources and generated
appendices are in `report/`, with mathematical sections in `proof/`.

The comparison is pinned to ProveIt commit
`1c9524d8bf2e0a27b9a16ff622359927f536e663`. It covers 61 filed packets and
11 incoming archives. The fresh census recognizes 3,422 literal/JSON table
occurrences and 638 complete spanning graph classes across all sizes.
All 82 historical complete spanning 194-state classes have frozen
representatives and recomputed canonical tuples. PA194AX11S matches none,
even after arbitrary relabeling, spanning-start choice, reflection,
symbol exchange, and ignoring the decoration on terminal halt edges.
This is structural novelty within the documented recognition scope.

## Machine and source

`machine/machine.tm` is the authoritative dense table:

- One two-way infinite tape; alphabet `{0,1}`; blank symbol `0`.
- Head starts at position zero; working state starts at `0`.
- Exactly 194 working states (`0` through `193`) and 388 transition rows.
- Terminal label `194` has no outgoing rows and is not counted.
- Every transition writes a bit and moves exactly one cell left or right.
- No external initialization or preloaded input.

Each row has five fields: `state read write direction next`.

Dense SHA-256:
`ae52144ee2bb48e2e90cd473b09054d2024cbdd05deb7261a9bb5bfbf67b4db1`

Native SHA-256:
`e20ddac13f587826e318e1d1e1f0d823033da438edd00a811b12a2ae28966909`

The new composition combines the inherited eleven-entry, four-operand AX
interface with the symmetric **original sum-based** Shift implementation.
It preserves AX11 command behavior, including nonhalting of Shift when
the visible top and cached head are both one. It changes recurring
execution rather than merely renaming controls or patching unused rows.

The source shrinks from 3,672 to 3,669 instructions. The complete blank
startup reaches the required frame in 58,004 transitions, versus 58,154
for the supplied AX11 parent. This is a startup saving, not a uniform
physical speedup theorem.

## What was verified

`full_verification.json` records a successful isolated deterministic run:

- Exact regeneration and byte comparison of 13 construction outputs.
- Construction checker: all 4,775 source outcomes, 1,485,873 symbolic steps.
- Independent literal-row checker: all 4,775 outcomes, 1,082,137 symbolic
  steps, four generic list lemmas derived from rows, no arithmetic-box
  oracle, and exact equality of the complete startup tape.
- Exact source graph boundaries and finite checks of the duration
  formulas. The all-natural iPRA argument is written in
  `proof/source_equivalence.tex`; it is not inferred from those samples.
- The cofinite coefficient-three obstruction certificates.
- Recomputed structural novelty against every frozen 194-state class.

These are executable mathematical certificates, not a new Lean or Rocq
kernel proof of the absolute consistency equivalence. No such theorem
is represented as established anywhere in the packet.

The recorded full verification preceded final packaging, so its
`integrity_files_checked` field is zero. A fresh run also verifies every
entry of the final `SHA256SUMS` manifest before doing the computations.

## Reproduce the deterministic checks

Python 3.10+ with its standard library is enough. Keep assertions enabled;
do not use `-O` or `PYTHONOPTIMIZE`. Run from the packet root:

```sh
python3 -B verify_all.py --receipt fresh_verification.json
```

The command works in a temporary copy and does not rewrite the frozen
construction or its receipts. It needs no network, original repository,
solver, or proof assistant. The chosen receipt is a new file; using the
example name keeps the frozen manifest valid.

The independent 193-state startup audit is also self-contained:

```sh
python3 -B comparison/check_rejected193.py --receipt fresh_rejected193.json
```

It checks all 53 classes' metadata and performs the documented 9,652
blank runs for the runtime/relay classes, finding 102 halts and 9,550
certified outward rays. The coefficient-three rejection is logical and
is attributed separately; this startup command does not replay the old
long primitive logical certificate.

The optional full corpus rescan requires a checkout at the pinned
revision. Its recognized formats and exact invocation are documented
under `comparison/`. Bounded search replays, compiler requirements,
candidate pools, and limitations are in `research/startup/README.md` and
`research/grammar/README.txt`. No search result is a state-count lower
bound.

## Rebuild the PDF

Install a normal LaTeX distribution with pdfLaTeX and the packages named
in `report/main.tex`, then run:

```sh
bash build_report.sh
```

This refreshes the report tables from the frozen receipts and runs
pdfLaTeX twice. Generated LaTeX auxiliary files are not needed to use the
delivered PDF. Rebuilding changes generated files, so the original
integrity manifest applies to the delivered bytes.

## Contents

| Path | Purpose |
|---|---|
| `report/` | Complete report, bibliography, all 72 deliveries, all 82 prior classes, complete transition table |
| `machine/` | Dense/native/raw tables, source, label bijection, folds, startup and contract evidence |
| `build.py`, `construction/` | Deterministic construction and attributed physical engines |
| `verification/` | Independent literal-row checker and inherited reference engines |
| `proof/` | Relative iPRA theorem, cofinite collision theorem, proof-status audit and checkers |
| `comparison/` | Full census, delivery ledger, 194-state frontier, 193-state replay and representatives |
| `research/` | Bounded startup/helper/decoder searches, inputs, logs and reproducible receipts |
| `reference/` | Pinned parent, inherited logical arguments, current status and conditional endpoints |
| `STATUS.json` | Machine-readable positive and unresolved claims |
| `PROVENANCE.json`, `NOTICE.md`, `licenses/` | Attribution, dependencies and preserved licenses |
| `SHA256SUMS` | SHA-256 manifest for every other delivered file |

The two main remaining obligations are the internal physical/controller
frame simulation and the arbitrary-internal-PA-proof compiler needed to
supply the existing all-model calibration premise. The report states
their scope explicitly. No remote repository was modified.
