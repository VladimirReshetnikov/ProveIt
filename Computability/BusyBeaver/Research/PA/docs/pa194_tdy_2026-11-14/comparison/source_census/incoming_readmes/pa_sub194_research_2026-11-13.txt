# PA consistency machines: comparison and sub-194 research

**Result: the requested blank-start machine with fewer than 194 working states
has not been established.** This archive contains a comparison of all 56 current
research packets, an explicit 193-state runtime core with verified source
contracts, certificates rejecting its tested unchanged startups, a broader
mathematical startup theorem, and the relevant search code and receipts.

The 193-state table is **not** presented as a blank-start Con(PA) machine.
Its runtime correctness and its failed initialization are separate results.
No lower bound on possible PA-consistency machines is claimed.

## Read first

Open `report/report.pdf`. Its complete LaTeX source is `report/report.tex`, with
the other `.tex` files in that directory. The report contains the full runtime
transition table, all 42 frontier classes, the ledger of all 56 packets, the
source-calibration audit, and the broad startup-seed proof.

The corpus snapshot is:

`5784600f8709872fa258af66a94df8deb7075c2f`

Sources: <https://github.com/VladimirReshetnikov/ProveIt/tree/5784600f8709872fa258af66a94df8deb7075c2f>

## Contents

| Directory | Contents and evidence scope |
|---|---|
| `report/` | PDF and complete editable LaTeX report. |
| `comparison/` | 56-packet ledger; census of 1,487 literal-table occurrences, 731 byte forms and 502 complete spanning graph classes; all 42 distinct 194-state representatives; graph and quotient checkers. Reported construction status is inherited from each packet, not a new end-to-end proof. |
| `runtime193/` | Exact 193-state runtime core, source paths/instructions, 4,780-outcome symbolic receipt, all 1,158 elementary startup certificates, reconstruction and independent replay scripts. |
| `reference/haz/` | Compact unmodified compiler/runtime dependencies, original primary native table and grammar, inspection-only mathematical references, licenses and per-file provenance. |
| `research/theory/` | Startup theorems, conservative PA proof-template classifier, atomic-orientation generators, frozen witnesses and search logs. |
| `research/reduction/` | Corrected scan-context collector, neutral-row and startup screens, zero/nonzero abstraction, two checked 194-state compositions, offline reproduction driver and receipts. |
| `research/decoder/` | Exact source-graph reassociation experiments; rejected nominal 193 scores and two auxiliary 194 runtime rotations. |
| `research/restoration_checks/` | Fresh replay receipts produced after reconstructing the portable scripts. |

## Reproduce the main checks offline

Use Python 3.10 or newer, without `-O`; inherited checkers use assertions.
Run these commands from the archive root:

```bash
python3 comparison/verify_frontier.py
python3 comparison/control_quotient.py
python3 runtime193/check_runtime88301.py
python3 runtime193/replay_fold88301.py
```

They check the 42 graph representatives, absence of ordinary one-step control
quotients, all 4,780 source outcomes, and every one of the 1,158 saved startup
traces. The runtime check additionally verifies the exact source-array and
table bytes. Its arithmetic interface depends on the inherited block lemmas
and the explicit two-step marker identity proved in the report.

The checkers do not prove the inherited logical PA calibration by executing
Python, and do not claim an end-to-end compiled Lean theorem for runtime193.
The bundled Lean files are inspection references, not a standalone Lean build.

To regenerate elementary startup classifications into a separate directory:

```bash
python3 runtime193/check_fold88301.py --out /tmp/runtime193-startups
```

The research subdirectories contain their own reproduction instructions.
The local-reduction replay requires a C++17 compiler. Long random searches
are optional and unnecessary for checking the frozen certificates. Copy the
archive before rerunning exploratory scripts that overwrite their own logs.

## Rebuild the PDF

With a normal TeX Live installation containing the packages named in the
report preamble:

```bash
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

`make report` performs those two passes; `make verify` runs the four main
offline checks. The supplied PDF was rendered and visually inspected.

## Exact runtime reduction

The primary native table has SHA-256
`e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54`.
Identify control 301 with 88, redirect all targets 301 to 88, delete control
301, and set the native rows to:

```text
88 0 0 L 51
51 0 0 R 122
```

The resulting sorted table has 193 controls, 386 rows, halt 254, and SHA-256
`50f7be44afb63293365270a83111299247d12d140614e4b4c9a52786163acb53`.
The original start 74 reaches an outward ray; changing only the initial
control does not provide a calibrated startup.

## Evidence boundaries

- A symbolic source contract quantifies over the complete prescribed register
  frame. A finite blank simulation does not replace that contract.
- A ray certificate proves its own infinite continuation; a bounded search
  result makes no claim beyond its explicit bound.
- Context-screen candidates are heuristic proposals until the full runtime
  checker, and any changed arithmetic-block lemma, have been verified.
- Graph equivalence ignores the chosen start while preserving symbols and
  directions. It does not imply equality of designated blank computations.
- The larger startup theorem allows arbitrary six work registers at sites
  25--44 with the three proof-store registers zero. A candidate must still
  reach a complete canonical tape frame.

## Provenance and integrity

Original code, machines and mathematical developments remain attributed to
their authors. See `NOTICE.md`, `reference/haz/PROVENANCE.json`, the retained
licenses, and the subdirectory provenance files. New scripts are separate
from the unmodified reference dependency set.

`STATUS.json` records the incomplete target explicitly. `SHA256SUMS` covers
every delivered file other than itself; check it using `sha256sum -c SHA256SUMS`
from the archive root. Historical absolute paths in logs identify the original
run location; the documented replay commands use bundled relative paths.
