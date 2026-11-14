# PA consistency machines: comparison and searches below 195 states

## Result

**This packet does not establish a machine with fewer than 195 working states.**
It supplies a newly validated, graph-distinct **195-state** binary machine,
M195S8, and a detailed account of the failed reductions and their proof
obligations. It does not claim that 195 is minimal.

The accepted machine uses a two-way infinite, all-zero initial tape, alphabet
{0,1}, start state 0, working states 0 through 194, and a separate halt
state 195. It has 390 transition rows. The ordinary mathematical argument in
the report establishes

    PA ⊢ Nonhalt(M195S8, blank) ↔ Con(PA),

by a PA-formalizable halting equivalence with the supplied PA195 construction.
The inherited PA195 arithmetic calibration is included for review. No new
end-to-end Lean or Rocq theorem is asserted.

The tempting 194-state quotient in `evidence/rejected_candidate_194/` is
**rejected**. Although its eight local folds and complete source CFG are valid,
its seven-zero source addresses violate the old physical scanner. The
negative checker reproduces its first failed primitive contract.

## Read first

- `report/pa195_followup.pdf`: complete report, comparisons, ordinary proof,
  full accepted transition table, archive catalogue, and new source lemmas.
- `report/pa195_followup.tex`: editable LaTeX source; its included fragments
  are all present in the packet.
- `machine_195s8/pa195_scanner8.tm`: definitive accepted dense transition table.
- `comparison/current_comparison.json`: evidence status and provenance of the
  36 selected earlier literal tables.

## Main replay

Use Python 3 without `-O`, from the extracted packet:

```bash
python3 verify_all.py --out /tmp/pa195-followup-replay.json
```

This hashes every manifest-listed file, reconstructs the accepted machine,
checks all 4,815 raw and all 4,815 folded symbolic contracts, independently
rechecks the source graph, local quotient and complete startup, verifies the
rejected-194 negative control, checks the comparison tables, and replays the
new finite source/deduction checks. It uses the Python standard library.
It creates temporary outputs outside the inputs.

For a deliberately edited research copy, `--skip-hashes` is available; the
receipt explicitly records that hashes were not checked. It does not skip
any mathematical or machine check. It must not be used to describe altered
inputs as matching the distributed packet.

The main command does **not** regenerate every search or compile a new
proof-assistant theorem. The complete two-rotation regeneration and bounded
search commands are documented in their own directories.

## Contents and evidence levels

| Directory | Contents and scope |
|---|---|
| `machine_195s8/` | Accepted 195-state table, native/dense labels, grammar, source CFG, raw203 parent, eight folds, local traces, exact startup, symbolic validation, portable checker and its unchanged dependencies |
| `reference_pa195_packet/` | Supplied PA195 report, machine, mathematical calibration, original reference sources and earlier comparison |
| `comparison/` | All 31 incoming ZIPs catalogued, hashes, 36 selected distinct rooted tables, statuses and independent structural checker |
| `source_extensions/` | Gamma relocation, 48 gate forms, witness-head bundling, literal-coincidence obstruction, explicit deduction trees, source checks and search receipts |
| `evidence/scanner8_independent_audit/` | Independent source parser/compiler, local executor and startup simulators; repeated symbolic runtime; bounded two-cell screens |
| `evidence/rejected_candidate_194/` | A 194-state local quotient that fails its source runtime; explicitly rejected |
| `search/two_rotation/` | Exhaustive neighborhood, full canonical keys, per-grammar census, independent verification and source code |
| `search/association/` | Seeded finite heuristic searches, complete C++ sources/inputs, logs and retained grammars |
| `search/window_merge/` | Five-cell and nine-cell nonrecursive local discovery screens |
| `search/added_routers/` | Finite one/two-router sharing searches, compatibility checks and receipts |
| `evidence/` | Additional receipts, scanner explanations, source-transfer proof and finite invariants |

The complete accepted table SHA-256 is:

    df6ec639713c4ae7bb3656e59c833dd55ca6336a46bea8327eca639341b34662

It is distinct from all 36 selected earlier rooted transition graphs.
Its 59,164-step blank startup ends at native state 84, head -2, with exactly
66 one cells and the intended complete physical register file.

Symbolic execution counts are counts in an accelerated checker. They are not
literal runtime bounds for all natural register values. The register-block
lemmas account for the unbounded finite excursions.

## Build the report

With an ordinary LaTeX installation:

```bash
cd report
pdflatex -interaction=nonstopmode -halt-on-error pa195_followup.tex
pdflatex -interaction=nonstopmode -halt-on-error pa195_followup.tex
```

The delivered PDF has been compiled and visually inspected.

## Provenance and attribution

Repository snapshot:

    5be8b9236df6a6d308195e62a906a173dc70d00a

Original PA195 ZIP SHA-256:

    0001250c43a40920027403d748bcca36e4519a5a45e94dec98cafad4f3c8ff9f

The underlying PA196/PA209 work is attributed to James Chang and the supplied
ProveIt research lineage. Original MIT notices are retained in `comparison/`.
Original files and new certificates have distinct paths and provenance.
The top-level manifest covers the delivered bytes; historical receipts may
retain the absolute scratch paths from their original runs. Those historical
paths are not needed by the portable replay commands.

No finite negative search here proves that a smaller consistency machine is
impossible. The strict state-reduction objective remains unresolved.
