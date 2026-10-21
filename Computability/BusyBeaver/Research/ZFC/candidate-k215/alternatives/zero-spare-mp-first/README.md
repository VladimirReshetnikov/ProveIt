# Zero-spare MP-first proof search at 215 states

This packet supplies one new composition, not a 214-state result. The exact machine combines the MP-first transfer command language with zero-valued spare allocation and a newly matched dirty-cache startup. The literal table has 215 working states and 430 rows.

## What is new

- Zero-spare allocation changes the unit-spare MP-first parent's physical row 198/read 0 from 1L40 to 0L40; initial state is native 74.
- A complete 73,172-step native/dense blank replay reaches source ordinal 119. A separate 177-step AX prefix identifies its exact meaning.
- Completing AX leaves eight theorem heads above a numerical suffix whose theoremhood is not assumed. The MP-first diagonal theorem gives conservative debt one, so at least seven theorem heads permanently protect that suffix.
- All 6,209 arbitrary-natural guarded physical cases pass, covering all 430 rows, with 1,610,781 symbolic rules and minimum affine duration constant 10.
- The candidate has no rooted state-renaming or reflected match in the frozen 77-table / 44-graph comparison set, covering all 28 current candidate-k215 table paths at the pinned snapshot.

The source calculus, compiler, backend, and their authors' prior work are explicitly inherited. This is an ordinary mathematical calibration with executable symbolic certificates, not a new Lean/Rocq endpoint for these exact bytes. The upstream original accepted K215 has compiled kernel evidence; that fact is not silently transferred to this alternative. No unconditional nonhalting or minimality claim is made.

## Files

- `report.pdf`, `report.tex`, `sections/`: standalone article and complete canonical transition table.
- `machine/candidate.tm`: dense table, initial 0, working labels 0..214, halt 215.
- `machine/candidate.native.tm`: native table, initial 74, halt 254.
- `machine/`: source, recipe, exact startup, complete symbolic runtime evidence, standalone verifier and unchanged parent packet.
- `research/rejected_biased/`: a separate exact rejection of the public scratch-biased experiment and a conditional adjacent-success-pair encoding lemma. These are NOT a second calibrated machine.
- `manifest.json`: complete release inventory with SHA-256 hashes.

## Reproduce offline

Use Python 3.10 or later, standard library only, with assertions enabled:

    python3 -B verify.py
    python3 -B verify.py --runtime --work /a/new/external/directory

The default reconstructs the literal machine, repeats blank/source checks, rechecks the bounded novelty corpus, audits the stored unbounded census, and independently repeats the rejected source's control-flow witness. It does not claim to freshly derive the unbounded census. The `--runtime` option does so and requires every per-case result and covered row to match the frozen evidence. Runtime refers to the proof-construction process, not to a numerical bound on the represented registers or machine execution.

Verification writes receipts outside the packet and checks the complete inventory before and after. The parent verifier and parent evidence retain the unit-spare predecessor's identity; the outer machine verifier binds the changed table and source explicitly. Python `-O` and `-OO` are rejected.

To rebuild the report with TeX Live, run `sh build.sh`. Compilation creates auxiliary files; build in a separate copy if you intend to preserve the original exact release manifest. Optional `K215_TEXFORMATS` supports installations with a separate prebuilt format directory.

Dependency paths printed in the report are relative to the `machine/` directory. The rejected experiment retains its original upstream notice verbatim; its added PROVENANCE.md explains that notice's historical scope.

The inspected repository snapshot is f5b2db607f8cf1daccf601b4ce14d7cee38b6770. The comparison scope and proof status are explicitly bounded to the identified artifacts. The packet was prepared for incorporation into ProveIt; no repository changes or commits are included in this delivery action.
