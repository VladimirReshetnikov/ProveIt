# Validation summary

Validated on 2026-11-16 against the packet contents.

## Executable reference model

- `python3 -m unittest -v reference/test_strive_reference.py`: **11 tests passed**.
- The tests include 250 randomized heterogeneous mixed-radix round trips,
  exhaustive soundness scans over every strategy code for the supplied small
  formulas, empty-bound conventions, malformed-code rejection, cyclic demand
  closure, and JSON serialization.
- All generated JSON examples and `metadata/CLAIMS.json` parse successfully.
- Python sources compile with `compileall`.

## PDF

- Main report: `paper/strive_ipra_framework.pdf`.
- Pages: **46**, letter size.
- PDF is openable, unencrypted, searchable, and not scan-only.
- All fonts reported by `pdffonts` are embedded.
- LaTeX log: **0 overfull boxes** and **0 PDF-string warnings**.
- PDF outline items: **124**; form fields: **0**.
- The PDF was rendered at 180 dpi into 46 PNG pages. Four contact sheets in
  `validation/contact_sheets/` were inspected for clipping, overlap, broken
  glyphs, tables, equations, code listings, and references. No visual defect
  was found.
- A forced rebuild produced PNG renders byte-identical to the inspected render.

## Lean status

- The runtime supplied no `lean` or `lake` executable, so no Lean elaboration
  or kernel replay was possible.
- `lean/STRIVE/Kernel.lean` has no `sorry`, `admit`, added `axiom`, or added
  `constant` declaration, but remains an **uncompiled source candidate**.
- The larger blueprint files contain **12 explicit `sorry` proof
  milestones**: MixedRadix.lean:77, MixedRadix.lean:86, MixedRadix.lean:97, MixedRadix.lean:112, MixedRadix.lean:124, MixedRadix.lean:141, MixedRadix.lean:152, CompiledFormula.lean:93, CompiledFormula.lean:98, CompiledFormula.lean:103, CompiledFormula.lean:115, CompiledFormula.lean:122.
- No new Lean-kernel-checked theorem is claimed.

## Reproduction

Run `bash build.sh` to rerun Python tests, regenerate examples, and rebuild the
PDF. Complete Lean verification follows `lean/FORMALIZATION_PLAN.md` inside the
pinned ProveIt checkout.
