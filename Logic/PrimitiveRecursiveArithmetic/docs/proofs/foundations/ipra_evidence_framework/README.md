# Evidence-indexed finite mathematics in iPRA

Read `report.pdf` (source: `report.tex`). The primary additional idea is a **finite relational-output/compatibility interface**. It avoids forcing a uniform exact choice when only finite approximate families are justified. A backward finite dynamic program proves a witness-amalgamation theorem. Includes a worked exact-rational square-root example, representation/obstruction caveats, and a Lean formalization roadmap.

## Source comparison

Consulted the ProveIt `Logic/PrimitiveRecursiveArithmetic` folder, especially:
- `docs/proofs/README.md` (catalog and verification caveats)
- `docs/proofs/foundations/ipra_embedding_framework/README.md`
- `docs/proofs/foundations/ipra_framework/README.md`
- `docs/proofs/foundations/ipra_framework_2026-11-15/README.md`
- `docs/proofs/algebra/puiseux_ipra/evidence/scope_obstruction.md`
- `docs/proofs/analytic-number-theory/pnt_li_ipra_2026-11-15/evidence/FINAL_MATHEMATICAL_AUDIT.txt`
- `ConciseIPRA/README.md` and an existing `lean/ObjectInterface.lean`

The prior framework results are **credited, not claimed as novel**. This is a targeted extension, not an audit of every report.

## Status

- Human proofs of bounded search, finite viability, monotonicity under constraints and the rational example: included.
- Python finite tests: run; outputs in `verification.txt`.
- Lean: source blueprint only, **not compiled**; object-level `Prf PRAAx` derivations remain an explicit obligation. The non-fuel `viable` definition illustrates the intended relation and may need its termination proof before it elaborates; the `viableFuel` variant is structurally recursive.
- No general analytic or arithmetic geometry conjecture is claimed solved.

## Rebuild

`pdflatex -halt-on-error report.tex` (twice for references); `python3 code/finite_chains.py`.
