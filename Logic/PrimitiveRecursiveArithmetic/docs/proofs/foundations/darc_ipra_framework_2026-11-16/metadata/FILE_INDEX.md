# File index

## Start here

- `README.md` - package overview and verification status.
- `paper/darc_ipra_framework.pdf` - 56-page report.
- `paper/darc_ipra_framework.tex` - main LaTeX source.
- `paper/sections/` - editable section sources.

## Lean

- `lean/DARC/StructuralKernel.lean` - no-placeholder source candidate using the
  current ordinary `Prf PRAAx` interface.
- `lean/DARC/DemandBlueprint.lean` - least finite demand closure targets.
- `lean/DARC/BoundedReflectionBlueprint.lean` - fixed bounded-formula compiler.
- `lean/DARC/TraceBlueprint.lean` - normalized trace targets.
- `lean/DARC/RelationalBlueprint.lean` - finite viability targets.
- `lean/DARC/CompilerBlueprint.lean` - global compiler target.
- `lean/DARC.lean` - umbrella import.
- `lean/FORMALIZATION_PLAN.md` - phased integration plan and acceptance tests.

## Executable finite reference layer

- `reference/darc_reference.py` - demand, strategy, trace, and viability
  algorithms.
- `reference/test_darc_reference.py` - 11 unit tests.
- `reference/generate_demo.py` - generated finite fixture.
- `reference/validate_artifact.py` - schema/source/claim consistency checks.
- `examples/demo.json` - generated analysis and certificates.
- `examples/sample_plan.json` - machine-readable DARC plan instance.
- `schema/darc_plan.schema.json` - JSON Schema Draft 2020-12.

## Audit metadata

- `metadata/THEOREM_LEDGER.csv` - theorem and formalization status.
- `metadata/DIFFICULTY_MATRIX.csv` - obstacle-by-obstacle resolution map.
- `metadata/SOURCE_AUDIT.md` - pinned repository audit and novelty boundary.
- `metadata/CLAIMS.json` - machine-readable claim limits.

## Validation

- `validation/test_output.txt` - passing test run.
- `validation/artifact_validation.txt` - static package checks.
- `validation/latex_build.log` - final LaTeX build transcript.
- `validation/pdfinfo.txt` and `validation/pdf_preflight.txt` - PDF metadata and
  preflight.
- `validation/pdftotext.txt` - extracted text for search/review.
- `validation/render_review.md` - visual inspection record.
- `validation/source_scan.txt` - final source-status summary.
