# Artifact manifest

## Core report

- `paper/fiber_ipra_framework.pdf` - 42-page compiled research report.
- `paper/fiber_ipra_framework.tex` - master LaTeX source.
- `paper/sections/*.tex` - modular report sections and appendices.

## Lean-oriented artifacts

- `lean/FIBER/Kernel.lean` - structural aliases targeting current
  `ConciseIPRA`/`IPRADerivations` APIs.
- `lean/FIBER/Blueprint.lean` - metalevel bounded-formula, interface, and source
  graph skeleton with dependency-ordered theorem targets.
- `lean/FIBER.lean` - aggregate import candidate.
- `lean/FORMALIZATION_PLAN.md` - phased path to compiled `Prf PRAAx` theorems.

## Executable finite reference layer

- `reference/fiber_reference.py` - exact finite algorithms for bundling, least
  search, demand closure, bounded strategies, dyadic bounds, finite nets,
  bisection, and Herbrand capsules.
- `reference/test_fiber_reference.py` - 14 unit tests.
- `reference/generate_examples.py` - deterministic JSON example generator.
- `examples/*.json` - generated finite certificates and traces.

## Audit and status

- `metadata/THEOREM_LEDGER.md` - claim-level proof status.
- `metadata/difficulty_matrix.csv` - consolidated obstacles and repairs.
- `metadata/framework_schema.json` - proposed source metadata schema.
- `metadata/proof_status.json` - machine-readable artifact status.
- `metadata/SOURCE_AUDIT.md` - inspected repository files and prior frameworks.

## Validation

- `validation/python_tests.txt` - complete passing test log.
- `validation/latex_build.txt` - successful LaTeX build log.
- `validation/pdf_preflight.txt` - PDF openability/page preflight.
- `validation/pdf_inspect.txt` - metadata/font/outline inspection.
- `validation/pdf_text.txt` - extracted text for search and sanity checks.
- `validation/visual_review.md` - record of full-document render inspection.

## Reproduction

- `build.sh` - rerun tests, regenerate examples, and compile the PDF.
- `SHA256SUMS` - checksums of every packaged file except the checksum file.
