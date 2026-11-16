# SCOPE-iPRA

**Scoped Certificates, Observational Projection, and Explicit Residuals** is a
general framework for compiling fixed finite mathematical interactions into
intuitionistic primitive recursive arithmetic.

The report is based on ProveIt main commit
`58627ed89814ba122e1f0f012f1aba103cda267b`.

## Main deliverables

- `scope_ipra_framework.pdf` - full report.
- `scope_ipra_framework.tex` plus `sections/*.tex` - editable source.
- `lean/SCOPE/StructuralKernel.lean` - no-placeholder structural candidate.
- `lean/SCOPE/*Blueprint.lean` and `lean/FORMALIZATION_PLAN.md` - definitions,
  theorem targets, and a dependency-ordered path to completion.
- `reference/scope_reference.py` - exact finite reference algorithms.
- `reference/test_scope_reference.py` - 14 passing tests.
- `examples/demo_certificate.json` - deterministic worked evidence.
- `metadata/` - theorem ledger, difficulty matrix, source audit, claims, and
  integration map.
- `validation/` - captured test and PDF-validation outputs.

## Central idea

A finite witness is a scoped proof resource. It may leave its scope only in one
of five ways:

1. it is eliminated privately by existential elimination;
2. it contributes only an outer existential output;
3. only a certificate-independent observation escapes;
4. it is named canonically by least bounded search;
5. its missing producer remains an explicit residual hypothesis.

This discipline prevents hidden choice and cleanly separates generic finite
verification from theorem-specific producers such as height bounds, analytic
constants, finite covers, and separation margins.

## Reproduce finite tests and demo

```bash
cd reference
python3 -m unittest -v test_scope_reference.py
python3 scope_reference.py --demo ../examples/demo_certificate.json
```

## Build the PDF

```bash
bash build.sh
```

The build script runs the finite tests, regenerates the demo, and compiles the
LaTeX source with `latexmk`. In the artifact runtime, `VERIFY_PDF=1 bash build.sh`
also runs preflight and page rendering. Lean integration requires a ProveIt
checkout; follow `lean/FORMALIZATION_PLAN.md`.

## Formal status

The generic arguments are fully written at the human mathematical level. The
new Lean implementation was not elaborated in this runtime, so the archive
claims no new kernel-checked theorem. Existing checked repository results are
identified separately from new human proofs and executable reference tests.
