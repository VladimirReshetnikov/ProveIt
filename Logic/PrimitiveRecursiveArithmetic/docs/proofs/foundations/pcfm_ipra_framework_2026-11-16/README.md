# Proof-Carrying Finitary Modules for iPRA

This archive develops **Proof-Carrying Finitary Modules (PCFM)**, a shallow
object-theory framework for turning finite mathematical computations and
certificates into derivations in the ordinary ProveIt iPRA calculus.

Repository baseline:

```
VladimirReshetnikov/ProveIt
7fa3ba48e8f62e8018ed954faaa48b908217eaf1
2026-11-16
```

## Main deliverables

- `paper/pcfm_ipra_framework.pdf` - the compiled research report.
- `paper/pcfm_ipra_framework.tex` and `paper/sections/*.tex` - complete source.
- `lean/` - Lean-oriented module skeletons and exact target signatures.
- `code/reference.py` - exact-integer/rational reference algorithms.
- `tests/test_reference.py` - regression tests.
- `metadata/status.json` - theorem and artifact status ledger.
- `SOURCE_AUDIT.md` - repository files and APIs inspected.
- `STATUS.md` - verification and limitation statement.

## Central idea

A module stores a literal object-theory proof:

```text
requirements |- [PRAAx] output
```

Specialization is `Prf.subst`, composition/discharge is `Prf.trans`, and loops
are compiled through a quantifier-free invariant. Missing moduli, height
bounds, separation gaps, finite-cover margins, and similar deep inputs remain
explicit residual formulas.

The framework is deliberately shallow. A theorem-specific Lean assembler
returns `Prf PRAAx` terms directly; it does not rely on a total universal
primitive-recursive evaluator or on a monolithic unverified compiler.

## Reproduction

From the archive root:

```bash
bash scripts/build.sh
```

The script runs the Python regression tests, executes the reference
demonstration, compiles the LaTeX report to convergence, and writes logs under
`metadata/`.

Lean is not installed in the artifact runtime. The included Lean files are
therefore not claimed compiled; see `lean/README.md`.

## No-overclaim summary

The paper gives complete human-readable arguments for the framework's main
lemmas and a clear Lean path. The PDF and Python tests are generated and
checked in this archive. No new kernel-checked ProveIt theorem is claimed until
the Lean skeletons are integrated and built in the repository.
