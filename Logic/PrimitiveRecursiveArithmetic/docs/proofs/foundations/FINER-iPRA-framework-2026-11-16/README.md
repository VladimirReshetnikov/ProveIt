# FINER-iPRA

**Finite-Interaction Normal Form with Explicit Residuals**

This artifact develops a general framework for compiling theorem-specific
finite mathematical arguments into ordinary intuitionistic primitive recursive
arithmetic (`Prf PRAAx`). It was prepared against
`VladimirReshetnikov/ProveIt` commit
`64bc0e997df6b8dbdf43f5ac9b3d9f74b4047ee5` on 2026-11-16.

## Main result

For each fixed finite-query proof graph, metalevel specialization generates:

- a least finite demand closure, including genuinely cyclic monotone demands;
- one bounded mixed-radix master-certificate space;
- a primitive-recursive Boolean checker and output decoder;
- checked-search selection of the least accepted certificate;
- deterministic trace reflection, backward viability, and stable observers;
- an ordinary object-theory endpoint
  `B₁, ..., Bᵣ, Γ ⊢[PRAAx] Φ` whose `Bᵢ` are exact residual producers.

The report gives full human proofs of the reusable schemas. Two additions are
especially concrete:

1. **Finite monotone demand closure.** On a product of finite chains, iteration
   of `d ↦ d ∨ F(d)` reaches the least prefixed point after at most the sum of
   coordinate capacities.
2. **Finite observational descent.** Exact, quotient, or metric compatibility
   along a checked spanning tree gives a root observation and an explicit
   global error without constructing an infinitary quotient or global witness.

## Verification status

This distinction is essential:

- Existing ProveIt calculus, induction, search, pairing, and arithmetic modules
  cited in the report are inherited checked dependencies.
- The new generic theorems in the report are fully developed **human proofs**.
- `lean/FINER/` contains source-oriented blueprints. Apart from the tiny wrapper
  file, they visibly contain `sorry` milestones and are **not claimed compiled**.
- `reference/` is an exact semantic reference implementation. Its fourteen
  tests pass, but it is **not an iPRA proof checker**.
- Deep theorem-specific producers, such as general effective Diophantine height
  bounds, remain explicit residuals.

This archive claims no new Lean-kernel-checked theorem.

## Contents

- `paper/finer_ipra_framework.pdf` - 54-page report.
- `paper/finer_ipra_framework.tex` and `paper/sections/` - complete LaTeX source.
- `lean/FINER/` - Lean-oriented definitions and theorem targets.
- `lean/FORMALIZATION_PLAN.md` - dependency-ordered route to checked modules.
- `reference/` - exact Python algorithms, tests, and fixture generator.
- `examples/` - JSON certificates for four benchmarks.
- `metadata/` - theorem ledger, difficulty matrix, graph schema, status record,
  and source audit.
- `validation/` - tests, PDF preflight, font/metadata reports, and static scans.

## Reproduce

Requirements: Python 3 and a TeX Live installation with `latexmk`.

```bash
./build.sh
```

Or run the pieces separately:

```bash
PYTHONPATH=reference python3 -m unittest -v reference/test_finer_reference.py
PYTHONPATH=reference python3 reference/generate_examples.py
cd paper && latexmk -pdf -interaction=nonstopmode -halt-on-error finer_ipra_framework.tex
```

For Lean, copy the sources into the pinned ProveIt checkout and follow
`lean/FORMALIZATION_PLAN.md`. A theorem becomes verified only after all `sorry`
markers are removed, its endpoint is literally `Prf PRAAx ...`, and the
repository axiom audit passes.
