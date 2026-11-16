# Uniform certificates for iPRA (research note)

This research note isolates a uniformization layer complementary to the existing ProveIt finite-contract frameworks: (1) finite-net lifting with an explicit modulus and rational error budgets, (2) uniform root names from sign brackets and algebraic separation, and (3) precision-contract composition. Its concrete benchmark is the stable cubic `y^3 + y = x`, `0 <= x <= 1`.

**Contents**: `framework.tex`, compiled `framework.pdf`, `lean/UniformRootBlueprint.lean` (uncompiled Lean Mathlib-oriented definitions and explicitly named target propositions), `code/cubic_cert.py` (exact rational regression tests), and `VALIDATION.txt`.

**Proof status**: The paper contains human mathematical proofs and an object-language induction plan. There is **no completed Lean `Prf PRAAx` proof** for the main theorems. The Python tests are evidence for exact finite instances, not proof of the universal results. The Lean blueprint is not a claim of successful compilation.

**Build**: `pdflatex -interaction=nonstopmode -halt-on-error framework.tex`, then `python3 code/cubic_cert.py`.

**Repositories consulted**: ProveIt `Logic/PrimitiveRecursiveArithmetic/docs/proofs/README.md`, foundational framework READMEs, `algebra/puiseux_ipra/evidence/scope_obstruction.md`, `diophantine-number-theory/faltings_ipra/README.md`, and `ConciseIPRA/README.md`, plus the existing `ipra_framework/lean/ObjectBridge.lean` adapter.
