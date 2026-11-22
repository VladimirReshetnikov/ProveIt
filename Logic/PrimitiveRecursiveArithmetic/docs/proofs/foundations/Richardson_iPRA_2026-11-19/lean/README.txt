LEAN SOURCE STATUS
==================

Files:
  LogicalCore.lean      Constructive logical implications and diagonal proof.
  Syntax.lean           AST for the exact elementary-expression language.
  FormalizationPlan.txt Object-level target, interfaces, sources, and proof gates.

The two .lean files use only Init. They contain no axiom declarations and no
proof holes. They were inspected manually but NOT COMPILED in this session.

The main proved-source theorem is parametric:
  Richardson.noDeciderExists (F : Richardson.Framework)

Framework explicitly assumes the arithmetic/analytic calibration and the
finite machine simulation facts. No inhabitant for the intended semantics
is supplied here. This is not an object-level Prf PRAAx proof.

Intended local checks when Lean 4 is available:
  lean Syntax.lean
  lean LogicalCore.lean

LogicalCore.lean includes #print axioms commands. The delivery makes no claim
about their compiler output.

For complete object-theory formalization, follow FormalizationPlan.txt and
target the actual ConciseIPRA judgment:
  ([] : List (Fm PTm 0)) ⊢[PRAAx] richardsonSentence

The human-readable mathematical proof and its citations are in the report.


PINNED TOOLCHAIN
The audited repository lean-toolchain is leanprover/lean4:v4.32.0.
The included lean-toolchain records that exact value. It is a reproducibility
pin, not a claim that the new Lean files were compiled.
