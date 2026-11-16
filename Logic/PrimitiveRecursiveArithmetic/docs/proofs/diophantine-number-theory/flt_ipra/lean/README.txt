LEAN BLUEPRINT: STATUS AND CHECKING INSTRUCTIONS
===============================================

These files are an outline with concrete definitions, not a completed
formalization of the mathematical paper. They were NOT compiled in the
delivery environment: no Lean executable was available.

ArithmeticBlueprint.lean
  Ambient Lean definitions for the four Fermat problems and their descent
  states; exact pair operations for Z[omega] and Z[phi]; finite iteration;
  a generic rank-descent argument; exponent lifting; and a covered-family
  theorem conditional on an uninstantiated FourBaseProofs structure.

ObjectLanguageTargets.lean
  Actual ProveIt PR function codes, terms, and first-order formulas for the
  intended internal iPRA derivations. RequiredProofObjects has no supplied
  inhabitant. The conditional toNative theorem only translates a supplied
  internal derivation with the existing pra_iff_native theorem.

Neither file fills the number-theoretic obligations by an axiom or an
admitted proof. No unconditional Lean proof of FLT3, FLT4, FLT5, or FLT7
is being delivered. The complete human arguments are in the paper.

PINNED ENVIRONMENT
------------------
ProveIt commit: bb4427b10219ad61e0d2875fdde04bcd23b47ec6
Lean: leanprover/lean4:v4.32.0
Mathlib: v4.32.0

The ProveIt root lakefile.toml already declares the ConciseIPRA library.
From a checkout of that commit, after its dependencies are available:

  lake build ConciseIPRA.PR ConciseIPRA.NativeBiInterpretation
  lake env lean /absolute/path/to/ArithmeticBlueprint.lean
  lake env lean /absolute/path/to/ObjectLanguageTargets.lean

These are reproduction instructions, not commands claimed to have passed.
Any elaboration repairs should preserve the exact intended equations and
should not turn the missing arithmetic derivations into assumptions hidden
inside a theorem. The paper gives a module-by-module dependency plan and
the exact quantifier-free invariants for constructing actual Prf PRAAx
proof objects.

ACCEPTANCE TARGET
-----------------
Provide checked inhabitants of InternalFLT 3, InternalFLT 4,
InternalFLT 5, InternalFLT 7, and InternalCoverage.
Check all function symbols are actual PR codes and all induction bodies
have Fm.QF proofs. Then export via pra_iff_native if desired.

An ordinary Lean theorem about Nat, even one proved without an explicit
classical tactic, is not itself a proof of object-theoretic iPRA derivability.
