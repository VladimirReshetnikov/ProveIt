import FQNF.CertificateSearch
import FQNF.KernelCore

/-!
# Finite-query normal form

This is the intended high-level API.  A package fixes a packed query language,
a primitive-recursive certificate bound and verifier, a producer theorem, and a
terminal extractor.  `compile` selects a least certificate and returns a
literal `Prf PRAAx` theorem.

The formula fields are kept explicit rather than hidden behind host-level
semantics.  This file is an outline because the final ergonomic API should be
chosen only after `CertificateSearch.lean` is checked in the repository.
-/

namespace LeanProofs.IPRA.FQNF

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

/-- Syntactic data of one finite-query theorem family. -/
structure Package where
  bound : PR 1
  check : PR 2
  pre : Fm PTm 1
  goalAt : Fm PTm 2
  checkerBoolean : Fm PTm 2

/-- Object-theory obligations of a finite-query package. -/
structure PackageProof (P : Package) where
  boolean : ([] : List (Fm PTm 2)) ⊢[PRAAx] P.checkerBoolean
  producer : ([] : List (Fm PTm 1)) ⊢[PRAAx]
    (P.pre ⟶ Fm.ex
      (lt (var 0) (Syn.shift (app P.bound var)) ⋏
       (app P.check ![var 0, var 1] ≐ succ zero)))
  extractor : ([] : List (Fm PTm 2)) ⊢[PRAAx]
    ((app P.check var ≐ succ zero) ⟶ P.goalAt)

variable {n : Nat}

/-- The selected certificate term. -/
def selected (P : Package) (query : PTm n) : PTm n :=
  selectT (app P.check var) (app P.bound ![query]) query

/-- Main compiler theorem target. -/
theorem compile (P : Package) (HP : PackageProof P) (query : PTm n)
    {Gamma : List (Fm PTm n)}
    (hpre : Gamma ⊢[PRAAx] P.pre.subst ![query]) :
    Gamma ⊢[PRAAx] P.goalAt.subst ![selected P query, query] := by
  -- 1. specialize `producer` at `query` and apply it to `hpre`;
  -- 2. invoke `select_of_exists`;
  -- 3. specialize `extractor` at the selected code and query;
  -- 4. use implication elimination.
  sorry

/-- A conditional package keeps its deep producer as an explicit premise. -/
structure ConditionalPackageProof (P : Package) where
  boundary : Fm PTm 1
  boolean : ([] : List (Fm PTm 2)) ⊢[PRAAx] P.checkerBoolean
  producer : ([] : List (Fm PTm 1)) ⊢[PRAAx]
    (P.pre ⟶ boundary ⟶ Fm.ex
      (lt (var 0) (Syn.shift (app P.bound var)) ⋏
       (app P.check ![var 0, var 1] ≐ succ zero)))
  extractor : ([] : List (Fm PTm 2)) ⊢[PRAAx]
    ((app P.check var ≐ succ zero) ⟶ P.goalAt)

end LeanProofs.IPRA.FQNF
