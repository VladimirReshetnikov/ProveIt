import ConciseIPRA.PR
import ConciseIPRA.BiInterpretation

/-!
# Constructive Bohr--Mollerup in iPRA: formalization scaffold

STATUS: outline only.  The declarations marked `opaque` specify interfaces and
all proofs containing `sorry` are milestones described in LEAN_ROADMAP.md.
This file has not been compiled in the artifact-building environment because a
Lean toolchain was unavailable there.

The intended completed development has two layers:

1. executable coded rationals / regular interval names and correctness proofs;
2. compilation of those algorithms and proofs into `ConciseIPRA.PR`, followed
   by transport through `ConciseIPRA.pra_theorem_iff`.
-/

set_option autoImplicit false

namespace LeanProofs.BohrMollerupIPRA

open Syn
open scoped Fm
open LeanProofs.ConciseIPRA

/-! ## Layer I: abstract interfaces to be replaced by concrete PR code -/

structure QCode where
  num : Int
  den : Nat
  den_pos : 0 < den

opaque qzero qone : QCode
opaque qadd qmul qsub : QCode → QCode → QCode
opaque qpowNat : QCode → Nat → QCode
opaque qle qlt : QCode → QCode → Prop
opaque qabsDiffLe : QCode → QCode → QCode → Prop
opaque dyadic : Nat → QCode                 -- 2^(-k)
opaque qOfNat : Nat → QCode
opaque qdivNat : QCode → Nat → QCode
opaque weightedPoint : Nat → Nat → QCode → QCode → QCode

structure RegularName where
  lo : Nat → QCode
  hi : Nat → QCode
  nested : ∀ k, qle (lo k) (lo (k + 1)) ∧
                  qle (lo (k + 1)) (hi (k + 1)) ∧
                  qle (hi (k + 1)) (hi k)
  width : ∀ k, qle (qsub (hi k) (lo k)) (dyadic k)

opaque center : RegularName → Nat → QCode

def RealEq (X Y : RegularName) : Prop :=
  ∀ k, qabsDiffLe (center X (k + 2)) (center Y (k + 2)) (dyadic k)

opaque RealLe : RegularName → RegularName → Prop
opaque StrongPositive : RegularName → Prop
opaque nameOne : RegularName
opaque nameMul : RegularName → RegularName → RegularName
opaque namePow : RegularName → Nat → RegularName
opaque nameOfRat : QCode → RegularName

structure PresentedFun where
  value : QCode → RegularName
  positive : ∀ q, qlt qzero q → StrongPositive (value q)
  modulus : QCode → QCode → Nat → Nat


def Normalized (F : PresentedFun) : Prop := RealEq (F.value qone) nameOne

def Recurrent (F : PresentedFun) : Prop :=
  ∀ x, qlt qzero x →
    RealEq (F.value (qadd x qone)) (nameMul (nameOfRat x) (F.value x))


def RLC (F : PresentedFun) : Prop :=
  ∀ (x y : QCode) (s j : Nat),
    qlt qzero x → qlt qzero y → j ≤ s → 0 < s →
    RealLe
      (namePow (F.value (weightedPoint s j x y)) s)
      (nameMul (namePow (F.value x) (s - j)) (namePow (F.value y) j))


def BMData (F : PresentedFun) : Prop :=
  Normalized F ∧ Recurrent F ∧ RLC F

/-! Concrete modules replacing the following opaque declaration:

* `BM.Root`: bounded integer-root bisection;
* `BM.EulerBracket`: A_n, B_n, nesting, width;
* `BM.GammaQ`: running intersections and recurrence extension;
* `BM.EulerConvex`: E_n and rational multiplicative convexity.
-/

opaque gammaPresented : PresentedFun

theorem gammaPresented_BM : BMData gammaPresented := by
  sorry

/-! The rational-core uniqueness theorem.  Its proof is the two-instance
Euler squeeze from the report. -/
theorem bohrMollerupQ (F : PresentedFun) (hF : BMData F) :
    ∀ q, qlt qzero q → RealEq (F.value q) (gammaPresented.value q) := by
  sorry

/-! A completion theorem using the `modulus` fields is the next semantic
milestone.  It should define a value at a regular input from canonical rational
centres and prove independence of the chosen precision. -/
opaque CompletedValue : PresentedFun → RegularName → RegularName

theorem bohrMollerupRegular (F : PresentedFun) (hF : BMData F) :
    ∀ X, StrongPositive X →
      RealEq (CompletedValue F X) (CompletedValue gammaPresented X) := by
  sorry

/-! ## Layer II: object-level iPRA

`bmClosedFormula` is a temporary interface.  Replace it with the explicit
closed `Fm PTm 0` obtained by expanding:

* rational-code and interval predicates;
* the fixed candidate presentation symbols;
* normalization, recurrence, RLC, and the precision equality conclusion.

The completed proof of `bmClosedFormula_derivable` must be assembled solely
from defining equations of `PR`, arithmetic lemmas, and `PRA.qfInd`.
-/

opaque bmClosedFormula : Fm PTm 0

theorem bmClosedFormula_derivable :
    ([] ⊢[PRAAx] bmClosedFormula) := by
  sorry

/-! This last step is already supplied by the existing bi-interpretation. -/
theorem bmClosedFormula_in_concise_core :
    ([] ⊢[TeqAx] bmClosedFormula.map fun _ => FromPRA.sigma) :=
  (pra_theorem_iff bmClosedFormula).mp bmClosedFormula_derivable

end LeanProofs.BohrMollerupIPRA
