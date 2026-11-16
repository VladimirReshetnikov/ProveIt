import ConciseIPRA.PR
import PFIG.ExactCore

/-!
# Application theorem targets

These declarations show how theorem packets should expose producer assumptions
and object conclusions.  They are blueprints, not checked implementations.
-/

namespace LeanProofs.ConciseIPRA.PFIG.Applications

open Syn
open scoped Fm

/-- Height/list adapter: all theorem-specific notions are supplied as formulas
and PR terms; the compiler performs only bounded enumeration and checking. -/
structure HeightEnumerationSpec (n : Nat) where
  point : Fm PTm (n + 1)       -- code, parameters
  pointQF : point.QF
  height : PTm (n + 1)         -- code, parameters
  bound : PTm n
  inHeightBox : Fm PTm (n + 1)
  inHeightBoxQF : inHeightBox.QF
  soundBox : Fm PTm n
  completeFromBound : Fm PTm n
  listCode : PTm n
  listSound : Fm PTm n
  listComplete : Fm PTm n

/-- Object target: an explicit height bound compiles to a complete finite list. -/
def HeightToListTarget : Prop :=
  ∀ (n : Nat) (S : HeightEnumerationSpec n)
    (Γ : List (Fm PTm n)),
    Γ ⊢[PRAAx] S.soundBox →
    Γ ⊢[PRAAx] S.completeFromBound →
    Γ ⊢[PRAAx] S.listSound ⋏ S.listComplete

/-- Finite-cover adapter. -/
structure FiniteCoverSpec (n : Nat) where
  chartCount : PTm n
  localValid : Fm PTm (n + 2)  -- local code, chart, parameters
  overlap : Fm PTm (n + 4)     -- witness, right, left, pair index, params
  localQF : localValid.QF
  overlapQF : overlap.QF
  tupleCode : PTm n
  tupleValid : Fm PTm n
  globalSpec : Fm PTm n
  localProofs : Fm PTm n
  overlapProofs : Fm PTm n
  extract : localProofs :: overlapProofs :: tupleValid :: []
    ⊢[PRAAx] globalSpec

/-- Object target: construct/check a compatible tuple and extract a global
specification. -/
def FiniteGluingTarget : Prop :=
  ∀ (n : Nat) (S : FiniteCoverSpec n)
    (Γ : List (Fm PTm n)),
    Γ ⊢[PRAAx] S.localProofs →
    Γ ⊢[PRAAx] S.overlapProofs →
    Γ ⊢[PRAAx] S.tupleValid →
    Γ ⊢[PRAAx] S.globalSpec

/-- Guarded branch adapter. -/
structure GapBranchSpec (n : Nat) where
  gap : PTm n
  error : PTm n
  selected : PTm n
  gapPositive : Fm PTm n
  errorSmall : Fm PTm n
  selectedCorrect : Fm PTm n

/-- Exact label selection is proved only from a positive gap and small error. -/
def GapBranchTarget : Prop :=
  ∀ (n : Nat) (S : GapBranchSpec n) (Γ : List (Fm PTm n)),
    Γ ⊢[PRAAx] S.gapPositive →
    Γ ⊢[PRAAx] S.errorSmall →
    Γ ⊢[PRAAx] S.selectedCorrect

end LeanProofs.ConciseIPRA.PFIG.Applications
