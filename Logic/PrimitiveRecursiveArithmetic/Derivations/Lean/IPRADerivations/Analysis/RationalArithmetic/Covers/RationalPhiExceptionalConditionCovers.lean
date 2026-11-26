import IPRADerivations.Analysis.RationalArithmetic.Covers.RationalPhiAssignedCovers
import IPRADerivations.Analysis.RationalArithmetic.Covers.RationalPhiExceptionalCover

/-!
# An exceptional list and separate cover budgets for each condition

After discarding the listed exceptions by actual rational point equality,
a bounded first-match scan partitions the remaining original points.
Each assigned group lies outside the exceptional list and satisfies its
own condition. A tuple-local cover with its own budget then gives the
source count E + m * sum_i M_i.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPhiExceptionalConditionCovers

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalPhiAssignedCovers (allPoints conditionCovers)
open RationalPhiExceptionalCover (outside pointEqual remainder)
open RationalPhiSectionNonzero (curveInput)
open RationalCurvePointsGaussianEmbedding (distinct)
open RationalSuperellipticNormDegree (pointPowers)
open LeanProofs.IPRA.Foundations.FiniteCoverAssignment (cover)
open LeanProofs.IPRA.Foundations.FiniteCoverGroupBudgets (budgetSum)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- A raw point, with the exception list as parameter, differs from every listed point. -/
def outsidePoint : Fm PTm 2 :=
  .all (lt (var 0) (length (var 2)) ⟶ neg (pointEqual (var 1) (entry (var 2) (var 0))))

theorem all_points_outside (X Q : PTm n) : allPoints outsidePoint Q X = outside X Q := by
  simp [allPoints,outsidePoint,outside,Syn.up,Syn.shift,Fm.subst]

/-- Coverage of each condition is required only for tuples outside the supplied list. -/
def outsideConditionCovers (t : PTm 3) (f s r p B X : PTm n) : Fm PTm n :=
  conditionCovers outsidePoint t f s r (length B) p B X

@[simp] theorem subst_outsideConditionCovers {k : ℕ} (σ : Fin n → PTm k) (t : PTm 3) (f s r p B X : PTm n) :
    (outsideConditionCovers t f s r p B X).subst σ =
      outsideConditionCovers t (Syn.subst σ f) (Syn.subst σ s) (Syn.subst σ r)
        (Syn.subst σ p) (Syn.subst σ B) (Syn.subst σ X) := by
  simp [outsideConditionCovers]

theorem exceptional_condition_bound (t : PTm 3) (f s r m X P E p B : PTm n)
    (hf : Γ ⊢[PRAAx] curveInput f s r m) (hd : Γ ⊢[PRAAx] distinct P) (hp : Γ ⊢[PRAAx] pointPowers f r P)
    (hx : Γ ⊢[PRAAx] le (length X) E) (ht : Γ ⊢[PRAAx] cover t (remainder X P) (length B) p)
    (hc : Γ ⊢[PRAAx] outsideConditionCovers t f s r p B X) :
    Γ ⊢[PRAAx] le (length P) (E + m * budgetSum (length B) B) := by
  have ho : Γ ⊢[PRAAx] allPoints outsidePoint (remainder X P) X := by
    rw [all_points_outside]
    exact RationalPhiExceptionalCover.remainder_outside X P
  have count := RationalPhiAssignedCovers.condition_cover_bound outsidePoint t f s r m (remainder X P)
    (length B) p B X hf (RationalPhiExceptionalCover.remainder_distinct X P hd)
    (RationalPhiExceptionalCover.remainder_powers f r X P hp) ht ho hc
  exact le_trans (RationalPhiExceptionalCover.split_bound X P hd) (add_le_add₂ hx count)

theorem actual_original_exceptional_condition_cover_closed (t : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (curveInput (var 0) (var 1) (var 2) (var 3) ⟶ distinct (var 5) ⟶ pointPowers (var 0) (var 2) (var 5) ⟶
      le (length (var 4)) (var 6) ⟶ cover t (remainder (var 4) (var 5)) (length (var 8)) (var 7) ⟶
      outsideConditionCovers t (var 0) (var 1) (var 2) (var 7) (var 8) (var 4) ⟶
      le (length (var 5)) (var 6 + var 3 * budgetSum (length (var 8)) (var 8))) :=
  closeUniv 9 (.impI (.impI (.impI (.impI (.impI (.impI (exceptional_condition_bound t
    (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0)))))))

end LeanProofs.IPRA.Analysis.RationalPhiExceptionalConditionCovers
