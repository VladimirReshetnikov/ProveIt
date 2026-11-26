import IPRADerivations.Analysis.Euler.QuadraticSubstitution.GaussianEulerQuadraticUpperEndpoint
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateComposition

/-!
# A cofinal observation budget for the quadratic Euler substitution

One program index pays for both omitted tails. The scale argument allows
the same calculation after multiplication by a bounded reciprocal factor.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerQuadraticImproperSchedule

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaIntegralCutoffs (height)
open GaussianEulerQuadraticLowerEndpoint (minimumIndex)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedRateComposition (leadingNumerator leadingDenominator)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def threshold (p A M : PTm n) : PTm n := GaussianFastValueCut.exponent ((A+one)*M) (succ p)
def index (p A M c d : PTm n) : PTm n := minimumIndex (threshold p A M) c d

@[simp] theorem subst_threshold {m : ℕ} (σ : Fin n → PTm m) (p A M : PTm n) :
    Syn.subst σ (threshold p A M) = threshold (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ M) := by simp [threshold]
@[simp] theorem subst_index {m : ℕ} (σ : Fin n → PTm m) (p A M c d : PTm n) :
    Syn.subst σ (index p A M c d) = index (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ M) (Syn.subst σ c) (Syn.subst σ d) :=
  by simp [index,minimumIndex]

theorem shared_budget (A M U D L H : PTm n) (hd : Γ ⊢[PRAAx] le one D)
    (hl : Γ ⊢[PRAAx] le D L) (hh : Γ ⊢[PRAAx] le D H)
    (hb : Γ ⊢[PRAAx] le ((A+one)*M*U) D) :
    Γ ⊢[PRAAx] le ((M*leadingNumerator A L one H)*U) (leadingDenominator L H) := by
  have low := mul_le_mul_right (A*H) hl
  have high := mul_le_mul_right L hh
  have sum : Γ ⊢[PRAAx] le ((A*H+L)*D) ((A+one)*(L*H)) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ low high)
  have first : Γ ⊢[PRAAx] le (D*((M*leadingNumerator A L one H)*U)) (((A+one)*M*U)*(L*H)) :=
    le_congr (by unfold leadingNumerator; ipra_ring) (by ipra_ring) (mul_le_mul_right (M*U) sum)
  have second : Γ ⊢[PRAAx] le (((A+one)*M*U)*(L*H)) (D*leadingDenominator L H) :=
    mul_le_mul_right (L*H) hb
  exact RationalValueBounds.positive_cancel hd (le_trans first second)

theorem cutoff_budget (p A R M c d : PTm n) : Γ ⊢[PRAAx]
    le ((M*leadingNumerator A (unit (height (threshold p A M) A R)) one (unit (index p A M c d+num 6)))*unit (succ p))
      (leadingDenominator (unit (height (threshold p A M) A R)) (unit (index p A M c d+num 6))) := by
  let k := threshold p A M
  have lower : Γ ⊢[PRAAx] le k (height k A R) := by
    unfold height
    exact le_trans (le_trans (le_add_right _ _) (le_add_right _ _)) (le_add_right _ _)
  have upper : Γ ⊢[PRAAx] le k (index p A M c d+num 6) := by
    unfold index minimumIndex
    exact le_trans (le_trans (le_add_right _ _) (le_add_right _ _)) (le_add_right _ _)
  exact shared_budget A M _ (unit k) _ _ (unit_positive k) (GaussianCompactRiemannName.dyadic_monotone _ _ lower)
    (GaussianCompactRiemannName.dyadic_monotone _ _ upper) (GaussianFastValueCut.query_budget _ _)

theorem actual_quadratic_improper_cutoff_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le ((var 3*leadingNumerator (var 1) (unit (height (threshold (var 0) (var 1) (var 3)) (var 1) (var 2))) one
      (unit (index (var 0) (var 1) (var 3) (var 4) (var 5)+num 6)))*unit (succ (var 0)))
      (leadingDenominator (unit (height (threshold (var 0) (var 1) (var 3)) (var 1) (var 2)))
        (unit (index (var 0) (var 1) (var 3) (var 4) (var 5)+num 6)))) :=
  closeUniv 6 (cutoff_budget _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerQuadraticImproperSchedule
