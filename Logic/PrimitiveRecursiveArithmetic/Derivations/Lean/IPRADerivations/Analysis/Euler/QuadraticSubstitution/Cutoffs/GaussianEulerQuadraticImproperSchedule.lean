import IPRADerivations.Analysis.Euler.QuadraticSubstitution.Cutoffs.GaussianEulerQuadraticUpperEndpoint
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateComposition

/-!
# A cofinal observation budget for the quadratic Euler substitution

One program index pays for both omitted tails. The scale argument allows
the same calculation after multiplication by a bounded reciprocal factor.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerQuadraticImproperSchedule

open_ipra
open GaussianGammaIntegralCutoffs (height etaDen top)
open GaussianEulerQuadraticUpperEndpoint (preimage)
open GaussianEulerQuadraticLowerEndpoint (minimumIndex)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedRateComposition (leadingNumerator leadingDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def threshold (p A M : PTm n) : PTm n := GaussianFastValueCut.exponent ((A+one)*M) (succ p)
def index (p A M c d : PTm n) : PTm n := minimumIndex (threshold p A M) c d

ipra_subst threshold
ipra_subst index [minimumIndex]

/-- The scheduled quadratic cutoff is at least the requested precision. -/
theorem index_later (p A M c d : PTm n) : Γ ⊢[PRAAx] le p (index p A M c d) := by
  unfold index threshold minimumIndex GaussianFastValueCut.exponent
  exact le_trans (le_succ_self p) (le_trans (le_add_right _ _) (le_trans (le_add_right _ _) (le_add_right _ _)))

private theorem index_le_height (j A R : PTm n) : Γ ⊢[PRAAx] le j (height j A R) :=
  le_trans (le_add_right _ _) (le_trans (le_add_right _ _) (le_add_right _ _))

/-- At a late cutoff with positive degree and scale, the lower reciprocal
denominator and the upper endpoint are both cofinal. -/
theorem endpoints_cofinal (p j A R d : PTm n) (hp : Γ ⊢[PRAAx] le p j)
    (hA : Γ ⊢[PRAAx] le one A) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    le (unit p) (etaDen j A R) ⋏ le p (preimage j A R d) := by
  let H := height j A R
  have late := le_trans hp (index_le_height j A R)
  have lower : Γ ⊢[PRAAx] le H (A*H) :=
    le_congr (one_mul H) (.eqRefl _) (mul_le_mul_right H hA)
  have upper : Γ ⊢[PRAAx] le H (top j A R) :=
    le_congr (one_mul H) (.eqRefl _) (mul_le_mul_right H (zero_lt_succ one))
  have image : Γ ⊢[PRAAx] le (top j A R) (preimage j A R d) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (top j A R) hd)
  exact .andI (GaussianCompactRiemannName.dyadic_monotone _ _ (le_trans late lower))
    (le_trans late (le_trans upper image))

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
  have lower := index_le_height (Γ := Γ) k A R
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
