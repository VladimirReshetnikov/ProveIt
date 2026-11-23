import IPRADerivations.Analysis.GaussianRationalDistanceOrder

/-!
# Exact balance rearrangements for actual Gaussian rational distances

All three operands may be raw codes. Their genuine representations are
rescaled to one computed positive denominator. Canonical normalized
subtraction and native Gaussian arithmetic prove both residual identities.
Only positivity of the requested radius denominator is needed to reverse
the resulting distance; no canonicality of an input is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalBalance

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qadd represents canonical_unique represents_congr positive_product qadd_represents)
open GaussianRationalMetric (qsub qnegative qsub_represents qnegative_represents distanceBounded)
open GaussianRationalSyntheticDivision (rescale_to)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalDistanceOrder (distance_symmetric)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def commonDen (x y b : PTm n) : PTm n := rawDen x*rawDen y*rawDen b

private theorem represented_identities (x y b X Y B E : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hx : Γ ⊢[PRAAx] represents x X E) (hy : Γ ⊢[PRAAx] represents y Y E) (hb : Γ ⊢[PRAAx] represents b B E) : Γ ⊢[PRAAx]
    qsub (qsub x y) b ≐ qsub (qsub x b) y ⋏
      qsub (qsub x y) (qnegative b) ≐ qsub (qadd x b) y := by
  have lowerLeft := qsub_represents _ _ _ _ E hE (qsub_represents x y X Y E hE hx hy) hb
  have lowerRight := qsub_represents _ _ _ _ E hE (qsub_represents x b X B E hE hx hb) hy
  have lower : Γ ⊢[PRAAx] qsub (qsub x y) b ≐ qsub (qsub x b) y := by
    apply canonical_unique _ _ _ _ (GaussianRationalMetric.qsub_canonical _ _) (GaussianRationalMetric.qsub_canonical _ _) hE (hrv := lowerRight)
    apply represents_congr (.eqRefl _) ?_ (.eqRefl _) lowerLeft
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub] <;> ring
  have upperLeft := qsub_represents _ _ _ _ E hE (qsub_represents x y X Y E hE hx hy) (qnegative_represents b B E hb)
  have upperRight := qsub_represents _ _ _ _ E hE (qadd_represents x b X B E hE hx hb) hy
  have upper : Γ ⊢[PRAAx] qsub (qsub x y) (qnegative b) ≐ qsub (qadd x b) y := by
    apply canonical_unique _ _ _ _ (GaussianRationalMetric.qsub_canonical _ _) (GaussianRationalMetric.qsub_canonical _ _) hE (hrv := upperRight)
    apply represents_congr (.eqRefl _) ?_ (.eqRefl _) upperLeft
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.im_neg,
        GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add] <;> ring
  exact .andI lower upper

/-- The identities hold even when a supplied raw input is not its
canonical recoding, because every displayed residual is normalized. -/
theorem balance_identities (x y b : PTm n) : Γ ⊢[PRAAx]
    qsub (qsub x y) b ≐ qsub (qsub x b) y ⋏
      qsub (qsub x y) (qnegative b) ≐ qsub (qadd x b) y := by
  let E := commonDen x y b
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ (positive_product _ _ (raw_den_positive x) (raw_den_positive y)) (raw_den_positive b)
  have hx := rescale_to x (rawGaussian x) (rawDen x) (rawDen y*rawDen b) E (raw_represents (Γ := Γ) x) (by dsimp only [E,commonDen]; ipra_ring)
  have hy := rescale_to y (rawGaussian y) (rawDen y) (rawDen x*rawDen b) E (raw_represents (Γ := Γ) y) (by dsimp only [E,commonDen]; ipra_ring)
  have hb := rescale_to b (rawGaussian b) (rawDen b) (rawDen x*rawDen y) E (raw_represents (Γ := Γ) b) (by dsimp only [E,commonDen]; ipra_ring)
  exact represented_identities x y b _ _ _ E hE hx hy hb

theorem lower_rearrangement (x y b : PTm n) : Γ ⊢[PRAAx]
    qsub (qsub x y) b ≐ qsub (qsub x b) y := (balance_identities x y b).andE₁

theorem upper_rearrangement (x y b : PTm n) : Γ ⊢[PRAAx]
    qsub (qsub x y) (qnegative b) ≐ qsub (qadd x b) y := (balance_identities x y b).andE₂

theorem lower_balance (x y b A D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded (qsub x y) b A D) : Γ ⊢[PRAAx]
    distanceBounded y (qsub x b) A D :=
  distance_symmetric _ _ _ _ hD (bound_congr (lower_rearrangement x y b) (.eqRefl _) (.eqRefl _) h)

theorem upper_balance (x y b A D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded (qsub x y) (qnegative b) A D) : Γ ⊢[PRAAx]
    distanceBounded y (qadd x b) A D :=
  distance_symmetric _ _ _ _ hD (bound_congr (upper_rearrangement x y b) (.eqRefl _) (.eqRefl _) h)

theorem actual_raw_Gaussian_balance_identities_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((qsub (qsub (var 0) (var 1)) (var 2) ≐ qsub (qsub (var 0) (var 2)) (var 1)) ⋏
      (qsub (qsub (var 0) (var 1)) (qnegative (var 2)) ≐ qsub (qadd (var 0) (var 2)) (var 1))) :=
  closeUniv 3 (balance_identities _ _ _)

theorem actual_raw_Gaussian_lower_balance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 4) ⋏ distanceBounded (qsub (var 0) (var 1)) (var 2) (var 3) (var 4)) ⟶
      distanceBounded (var 1) (qsub (var 0) (var 2)) (var 3) (var 4)) :=
  closeUniv 5 (.impI (lower_balance _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_raw_Gaussian_upper_balance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 4) ⋏ distanceBounded (qsub (var 0) (var 1)) (qnegative (var 2)) (var 3) (var 4)) ⟶
      distanceBounded (var 1) (qadd (var 0) (var 2)) (var 3) (var 4)) :=
  closeUniv 5 (.impI (upper_balance _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRationalBalance
