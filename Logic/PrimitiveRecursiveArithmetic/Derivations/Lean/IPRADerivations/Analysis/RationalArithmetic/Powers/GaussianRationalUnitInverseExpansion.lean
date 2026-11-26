import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalLinearProduct
import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalDistanceOrder
import IPRADerivations.Core.OrderCertificates

/-!
# First-order inversion with an observed reciprocal residual

If the actual rational sample P is within C/D² of 1+b, with |b|≤N/D,
an actual approximate inverse G has a matching expansion at 1−b.
The bound keeps the observed product residual |GP−1|≤A/D² and uses
only an upper bound K on the actual G sample.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalUnitInverseExpansion

open_ipra
open GaussianRationalHorner
  (qadd qmul qadd_canonical qadd_represents qmul_represents represents positive_product canonical_unique represents_congr represents_rescale)
open GaussianRationalMetric (qsub bounded qsub_canonical qsub_represents)
open GaussianRationalSyntheticDivision (qone rescale_to)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalReciprocal
  (qone_represents_scaled bounded_product bounded_difference bounded_sum bound_congr)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open ComplexLogarithmRemainder (oneCode scale)
open GaussianRootAlgebra (equal_of_values re_add im_add re_sub im_sub re_mul im_mul re_scale im_scale re_one im_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def productResidual (g p : PTm n) : PTm n := qsub (qmul g p) qone
def directError (p b : PTm n) : PTm n := qsub (qsub p qone) b
def inverseError (g b : PTm n) : PTm n := qadd (qsub g qone) b
def boundCoefficient (A C N K : PTm n) : PTm n := A+K*C+N*(A+K*(C+N))

private theorem identities_from_representations (g p b G P B E : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hg : Γ ⊢[PRAAx] represents g G E)
    (hp : Γ ⊢[PRAAx] represents p P E) (hb : Γ ⊢[PRAAx] represents b B E) :
    Γ ⊢[PRAAx] (qsub g qone ≐ qsub (productResidual g p) (qmul g (qsub p qone))) ⋏
      (inverseError g b ≐ qadd (qsub (productResidual g p) (qmul g (directError p b))) (qmul b (qsub qone g))) := by
  let S := E*E
  have hS : Γ ⊢[PRAAx] le one S := positive_product _ _ hE hE
  have unitE := qone_represents_scaled (Γ := Γ) E
  have unitS := qone_represents_scaled (Γ := Γ) S
  have gδ := qsub_represents _ _ _ _ _ hE hg unitE
  have pδ := qsub_represents _ _ _ _ _ hE hp unitE
  have δg := qsub_represents _ _ _ _ _ hE unitE hg
  have res := qsub_represents _ _ _ _ _ hS (qmul_represents _ _ _ _ _ _ hE hE hg hp) unitS
  refine .andI ?_ ?_
  · have lhs := represents_rescale _ _ E E gδ
    have rhs := qsub_represents _ _ _ _ _ hS res (qmul_represents _ _ _ _ _ _ hE hE hg pδ)
    apply canonical_unique _ _ _ _ (qsub_canonical _ _) (qsub_canonical _ _) hS (hrv := rhs)
    apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
    apply equal_of_values <;>
      simp only [S, re_sub, im_sub, re_mul, im_mul, re_scale, im_scale, re_one, im_one, Q.mk_mul, map_mul] <;> ring
  · have lhs := represents_rescale _ _ E E (qadd_represents _ _ _ _ _ hE gδ hb)
    have rhs := qadd_represents _ _ _ _ _ hS
      (qsub_represents _ _ _ _ _ hS res
        (qmul_represents _ _ _ _ _ _ hE hE hg (qsub_represents _ _ _ _ _ hE pδ hb)))
      (qmul_represents _ _ _ _ _ _ hE hE hb δg)
    apply canonical_unique _ _ _ _ (qadd_canonical _ _) (qadd_canonical _ _) hS (hrv := rhs)
    apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
    apply equal_of_values <;>
      simp only [S, re_add, im_add, re_sub, im_sub, re_mul, im_mul, re_scale, im_scale, re_one, im_one, Q.mk_mul, map_mul] <;> ring

theorem original_identities (g p b : PTm n) :
    Γ ⊢[PRAAx] (qsub g qone ≐ qsub (productResidual g p) (qmul g (qsub p qone))) ⋏
      (inverseError g b ≐ qadd (qsub (productResidual g p) (qmul g (directError p b))) (qmul b (qsub qone g))) := by
  let E := rawDen g*rawDen p*rawDen b
  have hg := rescale_to g (rawGaussian g) (rawDen g) (rawDen p*rawDen b) E
    (raw_represents (Γ := Γ) g) (by dsimp only [E]; ipra_ring)
  have hp := rescale_to p (rawGaussian p) (rawDen p) (rawDen g*rawDen b) E
    (raw_represents (Γ := Γ) p) (by dsimp only [E]; ipra_ring)
  have hb := rescale_to b (rawGaussian b) (rawDen b) (rawDen g*rawDen p) E
    (raw_represents (Γ := Γ) b) (by dsimp only [E]; ipra_ring)
  exact identities_from_representations _ _ _ _ _ _ E
    (positive_product _ _ (positive_product _ _ (raw_den_positive g) (raw_den_positive p)) (raw_den_positive b)) hg hp hb

private theorem residual_difference_bound (g p b D A C N K : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hr : Γ ⊢[PRAAx] bounded (productResidual g p) A (D*D))
    (he : Γ ⊢[PRAAx] bounded (directError p b) C (D*D))
    (hb : Γ ⊢[PRAAx] bounded b N D) (hg : Γ ⊢[PRAAx] bounded g K one) :
    Γ ⊢[PRAAx] bounded (qsub g qone) (A+K*(C+N)) D := by
  have hS := positive_product _ _ hD hD
  have first := bounded_sum _ _ _ _ _ _ hD hS hb he
  have point : Γ ⊢[PRAAx] bounded (qsub p qone) (C+N) D :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ hD hS) hD
      (by ipra_le 𝔞 C*(𝔞 D)^2*sl hD)
      (bound_congr (GaussianRationalLinearProduct.add_sub_right b (qsub p qone) (qsub_canonical _ _)) (.eqRefl _) (.eqRefl _) first)
  have small : Γ ⊢[PRAAx] bounded (productResidual g p) A D := bounded_radius_mono _ _ _ _ _ hS hD (by ipra_le 𝔞 A*𝔞 D*sl hD) hr
  have product := bound_congr (.eqRefl _) (.eqRefl _) (one_mul D)
    (bounded_product _ _ _ _ _ _ (le_refl one) hD hg point)
  have sum := bounded_difference _ _ _ _ _ _ hD hD small product
  exact bounded_radius_mono _ _ _ _ _ hS hD (le_of_eq_add (d := zero) (by ipra_ring))
    (bound_congr (original_identities g p b).andE₁.eqSymm (.eqRefl _) (.eqRefl _) sum)

theorem original_quadratic_bound (g p b D A C N K : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hr : Γ ⊢[PRAAx] bounded (productResidual g p) A (D*D))
    (he : Γ ⊢[PRAAx] bounded (directError p b) C (D*D))
    (hb : Γ ⊢[PRAAx] bounded b N D) (hg : Γ ⊢[PRAAx] bounded g K one) :
    Γ ⊢[PRAAx] bounded (inverseError g b) (boundCoefficient A C N K) (D*D) := by
  let S := D*D
  have hS : Γ ⊢[PRAAx] le one S := positive_product _ _ hD hD
  have near := residual_difference_bound g p b D A C N K hD hr he hb hg
  have reversed := GaussianRationalDistanceOrder.distance_symmetric g qone (A+K*(C+N)) D hD near
  have second := bound_congr (.eqRefl _) (.eqRefl _) (one_mul S)
    (bounded_product _ _ _ _ _ _ (le_refl one) hS hg he)
  have third := bounded_product _ _ _ _ _ _ hD hD hb reversed
  have first := bounded_difference _ _ _ _ _ _ hS hS hr second
  have combined := bounded_sum _ _ _ _ _ _ (positive_product _ _ hS hS) hS first third
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ (positive_product _ _ hS hS) hS) hS
    (le_of_eq_add (d := zero) (by dsimp only [boundCoefficient,S]; ipra_ring))
    (bound_congr (original_identities g p b).andE₂.eqSymm (.eqRefl _) (.eqRefl _) combined)

theorem actual_rational_unit_inverse_first_order_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((le one (var 3) ⋏ (bounded (productResidual (var 0) (var 1)) (var 4) (var 3*var 3) ⋏
      (bounded (directError (var 1) (var 2)) (var 5) (var 3*var 3) ⋏
        (bounded (var 2) (var 6) (var 3) ⋏ bounded (var 0) (var 7) one)))) ⟶
      bounded (inverseError (var 0) (var 2)) (boundCoefficient (var 4) (var 5) (var 6) (var 7)) (var 3*var 3)) :=
  closeUniv 8 (.impI (original_quadratic_bound _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRationalUnitInverseExpansion
