import IPRADerivations.Analysis.Euler.GaussianEulerQuadraticUpperEndpoint
import IPRADerivations.Analysis.Euler.GaussianEulerSquareCompactComparison

/-!
# Original cutoff intervals for the quadratic Euler substitution

The source interval is exactly [1/etaDen_n,d*top_n]. Its positive
numerical width and the square image are derived from the original
Gamma certificate. The image endpoints retain the actual incomplete
Euler encodings, including the unchanged upper-tail observation clock.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerQuadraticCutoffGeometry

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianEulerQuadraticUpperEndpoint (preimage image)
open GaussianRationalQuadratureSquarePartition (lowerNumerator widthNumerator intervalDenominator)
open GaussianEulerSquareTimeGeometry (upperEndpoint)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num monus)

variable {ℓ : ℕ} {Γ : List (Fm PTm ℓ)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def source (z R B A c d : PTm ℓ) : Fm PTm ℓ := GaussianEulerQuadraticUpperEndpoint.source z R B A c d
def width (n A R d : PTm ℓ) : PTm ℓ := monus (etaDen n A R*preimage n A R d) one
def lowerDenominator (n A R d : PTm ℓ) : PTm ℓ := d*etaDen n A R*etaDen n A R
def imageWidth (n A R c d : PTm ℓ) : PTm ℓ := c*width n A R d*(two+width n A R d)
def imageData (n z R B A c d : PTm ℓ) : PTm ℓ := GaussianEulerCompactAdditivity.data z R B
  c (imageWidth n A R c d) (lowerDenominator n A R d) (upperEndpoint c (preimage n A R d))
def leftData (n z R B A c d : PTm ℓ) : PTm ℓ := GaussianEulerIncompleteName.data z R B A c (lowerDenominator n A R d)
def rightData (n z R B A c d : PTm ℓ) : PTm ℓ := GaussianEulerIncompleteName.data z R B A
  (c+imageWidth n A R c d) (lowerDenominator n A R d)

@[simp] theorem subst_source {m : ℕ} (σ : Fin ℓ → PTm m) (z R B A c d : PTm ℓ) :
    (source z R B A c d).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ A) (Syn.subst σ c) (Syn.subst σ d) := by simp [source]
@[simp] theorem subst_width {m : ℕ} (σ : Fin ℓ → PTm m) (n A R d : PTm ℓ) :
    Syn.subst σ (width n A R d) = width (Syn.subst σ n) (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ d) := by
  simp [width,etaDen,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] theorem subst_lowerDenominator {m : ℕ} (σ : Fin ℓ → PTm m) (n A R d : PTm ℓ) :
    Syn.subst σ (lowerDenominator n A R d) = lowerDenominator (Syn.subst σ n) (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ d) := by
  simp [lowerDenominator,etaDen,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] theorem subst_imageWidth {m : ℕ} (σ : Fin ℓ → PTm m) (n A R c d : PTm ℓ) :
    Syn.subst σ (imageWidth n A R c d) = imageWidth (Syn.subst σ n) (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ c) (Syn.subst σ d) := by simp [imageWidth]
@[simp] theorem subst_imageData {m : ℕ} (σ : Fin ℓ → PTm m) (n z R B A c d : PTm ℓ) :
    Syn.subst σ (imageData n z R B A c d) = imageData (Syn.subst σ n) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ c) (Syn.subst σ d) := by simp [imageData]
@[simp] theorem subst_leftData {m : ℕ} (σ : Fin ℓ → PTm m) (n z R B A c d : PTm ℓ) :
    Syn.subst σ (leftData n z R B A c d) = leftData (Syn.subst σ n) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ c) (Syn.subst σ d) := by simp [leftData]
@[simp] theorem subst_rightData {m : ℕ} (σ : Fin ℓ → PTm m) (n z R B A c d : PTm ℓ) :
    Syn.subst σ (rightData n z R B A c d) = rightData (Syn.subst σ n) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ c) (Syn.subst σ d) := by simp [rightData]

theorem preimage_positive (n A R d : PTm ℓ) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    le one (preimage n A R d) := positive_product _ _ hd (GaussianGammaIntegralCutoffs.top_positive n A R)

theorem exact_right_endpoint (n A R d : PTm ℓ) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    one+width n A R d ≐ etaDen n A R*preimage n A R d :=
  (eq_add_of_le (positive_product _ _ (GaussianGammaIntegralCutoffs.eta_den_positive n A R) (preimage_positive n A R d hd))).eqSymm

theorem width_positive (n A R d : PTm ℓ) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx] le one (width n A R d) := by
  have ht : Γ ⊢[PRAAx] le two (top n A R) :=
    le_congr (one_mul two) (by unfold top; ipra_ring) (mul_le_mul_right two (GaussianGammaIntegralCutoffs.height_positive n A R))
  have hT : Γ ⊢[PRAAx] le (top n A R) (preimage n A R d) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (top n A R) hd)
  have hE := GaussianGammaIntegralCutoffs.eta_den_positive (Γ := Γ) n A R
  have htE : Γ ⊢[PRAAx] le (preimage n A R d) (etaDen n A R*preimage n A R d) :=
    le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right (preimage n A R d) hE)
  have hn : Γ ⊢[PRAAx] le (one+one) (one+width n A R d) :=
    le_congr (by ipra_ring) (exact_right_endpoint n A R d hd).eqSymm (le_trans ht (le_trans hT htE))
  exact le_of_add_le_add_right (le_congr (.eqRefl _) (add_comm one (width n A R d)) hn)

theorem denominator_positive (n A R d : PTm ℓ) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    le one (lowerDenominator n A R d) := GaussianEulerQuadraticLowerEndpoint.denominator_positive n A R d hd

theorem original_interval_source (n z R B A c d : PTm ℓ) (h : Γ ⊢[PRAAx] source z R B A c d) : Γ ⊢[PRAAx]
    GaussianEulerCompactAdditivity.intervalSource z R B one (width n A R d) (etaDen n A R) (preimage n A R d) := by
  have base := h.andE₁.andE₁.andE₂.andE₁
  exact .andI (.andI base.andE₁ (.andI (GaussianGammaIntegralCutoffs.eta_den_positive n A R) base.andE₂))
    (.andI (le_refl one) (le_congr (exact_right_endpoint n A R d h.andE₂.andE₂).eqSymm (.eqRefl _) (le_refl _)))

theorem original_square_source (n z R B A c d : PTm ℓ) (h : Γ ⊢[PRAAx] source z R B A c d) : Γ ⊢[PRAAx]
    GaussianEulerSquareCompactComparison.source z R B one (width n A R d) (etaDen n A R) (preimage n A R d) c d :=
  .andI (.andI (original_interval_source n z R B A c d h) h.andE₂) (width_positive n A R d h.andE₂.andE₂)

theorem image_left_numerator (c : PTm ℓ) : Γ ⊢[PRAAx] lowerNumerator c one ≐ c := by unfold lowerNumerator; ipra_ring

theorem image_width_numerator (n A R c d : PTm ℓ) : Γ ⊢[PRAAx]
    widthNumerator c one (width n A R d) ≐ imageWidth n A R c d := by unfold widthNumerator imageWidth; ipra_ring

theorem original_image_source (n z R B A c d : PTm ℓ) (h : Γ ⊢[PRAAx] source z R B A c d) : Γ ⊢[PRAAx]
    GaussianEulerCompactAdditivity.intervalSource z R B c (imageWidth n A R c d) (lowerDenominator n A R d)
      (upperEndpoint c (preimage n A R d)) := by
  have original := GaussianEulerSquareMappedInterval.original_interval z R B one (width n A R d) (etaDen n A R)
    (preimage n A R d) c d (original_square_source n z R B A c d h).andE₁
  exact .andI original.andE₁ (.andI h.andE₂.andE₁
    (le_congr (congrAdd (image_left_numerator c) (image_width_numerator n A R c d)) (.eqRefl _) original.andE₂.andE₂))

theorem actual_image_data (n z R B A c d : PTm ℓ) : Γ ⊢[PRAAx]
    GaussianEulerSquareCompactComparison.imageData z R B one (width n A R d) (etaDen n A R) (preimage n A R d) c d ≐
      imageData n z R B A c d := by
  unfold GaussianEulerSquareCompactComparison.imageData imageData GaussianEulerCompactAdditivity.data
    GaussianCompactRiemannName.data GaussianCompactRiemannName.sampleData
  exact congrPairT (image_left_numerator c) (congrPairT (image_width_numerator n A R c d) (.eqRefl _))

theorem exact_image_endpoint (n A R c d : PTm ℓ) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    c+imageWidth n A R c d ≐ image n A R c d*lowerDenominator n A R d := by
  have square := congrMul (exact_right_endpoint n A R d hd) (exact_right_endpoint n A R d hd)
  exact (by unfold imageWidth; ipra_ring : Γ ⊢[PRAAx] c+imageWidth n A R c d ≐ c*((one+width n A R d)*(one+width n A R d))).eqTrans
    ((congrMul (.eqRefl c) square).eqTrans (by unfold image lowerDenominator preimage; ipra_ring))

theorem exact_upper_value (n A R c d : PTm ℓ) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    fraction (c+imageWidth n A R c d) (lowerDenominator n A R d) ≐ fraction (image n A R c d) one :=
  (GaussianCompactRiemannName.fraction_congr _ _ _ _ ((exact_image_endpoint n A R c d hd).eqTrans (mul_comm _ _))
    (by ipra_ring : Γ ⊢[PRAAx] lowerDenominator n A R d ≐ lowerDenominator n A R d*one)).eqTrans
      (GaussianCompactRiemannSplit.fraction_cancel _ _ _ (denominator_positive n A R d hd) (le_refl one))

private theorem incomplete_data_congr (z R B A a a' b b' : PTm ℓ) (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') : Γ ⊢[PRAAx]
    GaussianEulerIncompleteName.data z R B A a b ≐ GaussianEulerIncompleteName.data z R B A a' b' := by
  unfold GaussianEulerIncompleteName.data
  exact congrPairT (.eqRefl _) (congrPairT (.eqRefl _) (congrPairT ha hb))

theorem left_endpoint_data (n z R B A c d : PTm ℓ) : Γ ⊢[PRAAx]
    leftData n z R B A c d ≐ GaussianEulerQuadraticLowerEndpoint.data n z R B A c d := .eqRefl _

theorem right_endpoint_data (n z R B A c d : PTm ℓ) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    rightData n z R B A c d ≐ GaussianEulerQuadraticUpperEndpoint.gridData n one z R B A c d := by
  have hn : Γ ⊢[PRAAx] c+imageWidth n A R c d ≐ GaussianEulerQuadraticUpperEndpoint.gridNumerator n A R c d one :=
    (exact_image_endpoint n A R c d hd).eqTrans
      ((by unfold lowerDenominator GaussianEulerQuadraticUpperEndpoint.gridDenominator; ipra_ring : Γ ⊢[PRAAx]
        image n A R c d*lowerDenominator n A R d ≐ image n A R c d*GaussianEulerQuadraticUpperEndpoint.gridDenominator n A R d one).eqTrans
          (GaussianEulerQuadraticUpperEndpoint.exact_grid_numerator n A R c d one).eqSymm)
  exact incomplete_data_congr z R B A _ _ _ _ hn (by unfold lowerDenominator GaussianEulerQuadraticUpperEndpoint.gridDenominator; ipra_ring)

theorem original_right_upper_bound (p n z R B A c d : PTm ℓ) (h : Γ ⊢[PRAAx] source z R B A c d) : Γ ⊢[PRAAx]
    bounded (ap2 GaussianEulerIncompleteName.upperF p (rightData n z R B A c d))
      (unit p+unit (n+num 6)) (unit (n+num 6)*unit p) :=
  GaussianRationalReciprocal.bound_congr (congrAp2 GaussianEulerIncompleteName.upperF (.eqRefl p) (right_endpoint_data n z R B A c d h.andE₂.andE₂)).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianEulerQuadraticUpperEndpoint.original_grid_upper_bound p n one z R B A c d h (le_refl one))

theorem actual_quadratic_cutoff_compact_source_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      GaussianEulerSquareCompactComparison.source (var 1) (var 2) (var 3) one (width (var 0) (var 4) (var 2) (var 6))
        (etaDen (var 0) (var 4) (var 2)) (preimage (var 0) (var 4) (var 2) (var 6)) (var 5) (var 6)) :=
  closeUniv 7 (.impI (original_square_source _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_quadratic_cutoff_upper_endpoint_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      bounded (ap2 GaussianEulerIncompleteName.upperF (var 0) (rightData (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))
        (unit (var 0)+unit (var 1+num 6)) (unit (var 1+num 6)*unit (var 0))) :=
  closeUniv 8 (.impI (original_right_upper_bound _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerQuadraticCutoffGeometry
