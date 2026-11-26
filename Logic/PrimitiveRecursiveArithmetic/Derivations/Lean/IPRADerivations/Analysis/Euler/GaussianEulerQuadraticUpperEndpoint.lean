import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIncompleteLargeEndpoint
import IPRADerivations.Analysis.Euler.GaussianEulerQuadraticLowerEndpoint

/-!
# Original upper tails at quadratically mapped cofinal endpoints

Choose the positive preimage d*top_n. Its image under (c/d)u^2 is
an original integer top cutoff at a computed index at least n. Both
the reduced rational encoding and the literal square-grid encoding
therefore retain the original dyadic upper-tail budget.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerQuadraticUpperEndpoint

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaIntegralCutoffs (height etaDen top tailCoefficient)
open GaussianEulerIncompleteName (upperF)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num monus)

variable {ℓ : ℕ} {Γ : List (Fm PTm ℓ)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def source (z R B A c d : PTm ℓ) : Fm PTm ℓ := GaussianEulerQuadraticLowerEndpoint.source z R B A c d
def baseline (A R : PTm ℓ) : PTm ℓ := A+tailCoefficient R+num 10
def halfImage (n A R c d : PTm ℓ) : PTm ℓ := two*c*d*height n A R*height n A R
def imageIndex (n A R c d : PTm ℓ) : PTm ℓ := monus (halfImage n A R c d) (baseline A R)
def preimage (n A R d : PTm ℓ) : PTm ℓ := d*top n A R
def image (n A R c d : PTm ℓ) : PTm ℓ := c*d*top n A R*top n A R
def data (n z R B A c d b : PTm ℓ) : PTm ℓ :=
  GaussianEulerIncompleteName.data z R B A (image n A R c d*b) b
def gridDenominator (n A R d M : PTm ℓ) : PTm ℓ := d*(etaDen n A R*M)*(etaDen n A R*M)
def gridNumerator (n A R c d M : PTm ℓ) : PTm ℓ :=
  c*(preimage n A R d*(etaDen n A R*M))*(preimage n A R d*(etaDen n A R*M))
def gridData (n M z R B A c d : PTm ℓ) : PTm ℓ :=
  GaussianEulerIncompleteName.data z R B A (gridNumerator n A R c d M) (gridDenominator n A R d M)

@[simp] theorem subst_source {m : ℕ} (σ : Fin ℓ → PTm m) (z R B A c d : PTm ℓ) :
    (source z R B A c d).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ c) (Syn.subst σ d) := by simp [source]
@[simp] theorem subst_baseline {m : ℕ} (σ : Fin ℓ → PTm m) (A R : PTm ℓ) :
    Syn.subst σ (baseline A R) = baseline (Syn.subst σ A) (Syn.subst σ R) := by simp [baseline,tailCoefficient]
@[simp] theorem subst_halfImage {m : ℕ} (σ : Fin ℓ → PTm m) (n A R c d : PTm ℓ) :
    Syn.subst σ (halfImage n A R c d) = halfImage (Syn.subst σ n) (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ c) (Syn.subst σ d) := by simp [halfImage,height,tailCoefficient]
@[simp] theorem subst_imageIndex {m : ℕ} (σ : Fin ℓ → PTm m) (n A R c d : PTm ℓ) :
    Syn.subst σ (imageIndex n A R c d) = imageIndex (Syn.subst σ n) (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ c) (Syn.subst σ d) := by simp [imageIndex]
@[simp] theorem subst_preimage {m : ℕ} (σ : Fin ℓ → PTm m) (n A R d : PTm ℓ) :
    Syn.subst σ (preimage n A R d) = preimage (Syn.subst σ n) (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ d) := by simp [preimage,top,height,tailCoefficient]
@[simp] theorem subst_image {m : ℕ} (σ : Fin ℓ → PTm m) (n A R c d : PTm ℓ) :
    Syn.subst σ (image n A R c d) = image (Syn.subst σ n) (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ c) (Syn.subst σ d) := by simp [image,top,height,tailCoefficient]
@[simp] theorem subst_data {m : ℕ} (σ : Fin ℓ → PTm m) (n z R B A c d b : PTm ℓ) :
    Syn.subst σ (data n z R B A c d b) = data (Syn.subst σ n) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ c) (Syn.subst σ d) (Syn.subst σ b) := by simp [data]
@[simp] theorem subst_gridDenominator {m : ℕ} (σ : Fin ℓ → PTm m) (n A R d M : PTm ℓ) :
    Syn.subst σ (gridDenominator n A R d M) = gridDenominator (Syn.subst σ n) (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ d) (Syn.subst σ M) := by simp [gridDenominator,etaDen,height,tailCoefficient]
@[simp] theorem subst_gridNumerator {m : ℕ} (σ : Fin ℓ → PTm m) (n A R c d M : PTm ℓ) :
    Syn.subst σ (gridNumerator n A R c d M) = gridNumerator (Syn.subst σ n) (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ c) (Syn.subst σ d) (Syn.subst σ M) := by simp [gridNumerator,etaDen,height,tailCoefficient]
@[simp] theorem subst_gridData {m : ℕ} (σ : Fin ℓ → PTm m) (n M z R B A c d : PTm ℓ) :
    Syn.subst σ (gridData n M z R B A c d) = gridData (Syn.subst σ n) (Syn.subst σ M) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ c) (Syn.subst σ d) := by simp [gridData]

theorem height_le_half_image (n A R c d : PTm ℓ) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    le (height n A R) (halfImage n A R c d) := by
  have hh := GaussianGammaIntegralCutoffs.height_positive (Γ := Γ) n A R
  have square : Γ ⊢[PRAAx] le (height n A R) (height n A R*height n A R) :=
    le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right (height n A R) hh)
  have coeff := positive_product two (c*d) (zero_lt_succ one) (positive_product _ _ hc hd)
  exact le_trans square (le_congr (by ipra_ring) (by unfold halfImage; ipra_ring)
    (mul_le_mul_right (height n A R*height n A R) coeff))

theorem image_height (n A R c d : PTm ℓ) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    height (imageIndex n A R c d) A R ≐ halfImage n A R c d := by
  have hb : Γ ⊢[PRAAx] le (baseline A R) (height n A R) :=
    le_of_eq_add (d := n) (by unfold baseline height; ipra_ring)
  have e := eq_add_of_le (le_trans hb (height_le_half_image n A R c d hc hd))
  exact (by unfold height imageIndex baseline; ipra_ring : Γ ⊢[PRAAx]
    height (imageIndex n A R c d) A R ≐ baseline A R+imageIndex n A R c d).eqTrans e.eqSymm

theorem image_index_later (n A R c d : PTm ℓ) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    le n (imageIndex n A R c d) := by
  have bound := le_congr (.eqRefl _) (image_height n A R c d hc hd).eqSymm (height_le_half_image n A R c d hc hd)
  exact le_of_add_le_add_right (le_congr (by unfold height baseline; ipra_ring) (by unfold height baseline; ipra_ring) bound :
    Γ ⊢[PRAAx] le (n+baseline A R) (imageIndex n A R c d+baseline A R))

theorem exact_image_top (n A R c d : PTm ℓ) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    top (imageIndex n A R c d) A R ≐ image n A R c d :=
  (congrMul (.eqRefl two) (image_height n A R c d hc hd)).eqTrans (by unfold halfImage image top; ipra_ring)

theorem exact_mapping (n A R c d : PTm ℓ) : Γ ⊢[PRAAx]
    c*preimage n A R d*preimage n A R d ≐ d*image n A R c d := by unfold preimage image; ipra_ring

private theorem incomplete_data_congr (z R B A a a' b : PTm ℓ) (ha : Γ ⊢[PRAAx] a ≐ a') : Γ ⊢[PRAAx]
    GaussianEulerIncompleteName.data z R B A a b ≐ GaussianEulerIncompleteName.data z R B A a' b := by
  unfold GaussianEulerIncompleteName.data
  exact congrPairT (.eqRefl _) (congrPairT (.eqRefl _) (congrPairT ha (.eqRefl _)))

theorem original_upper_bound (p n z R B A c d b : PTm ℓ) (hs : Γ ⊢[PRAAx] source z R B A c d) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    bounded (ap2 upperF p (data n z R B A c d b)) (unit p+unit (n+num 6)) (unit (n+num 6)*unit p) := by
  let k := imageIndex n A R c d
  have raw := GaussianEulerIncompleteLargeEndpoint.original_dyadic_upper_bound p k z R B A b (.andI hs.andE₁ hb)
  have he := incomplete_data_congr z R B A _ _ b (congrMul (exact_image_top n A R c d hs.andE₂.andE₁ hs.andE₂.andE₂) (.eqRefl b))
  have atImage := GaussianRationalReciprocal.bound_congr (congrAp2 upperF (.eqRefl p) he) (.eqRefl _) (.eqRefl _) raw
  have hu := GaussianExponentialReference.unit_monotone
    (add_le_add_right (num 6) (image_index_later n A R c d hs.andE₂.andE₁ hs.andE₂.andE₂))
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (unit_positive _) (unit_positive _)) (positive_product _ _ (unit_positive _) (unit_positive _))
    (by ipra_le (𝔞(unit p)*𝔞(unit p))*sl hu) atImage

theorem exact_grid_numerator (n A R c d M : PTm ℓ) : Γ ⊢[PRAAx]
    gridNumerator n A R c d M ≐ image n A R c d*gridDenominator n A R d M := by
  unfold gridNumerator preimage image gridDenominator; ipra_ring

theorem original_grid_upper_bound (p n M z R B A c d : PTm ℓ) (hs : Γ ⊢[PRAAx] source z R B A c d) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    bounded (ap2 upperF p (gridData n M z R B A c d)) (unit p+unit (n+num 6)) (unit (n+num 6)*unit p) := by
  have hE := positive_product _ _ (GaussianGammaIntegralCutoffs.eta_den_positive n A R) hM
  have hb := positive_product _ _ (positive_product _ _ hs.andE₂.andE₂ hE) hE
  have he := incomplete_data_congr (Γ := Γ) z R B A _ _ (gridDenominator n A R d M) (exact_grid_numerator n A R c d M)
  exact GaussianRationalReciprocal.bound_congr (congrAp2 upperF (.eqRefl p) he.eqSymm) (.eqRefl _) (.eqRefl _)
    (original_upper_bound p n z R B A c d (gridDenominator n A R d M) hs hb)

theorem actual_original_quadratic_upper_omitted_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⋏ le one (var 2)) ⟶
      bounded (ap2 upperF (var 0) (gridData (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))
        (unit (var 0)+unit (var 1+num 6)) (unit (var 1+num 6)*unit (var 0))) :=
  closeUniv 9 (.impI (original_grid_upper_bound _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerQuadraticUpperEndpoint
