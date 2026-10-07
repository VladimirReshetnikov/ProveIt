import OAI.Combinatorics.Progressions.Dynamics.JetOutputRadiusLogBudget
import OAI.Combinatorics.Progressions.Estimates.NormalizedJetL1Parameter
import OAI.Combinatorics.Progressions.Estimates.NormalizedJetMeasurability
import OAI.Combinatorics.Progressions.Estimates.SelectedProfileTranslationL1
import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityRiemann
import OAI.Combinatorics.Progressions.Probability.CoefficientDensitySplit

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem affineProductProfile_range_bound {J : Type*} [Fintype J]
    (c w : J → ℝ) {δ : ℝ≥0} (hδ : 0 < δ) (hw : ∀ j, (δ : ℝ) ≤ w j) (x : J → ℝ) :
    affineProductProfile c w x ∈ Set.Icc (0 : ℝ) ((δ⁻¹^Fintype.card J : ℝ≥0) : ℝ) := by
  have hwpos : ∀ j, 0 < w j := fun j => (show (0 : ℝ) < δ from hδ).trans_le (hw j)
  refine ⟨affineProductProfile_nonneg c w hwpos x, ?_⟩
  have hb := affineProductProfile_cap c w (show (0 : ℝ) < δ from hδ) hw x
  rw [Real.norm_eq_abs, abs_of_nonneg (affineProductProfile_nonneg c w hwpos x)] at hb
  simpa only [NNReal.coe_pow, NNReal.coe_inv] using hb

theorem affineCoefficientDensity_split {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix I J ℤ) (C : Matrix I N ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (hfull : ((Matrix.fromCols A C).submatrix id (s.trans Function.Embedding.inl)).det ≠ 0)
    (S : J → ℝ) (T : N → ℝ) (P : I → ℝ) (hS : ∀ j, 0 < S j) (hT : ∀ n, 0 < T n)
    (hP : ∀ i, 0 < P i) (c w : J ⊕ N → ℝ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hw : ∀ j, (δ : ℝ) ≤ w j) (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R) :
    selectedCoefficientDensity (Matrix.fromCols A C) (s.trans Function.Embedding.inl) hfull
      (Sum.elim S T) P (Sum.rec hS hT) hP (affineProductProfile c w) =
      pivotOutputDensity
        (normalizedPivotEquiv (A.submatrix id s) hA (fun i => S (s i)) P (fun i => hS (s i)) hP)
        (splitFreeColumns
          (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s) (fun j => S j.val) P))
          (matrixSupCLM (normalizedIntegerColumns C T P)))
        (splitFreeProfile
          (selectedCoefficientProfile s (affineProductProfile (fun j => c (.inl j)) (fun j => w (.inl j))))
          (affineProductProfile (fun n => c (.inr n)) (fun n => w (.inr n)))) := by
  have hwpos : ∀ j, 0 < w j := fun j => (show (0 : ℝ) < δ from hδ).trans_le (hw j)
  rw [affineProductProfile_joined]
  exact selectedCoefficientDensity_split A C s hA hfull S T P hS hT hP _ _ R R
    (δ⁻¹^Fintype.card J) (δ⁻¹^Fintype.card N) (affineProductProfileLip J δ) (affineProductProfileLip N δ)
    (affineProductProfile_lipschitz _ _ hδ (fun j => hw (.inl j)))
    (affineProductProfile_lipschitz _ _ hδ (fun n => hw (.inr n)))
    (affineProductProfile_range_bound _ _ hδ (fun j => hw (.inl j)))
    (affineProductProfile_range_bound _ _ hδ (fun n => hw (.inr n)))
    (affineProductProfile_zero_outside _ _ (fun j => hwpos (.inl j)) R.coe_nonneg (fun j => hsupport (.inl j)))
    (affineProductProfile_zero_outside _ _ (fun n => hwpos (.inr n)) R.coe_nonneg (fun n => hsupport (.inr n)))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def affineSelectedJetDensity {Z X K α I J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (s : I ↪ J) (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (F : (UnselectedColumn s → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ) (rows : I → Finset α)
    (c w : J ⊕ N → ℝ) (x : X → ℝ) : (I → ℝ) → ℝ :=
  normalizedJetDensity A F e input z rows
    (selectedCoefficientProfile s (affineProductProfile (fun j => c (.inl j)) (fun j => w (.inl j))))
    (affineProductProfile (fun n => c (.inr n)) (fun n => w (.inr n))) x

theorem affineSelectedJetDensity_bounds {Z X K α I J N : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (s : I ↪ J) (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (F : (UnselectedColumn s → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1)
    (rows : I → Finset α) {degree : ℕ} (hd : ∀ n, (e n).sum (fun _ k => k) ≤ degree)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) {δ : ℝ≥0} (hδ : 0 < δ)
    (hwidth : ∀ j, (δ : ℝ) ≤ w (.inl j)) (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R)
    (v : I → ℝ) :
    (∀ x, ‖affineSelectedJetDensity s A F e input z rows c w x v‖ ≤
      pivotKernelCap (UnselectedColumn s) A R (δ⁻¹^Fintype.card J)) ∧
    LipschitzOnWith (pivotKernelLip (UnselectedColumn s) A R (affineProductProfileLip J δ) *
      (Fintype.card N * polynomialBoxLip (Fintype.card X) degree (normalizedJetMass α degree)) * R)
      (fun x => affineSelectedJetDensity s A F e input z rows c w x v) (Metric.closedBall 0 1) := by
  have hcap := affineProductProfile_cap (fun j => c (.inl j)) (fun j => w (.inl j))
    (show (0 : ℝ) < δ from hδ) hwidth
  have hcap' : ∀ x, ‖affineProductProfile (fun j => c (.inl j)) (fun j => w (.inl j)) x‖ ≤
      ((δ⁻¹^Fintype.card J : ℝ≥0) : ℝ) := by
    simpa only [NNReal.coe_pow, NNReal.coe_inv] using hcap
  exact normalizedJetDensity_bounds A F e input z hz rows hd R (δ⁻¹^Fintype.card J)
    (affineProductProfileLip J δ) R
    (selectedCoefficientProfile_lipschitz s (affineProductProfile_lipschitz _ _ hδ hwidth))
    (affineProductProfile_contDiff _ _).continuous
    (selectedCoefficientProfile_zero_outside s
      (affineProductProfile_zero_outside _ _ (fun j => hw (.inl j)) R.coe_nonneg (fun j => hsupport (.inl j))))
    (affineProductProfile_zero_outside _ _ (fun n => hw (.inr n)) R.coe_nonneg (fun n => hsupport (.inr n)))
    (selectedCoefficientProfile_norm_le s hcap')
    (affineProductProfile_nonneg _ _ (fun n => hw (.inr n)))
    (affineProductProfile_integral _ _ (fun n => hw (.inr n))) v

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def affineJetL1Cost (P α J N : Type*) [Fintype P] [Fintype α] [Fintype J] [Fintype N]
    {I : Type*} [Fintype I] (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (degree : ℕ) (δ R : ℝ≥0) : ℝ≥0 :=
  (Fintype.card J * (4 * probabilityProfileLipschitz / δ) * ‖A.symm.toContinuousLinearMap‖₊) *
    (Fintype.card N * polynomialBoxLip (Fintype.card P) degree (normalizedJetMass α degree)) * R

theorem affineSelectedJetDensity_l1_regular {Z P K α I J N : Type*}
    [Fintype P] [DecidableEq P] [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (s : I ↪ J) (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (F : (UnselectedColumn s → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1)
    (rows : I → Finset α) {degree : ℕ} (hd : ∀ n, (e n).sum (fun _ k => k) ≤ degree)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) {δ : ℝ≥0} (hδ : 0 < δ)
    (hwidth : ∀ j, (δ : ℝ) ≤ w (.inl j)) (R : ℝ≥0) (hsupport : ∀ j, |c j| + w j ≤ R)
    (a : P → ℝ) (ha : a ∈ Metric.closedBall 0 1) (b : P → ℝ) (hb : b ∈ Metric.closedBall 0 1) :
    (∫ v, |affineSelectedJetDensity s A F e input z rows c w a v -
      affineSelectedJetDensity s A F e input z rows c w b v|) ≤
        affineJetL1Cost P α J N A degree δ R * dist a b := by
  have hf : Continuous (selectedCoefficientProfile s
      (affineProductProfile (fun j => c (.inl j)) (fun j => w (.inl j)))) :=
    (affineProductProfile_contDiff (fun j => c (.inl j)) (fun j => w (.inl j))).continuous.comp
      (selectedCoefficientEquiv_lipschitz s).continuous
  apply normalizedJetDensity_l1_regular A F e input z hz rows hd hf
    (affineProductProfile_contDiff (fun n => c (.inr n)) (fun n => w (.inr n))).continuous R R
    (Fintype.card J * (4 * probabilityProfileLipschitz / δ) * ‖A.symm.toContinuousLinearMap‖₊)
    (selectedCoefficientProfile_zero_outside s (affineProductProfile_zero_outside _ _
      (fun j => hw (.inl j)) R.coe_nonneg (fun j => hsupport (.inl j))))
    (affineProductProfile_zero_outside _ _ (fun n => hw (.inr n)) R.coe_nonneg (fun n => hsupport (.inr n)))
    (selectedCoefficientProfile_nonneg s (affineProductProfile_nonneg _ _ (fun j => hw (.inl j))))
    (affineProductProfile_nonneg _ _ (fun n => hw (.inr n)))
    _ (affineProductProfile_integral _ _ (fun n => hw (.inr n))) _ a ha b hb
  · rw [selectedCoefficientProfile_integral, affineProductProfile_integral _ _ (fun j => hw (.inl j))]
  · intro u v
    simpa only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm] using
      affineSelectedPivot_translation_l1 s A F (fun j => c (.inl j)) (fun j => w (.inl j))
        (show (0 : ℝ) < δ from hδ) hwidth u v

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem affineSelectedJetDensity_principalTuple_riemann {Z K D α I J N : Type*}
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    [Fintype I] [Fintype J] [Fintype N]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (s : I ↪ J) (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (F : (UnselectedColumn s → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ JointBlockParameter B h α)
    (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1) (rows : I → Finset α)
    {degree : ℕ} (hd : ∀ n, (e n).sum (fun _ k => k) ≤ degree)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) {δ : ℝ≥0} (hδ : 0 < δ)
    (hwidth : ∀ j, (δ : ℝ) ≤ w (.inl j)) (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R)
    (L M : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (m : PrincipalTupleIndex B h → Option α → ℕ) (r : ∀ j i, ZMod (m j i))
    (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M j)
    (hsize : ∀ j, (Fintype.card α+1)*M j ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((M j : ℝ)/L j) < volume.real (scalarCubeDomain α))
    (v : I → ℝ) :
    let ρ := fun x => affineSelectedJetDensity s A F e input z rows c w x v
    let Cap := pivotKernelCap (UnselectedColumn s) A R (δ⁻¹^Fintype.card J)
    let Lip := pivotKernelLip (UnselectedColumn s) A R (affineProductProfileLip J δ) *
      (Fintype.card N * polynomialBoxLip (Fintype.card (JointBlockParameter B h α)) degree
        (normalizedJetMass α degree)) * R
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (L j) (M j) (hL j)
      (m j) (r j) (hm j) (hmM j) (hsize j))).mean
        (fun y => ρ (fun a => (y ⟨a.1, a.2.1, a.2.2.1⟩ a.2.2.2 : ℝ) / L ⟨a.1, a.2.1, a.2.2.1⟩)) -
      ∫ x, ρ x ∂jointBooleanSource h| ≤
      (2 * (Cap : ℝ) * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) + Lip) *
        ∑ j, (M j : ℝ)/L j := by
  dsimp only
  have hb := affineSelectedJetDensity_bounds s A F e input z hz rows hd c w hw hδ hwidth R hsupport v
  exact principalTuple_residue_riemann_on_box B h L M hL m r hm hmM hsize hsmall _ hb.2
    (pivotKernelCap (UnselectedColumn s) A R (δ⁻¹^Fintype.card J)).coe_nonneg (fun x _ => hb.1 x)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem splitPivotDensity_output_lipschitz {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    (C : (N → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (R K S : ℝ≥0) (hf : LipschitzWith K f) (hg : Continuous g)
    (hfs : ∀ p, (R : ℝ) < ‖p‖ → f p = 0) (hgs : ∀ n, (S : ℝ) < ‖n‖ → g n = 0)
    (hg0 : ∀ n, 0 ≤ g n) (hgmass : (∫ n, g n) = 1) :
    LipschitzWith (pivotKernelLip J A R K)
      (pivotOutputDensity A (splitFreeColumns B C) (splitFreeProfile f g)) := by
  have hρ := pivotOutputDensity_lipschitz A B R K hf hfs
  have hi (v : I → ℝ) : Integrable (fun n => g n*pivotOutputDensity A B f (v-C n)) :=
    compactBox_integrable _ (hg.mul (hρ.continuous.comp (by fun_prop))) S
      (fun n hn => by rw [hgs n hn, zero_mul])
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [Real.dist_eq, splitPivotDensity_formula A B C hf.continuous hg hfs hgs v,
    splitPivotDensity_formula A B C hf.continuous hg hfs hgs w]
  apply fixedKernelMixture_difference_le volume g _ _ (compactBox_integrable g hg S hgs) hg0 hgmass (hi v) (hi w)
  intro n _
  simpa only [Real.dist_eq, dist_sub_right] using hρ.dist_le_mul (v-C n) (w-C n)

theorem affineSelectedJetDensity_output_lipschitz {Z X K α I J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (s : I ↪ J) (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (F : (UnselectedColumn s → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ) (rows : I → Finset α)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) {δ : ℝ≥0} (hδ : 0 < δ)
    (hwidth : ∀ j, (δ : ℝ) ≤ w (.inl j)) (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R)
    (x : X → ℝ) :
    LipschitzWith (pivotKernelLip (UnselectedColumn s) A R (affineProductProfileLip J δ))
      (affineSelectedJetDensity s A F e input z rows c w x) := by
  apply splitPivotDensity_output_lipschitz A F _ R (affineProductProfileLip J δ) R
    (selectedCoefficientProfile_lipschitz s (affineProductProfile_lipschitz _ _ hδ hwidth))
    (affineProductProfile_contDiff _ _).continuous
    (selectedCoefficientProfile_zero_outside s
      (affineProductProfile_zero_outside _ _ (fun j => hw (.inl j)) R.coe_nonneg (fun j => hsupport (.inl j))))
    (affineProductProfile_zero_outside _ _ (fun n => hw (.inr n)) R.coe_nonneg (fun n => hsupport (.inr n)))
    (affineProductProfile_nonneg _ _ (fun n => hw (.inr n)))
    (affineProductProfile_integral _ _ (fun n => hw (.inr n)))

theorem affineSelectedJetDensity_output_cap {Z X K α I J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (s : I ↪ J) (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (F : (UnselectedColumn s → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ) (rows : I → Finset α)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) {δ : ℝ≥0} (hδ : 0 < δ)
    (hwidth : ∀ j, (δ : ℝ) ≤ w (.inl j)) (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R)
    (x : X → ℝ) (v : I → ℝ) :
    |affineSelectedJetDensity s A F e input z rows c w x v| ≤
      pivotKernelCap (UnselectedColumn s) A R (δ⁻¹^Fintype.card J) := by
  have hcap : ∀ u, ‖affineProductProfile (fun j => c (.inl j)) (fun j => w (.inl j)) u‖ ≤
      ((δ⁻¹^Fintype.card J : ℝ≥0) : ℝ) := by
    simpa only [NNReal.coe_pow, NNReal.coe_inv] using
      affineProductProfile_cap (fun j => c (.inl j)) (fun j => w (.inl j))
        (show (0 : ℝ) < δ from hδ) hwidth
  exact splitPivotDensity_norm_le_cap A F _ R (δ⁻¹^Fintype.card J) R
    (selectedCoefficientProfile_lipschitz s (affineProductProfile_lipschitz _ _ hδ hwidth)).continuous
    (affineProductProfile_contDiff _ _).continuous
    (selectedCoefficientProfile_zero_outside s
      (affineProductProfile_zero_outside _ _ (fun j => hw (.inl j)) R.coe_nonneg (fun j => hsupport (.inl j))))
    (affineProductProfile_zero_outside _ _ (fun n => hw (.inr n)) R.coe_nonneg (fun n => hsupport (.inr n)))
    (selectedCoefficientProfile_norm_le s hcap) (affineProductProfile_nonneg _ _ (fun n => hw (.inr n)))
    (affineProductProfile_integral _ _ (fun n => hw (.inr n))) v

theorem affineSelectedJetDensity_output_support {Z X K α I J N : Type*}
    [Fintype X] [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (s : I ↪ J) (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (F : (UnselectedColumn s → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1)
    (rows : I → Finset α) {degree : ℕ} (hd : ∀ n, (e n).sum (fun _ k => k) ≤ degree)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R)
    (x : X → ℝ) (hx : ‖x‖ ≤ 1) (v : I → ℝ)
    (hv : (normalizedJetOutputRadius α N A F degree R R : ℝ) < ‖v‖) :
    affineSelectedJetDensity s A F e input z rows c w x v = 0 := by
  exact normalizedJetDensity_zero_outside A F e input z hz rows hd R R
    ((affineProductProfile_contDiff _ _).continuous.comp (selectedCoefficientEquiv_lipschitz s).continuous)
    (affineProductProfile_contDiff _ _).continuous
    (selectedCoefficientProfile_zero_outside s
      (affineProductProfile_zero_outside _ _ (fun j => hw (.inl j)) R.coe_nonneg (fun j => hsupport (.inl j))))
    (affineProductProfile_zero_outside _ _ (fun n => hw (.inr n)) R.coe_nonneg (fun n => hsupport (.inr n)))
    x hx v hv

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

noncomputable def jointAffineJetDensity {Q Z X K α : Type*} [Fintype Q]
    [Fintype α] [DecidableEq α] {I J N : Q → Type*}
    [∀ q, Fintype (I q)] [∀ q, Fintype (J q)] [∀ q, Fintype (N q)]
    (s : ∀ q, I q ↪ J q) (A : ∀ q, (I q → ℝ) ≃L[ℝ] (I q → ℝ))
    (F : ∀ q, (UnselectedColumn (s q) → ℝ) →L[ℝ] (I q → ℝ))
    (e : ∀ q, N q → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ)
    (rows : ∀ q, I q → Finset α) (c w : ∀ q, J q ⊕ N q → ℝ)
    (x : X → ℝ) (v : ∀ q, I q → ℝ) : ℝ :=
  ∏ q, affineSelectedJetDensity (s q) (A q) (F q) (e q) input z (rows q) (c q) (w q) x (v q)

theorem jointAffineJetDensity_bounds {Q Z X K α : Type*} [Fintype Q]
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α] {I J N : Q → Type*}
    [∀ q, Fintype (I q)] [∀ q, Fintype (J q)] [∀ q, Fintype (N q)]
    (s : ∀ q, I q ↪ J q) (A : ∀ q, (I q → ℝ) ≃L[ℝ] (I q → ℝ))
    (F : ∀ q, (UnselectedColumn (s q) → ℝ) →L[ℝ] (I q → ℝ))
    (e : ∀ q, N q → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1)
    (rows : ∀ q, I q → Finset α) (degree : Q → ℕ)
    (hd : ∀ q n, (e q n).sum (fun _ k => k) ≤ degree q)
    (c w : ∀ q, J q ⊕ N q → ℝ) (hw : ∀ q j, 0 < w q j) (δ R : Q → ℝ≥0)
    (hδ : ∀ q, 0 < δ q) (hwidth : ∀ q j, (δ q : ℝ) ≤ w q (.inl j))
    (hsupport : ∀ q j, |c q j|+w q j ≤ R q)
    (Cap Lip : ℝ≥0) (hCap : 1 ≤ Cap)
    (hcap : ∀ q, pivotKernelCap (UnselectedColumn (s q)) (A q) (R q) ((δ q)⁻¹^Fintype.card (J q)) ≤ Cap)
    (hlip : ∀ q, pivotKernelLip (UnselectedColumn (s q)) (A q) (R q) (affineProductProfileLip (J q) (δ q)) *
      (Fintype.card (N q) * polynomialBoxLip (Fintype.card X) (degree q) (normalizedJetMass α (degree q))) * R q ≤ Lip)
    (v : ∀ q, I q → ℝ) :
    (∀ x, |jointAffineJetDensity s A F e input z rows c w x v| ≤ (Cap : ℝ)^Fintype.card Q) ∧
      LipschitzOnWith (Fintype.card Q*Lip*Cap^Fintype.card Q)
        (fun x => jointAffineJetDensity s A F e input z rows c w x v) (Metric.closedBall 0 1) := by
  let f := fun q x => affineSelectedJetDensity (s q) (A q) (F q) (e q) input z (rows q) (c q) (w q) x (v q)
  have hreg (q) := affineSelectedJetDensity_bounds (s q) (A q) (F q) (e q) input z hz
    (rows q) (hd q) (c q) (w q) (hw q) (hδ q) (hwidth q) (R q) (hsupport q) (v q)
  have hfcap : ∀ q x, |f q x| ≤ Cap := fun q x => (hreg q).1 x |>.trans (hcap q)
  have hfLip : ∀ q, LipschitzOnWith Lip (f q) (Metric.closedBall 0 1) := by
    intro q
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    exact ((hreg q).2.dist_le_mul x hx y hy).trans
      (mul_le_mul_of_nonneg_right (show (_ : ℝ) ≤ Lip from hlip q) dist_nonneg)
  exact ⟨finiteProduct_cap f Cap.coe_nonneg hfcap,
    finiteProduct_lipschitzOn f (Metric.closedBall 0 1) Cap Lip hCap hfLip (fun q x _ => hfcap q x)⟩

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def affineJetL1Log (u a j n d : ℕ) (p v : ℝ) : ℝ :=
  j + 4 * (probabilityProfileLipschitz : ℝ) + 2*p + v +
    n + 3*(u : ℝ)*d + (a : ℝ)*(d+1)

theorem affineJetL1Log_nonneg (u a j n d : ℕ) {p v : ℝ}
    (hp : 0 ≤ p) (hv : 0 ≤ v) : 0 ≤ affineJetL1Log u a j n d p v := by
  unfold affineJetL1Log
  positivity

theorem affineJetL1Cost_le_exp (P α J N : Type*)
    [Fintype P] [Fintype α] [Fintype J] [Fintype N]
    {I : Type*} [Fintype I] (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (d : ℕ)
    (δ R : ℝ≥0) {p v : ℝ} (hδ : (δ : ℝ)⁻¹ ≤ Real.exp p)
    (hR : (R : ℝ) ≤ Real.exp p) (hi : ‖A.symm.toContinuousLinearMap‖ ≤ Real.exp v) :
    (affineJetL1Cost P α J N A d δ R : ℝ) ≤
      Real.exp (affineJetL1Log (Fintype.card P) (Fintype.card α)
        (Fintype.card J) (Fintype.card N) d p v) := by
  have hj : (Fintype.card J : ℝ) ≤ Real.exp (Fintype.card J : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card J : ℝ)]
  have ha : 4 * (probabilityProfileLipschitz : ℝ) ≤
      Real.exp (4 * (probabilityProfileLipschitz : ℝ)) := by
    linarith [Real.add_one_le_exp (4 * (probabilityProfileLipschitz : ℝ))]
  have hn := normalizedJetColumnLip_le_exp α (Fintype.card N) (Fintype.card P) d
  simp only [affineJetL1Cost, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_inv,
    NNReal.coe_ofNat, coe_nnnorm, div_eq_mul_inv]
  calc
    _ ≤ (Real.exp (Fintype.card J : ℝ) *
        (Real.exp (4 * (probabilityProfileLipschitz : ℝ)) * Real.exp p) * Real.exp v) *
        Real.exp (Fintype.card N + 3*(Fintype.card P : ℝ)*d + (Fintype.card α : ℝ)*(d+1)) *
        Real.exp p := by gcongr
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold affineJetL1Log
      ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

noncomputable def affineSelectedJetProfile {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    (s : I ↪ J) (c w : J ⊕ N → ℝ) : (UnselectedColumn s ⊕ N → ℝ) × (I → ℝ) → ℝ :=
  splitFreeProfile
    (selectedCoefficientProfile s (affineProductProfile (fun j => c (.inl j)) (fun j => w (.inl j))))
    (affineProductProfile (fun n => c (.inr n)) (fun n => w (.inr n)))

theorem affineSelectedJetProfile_probability_data {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N] (s : I ↪ J) (c w : J ⊕ N → ℝ)
    (hw : ∀ j, 0 < w j) (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R) :
    Integrable (affineSelectedJetProfile s c w) ∧
      (∀ u, 0 ≤ affineSelectedJetProfile s c w u) ∧
      (∫ u, affineSelectedJetProfile s c w u) = 1 := by
  have hf : Continuous (selectedCoefficientProfile s
      (affineProductProfile (fun j => c (.inl j)) (fun j => w (.inl j)))) :=
    (affineProductProfile_contDiff (fun j => c (.inl j)) (fun j => w (.inl j))).continuous.comp
      (selectedCoefficientEquiv_lipschitz s).continuous
  have hg := (affineProductProfile_contDiff (fun n => c (.inr n)) (fun n => w (.inr n))).continuous
  have hfs := selectedCoefficientProfile_zero_outside s
    (affineProductProfile_zero_outside _ _ (fun j => hw (.inl j)) R.coe_nonneg (fun j => hsupport (.inl j)))
  have hgs := affineProductProfile_zero_outside _ _ (fun n => hw (.inr n)) R.coe_nonneg
    (fun n => hsupport (.inr n))
  refine ⟨splitFreeProfile_integrable hf hg hfs hgs,
    splitFreeProfile_nonneg (selectedCoefficientProfile_nonneg s
      (affineProductProfile_nonneg _ _ (fun j => hw (.inl j))))
      (affineProductProfile_nonneg _ _ (fun n => hw (.inr n))), ?_⟩
  change (∫ u, splitFreeProfile _ _ u) = 1
  rw [splitFreeProfile_integral hf hg hfs hgs, selectedCoefficientProfile_integral,
    affineProductProfile_integral _ _ (fun j => hw (.inl j)),
    affineProductProfile_integral _ _ (fun n => hw (.inr n)), one_mul]

theorem jointAffineJetDensity_law {Q Z X K α : Type*} [Fintype Q]
    [Fintype α] [DecidableEq α] {I J N : Q → Type*}
    [∀ q, Fintype (I q)] [∀ q, Fintype (J q)] [∀ q, Fintype (N q)]
    (s : ∀ q, I q ↪ J q) (A : ∀ q, (I q → ℝ) ≃L[ℝ] (I q → ℝ))
    (F : ∀ q, (UnselectedColumn (s q) → ℝ) →L[ℝ] (I q → ℝ))
    (e : ∀ q, N q → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ)
    (rows : ∀ q, I q → Finset α) (c w : ∀ q, J q ⊕ N q → ℝ) (hw : ∀ q j, 0 < w q j)
    (R : Q → ℝ≥0) (hsupport : ∀ q j, |c q j|+w q j ≤ R q) (x : X → ℝ) :
    (Measure.pi (fun q => realDensityMeasure volume (affineSelectedJetProfile (s q) (c q) (w q)))).map
      (fun u q => A q (u q).2 +
        splitFreeColumns (F q)
          (polynomialColumns (fun o n => normalizedJetColumn (e q n) input z (rows q o)) x) (u q).1) =
      realDensityMeasure (Measure.pi (fun q => (volume : Measure (I q → ℝ))))
        (jointAffineJetDensity s A F e input z rows c w x) := by
  let V := fun q => splitFreeColumns (F q)
    (polynomialColumns (fun o n => normalizedJetColumn (e q n) input z (rows q o)) x)
  have hp (q) := affineSelectedJetProfile_probability_data (s q) (c q) (w q) (hw q) (R q) (hsupport q)
  let : ∀ q, IsProbabilityMeasure (realDensityMeasure volume (affineSelectedJetProfile (s q) (c q) (w q))) :=
    fun q => realDensityMeasure_probability volume _ (hp q).1 (hp q).2.1 (hp q).2.2
  have hm (q) : Measurable (fun u : (UnselectedColumn (s q) ⊕ N q → ℝ) × (I q → ℝ) =>
      A q u.2 + V q u.1) := by fun_prop
  change (Measure.pi _).map
    (fun (u : ∀ q, (UnselectedColumn (s q) ⊕ N q → ℝ) × (I q → ℝ)) q =>
      A q (u q).2 + V q (u q).1) = _
  rw [Measure.pi_map_pi (fun q => (hm q).aemeasurable)]
  have hlaw (q) := pivotOutputDensity_law (A q) (V q) (hp q).1 (hp q).2.1
  simp_rw [hlaw]
  exact realDensityMeasure_pi (fun _ => volume) _
    (fun q => pivotOutputDensity_integrable (A q) (V q) (hp q).1)
    (fun q => pivotOutputDensity_nonneg (A q) (V q) (hp q).2.1)

theorem jointAffineJetDensity_probability_data {Q Z X K α : Type*} [Fintype Q]
    [Fintype α] [DecidableEq α] {I J N : Q → Type*}
    [∀ q, Fintype (I q)] [∀ q, Fintype (J q)] [∀ q, Fintype (N q)]
    (s : ∀ q, I q ↪ J q) (A : ∀ q, (I q → ℝ) ≃L[ℝ] (I q → ℝ))
    (F : ∀ q, (UnselectedColumn (s q) → ℝ) →L[ℝ] (I q → ℝ))
    (e : ∀ q, N q → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ)
    (rows : ∀ q, I q → Finset α) (c w : ∀ q, J q ⊕ N q → ℝ) (hw : ∀ q j, 0 < w q j)
    (R : Q → ℝ≥0) (hsupport : ∀ q j, |c q j|+w q j ≤ R q) (x : X → ℝ) :
    Integrable (jointAffineJetDensity s A F e input z rows c w x) (Measure.pi (fun _ => volume)) ∧
      (∀ v, 0 ≤ jointAffineJetDensity s A F e input z rows c w x v) ∧
      (∫ v, jointAffineJetDensity s A F e input z rows c w x v ∂Measure.pi (fun _ => volume)) = 1 := by
  let V := fun q => splitFreeColumns (F q)
    (polynomialColumns (fun o n => normalizedJetColumn (e q n) input z (rows q o)) x)
  have hp (q) := affineSelectedJetProfile_probability_data (s q) (c q) (w q) (hw q) (R q) (hsupport q)
  have hfi (q) := pivotOutputDensity_integrable (A q) (V q) (hp q).1
  refine ⟨Integrable.fintype_prod_dep hfi, ?_, ?_⟩
  · intro v
    exact Finset.prod_nonneg (fun q _ => pivotOutputDensity_nonneg (A q) (V q) (hp q).2.1 (v q))
  · change (∫ v, (∏ q, pivotOutputDensity (A q) (V q) (affineSelectedJetProfile (s q) (c q) (w q)) (v q))
      ∂Measure.pi (fun _ => volume)) = 1
    rw [integral_fintype_prod_eq_prod]
    apply Finset.prod_eq_one
    intro q _
    exact (pivotOutputDensity_integral (A q) (V q) (hp q).1).trans (hp q).2.2

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem jointAffineJetDensity_measurable_comp {Ω Q Z X K α : Type*}
    [MeasurableSpace Ω] [Fintype Q] [Fintype α] [DecidableEq α] {I J N : Q → Type*}
    [∀ q, Fintype (I q)] [∀ q, Fintype (J q)] [∀ q, Fintype (N q)]
    (s : ∀ q, I q ↪ J q) (A : ∀ q, (I q → ℝ) ≃L[ℝ] (I q → ℝ))
    (F : ∀ q, (UnselectedColumn (s q) → ℝ) →L[ℝ] (I q → ℝ))
    (e : ∀ q, N q → K →₀ ℕ) (input : K → Option α → Z ⊕ X)
    (rows : ∀ q, I q → Finset α) (c w : ∀ q, J q ⊕ N q → ℝ)
    (hw : ∀ q j, 0 < w q j) (R : Q → ℝ≥0) (hsupport : ∀ q j, |c q j|+w q j ≤ R q)
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun ω => z ω j))
    (x : Ω → X → ℝ) (hx : ∀ j, Measurable (fun ω => x ω j))
    (v : Ω → ∀ q, I q → ℝ) (hv : ∀ q i, Measurable (fun ω => v ω q i)) :
    Measurable (fun ω => jointAffineJetDensity s A F e input (z ω) rows c w (x ω) (v ω)) := by
  have hm (q) : Measurable (fun ω =>
      affineSelectedJetDensity (s q) (A q) (F q) (e q) input (z ω) (rows q) (c q) (w q) (x ω) (v ω q)) :=
    normalizedJetDensity_measurable_comp (Ω := Ω) (A q) (F q) (e q) input (rows q)
      ((affineProductProfile_contDiff _ _).continuous.comp (selectedCoefficientEquiv_lipschitz (s q)).continuous)
      (affineProductProfile_contDiff _ _).continuous
      (selectedCoefficientProfile_zero_outside (s q)
        (affineProductProfile_zero_outside _ _ (fun j => hw q (.inl j)) (R q).coe_nonneg
          (fun j => hsupport q (.inl j))))
      (affineProductProfile_zero_outside _ _ (fun n => hw q (.inr n)) (R q).coe_nonneg
        (fun n => hsupport q (.inr n)))
      z hz x hx (fun ω => v ω q) (hv q)
  unfold jointAffineJetDensity
  exact Finset.measurable_prod Finset.univ (fun q _ => hm q)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem affineSelectedJetDensity_probability_data {Z P K α I J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (s : I ↪ J) (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (F : (UnselectedColumn s → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (rows : I → Finset α)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) (R : ℝ≥0) (hsupport : ∀ j, |c j| + w j ≤ R)
    (x : P → ℝ) :
    (∀ v, 0 ≤ affineSelectedJetDensity s A F e input z rows c w x v) ∧
      Integrable (affineSelectedJetDensity s A F e input z rows c w x) ∧
      (∫ v, affineSelectedJetDensity s A F e input z rows c w x v) = 1 := by
  have hp := affineSelectedJetProfile_probability_data s c w hw R hsupport
  exact ⟨pivotOutputDensity_nonneg _ _ hp.2.1, pivotOutputDensity_integrable _ _ hp.1,
    (pivotOutputDensity_integral _ _ hp.1).trans hp.2.2⟩

theorem jointAffineJetDensity_l1_regular {Q Z P K α : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype P] [DecidableEq P] [Fintype α] [DecidableEq α] {I J N : Q → Type*}
    [∀ q, Fintype (I q)] [∀ q, Fintype (J q)] [∀ q, Fintype (N q)]
    (s : ∀ q, I q ↪ J q) (A : ∀ q, (I q → ℝ) ≃L[ℝ] (I q → ℝ))
    (F : ∀ q, (UnselectedColumn (s q) → ℝ) →L[ℝ] (I q → ℝ))
    (e : ∀ q, N q → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1)
    (rows : ∀ q, I q → Finset α) (degree : Q → ℕ) (hd : ∀ q n, (e q n).sum (fun _ k => k) ≤ degree q)
    (c w : ∀ q, J q ⊕ N q → ℝ) (hw : ∀ q j, 0 < w q j) (δ R : Q → ℝ≥0)
    (hδ : ∀ q, 0 < δ q) (hwidth : ∀ q j, (δ q : ℝ) ≤ w q (.inl j))
    (hsupport : ∀ q j, |c q j| + w q j ≤ R q)
    (a : P → ℝ) (ha : a ∈ Metric.closedBall 0 1) (b : P → ℝ) (hb : b ∈ Metric.closedBall 0 1) :
    (∫ v, |jointAffineJetDensity s A F e input z rows c w a v -
      jointAffineJetDensity s A F e input z rows c w b v| ∂Measure.pi (fun _ => volume)) ≤
      ((∑ q, affineJetL1Cost P α (J q) (N q) (A q) (degree q) (δ q) (R q) : ℝ≥0) : ℝ) * dist a b := by
  have hp (q) (x : P → ℝ) := affineSelectedJetDensity_probability_data (s q) (A q) (F q)
    (e q) input z (rows q) (c q) (w q) (hw q) (R q) (hsupport q) x
  have he := tensor_density_l1_le_sum (fun q => (volume : Measure (I q → ℝ)))
    (fun q => affineSelectedJetDensity (s q) (A q) (F q) (e q) input z (rows q) (c q) (w q) a)
    (fun q => affineSelectedJetDensity (s q) (A q) (F q) (e q) input z (rows q) (c q) (w q) b)
    (fun q => (hp q a).2.1) (fun q => (hp q b).2.1) (fun q => (hp q a).1) (fun q => (hp q b).1)
    (fun q => (hp q a).2.2) (fun q => (hp q b).2.2)
  apply he.trans
  rw [NNReal.coe_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro q _
  exact affineSelectedJetDensity_l1_regular (s q) (A q) (F q) (e q) input z hz (rows q)
    (hd q) (c q) (w q) (hw q) (hδ q) (hwidth q) (R q) (hsupport q) a ha b hb

end Erdos3

end

end OAI
