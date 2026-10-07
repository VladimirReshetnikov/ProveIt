/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Geometry.PartitionedIdealSupport
import OAI.Combinatorics.Progressions.Lattices.RegularizedAffineComparison
import OAI.Combinatorics.Progressions.Probability.CoefficientDensityAverage

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {S R T U : Type*} [Fintype S] [Fintype R] [Fintype T]

noncomputable def maskedSiteFactor (label : S → U → R) (r : S → R)
    (f : T → S → U → ℂ) (k : T) (s : S) (u : U) : ℂ :=
  if label s u = r s then f k s u else 0

omit [Fintype R] [Fintype T] in
theorem maskedSiteFactor_prod (label : S → U → R) (r : S → R)
    (f : T → S → U → ℂ) (k : T) (u : S → U) :
    (∏ s, maskedSiteFactor label r f k s (u s)) =
      if (fun s => label s (u s)) = r then ∏ s, f k s (u s) else 0 := by
  by_cases hr : (fun s => label s (u s)) = r
  · have hs (s : S) : label s (u s) = r s := congrFun hr s
    simp only [ite_true, maskedSiteFactor, hs]
  · simp only [hr, ite_false]
    obtain ⟨s, hs⟩ : ∃ s, label s (u s) ≠ r s := by
      by_contra hn
      apply hr
      funext s
      by_contra hs
      exact hn ⟨s, hs⟩
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp only [maskedSiteFactor, hs, ite_false])

theorem maskedSiteExpansion_identity [DecidableEq S] (label : S → U → R) (mask : (S → R) → ℂ)
    (c : T → ℂ) (f : T → S → U → ℂ) (u : S → U) :
    (∑ r : S → R, ∑ k, (mask r*c k)*∏ s, maskedSiteFactor label r f k s (u s)) =
      mask (fun s => label s (u s))*(∑ k, c k*∏ s, f k s (u s)) := by
  simp_rw [maskedSiteFactor_prod]
  rw [Finset.sum_eq_single (fun s => label s (u s))]
  · simp only [ite_true, Finset.mul_sum, mul_assoc]
  · intro r _ hr
    simp only [Ne.symm hr, ite_false, mul_zero, Finset.sum_const_zero]
  · simp

omit [Fintype S] [Fintype R] [Fintype T] in
theorem maskedSiteFactor_bound (label : S → U → R) (r : S → R)
    (f : T → S → U → ℂ) (hf : ∀ k s u, ‖f k s u‖ ≤ 1) (k : T) (s : S) (u : U) :
    ‖maskedSiteFactor label r f k s u‖ ≤ 1 := by
  unfold maskedSiteFactor
  split_ifs
  · exact hf k s u
  · simp

theorem maskedSiteExpansion_coefficient_sum [DecidableEq S] (mask : (S → R) → ℂ) (c : T → ℂ)
    {G A : ℝ} (hG : 0 ≤ G) (hm : ∀ r, ‖mask r‖ ≤ G) (hc : (∑ k, ‖c k‖) ≤ A) :
    (∑ r : S → R, ∑ k, ‖mask r*c k‖) ≤ (Fintype.card R : ℝ)^Fintype.card S*G*A := by
  simp_rw [norm_mul]
  calc
    _ ≤ ∑ _r : S → R, G*A := by
      apply Finset.sum_le_sum
      intro r _
      rw [← Finset.mul_sum]
      exact mul_le_mul (hm r) hc (Finset.sum_nonneg (fun k _ => norm_nonneg _)) hG
    _ = _ := by simp [mul_assoc]

theorem maskedSiteExpansion_error [DecidableEq S] (label : S → U → R) (mask : (S → R) → ℂ)
    (F : (S → U) → ℂ) (c : T → ℂ) (f : T → S → U → ℂ)
    {G ε : ℝ} (hG : 0 ≤ G) (hm : ∀ r, ‖mask r‖ ≤ G)
    (he : ∀ u, ‖F u-∑ k, c k*∏ s, f k s (u s)‖ ≤ ε) (u : S → U) :
    ‖mask (fun s => label s (u s))*F u-
      ∑ r : S → R, ∑ k, (mask r*c k)*∏ s, maskedSiteFactor label r f k s (u s)‖ ≤ G*ε := by
  rw [maskedSiteExpansion_identity, ← mul_sub, norm_mul]
  exact mul_le_mul (hm _) (he u) (norm_nonneg _) hG

theorem maskedSiteExpansion_coefficient_le_exp [DecidableEq S] (mask : (S → R) → ℂ) (c : T → ℂ)
    {P Q A : ℝ} (hR : (Fintype.card R : ℝ) ≤ Real.exp P)
    (hm : ∀ r, ‖mask r‖ ≤ Real.exp Q) (hc : (∑ k, ‖c k‖) ≤ Real.exp A) :
    (∑ r : S → R, ∑ k, ‖mask r*c k‖) ≤ Real.exp (Fintype.card S*P+Q+A) := by
  apply (maskedSiteExpansion_coefficient_sum mask c (Real.exp_nonneg Q) hm hc).trans
  calc
    _ ≤ (Real.exp P)^Fintype.card S*Real.exp Q*Real.exp A := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]

theorem maskedSiteIndex_card [DecidableEq S] :
    Fintype.card ((S → R) × T) = Fintype.card R^Fintype.card S*Fintype.card T := by simp

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem unitCoefficientSource_abs_le (I : Type*) [Fintype I] :
    ∀ᵐ r ∂unitCoefficientSource I, ∀ i, |r i| ≤ 1 := by
  filter_upwards [unitCoefficientSource_norm_le I] with r hr i
  exact (Real.norm_eq_abs (r i)).symm.trans_le ((norm_le_pi_norm r i).trans hr)

theorem jointUnitCoefficientSource_abs_le {D : Type*} [Fintype D]
    (J N : D → Type*) [∀ d, Fintype (J d)] [∀ d, Fintype (N d)] :
    ∀ᵐ r ∂jointUnitCoefficientSource J N, ∀ d j, |r d j| ≤ 1 := by
  apply (ae_all_iff).mpr
  intro d
  exact (measurePreserving_eval (fun d => unitCoefficientSource (J d ⊕ N d)) d).quasiMeasurePreserving.ae
    (unitCoefficientSource_abs_le (J d ⊕ N d))

theorem affineAuxiliaryVariables_joint_unit_bound {D Z : Type*} [Fintype D]
    (J N : D → Type*) [∀ d, Fintype (J d)] [∀ d, Fintype (N d)]
    (c w : ∀ d, J d ⊕ N d → ℝ) (z : Z → ℝ) (hz : ∀ a, |z a| ≤ 1) :
    ∀ᵐ r ∂jointUnitCoefficientSource J N, ∀ a, |affineAuxiliaryVariables c w z r a| ≤ 1 := by
  filter_upwards [jointUnitCoefficientSource_abs_le J N] with r hr
  exact affineAuxiliaryVariables_abs_le c w z r hz hr

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def averagedRegularizedIdeal {D G α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    {B O J N : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    [∀ d, Fintype (J d)] [∀ d, Fintype (N d)]
    (h : D → ℕ) (e : ∀ d, J d ⊕ N d → SamplerTupleIndex G B h →₀ ℕ)
    (index : ∀ d, B d → J d ⊕ N d) (c w : ∀ d, J d ⊕ N d → ℝ)
    (sets : ∀ d, O d → Finset α) (δ : ℝ≥0) : ((Σ d, O d) → ℝ) → ℝ :=
  densityMixture (jointUnitCoefficientSource J N) (regularizedAffineIdealDensity h e index c w sets δ)

theorem regularizedAffineIdealDensity_joint_measurable {D G α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    {B O J N : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    [∀ d, Fintype (J d)] [∀ d, Fintype (N d)]
    (h : D → ℕ) (e : ∀ d, J d ⊕ N d → SamplerTupleIndex G B h →₀ ℕ)
    (index : ∀ d, B d → J d ⊕ N d) (c w : ∀ d, J d ⊕ N d → ℝ)
    (sets : ∀ d, O d → Finset α) (δ : ℝ≥0) :
    Measurable (Function.uncurry (regularizedAffineIdealDensity h e index c w sets δ)) :=
  regularizedAffineIdealDensity_measurable_comp
    (Ω := (∀ d, J d ⊕ N d → ℝ) × ((Σ d, O d) → ℝ)) h e index c w sets δ (fun p => p.1)
    (fun d j => (measurable_pi_apply j).comp ((measurable_pi_apply d).comp measurable_fst))
    (fun p => p.2) measurable_snd

theorem averagedRegularizedIdeal_measurable {D G α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    {B O J N : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    [∀ d, Fintype (J d)] [∀ d, Fintype (N d)]
    (h : D → ℕ) (e : ∀ d, J d ⊕ N d → SamplerTupleIndex G B h →₀ ℕ)
    (index : ∀ d, B d → J d ⊕ N d) (c w : ∀ d, J d ⊕ N d → ℝ)
    (sets : ∀ d, O d → Finset α) (δ : ℝ≥0) :
    Measurable (averagedRegularizedIdeal h e index c w sets δ) :=
  (regularizedAffineIdealDensity_joint_measurable h e index c w sets δ).stronglyMeasurable.integral_prod_left'.measurable

theorem averagedRegularizedIdeal_spec {D G α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    {B O J N : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    [∀ d, Fintype (J d)] [∀ d, Fintype (N d)]
    (h : D → ℕ) (e : ∀ d, J d ⊕ N d → SamplerTupleIndex G B h →₀ ℕ)
    (index : ∀ d, B d → J d ⊕ N d) (c w : ∀ d, J d ⊕ N d → ℝ)
    (sets : ∀ d, O d → Finset α) (δ : ℝ≥0) (hδ : 0 < δ) :
    (∀ x, averagedRegularizedIdeal h e index c w sets δ x ∈
      Set.Icc (0 : ℝ) (δ⁻¹ ^ Fintype.card (Σ d, O d) : ℝ≥0)) ∧
      LipschitzWith (affineProductProfileLip (Σ d, O d) δ) (averagedRegularizedIdeal h e index c w sets δ) ∧
      Integrable (averagedRegularizedIdeal h e index c w sets δ) ∧
      (∫ x, averagedRegularizedIdeal h e index c w sets δ x) = 1 := by
  have hm := regularizedAffineIdealDensity_joint_measurable h e index c w sets δ
  have hb := densityMixture_uniform_bound (jointUnitCoefficientSource J N) _
    (δ⁻¹ ^ Fintype.card (Σ d, O d)) (affineProductProfileLip (Σ d, O d) δ)
    (fun x => (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun r => regularizedAffineIdealDensity_bounds h e index c w sets δ hδ r))
  have hp := densityMixture_probability_density (jointUnitCoefficientSource J N) volume _ hm
    (Filter.Eventually.of_forall (fun r => regularizedAffineIdealDensity_probability h e index c w sets δ hδ r))
  exact ⟨hb.1, hb.2, hp.2.1, hp.2.2⟩

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def idealSiteLogBudget (m q : ℕ) (P : ℝ) : ℝ :=
  q+(m : ℝ)*P+affineProfileLogBound m P+P+1

theorem idealSiteLogBudget_bounds (m q : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ idealSiteLogBudget m q P ∧ P ≤ idealSiteLogBudget m q P ∧
    (m : ℝ)*P ≤ idealSiteLogBudget m q P ∧
    affineProfileLogBound m P+q ≤ idealSiteLogBudget m q P := by
  have hf := affineProfileLogBound_nonneg m hP
  have hm : 0 ≤ (m : ℝ)*P := by positivity
  unfold idealSiteLogBudget
  constructor
  · positivity
  constructor
  · linarith [Nat.cast_nonneg (α := ℝ) q]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) q]

theorem idealSiteProfile_bounds (I : Type*) [Fintype I] (q : ℕ)
    (η : ℝ≥0) (hη : 0 < η) {P : ℝ} (hP : 0 ≤ P) (hηP : (η : ℝ)⁻¹ ≤ Real.exp P) :
    ((η⁻¹^Fintype.card I : ℝ≥0) : ℝ) ≤ Real.exp (idealSiteLogBudget (Fintype.card I) q P) ∧
    ((affineProductProfileLip I η*(2 : ℝ≥0)^q : ℝ≥0) : ℝ) ≤
      Real.exp (idealSiteLogBudget (Fintype.card I) q P) := by
  have hb := idealSiteLogBudget_bounds (Fintype.card I) q hP
  constructor
  · apply le_trans _ (Real.exp_le_exp.mpr hb.2.2.1)
    simpa only [NNReal.coe_pow, NNReal.coe_inv] using
      profileWidthPower_le_exp (Fintype.card I) (show (0 : ℝ) < η from hη) hηP
  · have hp := affineProductProfileLip_le_exp I hηP
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hq : (2 : ℝ)^q ≤ Real.exp q := by
      calc
        _ ≤ (Real.exp 1)^q := by gcongr
        _ = _ := by rw [← Real.exp_nat_mul]; simp
    apply le_trans _ (Real.exp_le_exp.mpr hb.2.2.2)
    simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat]
    calc
      _ ≤ Real.exp (affineProfileLogBound (Fintype.card I) P)*Real.exp q := by gcongr
      _ = _ := (Real.exp_add _ _).symm

section Ideal

variable {D G α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O J N : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, Fintype (J d)] [∀ d, Fintype (N d)]
  (h : D → ℕ) (e : ∀ d, J d ⊕ N d → SamplerTupleIndex G B h →₀ ℕ)
  (index : ∀ d, B d → J d ⊕ N d) (c w : ∀ d, J d ⊕ N d → ℝ)
  (sets : ∀ d, O d → Finset α)

noncomputable def averagedIdealSiteFunction (η : ℝ≥0) (x : Finset α → D → ℝ) : ℂ :=
  averagedRegularizedIdeal h e index c w sets η (booleanSiteJets sets x)

theorem averagedIdealSiteFunction_bound (η : ℝ≥0) (hη : 0 < η) (x : Finset α → D → ℝ) :
    ‖averagedIdealSiteFunction h e index c w sets η x‖ ≤ (η⁻¹^Fintype.card (Σ d, O d) : ℝ≥0) := by
  have hx := (averagedRegularizedIdeal_spec h e index c w sets η hη).1 (booleanSiteJets sets x)
  simpa only [averagedIdealSiteFunction, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2

theorem averagedIdealSiteFunction_lipschitz (η : ℝ≥0) (hη : 0 < η) :
    LipschitzWith (affineProductProfileLip (Σ d, O d) η*(2 : ℝ≥0)^Fintype.card α)
      (averagedIdealSiteFunction h e index c w sets η) := by
  unfold averagedIdealSiteFunction
  have hi := (averagedRegularizedIdeal_spec h e index c w sets η hη).2.1
  simpa only [one_mul, Function.comp_def] using
    Complex.isometry_ofReal.lipschitzWith.comp (hi.comp (booleanSiteJets_lipschitz sets))

end Ideal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem exists_averaged_ideal_site_approximation
    {D G α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
    {B O J N : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    [∀ d, Fintype (J d)] [∀ d, Fintype (N d)]
    (h : D → ℕ) (e : ∀ d, J d ⊕ N d → SamplerTupleIndex G B h →₀ ℕ)
    (index : ∀ d, B d → J d ⊕ N d) (c w : ∀ d, J d ⊕ N d → ℝ)
    (sets : ∀ d, O d → Finset α) (η : ℝ≥0) (hη : 0 < η)
    {R ε P : ℝ} (hR : 0 < R) (hε : 0 < ε) (hP : 0 ≤ P)
    (hRP : R ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) (hηP : (η : ℝ)⁻¹ ≤ Real.exp P) :
    let Q := idealSiteLogBudget (Fintype.card (Σ d, O d)) (Fintype.card α) P
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4*Q+8) ∧
      ∃ (a : (Finset α × D → Fin n) → ℂ)
        (f : (Finset α × D → Fin n) → Finset α → (D → ℝ) → ℂ),
        (∑ k, ‖a k‖) ≤ Real.exp ((Fintype.card (Finset α)*Fintype.card D : ℕ)*(4*Q+8)+Q) ∧
        (∀ k s x, ‖f k s x‖ ≤ 1) ∧
        (∀ k s, LipschitzWith ⟨Real.exp (Fintype.card D+6*Q+12), Real.exp_nonneg _⟩ (f k s)) ∧
        ∀ x : Finset α → D → ℝ, (∀ s d, |x s d| ≤ R) →
          ‖(averagedRegularizedIdeal h e index c w sets η (booleanSiteJets sets x) : ℂ)-
            ∑ k, a k*∏ s, f k s (x s)‖ ≤ ε := by
  have hb := idealSiteLogBudget_bounds (Fintype.card (Σ d, O d)) (Fintype.card α) hP
  have hp := idealSiteProfile_bounds (Σ d, O d) (Fintype.card α) η hη hP hηP
  have happrox := exists_grouped_site_approximation (S := Finset α) (D := D)
    (averagedIdealSiteFunction h e index c w sets η)
    (η⁻¹^Fintype.card (Σ d, O d))
    (affineProductProfileLip (Σ d, O d) η*(2 : ℝ≥0)^Fintype.card α)
    (averagedIdealSiteFunction_bound h e index c w sets η hη)
    (averagedIdealSiteFunction_lipschitz h e index c w sets η hη)
    (B := R) (ε := ε)
    (P := idealSiteLogBudget (Fintype.card (Σ d, O d)) (Fintype.card α) P)
    hR hε hb.1 (hRP.trans (Real.exp_le_exp.mpr hb.2.1)) hp.1 hp.2
    (hεP.trans (Real.exp_le_exp.mpr hb.2.1))
  dsimp only
  obtain ⟨n, hn, a, f, ha, hf, hLip, herr⟩ := happrox
  refine ⟨n, hn, a, f, ha, hf, hLip, ?_⟩
  intro x hx
  exact herr x hx

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem exists_buffered_ideal_site_approximation
    {D G α U : Type*} [Fintype D] [Fintype α] [DecidableEq α] [PseudoMetricSpace U]
    {B O J N : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    [∀ d, Fintype (J d)] [∀ d, Fintype (N d)]
    (h : D → ℕ) (e : ∀ d, J d ⊕ N d → SamplerTupleIndex G B h →₀ ℕ)
    (index : ∀ d, B d → J d ⊕ N d) (c w : ∀ d, J d ⊕ N d → ℝ)
    (sets : ∀ d, O d → Finset α) (η : ℝ≥0) (hη : 0 < η)
    {R ε P : ℝ} (hR : 0 < R) (hε : 0 < ε) (hP : 0 ≤ P)
    (hRP : R ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) (hηP : (η : ℝ)⁻¹ ≤ Real.exp P)
    (y : Finset α → U → D → ℝ) (χ : Finset α → U → ℂ) {L C : ℝ≥0}
    (hy : ∀ s, LipschitzWith L (y s)) (hχ : ∀ s, LipschitzWith C (χ s))
    (hχ1 : ∀ s u, ‖χ s u‖ ≤ 1) (hsupport : ∀ s u, χ s u ≠ 0 → ∀ d, |y s u d| ≤ R) :
    let Q := idealSiteLogBudget (Fintype.card (Σ d, O d)) (Fintype.card α) P
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4*Q+8) ∧
      ∃ (a : (Finset α × D → Fin n) → ℂ) (f : (Finset α × D → Fin n) → Finset α → U → ℂ),
        (∑ k, ‖a k‖) ≤ Real.exp ((Fintype.card (Finset α)*Fintype.card D : ℕ)*(4*Q+8)+Q) ∧
        (∀ k s u, ‖f k s u‖ ≤ 1) ∧
        (∀ k s, LipschitzWith (⟨Real.exp (Fintype.card D+6*Q+12), Real.exp_nonneg _⟩*L+C) (f k s)) ∧
        ∀ u : Finset α → U,
          ‖(∏ s, χ s (u s))*(averagedRegularizedIdeal h e index c w sets η
              (booleanSiteJets sets (fun s => y s (u s))) : ℂ)-
            ∑ k, a k*∏ s, f k s (u s)‖ ≤ ε := by
  obtain ⟨n, hn, a, f, ha, hf, hLip, herr⟩ :=
    exists_averaged_ideal_site_approximation h e index c w sets η hη hR hε hP hRP hεP hηP
  dsimp only
  refine ⟨n, hn, a, bufferedSiteFactor y χ f, ha, ?_, ?_, ?_⟩
  · exact bufferedSiteFactor_bound y χ f hχ1 hf
  · exact bufferedSiteFactor_lipschitz y χ f hy hχ hLip hχ1 hf
  · intro u
    exact bufferedSiteExpansion_error y χ (averagedIdealSiteFunction h e index c w sets η)
      a f hε.le hχ1 hsupport herr u

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem exists_masked_ideal_site_approximation
    {D G α U R₀ : Type*} [Fintype D] [Fintype α] [DecidableEq α]
    [PseudoMetricSpace U] [Fintype R₀]
    {B O J N : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    [∀ d, Fintype (J d)] [∀ d, Fintype (N d)]
    (h : D → ℕ) (e : ∀ d, J d ⊕ N d → SamplerTupleIndex G B h →₀ ℕ)
    (index : ∀ d, B d → J d ⊕ N d) (c w : ∀ d, J d ⊕ N d → ℝ)
    (sets : ∀ d, O d → Finset α) (η : ℝ≥0) (hη : 0 < η)
    {R ε P Z : ℝ} (hR : 0 < R) (hε : 0 < ε) (hP : 0 ≤ P)
    (hRP : R ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) (hηP : (η : ℝ)⁻¹ ≤ Real.exp P)
    (y : Finset α → U → D → ℝ) (χ : Finset α → U → ℂ) {L C : ℝ≥0}
    (hy : ∀ s, LipschitzWith L (y s)) (hχ : ∀ s, LipschitzWith C (χ s))
    (hχ1 : ∀ s u, ‖χ s u‖ ≤ 1) (hsupport : ∀ s u, χ s u ≠ 0 → ∀ d, |y s u d| ≤ R)
    (label : Finset α → U → R₀) (mask : (Finset α → R₀) → ℂ)
    (hresidue : (Fintype.card R₀ : ℝ) ≤ Real.exp Z) (hmask : ∀ r, ‖mask r‖ ≤ Real.exp Z) :
    let Q := idealSiteLogBudget (Fintype.card (Σ d, O d)) (Fintype.card α) P
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4*Q+8) ∧
      ∃ (a : (Finset α × D → Fin n) → ℂ) (f : (Finset α × D → Fin n) → Finset α → U → ℂ),
        (∑ r : Finset α → R₀, ∑ k, ‖mask r*a k‖) ≤
          Real.exp (Fintype.card (Finset α)*Z+Z+
            ((Fintype.card (Finset α)*Fintype.card D : ℕ)*(4*Q+8)+Q)) ∧
        (∀ k s u, ‖f k s u‖ ≤ 1) ∧
        (∀ k s, LipschitzWith (⟨Real.exp (Fintype.card D+6*Q+12), Real.exp_nonneg _⟩*L+C) (f k s)) ∧
        ∀ u : Finset α → U,
          ‖mask (fun s => label s (u s))*((∏ s, χ s (u s))*
              (averagedRegularizedIdeal h e index c w sets η
                (booleanSiteJets sets (fun s => y s (u s))) : ℂ))-
            ∑ r : Finset α → R₀, ∑ k, (mask r*a k)*∏ s, maskedSiteFactor label r f k s (u s)‖ ≤
              Real.exp Z*ε := by
  obtain ⟨n, hn, a, f, ha, hf, hLip, herr⟩ :=
    exists_buffered_ideal_site_approximation h e index c w sets η hη hR hε hP hRP hεP hηP
      y χ hy hχ hχ1 hsupport
  dsimp only
  refine ⟨n, hn, a, f, ?_, hf, hLip, ?_⟩
  · exact maskedSiteExpansion_coefficient_le_exp mask a hresidue hmask ha
  · intro u
    exact maskedSiteExpansion_error label mask
      (fun u => (∏ s, χ s (u s))*(averagedIdealSiteFunction h e index c w sets η (fun s => y s (u s))))
      a f (Real.exp_nonneg Z) hmask herr u

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {D G α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
  (Z : Type*) [Fintype Z] {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
  (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α)

noncomputable def activeProfileIdeal (δ : ℝ≥0)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ) : ((Σ d, O d) → ℝ) → ℝ :=
  partitionedRegularizedIdeal h P sets δ (profileNoiseWithActive (Z := Z) h P (fun _ => 0) r)

omit [Fintype G] [Fintype Z] in
theorem activeProfileIdeal_measurable (δ : ℝ≥0) :
    Measurable (Function.uncurry (activeProfileIdeal (G := G) (B := B) Z h P sets δ)) := by
  apply partitionedRegularizedIdeal_measurable h P sets δ
  intro j
  exact profileNoiseWithActive_measurable h P (fun _ _ => 0) id
    (fun _ => measurable_const) (fun i => measurable_pi_apply i) j

noncomputable def activeAveragedProfileIdeal (δ : ℝ≥0) : ((Σ d, O d) → ℝ) → ℝ :=
  densityMixture (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P))
    (activeProfileIdeal Z h P sets δ)

omit [Fintype Z] in
theorem activeAveragedProfileIdeal_measurable (δ : ℝ≥0) :
    Measurable (activeAveragedProfileIdeal (G := G) (B := B) Z h P sets δ) :=
  (activeProfileIdeal_measurable (G := G) (B := B) Z h P sets δ).stronglyMeasurable.integral_prod_left'.measurable

omit [Fintype Z] in
theorem activeAveragedProfileIdeal_spec (δ : ℝ≥0) (hδ : 0 < δ) :
    (∀ v, activeAveragedProfileIdeal (G := G) (B := B) Z h P sets δ v ∈
      Set.Icc (0 : ℝ) (δ⁻¹ ^ Fintype.card (Σ d, O d) : ℝ≥0)) ∧
    LipschitzWith (affineProductProfileLip (Σ d, O d) δ)
      (activeAveragedProfileIdeal (G := G) (B := B) Z h P sets δ) ∧
    Integrable (activeAveragedProfileIdeal (G := G) (B := B) Z h P sets δ) ∧
    (∫ v, activeAveragedProfileIdeal (G := G) (B := B) Z h P sets δ v) = 1 := by
  have hm := activeProfileIdeal_measurable (G := G) (B := B) Z h P sets δ
  have hb := densityMixture_uniform_bound (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P))
    (activeProfileIdeal Z h P sets δ) (δ⁻¹ ^ Fintype.card (Σ d, O d))
    (affineProductProfileLip (Σ d, O d) δ)
    (fun v => (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun r => partitionedRegularizedIdeal_bounds h P sets δ hδ
      (profileNoiseWithActive (Z := Z) h P (fun _ => 0) r)))
  have hp := densityMixture_probability_density
    (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P)) volume
    (activeProfileIdeal Z h P sets δ) hm
    (Filter.Eventually.of_forall (fun r => partitionedRegularizedIdeal_probability h P sets δ hδ
      (profileNoiseWithActive (Z := Z) h P (fun _ => 0) r)))
  exact ⟨hb.1, hb.2, hp.2.1, hp.2.2⟩

theorem activeAveragedProfileIdeal_zero_outside {degree : ℕ}
    (hdegree : ∀ d, h d ≤ degree) (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (v : (Σ d, O d) → ℝ) (hv : partitionedIdealRadius α degree + 1 < ‖v‖) :
    activeAveragedProfileIdeal (G := G) (B := B) Z h P sets δ v = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [unitCoefficientSource_abs_le (ActiveProfileCoefficientIndex G B h P)] with r hr
  exact partitionedRegularizedIdeal_zero_outside h P sets hdegree δ hδ hδ1
    (profileNoiseWithActive (Z := Z) h P (fun _ => 0) r)
    (profileNoiseWithActive_abs_le h P (fun _ => 0) r (fun _ => by simp) hr) v hv

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal

noncomputable def activeProfileSample {W D G Z α : Type*}
    [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
    (P : D → Prop) [DecidablePred P] (extra : G → Option α → Z)
    {O : {d // ¬P d} → Type*} (sets : ∀ d, O d → Finset α) (R : D → ℝ) (s : ℝ)
    (z : W → PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (p : (W × (ActiveProfileCoefficientIndex G B h P → ℝ)) ×
      (PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)) :
    W × ((Σ d, O d) → ℝ) :=
  (p.1.1, partitionedAllocatedProfileJet h P extra sets R s
    (profileNoiseWithActive h P (z p.1.1) p.1.2) p.2)

theorem exists_active_averaged_profile_comparison
    {W D G Z α : Type*} [MeasurableSpace W]
    [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B) (O := O) (α := α) h
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T (ε / 2) ∧
      let t := booleanMassPerturbationScale (B := B) (O := O) (α := α)
        (Z ⊕ (Σ d, SamplerCoefficientSlot G B h d)) h
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T degree 1 (ε / 2)
      0 < t ∧ t ≤ 1 ∧
      ∀ (P : D → Prop) [DecidablePred P],
      ∀ (extra : G → Option α → Z) (sets : ∀ d : {d // ¬P d}, O d.val → Finset α),
      (∀ d, Function.Injective (sets d)) → (∀ d o, (sets d o).card ≤ h d.val) →
      ∀ block : ∀ d : {d // ¬P d}, O d.val → B d.val,
      (∀ d, Function.Injective (block d)) →
      ∀ z : W → PartitionedProfileNoiseIndex G Z α B h P → ℝ,
      (∀ j, Measurable (fun a => z a j)) →
      ∀ s : ℝ, |s| ≤ t → ∀ μ : Measure W, IsProbabilityMeasure μ →
      (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
      ∀ R : D → ℝ, ∀ f : W × ((Σ d : {d // ¬P d}, O d.val) → ℝ) → ℝ,
      Measurable f → (∀ p, ‖f p‖ ≤ 1) →
      |(∫ p, activeAveragedProfileIdeal (G := G) (B := B) Z h P sets δ p.2 *
          f (p.1, fun o => R o.1.val * p.2 o) ∂μ.prod volume) -
        ∫ p, f (activeProfileSample h P extra sets R s z p)
          ∂(μ.prod (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P))).prod
            (jointBooleanSource (fun d : {d // ¬P d} => h d.val))| ≤ ε := by
  classical
  obtain ⟨δ, hδ, hδ1, hδeq, ht, ht1, _⟩ := exists_uniform_regularized_profile_comparison
    (Ω := W) (G := G) (Z := Z) (B := B) (O := O) (α := α)
    h hh ψ hψ hrange hzero hone A T hLip hTransition hdegree hε
  refine ⟨δ, hδ, hδ1, hδeq, ht, ht1, ?_⟩
  intro P instP extra sets hsets hcard block hblock z hz s hs μ hμ hbox R f hf hfb
  let : IsProbabilityMeasure μ := hμ
  obtain ⟨δ', _, _, hδ'eq, _, _, hcomp⟩ := exists_uniform_regularized_profile_comparison
    (Ω := W × (ActiveProfileCoefficientIndex G B h P → ℝ))
    (G := G) (Z := Z) (B := B) (O := O) (α := α)
    h hh ψ hψ hrange hzero hone A T hLip hTransition hdegree hε
  have hsame : δ' = δ := NNReal.coe_injective (hδ'eq.trans hδeq.symm)
  subst δ'
  let ζ := fun p : W × (ActiveProfileCoefficientIndex G B h P → ℝ) =>
    profileNoiseWithActive h P (z p.1) p.2
  have hζ (j : PartitionedProfileNoiseIndex G Z α B h P) : Measurable (fun p => ζ p j) :=
    profileNoiseWithActive_measurable h P
      (fun p : W × (ActiveProfileCoefficientIndex G B h P → ℝ) => z p.1) Prod.snd
      (fun i => (hz i).comp measurable_fst)
      (fun i => (measurable_pi_apply i).comp measurable_snd) j
  have hζbox : ∀ᵐ p ∂μ.prod (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P)),
      ∀ j, |ζ p j| ≤ 1 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hbox,
      Measure.quasiMeasurePreserving_snd.ae
        (unitCoefficientSource_abs_le (ActiveProfileCoefficientIndex G B h P))] with p hp hr
    exact profileNoiseWithActive_abs_le h P (z p.1) p.2 hp hr
  let f' := fun p : (W × (ActiveProfileCoefficientIndex G B h P → ℝ)) ×
      ((Σ d : {d // ¬P d}, O d.val) → ℝ) => f (p.1.1, p.2)
  have hf' : Measurable f' := hf.comp (measurable_fst.fst.prodMk measurable_snd)
  have he := hcomp P extra sets hsets hcard block hblock ζ hζ s hs
    (μ.prod (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P))) inferInstance
    hζbox R f' hf' (fun p => hfb (p.1.1, p.2))
  simp only [ζ, partitionedRegularizedIdeal_withActive_eq] at he
  let Φ := fun p : W × ((Σ d : {d // ¬P d}, O d.val) → ℝ) =>
    f (p.1, fun o => R o.1.val * p.2 o)
  have hΦ : Measurable Φ := by
    apply hf.comp
    apply measurable_fst.prodMk
    apply Measurable.of_eval
    intro o
    exact measurable_const.mul ((measurable_pi_apply o).comp measurable_snd)
  have havg := retained_coefficient_density_average μ
    (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P)) volume
    (activeProfileIdeal Z h P sets δ) (activeProfileIdeal_measurable Z h P sets δ)
    (fun r => partitionedRegularizedIdeal_probability h P sets δ hδ
      (profileNoiseWithActive (Z := Z) h P (fun _ => 0) r)) Φ hΦ
    (fun p => hfb (p.1, fun o => R o.1.val * p.2 o))
  change |(∫ p : (W × (ActiveProfileCoefficientIndex G B h P → ℝ)) ×
      ((Σ d : {d // ¬P d}, O d.val) → ℝ),
      activeProfileIdeal Z h P sets δ p.1.2 p.2 * Φ (p.1.1, p.2)
      ∂(μ.prod (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P))).prod volume) -
      ∫ p, f (activeProfileSample h P extra sets R s z p)
        ∂(μ.prod (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P))).prod
          (jointBooleanSource (fun d : {d // ¬P d} => h d.val))| ≤ ε at he
  rw [havg] at he
  exact he

end Erdos3

end

end OAI
