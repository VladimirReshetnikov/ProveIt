import OAI.Combinatorics.Progressions.Probability.AllocatedSlicedIdealDensity
import OAI.Combinatorics.Progressions.Probability.SlicedDensityBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree grid
local notation "Row" => OneCubeActiveRow grid
local notation "axis" => (fun e : Row => Subtype.val (Prod.snd e))

theorem allocatedSlicedAveragedIdealDensity_cap_lipschitz
    (hB : ∀ a : {a // ¬grid a}, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (degree a.val) → ℝ)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p) :
    let K := fun e : Row => SlicedProductBlock.uniformCap
      {j : Fin (degree e.2.val) // j ≠ ⟨0, Nat.zero_lt_succ _⟩}
      (a * δ ^ (Fintype.card {j : Fin (degree e.2.val) // j ≠ ⟨0, Nat.zero_lt_succ _⟩} + 1))
      (mul_pos ha (pow_pos hδ _))
    (∀ y, allocatedSlicedAveragedIdealDensity B U basis S hB lower width y ∈ Set.Icc (0 : ℝ) (∏ e, K e)) ∧
      LipschitzWith ((∏ e, (K e + 1)) * ∑ e, K e * (2 * K e))
        (allocatedSlicedAveragedIdealDensity B U basis S hB lower width) := by
  intro K
  have hm := allocatedSlicedConditionalIdealDensity_measurable B U basis S hB lower width
  simp only [← NNReal.coe_prod]
  apply densityMixture_uniform_bound (unitCoefficientSource Coeff)
    (allocatedSlicedConditionalIdealDensity B U basis S hB lower width)
    (∏ e, K e) ((∏ e, (K e + 1)) * ∑ e, K e * (2 * K e))
  · intro y
    exact (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · filter_upwards [unitCoefficientSource_abs_le Coeff] with r hr
    have hc (e : Row) (b : B e.2.val) : a ≤
        |jointSlicedProfilePrincipal degree axis (unitProfilePrincipalSize (B := B))
          (fun e j => r ⟨e.2, j⟩) e b| :=
      (hprincipal e.2).trans (jointSlicedProfilePrincipal_unit_bounds degree axis
        (fun e j => r ⟨e.2, j⟩) (fun e j => hr _) e b).1
    have he := jointSlicedPrincipalDensity_cap_lipschitz (fun e : Row => hB e.2)
      (fun e => ⟨0, Nat.zero_lt_succ _⟩) _ (fun e => lower e.2) (fun e => width e.2)
      (fun e => (1 / 4 : ℝ) * r ⟨e.2, constantCoefficientSlot _ _⟩) ha hδ hc (fun e => hw e.2) (fun e => hl e.2)
    simpa only [allocatedSlicedConditionalIdealDensity, K, NNReal.coe_prod] using he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree grid
local notation "Row" => OneCubeActiveRow grid
local notation "axis" => (fun e : Row => Subtype.val (Prod.snd e))

noncomputable def slicedJointDensityLogBudget (O m : ℕ) (P : ℝ) : ℝ :=
  (O + 2) * (P + (P + 2) * (m + 1) + 1) + O + 1

theorem slicedJointDensityLogBudget_nonneg (O m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ slicedJointDensityLogBudget O m P := by
  unfold slicedJointDensityLogBudget
  positivity

theorem allocatedSlicedAveragedIdealDensity_uniform_bounds
    (O : ℕ) (hO : Fintype.card Row ≤ O)
    (hB : ∀ a : {a // ¬grid a}, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (degree a.val) → ℝ)
    {a δ P : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hP : 0 ≤ P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p) :
    let L := slicedJointDensityLogBudget O m P
    (∀ y, allocatedSlicedAveragedIdealDensity B U basis S hB lower width y ∈ Set.Icc 0 (Real.exp L)) ∧
      LipschitzWith ⟨Real.exp L, Real.exp_nonneg _⟩
        (allocatedSlicedAveragedIdealDensity B U basis S hB lower width) := by
  let K := fun e : Row => SlicedProductBlock.uniformCap
    {j : Fin (degree e.2.val) // j ≠ ⟨0, Nat.zero_lt_succ _⟩}
    (a * δ ^ (Fintype.card {j : Fin (degree e.2.val) // j ≠ ⟨0, Nat.zero_lt_succ _⟩} + 1))
    (mul_pos ha (pow_pos hδ _))
  have hk (e : Row) : (K e : ℝ) ≤ Real.exp (P + (P + 2) * (m + 1)) := by
    apply slicedUniformCap_le_exp ha hδ hP haP hδP m
    apply (Fintype.card_subtype_le _).trans
    rw [Fintype.card_fin]
    exact Nat.succ_le_of_lt e.2.val.1.isLt
  have hb := densityProductConstants_le_exp K (by positivity) hk O hO
  have he := allocatedSlicedAveragedIdealDensity_cap_lipschitz B U basis S hB lower width ha hδ hprincipal hw hl
  constructor
  · intro y
    refine ⟨(he.1 y).1, (he.1 y).2.trans ?_⟩
    simpa only [K, NNReal.coe_prod, slicedJointDensityLogBudget] using hb.1
  · apply he.2.weaken
    apply NNReal.coe_le_coe.mp
    convert hb.2 using 1
    rfl

theorem exists_allocatedSlicedIdeal_site_expansion
    [∀ j, DecidableEq (I j)]
    (O : ℕ) (hO : Fintype.card Row ≤ O)
    (hB : ∀ a : {a // ¬grid a}, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (degree a.val) → ℝ)
    {a δ P H ε : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hP : 0 ≤ P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (hH : 0 < H) (hε : 0 < ε)
    (hHP : H ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    let Q := slicedJointDensityLogBudget O m P + P
    ∃ z : ℕ, (z : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      ∃ (c : (Bool × LayerSamplerAxis I n → Fin z) → ℂ)
        (f : (Bool × LayerSamplerAxis I n → Fin z) → Bool → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ k, ‖c k‖) ≤ Real.exp ((2 * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q) ∧
        (∀ k s x, ‖f k s x‖ ≤ 1) ∧
        (∀ k s, LipschitzWith ⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ (f k s)) ∧
        ∀ x : Bool → LayerSamplerAxis I n → ℝ, (∀ s d, |x s d| ≤ H) →
          ‖(allocatedSlicedAveragedIdealDensity B U basis S hB lower width
              (siteDensityRestriction grid x) : ℂ) - ∑ k, c k * ∏ s, f k s (x s)‖ ≤ ε := by
  let L := slicedJointDensityLogBudget O m P
  have hL : 0 ≤ L := slicedJointDensityLogBudget_nonneg O m hP
  have hb := allocatedSlicedAveragedIdealDensity_uniform_bounds B U basis S O hO hB lower width
    ha hδ hP haP hδP hprincipal hw hl
  let F : (Bool → LayerSamplerAxis I n → ℝ) → ℂ := fun x =>
    (allocatedSlicedAveragedIdealDensity B U basis S hB lower width (siteDensityRestriction grid x) : ℂ)
  have hcap (x) : ‖F x‖ ≤ Real.exp L := by
    rw [Complex.norm_real, Real.norm_of_nonneg (hb.1 _).1]
    exact (hb.1 _).2
  have hLip := siteDensityRestriction_complex_lipschitz grid
    (allocatedSlicedAveragedIdealDensity B U basis S hB lower width) hb.2
  have hPL : Real.exp P ≤ Real.exp (L + P) := Real.exp_le_exp.mpr (by linarith)
  have hLL : Real.exp L ≤ Real.exp (L + P) := Real.exp_le_exp.mpr (by linarith)
  have he := exists_grouped_site_approximation F
    ⟨Real.exp L, Real.exp_nonneg _⟩ ⟨Real.exp L, Real.exp_nonneg _⟩ hcap hLip
    hH hε (add_nonneg hL hP) (hHP.trans hPL) hLL hLL (hεP.trans hPL)
  simpa only [Fintype.card_bool] using he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree grid
local notation "Row" => OneCubeActiveRow grid
local notation "axis" => (fun e : Row => Subtype.val (Prod.snd e))

theorem exists_allocatedSlicedIdeal_boolean_site_expansion
    [∀ j, DecidableEq (I j)]
    (O : ℕ) (hO : Fintype.card Row ≤ O)
    (hB : ∀ a : {a // ¬grid a}, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (degree a.val) → ℝ)
    {a δ P H ε : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hP : 0 ≤ P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (hH : 0 < H) (hε : 0 < ε)
    (hHP : H ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    let Q := slicedJointDensityLogBudget O m P + P
    ∃ z : ℕ, (z : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      ∃ (c : (Finset (Fin 1) × LayerSamplerAxis I n → Fin z) → ℂ)
        (f : (Finset (Fin 1) × LayerSamplerAxis I n → Fin z) → Finset (Fin 1) → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ k, ‖c k‖) ≤ Real.exp ((2 * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q) ∧
        (∀ k s x, ‖f k s x‖ ≤ 1) ∧
        (∀ k s, LipschitzWith ⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ (f k s)) ∧
        ∀ x : Finset (Fin 1) → LayerSamplerAxis I n → ℝ, (∀ s d, |x s d| ≤ H) →
          ‖(allocatedSlicedAveragedIdealDensity B U basis S hB lower width
              (oneCubeSiteRestriction grid x) : ℂ) - ∑ k, c k * ∏ s, f k s (x s)‖ ≤ ε := by
  let L := slicedJointDensityLogBudget O m P
  have hL : 0 ≤ L := slicedJointDensityLogBudget_nonneg O m hP
  have hb := allocatedSlicedAveragedIdealDensity_uniform_bounds B U basis S O hO hB lower width
    ha hδ hP haP hδP hprincipal hw hl
  let F : (Finset (Fin 1) → LayerSamplerAxis I n → ℝ) → ℂ := fun x =>
    (allocatedSlicedAveragedIdealDensity B U basis S hB lower width (oneCubeSiteRestriction grid x) : ℂ)
  have hcap (x) : ‖F x‖ ≤ Real.exp L := by
    rw [Complex.norm_real, Real.norm_of_nonneg (hb.1 _).1]
    exact (hb.1 _).2
  have hLip := oneCubeSiteRestriction_complex_lipschitz grid
    (allocatedSlicedAveragedIdealDensity B U basis S hB lower width) hb.2
  have hPL : Real.exp P ≤ Real.exp (L + P) := Real.exp_le_exp.mpr (by linarith)
  have hLL : Real.exp L ≤ Real.exp (L + P) := Real.exp_le_exp.mpr (by linarith)
  have he := exists_grouped_site_approximation F
    ⟨Real.exp L, Real.exp_nonneg _⟩ ⟨Real.exp L, Real.exp_nonneg _⟩ hcap hLip
    hH hε (add_nonneg hL hP) (hHP.trans hPL) hLL hLL (hεP.trans hPL)
  simpa only [Fintype.card_finset, Fintype.card_fin, pow_one] using he

end Erdos3.VectorPolynomial

end

end OAI
