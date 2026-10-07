import Mathlib.Data.PNat.Defs
import OAI.Combinatorics.Progressions.Dynamics.AllocatedCommonScaleBudget
import OAI.Combinatorics.Progressions.Lattices.AllocatedIdealResidueData
import OAI.Combinatorics.Progressions.Sampling.AllocatedFixedSamplingCover

namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

noncomputable def allocatedCommonScale (p c P e E : ℝ) : LayerSamplerScale (G := G) B U b R σ :=
  allocatedIdealScale (G := G) B U b hR hσ (allocatedComparisonDimension m p)
    (allocatedCommonScaleNumeric m p c P E) e (allocatedSiteKernelMaskLog m P)
    (allocatedReferenceIdealError m (allocatedComparisonDimension m p) P E)

theorem allocatedCommonScale_lower {p c P e E : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e) (hE : 0 ≤ E) :
    Real.exp (allocatedCommonScaleNumeric m p c P E) ≤
      (allocatedCommonScale (G := G) B U b hR hσ p c P e E).value := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  exact allocatedIdealScale_ge_exp B U b hR hσ hD
    (allocatedCommonScaleNumeric_bounds m hp hc hP hE).1 he
    (allocatedSiteKernelMaskLog_nonneg m hP) (allocatedReferenceIdealError_nonneg m hD hP hE)

theorem allocatedCommonScale_period_window {dim M : ℕ} {p c P e E : ℝ}
    (hdim : dim ≤ m + 1) (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hM : (M : ℝ) ≤ Real.exp P) :
    (Fintype.card (Fin dim) + 1) * M ^ (m + 1) ≤
      (allocatedCommonScale (G := G) B U b hR hσ p c P e E).value := by
  have hd : ((dim + 1 : ℕ) : ℝ) ≤ (m + 2 : ℕ) := by
    exact_mod_cast (show dim + 1 ≤ m + 2 by omega)
  have hdim' : ((dim + 1 : ℕ) : ℝ) ≤ Real.exp (m + 2 : ℕ) :=
    hd.trans (by linarith [Real.add_one_le_exp ((m + 2 : ℕ) : ℝ)])
  have hpow := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg M) hM hP (m + 1) le_rfl
  have hprod := (mul_le_mul hdim' hpow (pow_nonneg (Nat.cast_nonneg M) _) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  obtain ⟨_, _, _, _, _, _, hnum⟩ := allocatedCommonScaleNumeric_bounds m hp hc hP hE
  have hlog : ((m + 2 : ℕ) : ℝ) + (m + 1 : ℕ) * P ≤ allocatedCommonScaleNumeric m p c P E := by
    nlinarith [sq_nonneg P]
  have hout := hprod.trans ((Real.exp_le_exp.mpr hlog).trans
    (allocatedCommonScale_lower (G := G) B U b hR hσ hp hc hP he hE))
  simpa only [Fintype.card_fin] using
    (show (dim + 1) * M ^ (m + 1) ≤ (allocatedCommonScale (G := G) B U b hR hσ p c P e E).value by
      exact_mod_cast hout)

theorem allocatedCommonScale_upper
    {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset α) (hq : Fintype.card α ≤ m + 1)
    (hinj : ∀ j, Function.Injective (rows j))
    {p c P e E : ℝ} (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp c) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp c) :
    ((allocatedCommonScale (G := G) B U b hR hσ p c P e E).value : ℝ) ≤
      Real.exp (allocatedCommonScaleLog m p c P e E) := by
  have hd := allocatedComparisonDimensions_of_primitive B rows hq hinj hp hvars hI hn
  obtain ⟨hq, _, hcq, _⟩ := allocatedCommonScaleNumeric_bounds m hp hc hP hE
  exact allocatedIdealScale_upper B U b hR hσ hd hq he
    (allocatedSiteKernelMaskLog_nonneg m hP) (allocatedReferenceIdealError_nonneg m hd.nonneg hP hE)
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hcq))
    (fun j => (hσi j).trans (Real.exp_le_exp.mpr hcq))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

theorem allocatedCommonScale_refined_period_window
    {dim M modulus : ℕ} {p c P e E : ℝ}
    (hdim : dim ≤ m + 1) (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P)
    (he : 0 ≤ e) (hE : 0 ≤ E)
    (hmodulus : modulus ≤ M ^ (m + 1)) (hM : (M : ℝ) ≤ Real.exp P)
    {X : Type*} [Fintype X] (hX : (Fintype.card X : ℝ) ≤ P)
    (stride : X → ℕ) (hs : ∀ t, (stride t : ℝ) ≤ Real.exp P) :
    (Fintype.card (Fin dim) + 1) * residueRefinedPeriod modulus stride ≤
      (allocatedCommonScale (G := G) B U b hR hσ p c P e E).value := by
  have hmod : (modulus : ℝ) ≤ Real.exp ((m + 1 : ℕ) * P) := by
    calc
      _ ≤ (M : ℝ) ^ (m + 1) := by exact_mod_cast hmodulus
      _ ≤ (Real.exp P) ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM _
      _ = _ := (Real.exp_nat_mul P (m + 1)).symm
  have hrefined := residueRefinedPeriod_exp_bound modulus stride hmod hs
  have hd : ((dim + 1 : ℕ) : ℝ) ≤ (m + 2 : ℕ) := by
    exact_mod_cast (show dim + 1 ≤ m + 2 by omega)
  have hde : ((dim + 1 : ℕ) : ℝ) ≤ Real.exp (m + 2 : ℕ) :=
    hd.trans (by linarith [Real.add_one_le_exp ((m + 2 : ℕ) : ℝ)])
  obtain ⟨_, _, _, _, _, _, hnum⟩ := allocatedCommonScaleNumeric_bounds m hp hc hP hE
  have hcost : ((m + 2 : ℕ) : ℝ) + ((m + 1 : ℕ) * P + Fintype.card X * P) ≤
      allocatedCommonScaleNumeric m p c P E := by
    nlinarith [mul_le_mul_of_nonneg_right hX hP]
  have hsize : ((dim + 1 : ℕ) : ℝ) * residueRefinedPeriod modulus stride ≤
      ((allocatedCommonScale (G := G) B U b hR hσ p c P e E).value : ℝ) := by
    calc
      _ ≤ Real.exp (m + 2 : ℕ) * Real.exp ((m + 1 : ℕ) * P + Fintype.card X * P) :=
        mul_le_mul hde hrefined (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (((m + 2 : ℕ) : ℝ) + ((m + 1 : ℕ) * P + Fintype.card X * P)) :=
        (Real.exp_add _ _).symm
      _ ≤ Real.exp (allocatedCommonScaleNumeric m p c P E) := Real.exp_le_exp.mpr hcost
      _ ≤ _ := allocatedCommonScale_lower (G := G) B U b hR hσ hp hc hP he hE
  simpa only [Fintype.card_fin] using
    (show (dim + 1) * residueRefinedPeriod modulus stride ≤
      (allocatedCommonScale (G := G) B U b hR hσ p c P e E).value by exact_mod_cast hsize)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

def allocatedRefinedPeriodLog {A : Type*} [Semiring A] (m : ℕ) (P : A) : A :=
  (m + 1 : ℕ) * P + P ^ 2

noncomputable def allocatedRefinedPeriodCutoff (m : ℕ) (P : ℝ) : ℕ :=
  ⌈Real.exp (allocatedRefinedPeriodLog m P)⌉₊

theorem allocatedRefinedPeriodCutoff_bounds (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    1 ≤ allocatedRefinedPeriodCutoff m P ∧
      (allocatedRefinedPeriodCutoff m P : ℝ) ≤ Real.exp (allocatedRefinedPeriodLog m P + 1) := by
  refine ⟨one_le_ceil_exp _, ?_⟩
  apply ceil_exp_le_exp_add_one
  unfold allocatedRefinedPeriodLog
  positivity

theorem allocatedRefinedPeriodCutoff_contains {X : Type*} [Fintype X]
    (m : ℕ) {P : ℝ} {M modulus : ℕ} (hP : 0 ≤ P)
    (hM : (M : ℝ) ≤ Real.exp P) (hmodulus : modulus ≤ M ^ (m + 1))
    (hX : (Fintype.card X : ℝ) ≤ P) (stride : X → ℕ)
    (hstride : ∀ t, (stride t : ℝ) ≤ Real.exp P) :
    residueRefinedPeriod modulus stride ≤ allocatedRefinedPeriodCutoff m P := by
  have hmod : (modulus : ℝ) ≤ Real.exp ((m + 1 : ℕ) * P) := by
    calc
      _ ≤ (M : ℝ) ^ (m + 1) := by exact_mod_cast hmodulus
      _ ≤ (Real.exp P) ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM _
      _ = _ := (Real.exp_nat_mul P (m + 1)).symm
  have hbound := residueRefinedPeriod_exp_bound modulus stride hmod hstride
  have hlog : ((m + 1 : ℕ) : ℝ) * P + Fintype.card X * P ≤ allocatedRefinedPeriodLog m P := by
    unfold allocatedRefinedPeriodLog
    nlinarith [mul_le_mul_of_nonneg_right hX hP]
  have hreal := hbound.trans ((Real.exp_le_exp.mpr hlog).trans (Nat.le_ceil _))
  exact_mod_cast hreal

theorem allocatedRefinedPeriodCutoff_contains_power {X : Type*} [Fintype X]
    (m : ℕ) {P : ℝ} {M modulus : ℕ} (hP : 0 ≤ P)
    (hM : (M : ℝ) ≤ Real.exp P) (hmodulus : modulus ≤ M ^ (m + 1))
    (hX : (Fintype.card X : ℝ) ≤ P) (stride : X → ℕ)
    (hstride : ∀ t, (stride t : ℝ) ≤ Real.exp P) :
    residueRefinedPeriod modulus stride ≤ allocatedRefinedPeriodCutoff m P ^ (m + 1) := by
  apply (allocatedRefinedPeriodCutoff_contains m hP hM hmodulus hX stride hstride).trans
  calc
    _ = allocatedRefinedPeriodCutoff m P ^ 1 := (pow_one _).symm
    _ ≤ _ := pow_le_pow_right₀ (allocatedRefinedPeriodCutoff_bounds m hP).1 (by omega)

abbrev AllocatedRefinedPeriodCandidate (m : ℕ) (P : ℝ) :=
  {q : ℕ+ // (q : ℕ) ≤ allocatedRefinedPeriodCutoff m P ^ (m + 1)}

noncomputable def allocatedRefinedPeriodCandidate {X : Type*} [Fintype X]
    (m : ℕ) {P : ℝ} {M modulus : ℕ} (hP : 0 ≤ P)
    (hM : (M : ℝ) ≤ Real.exp P) (hmodulus : modulus ≤ M ^ (m + 1))
    (hX : (Fintype.card X : ℝ) ≤ P) (hmodulusPos : 0 < modulus)
    (stride : X → ℕ) (hs : ∀ t, 0 < stride t)
    (hstride : ∀ t, (stride t : ℝ) ≤ Real.exp P) : AllocatedRefinedPeriodCandidate m P :=
  ⟨⟨residueRefinedPeriod modulus stride, residueRefinedPeriod_pos hmodulusPos stride hs⟩,
    allocatedRefinedPeriodCutoff_contains_power m hP hM hmodulus hX stride hstride⟩

theorem allocatedRefinedPeriodCandidate_value {X : Type*} [Fintype X]
    (m : ℕ) {P : ℝ} {M modulus : ℕ} (hP : 0 ≤ P)
    (hM : (M : ℝ) ≤ Real.exp P) (hmodulus : modulus ≤ M ^ (m + 1))
    (hX : (Fintype.card X : ℝ) ≤ P) (hmodulusPos : 0 < modulus)
    (stride : X → ℕ) (hs : ∀ t, 0 < stride t)
    (hstride : ∀ t, (stride t : ℝ) ≤ Real.exp P) :
    ((allocatedRefinedPeriodCandidate m hP hM hmodulus hX hmodulusPos stride hs hstride).val : ℕ) =
      residueRefinedPeriod modulus stride := rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

theorem allocatedCommonScale_cutoff_window
    {dim : ℕ} {p c P e E : ℝ} (hdim : dim ≤ m + 1)
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e) (hE : 0 ≤ E) :
    (Fintype.card (Fin dim) + 1) * allocatedRefinedPeriodCutoff m P ≤
      (allocatedCommonScale (G := G) B U b hR hσ p c P e E).value := by
  have hd : ((dim + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show dim + 1 ≤ (m + 1) + 1 from Nat.succ_le_succ hdim)
  have hde := hd.trans (Real.add_one_le_exp ((m + 1 : ℕ) : ℝ))
  have hcutoff := (allocatedRefinedPeriodCutoff_bounds m hP).2
  obtain ⟨_, _, _, _, _, _, hnum⟩ := allocatedCommonScaleNumeric_bounds m hp hc hP hE
  have hcost : ((m + 1 : ℕ) : ℝ) + (allocatedRefinedPeriodLog m P + 1) ≤
      allocatedCommonScaleNumeric m p c P E := by
    dsimp only [allocatedRefinedPeriodLog]
    push_cast at hnum ⊢
    linarith
  have hsize : ((dim + 1 : ℕ) : ℝ) * allocatedRefinedPeriodCutoff m P ≤
      ((allocatedCommonScale (G := G) B U b hR hσ p c P e E).value : ℝ) := by
    calc
      _ ≤ Real.exp ((m + 1 : ℕ) : ℝ) * Real.exp (allocatedRefinedPeriodLog m P + 1) :=
        mul_le_mul hde hcutoff (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (((m + 1 : ℕ) : ℝ) + (allocatedRefinedPeriodLog m P + 1)) :=
        (Real.exp_add _ _).symm
      _ ≤ Real.exp (allocatedCommonScaleNumeric m p c P E) := Real.exp_le_exp.mpr hcost
      _ ≤ _ := allocatedCommonScale_lower (G := G) B U b hR hσ hp hc hP he hE
  simpa only [Fintype.card_fin] using
    (show (dim + 1) * allocatedRefinedPeriodCutoff m P ≤
      (allocatedCommonScale (G := G) B U b hR hσ p c P e E).value by exact_mod_cast hsize)

abbrev AllocatedRefinedPeriodIndex (m : ℕ) (P : ℝ) :=
  {q : ℕ+ // (q : ℕ) ≤ allocatedRefinedPeriodCutoff m P}

theorem allocatedRefinedPeriodIndex_power (m : ℕ) {P : ℝ} (hP : 0 ≤ P)
    (q : AllocatedRefinedPeriodIndex m P) :
    (q.val : ℕ) ≤ allocatedRefinedPeriodCutoff m P ^ (m + 1) := by
  calc
    _ ≤ allocatedRefinedPeriodCutoff m P := q.property
    _ = allocatedRefinedPeriodCutoff m P ^ 1 := (pow_one _).symm
    _ ≤ _ := pow_le_pow_right₀ (allocatedRefinedPeriodCutoff_bounds m hP).1 (by omega)

noncomputable def allocatedRefinedPeriodIndex {X : Type*} [Fintype X]
    (m : ℕ) {P : ℝ} {M modulus : ℕ} (hP : 0 ≤ P)
    (hM : (M : ℝ) ≤ Real.exp P) (hmodulus : modulus ≤ M ^ (m + 1))
    (hX : (Fintype.card X : ℝ) ≤ P) (hmodulusPos : 0 < modulus)
    (stride : X → ℕ) (hs : ∀ t, 0 < stride t)
    (hstride : ∀ t, (stride t : ℝ) ≤ Real.exp P) : AllocatedRefinedPeriodIndex m P :=
  ⟨⟨residueRefinedPeriod modulus stride, residueRefinedPeriod_pos hmodulusPos stride hs⟩,
    allocatedRefinedPeriodCutoff_contains m hP hM hmodulus hX stride hstride⟩

theorem allocatedRefinedPeriodIndex_value {X : Type*} [Fintype X]
    (m : ℕ) {P : ℝ} {M modulus : ℕ} (hP : 0 ≤ P)
    (hM : (M : ℝ) ≤ Real.exp P) (hmodulus : modulus ≤ M ^ (m + 1))
    (hX : (Fintype.card X : ℝ) ≤ P) (hmodulusPos : 0 < modulus)
    (stride : X → ℕ) (hs : ∀ t, 0 < stride t)
    (hstride : ∀ t, (stride t : ℝ) ≤ Real.exp P) :
    ((allocatedRefinedPeriodIndex m hP hM hmodulus hX hmodulusPos stride hs hstride).val : ℕ) =
      residueRefinedPeriod modulus stride := rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

abbrev AllocatedFittingPeriod (m dim L : ℕ) (P : ℝ) :=
  {q : ℕ+ // (q : ℕ) ≤ allocatedRefinedPeriodCutoff m P ∧ (dim + 1) * (q : ℕ) ≤ L}

theorem allocatedFittingPeriod_power {m dim L : ℕ} {P : ℝ} (hP : 0 ≤ P)
    (q : AllocatedFittingPeriod m dim L P) :
    (q.val : ℕ) ≤ allocatedRefinedPeriodCutoff m P ^ (m + 1) := by
  apply q.property.1.trans
  calc
    _ = allocatedRefinedPeriodCutoff m P ^ 1 := (pow_one _).symm
    _ ≤ _ := pow_le_pow_right₀ (allocatedRefinedPeriodCutoff_bounds m hP).1 (by omega)

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

noncomputable def allocatedCommonFittingPeriod
    {dim M modulus : ℕ} {p c P e E : ℝ}
    (hdim : dim ≤ m + 1) (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P)
    (he : 0 ≤ e) (hE : 0 ≤ E)
    (hmodulus : modulus ≤ M ^ (m + 1)) (hM : (M : ℝ) ≤ Real.exp P)
    {X : Type*} [Fintype X] (hX : (Fintype.card X : ℝ) ≤ P)
    (hmodulusPos : 0 < modulus) (stride : X → ℕ) (hs : ∀ t, 0 < stride t)
    (hstride : ∀ t, (stride t : ℝ) ≤ Real.exp P) :
    AllocatedFittingPeriod m dim (allocatedCommonScale (G := G) B U b hR hσ p c P e E).value P :=
  ⟨⟨residueRefinedPeriod modulus stride, residueRefinedPeriod_pos hmodulusPos stride hs⟩,
    allocatedRefinedPeriodCutoff_contains m hP hM hmodulus hX stride hstride,
    by simpa only [Fintype.card_fin, PNat.mk_coe] using
      allocatedCommonScale_refined_period_window (G := G) B U b hR hσ hdim hp hc hP he hE
        hmodulus hM hX stride hstride⟩

theorem allocatedCommonFittingPeriod_value
    {dim M modulus : ℕ} {p c P e E : ℝ}
    (hdim : dim ≤ m + 1) (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P)
    (he : 0 ≤ e) (hE : 0 ≤ E)
    (hmodulus : modulus ≤ M ^ (m + 1)) (hM : (M : ℝ) ≤ Real.exp P)
    {X : Type*} [Fintype X] (hX : (Fintype.card X : ℝ) ≤ P)
    (hmodulusPos : 0 < modulus) (stride : X → ℕ) (hs : ∀ t, 0 < stride t)
    (hstride : ∀ t, (stride t : ℝ) ≤ Real.exp P) :
    ((allocatedCommonFittingPeriod (G := G) B U b hR hσ hdim hp hc hP he hE hmodulus hM hX
      hmodulusPos stride hs hstride).val : ℕ) = residueRefinedPeriod modulus stride := rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq
attribute [local instance] ScalarSiteExpansion.termFinite

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {p c Psp e E : ℝ}
local notation "S" => allocatedCommonScale (G := G) B U b hR hσ p c Psp e E
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

variable (M₀ : ℕ)
local notation "period" => kernelPeriodCandidate (m + 1)
local notation "P" => canonicalScalarSourceEnvelope m M₀
local notation "L" => scalarSourceTransitionBound

local notation "sourceParameter" => allocatedCommonSourceLog m p c Psp e E
local notation "maskLog" => allocatedSiteKernelMaskLog m Psp
local notation "δ" => allocatedSitePrimitiveTolerance m sourceParameter maskLog (allocatedIdealProfileLog m sourceParameter e) E
local notation "Λ" => allocatedSiteSpectrumLog m sourceParameter maskLog (allocatedIdealProfileLog m sourceParameter e) E
local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "active" => allocatedActiveGrid B U b S
local notation "activeAxes" => {a : {a // grid a} // active a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S

local notation "sitePeriods" => (fun a : activeAxes =>
  (allocatedPositiveSitePeriod B (Fin dim) U b hR S (Subtype.val a) : ℕ))

local notation "pointTolerance" => allocatedSitePointTolerance (G := G) B rowSets δ
local notation "torus" => (fun a : activeAxes => allocatedGridTorusFactor B (Fin dim) (ig (Subtype.val a)))
local notation "siteLip" => (NNReal.mk (Real.exp (1 + 6 * Λ + 12)) (Real.exp_nonneg _) + 4 : ℝ≥0)
local notation "coefficientCap" => (fun a : activeAxes =>
  allocatedGridPointCap B P (ig (Subtype.val a)) (rowSets (Sigma.fst (ig (Subtype.val a)))) *
    Real.exp (Fintype.card (Finset (Fin dim)) * (4 * Λ + 8) + Λ))

variable {K : ℕ}
variable (hSampling : ∀ inst : ∀ j : Fin m,
    Fintype {s : Finset (Fin dim) // s ∈ boundedBooleanJetRows (Fin dim) (j.val + 1)},
  @AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim K
    (fun j => {s : Finset (Fin dim) // s ∈ boundedBooleanJetRows (Fin dim) (j.val + 1)})
    inst (fun _ => Subtype.val))

include hSampling in
theorem common_scale_good_kernel_ideal_cover_at_sampling
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hPsp : 0 ≤ Psp) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn₁ : ∀ j, (n j : ℝ) ≤ p)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hcutoff : (M₀ : ℝ) ≤ Real.exp Psp)
    (hRi₀ : ∀ j, (R j)⁻¹ ≤ Real.exp c)
    (hσi₀ : ∀ j, (σ j)⁻¹ ≤ Real.exp c)
    (hR1 : ∀ j, R j ≤ 1)
    (hBlocks : ∀ j i, siteSpectrumBlockCount m ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) :
    ∃ witnesses : (t : Fin M₀) → (r : AllocatedPositiveResidue (dim := dim) B U b S (period t)) →
        AllocatedResidueSiteWitness (dim := dim) B U b S (period t) r.val,
      (∀ t r, allocatedActiveSiteBounds B U b S rowSets P pointTolerance Λ sitePeriods (witnesses t r).expansion) ∧ ∀
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCexp : ∀ j, (C j : ℝ) ≤ Real.exp sourceParameter) (_hVexp : ∀ j, (V j : ℝ) ≤ Real.exp sourceParameter)
    (_hσ1 : ∀ j, σ j ≤ 1)
    (Qsite : ℝ≥0) (_hQsite : ∀ a : activeAxes, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (ig a.val).1 (ig a.val).2) : ℝ) + 1) ≤ Qsite)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, R j ≤ allocatedIdealCoverRadius (G := G) B rowSets Cinv j),
    ∃ g : (t : Fin M₀) → (r : AllocatedPositiveResidue (dim := dim) B U b S (period t)) →
        (∀ a, ((witnesses t r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ t r k s, LipschitzWith (max (((Fintype.card activeAxes * siteLip) * Qsite) *
        (Real.toNNReal (Real.exp sourceParameter) * ∑ j, C j * Fintype.card (J j)) * commonSitePeriod (witnesses t r).expansion k)
          (4 * commonSitePeriod (witnesses t r).expansion k)) (g t r k s) ∧ ∀ z, ‖g t r k s z‖ ≤ 1) ∧
      (∀ t r, (∑ k, ‖coverSiteCoefficient (witnesses t r).expansion k‖) ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, (coefficientCap) a) ∧
      (∀ t, allocatedResidueCoverCoefficientMass B U b S (period t) (witnesses t) ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, (coefficientCap) a) ∧
      ∀ (x : G → IntegerScalarCubeBox (Fin dim) (LayerSamplerScale.value S))
        (selection : Fin dim ↪ G) {κ : ℝ}
        (_hx : GoodScalarKernelTuple selection κ M₀ x),
      ∃ t : Fin M₀,
        (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (period t : ℤ) ≤
          pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
            (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
        (∀ j, integerScalarLattice (rowTypes j) (period t : ℤ) ≤
          (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range) ∧
      ∀ (τ : ℝ≥0), 0 < τ → τ ≤ 1 → (τ : ℝ)⁻¹ ≤ Real.exp e → ∀
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
    (_hbudget : allocatedSiteErrorFourierOutput m sourceParameter maskLog (allocatedIdealProfileLog m sourceParameter e) ≤ P₀)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hmp : ∀ j e, coefficients (p j) e ∈ U j)
    (stride : X → ℕ) (_hs : ∀ x, 0 < stride x)
    {R₁ S₀ ρ : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P₀) (_hρ : 0 < ρ)
    (_hρP : 1 / ρ ≤ Real.exp P₀)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (H : X → ℝ) (_hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ H x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁)
    (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride)) (_hcells : cells.Nonempty)
    (W : Option (Fin dim) × X → ℝ) (hW : ∀ z, 0 < W z) (_hwidth : ∀ z, ρ * H z.2 ≤ W z),
    let f := allocatedPhysicalLongIdeal B U b hR S rowSets τ
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let error := fun z : Option (Fin dim) × X → ℤ =>
      law.complexMean (fun y₀ =>
        (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows) hb o bW d y₀ (period t) f
          (physicalCubeRowSample U d (rows) p hmp (standardPhysicalCubeOutput z)) : ℂ)) -
      (law.fiberLaw (principalResidueLabel (period t))).complexMean
        (allocatedSupportedIdealCoverValue B U b hR hσ S (period t) (witnesses t) hb o bW d (g t) τ x p hmp
          (standardPhysicalCubeOutput z))
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      selectedResidueDensityMass stride cells W (fun z => ‖error z‖) ≤ Real.exp (-E) ∧
      ∀ φ : (Option (Fin dim) × X → ℤ) → ℂ, (∀ z, ‖φ z‖ ≤ 1) →
        ‖∑' z, ((selectedResidueSmoothPMF stride cells W hW hZ z).toReal : ℂ) *
          (error z * φ z)‖ ≤ Real.exp (-E) := by
  obtain ⟨_, _, hpSource, hcSource, _, hEbudget, hCSource, hScaleSource, _⟩ :=
    allocatedCommonSourceLog_bounds m hp hc hPsp he hE
  have hw := allocatedSiteKernelMaskLog_nonneg m hPsp
  have hrowdim : Fintype.card (Fin dim) ≤ m + 1 := by
    simpa only [Fintype.card_fin] using hdimSmall
  have hscale := allocatedCommonScale_upper (G := G) B U b hR hσ rows hrowdim
    (fun _ => Subtype.val_injective) hp hc hPsp he hE hvars hI hn₁ hRi₀ hσi₀
  have hsize := allocatedCommonScale_period_window (G := G) B U b hR hσ hdimSmall hp hc hPsp he hE hcutoff
  have hblocks := allocatedUniformBlocks_spectrum_bound B rowSets hrowdim hBlocks
  have hgamma (a : activeAxes) : principalProfileSize (R (ig a.val).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (ig a.val).1 (ig a.val).2)) ≤ (LayerSamplerScale.value S) :=
    principalProfileSize_le_natScale (hR _).le (hR1 _) _ (LayerSamplerScale.value S) (LayerSamplerScale.positive S)
  obtain ⟨witnesses, hBounds, hgeometry⟩ := cutoff_mask_good_kernel_ideal_cover_at_sampling
    (B := B) (U := U) (b := b) (hR := hR) (hσ := hσ) («S» := S) (M₀ := M₀)
    (hsize := hsize) (M := sitePeriods) (hSampling := hSampling) (p₀ := Psp) (p₁ := sourceParameter) (w := maskLog)
    hw he hE hdimSmall (hvars.trans hpSource) (fun j => (hI j).trans hpSource)
    (fun j => (hn₁ j).trans hpSource) (fun j => (hJ j).trans hpSource)
    hPsp hcutoff hCSource le_rfl (hscale.trans (Real.exp_le_exp.mpr hScaleSource))
    hEbudget hgamma (fun _ => rfl) (fun a => hblocks (ig a.val))
  refine ⟨witnesses, hBounds, ?_⟩
  intro hb o Q _ bW d _ _ C V hC hV hCexp hVexp hσ1 Qsite hQsite Cinv hCinv hchart hsmall
  exact hgeometry hb o bW d C V hC hV hCexp hVexp
    (fun j => (hRi₀ j).trans (Real.exp_le_exp.mpr hcSource))
    hσ1 Qsite hQsite Cinv hCinv hchart hsmall

end Erdos3.VectorPolynomial

end

end OAI
