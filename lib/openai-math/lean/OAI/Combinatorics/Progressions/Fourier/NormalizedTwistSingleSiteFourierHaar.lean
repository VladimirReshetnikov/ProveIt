/- Modified for ProveIt: import Lean 4.32 compatibility declarations and
provide explicit sigma-finite instances for the nested Haar product integral.
All upstream statements and quantitative bounds are unchanged. -/
import OAI.Compat.Core
import Mathlib.MeasureTheory.Integral.Pi
import OAI.Combinatorics.Progressions.Estimates.AmbientBooleanReconstruction
import OAI.Combinatorics.Progressions.Estimates.PhysicalSingleSiteCommonCover

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

noncomputable def ambientIntegerCharacter {J : Type*} [Fintype J] (frequency : J → ℤ)
    (x : J → UnitAddCircle) : ℂ :=
  ∏ j, CircleFourier.character (frequency j • x j)

theorem ambientIntegerCharacter_norm {J : Type*} [Fintype J]
    (frequency : J → ℤ) (x : J → UnitAddCircle) :
    ‖ambientIntegerCharacter frequency x‖ = 1 := by
  simp [ambientIntegerCharacter, norm_prod, CircleFourier.norm_character]

theorem ambientIntegerCharacter_lipschitz {J : Type*} [Fintype J]
    (frequency : J → ℤ) (C : ℝ≥0) (hC : ∀ j, |(frequency j : ℝ)| ≤ C) :
    LipschitzWith (Fintype.card J * (CircleFourier.characterLipConstant * C))
      (ambientIntegerCharacter frequency) := by
  have hcoord (j : J) : LipschitzWith C (fun x : J → UnitAddCircle => frequency j • x j) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, ← smul_sub]
    apply (norm_zsmul_le (frequency j) (x j - y j)).trans
    apply mul_le_mul
    · simpa only [Int.norm_eq_abs] using hC j
    · simpa only [dist_eq_norm] using dist_le_pi_dist x y j
    · exact norm_nonneg _
    · exact C.coe_nonneg
  have h := (bounded_lipschitz_fintype_prod
    (fun j (x : J → UnitAddCircle) => CircleFourier.character (frequency j • x j))
    (B := 1) le_rfl (fun j => CircleFourier.character_lipschitz.comp (hcoord j))
    (fun j x => (CircleFourier.norm_character _).le)).2
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [one_pow, mul_one, ambientIntegerCharacter] using h.dist_le_mul x y

theorem ambientIntegerCharacter_reconstruction {J S : Type*} [Fintype J] [Fintype S]
    (frequency : J → ℤ) (A : Matrix J S ℤ) (x : S → UnitAddCircle) :
    ambientIntegerCharacter frequency (fun j => ∑ s, A j s • x s) =
      ambientIntegerCharacter (fun s => ∑ j, frequency j * A j s) x := by
  simp only [ambientIntegerCharacter, Finset.smul_sum, Finset.sum_smul,
    ← mul_smul, CircleFourier.character_fintype_sum]
  exact Finset.prod_comm

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators NNReal

noncomputable def ambientFourierSum {J F : Type*} [Fintype J] [Fintype F]
    (frequency : F → J → ℤ) (coeff : F → ℂ) (x : J → UnitAddCircle) : ℂ :=
  ∑ a, coeff a * ambientIntegerCharacter (frequency a) x

theorem ambientFourierSum_norm_le {J F : Type*} [Fintype J] [Fintype F]
    (frequency : F → J → ℤ) (coeff : F → ℂ) {B : ℝ}
    (hcoeff : (∑ a, ‖coeff a‖) ≤ B) (x : J → UnitAddCircle) :
    ‖ambientFourierSum frequency coeff x‖ ≤ B := by
  apply (norm_sum_le _ _).trans
  simpa only [norm_mul, ambientIntegerCharacter_norm, mul_one] using hcoeff

theorem ambientFourierSum_lipschitz {J F : Type*} [Fintype J] [Fintype F]
    (frequency : F → J → ℤ) (coeff : F → ℂ) (C B : ℝ≥0)
    (hfreq : ∀ a j, |(frequency a j : ℝ)| ≤ C)
    (hcoeff : (∑ a, ‖coeff a‖) ≤ B) :
    LipschitzWith (B * (Fintype.card J * (CircleFourier.characterLipConstant * C)))
      (ambientFourierSum frequency coeff) := by
  let L : ℝ≥0 := Fintype.card J * (CircleFourier.characterLipConstant * C)
  have hL (a) := ambientIntegerCharacter_lipschitz (frequency a) C (hfreq a)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (ambientFourierSum frequency coeff x) (ambientFourierSum frequency coeff y) ≤
    (B * L : ℝ≥0) * dist x y
  simp only [dist_eq_norm, ambientFourierSum, ← Finset.sum_sub_distrib, ← mul_sub, NNReal.coe_mul]
  calc
    _ ≤ ∑ a, ‖coeff a * (ambientIntegerCharacter (frequency a) x -
        ambientIntegerCharacter (frequency a) y)‖ := norm_sum_le _ _
    _ ≤ ∑ a, ‖coeff a‖ * ((L : ℝ) * ‖x - y‖) := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [dist_eq_norm] using (hL a).dist_le_mul x y
    _ = (∑ a, ‖coeff a‖) * ((L : ℝ) * ‖x - y‖) := (Finset.sum_mul _ _ _).symm
    _ ≤ (B : ℝ) * ((L : ℝ) * ‖x - y‖) :=
      mul_le_mul_of_nonneg_right hcoeff (mul_nonneg L.coe_nonneg (norm_nonneg _))
    _ = _ := (mul_assoc _ _ _).symm

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

variable {K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (coeff : F → ℂ)

noncomputable def coefficientFourierAmbient : (CoefficientAmbientIndex K J → UnitAddCircle) → ℂ :=
  ambientFourierSum (fun a t => frequency a t.1.1 t.1.2.val t.2) coeff

theorem coefficientFourierAmbient_eq (z : CoefficientTorus (K := K) U) :
    coefficientFourierAmbient frequency coeff (coefficientAmbientTorus U z) =
      coefficientTorusFourierSum U frequency coeff z := by
  unfold coefficientFourierAmbient ambientFourierSum coefficientTorusFourierSum
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  rw [ambientIntegerCharacter, coefficientAmbientTorus_character]
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) z
  simp only [coefficientTorusCharacter_mk, coefficientArrayFunctional,
    LinearMap.coe_mk, AddHom.coe_mk, coefficientSlotFrequency_apply]

theorem coefficientFourierAmbient_norm_le {C : ℝ} (hc : (∑ a, ‖coeff a‖) ≤ C)
    (z : CoefficientAmbientIndex K J → UnitAddCircle) :
    ‖coefficientFourierAmbient frequency coeff z‖ ≤ C :=
  ambientFourierSum_norm_le _ coeff hc z

theorem coefficientFourierAmbient_lipschitz (L C : ℝ≥0)
    (hfreq : ∀ a j e, e.degree ≤ j.val + 1 → ∀ t, |(frequency a j e t : ℝ)| ≤ L)
    (hc : (∑ a, ‖coeff a‖) ≤ C) :
    LipschitzWith (C * (Fintype.card (CoefficientAmbientIndex K J) *
      (CircleFourier.characterLipConstant * L))) (coefficientFourierAmbient frequency coeff) :=
  ambientFourierSum_lipschitz _ coeff L C (fun a t => hfreq a t.1.1 t.1.2.val t.1.2.property t.2) hc

theorem exists_mean_coefficient_ambient_approximation
    {Y : Type*} [Fintype Y] (law : FiniteProbabilityWeights Y)
    (g : Y → CoefficientTorus (K := K) U → ℝ) (C L : ℝ≥0) {δ : ℝ}
    (h : ∀ y, ∃ (F : Type) (inst : Fintype F), let _ := inst
      ∃ (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (coeff : F → ℂ),
        (∀ a j e, e.degree ≤ j.val + 1 → ∀ t, |(frequency a j e t : ℝ)| ≤ L) ∧
        (∑ a, ‖coeff a‖) ≤ C ∧
        ∀ z, ‖(g y z : ℂ) - coefficientTorusFourierSum U frequency coeff z‖ ≤ δ) :
    ∃ f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℂ,
      LipschitzWith (C * (Fintype.card (CoefficientAmbientIndex K J) *
        (CircleFourier.characterLipConstant * L))) f ∧
      (∀ z, ‖f z‖ ≤ C) ∧
      ∀ z, ‖(law.mean (fun y => g y z) : ℂ) - f (coefficientAmbientTorus U z)‖ ≤ δ := by
  obtain ⟨F, inst, frequency, coeff, hfreq, hc, happ⟩ :=
    exists_coefficientFourierMixture U law g h
  let _ := inst
  refine ⟨coefficientFourierAmbient frequency coeff,
    coefficientFourierAmbient_lipschitz frequency coeff L C hfreq hc,
    coefficientFourierAmbient_norm_le frequency coeff hc, ?_⟩
  intro z
  rw [coefficientFourierAmbient_eq]
  exact happ z

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))

noncomputable def booleanSiteAmbientFrequency
    (frequency : JetAmbientIndex jets J → ℤ) (s : Finset α) :
    JetAmbientIndex (fun _ : Fin m => Unit) J → ℤ := fun a =>
  ∑ r : jets a.1, frequency ⟨a.1, r, a.2.2⟩ * booleanJetExtractionMatrix Subtype.val r s

omit [∀ j, Fintype (J j)] in
theorem booleanSiteAmbientFrequency_bound
    (frequency : JetAmbientIndex jets J → ℤ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ a, |(frequency a : ℝ)| ≤ C)
    (s : Finset α) (a : JetAmbientIndex (fun _ : Fin m => Unit) J) :
    |(booleanSiteAmbientFrequency frequency s a : ℝ)| ≤ Fintype.card (jets a.1) * C := by
  simp only [booleanSiteAmbientFrequency, Int.cast_sum, Int.cast_mul]
  calc
    _ ≤ ∑ r : jets a.1, |(frequency ⟨a.1, r, a.2.2⟩ : ℝ) *
        (booleanJetExtractionMatrix Subtype.val r s : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : jets a.1, C := by
      apply Finset.sum_le_sum
      intro r _
      rw [abs_mul]
      exact (mul_le_mul (hf _) (booleanJetExtractionMatrix_abs_le_one Subtype.val r s)
        (abs_nonneg _) hC).trans_eq (mul_one C)
    _ = _ := by simp

theorem ambientJetCharacter_site_factorization
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ)
    (frequency : JetAmbientIndex jets J → ℤ) (y : EuclideanJetLayers U jets) :
    ambientIntegerCharacter frequency (coveredJetAmbientTorus U d y) =
      ∏ s : Finset α, ambientIntegerCharacter (booleanSiteAmbientFrequency frequency s)
        (coveredJetAmbientTorus U d (coveredBooleanSiteValue U y s)) := by
  let term := fun (s : Finset α) (j : Fin m) (i : J j) =>
    CircleFourier.character (booleanSiteAmbientFrequency frequency s ⟨j, (), i⟩ •
      coveredJetAmbientTorus U d (coveredBooleanSiteValue U y s) ⟨j, (), i⟩)
  have hrow (j : Fin m) (i : J j) :
      (∏ r : jets j, CircleFourier.character
        (frequency ⟨j, r, i⟩ • coveredJetAmbientTorus U d y ⟨j, r, i⟩)) =
      ∏ s : Finset α, term s j i := by
    simpa only [ambientIntegerCharacter, booleanSiteAmbientFrequency, term,
      coveredJetAmbientTorus_booleanInverse] using
      ambientIntegerCharacter_reconstruction (fun r : jets j => frequency ⟨j, r, i⟩)
        (booleanJetExtractionMatrix Subtype.val)
        (fun s => coveredJetAmbientTorus U d (coveredBooleanSiteValue U y s) ⟨j, (), i⟩)
  simp only [ambientIntegerCharacter, Fintype.prod_sigma, Fintype.prod_prod_type,
    Fintype.prod_unique]
  change (∏ j, ∏ r : jets j, ∏ i : J j, CircleFourier.character
      (frequency ⟨j, r, i⟩ • coveredJetAmbientTorus U d y ⟨j, r, i⟩)) =
    ∏ s : Finset α, ∏ j, ∏ i : J j, term s j i
  calc
    _ = ∏ j, ∏ i : J j, ∏ r : jets j, CircleFourier.character
        (frequency ⟨j, r, i⟩ • coveredJetAmbientTorus U d y ⟨j, r, i⟩) :=
      Finset.prod_congr rfl (fun _ _ => Finset.prod_comm)
    _ = ∏ j, ∏ i : J j, ∏ s : Finset α, term s j i := by
      simp_rw [hrow]
    _ = ∏ j, ∏ s : Finset α, ∏ i : J j, term s j i :=
      Finset.prod_congr rfl (fun _ _ => Finset.prod_comm)
    _ = _ := Finset.prod_comm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "siteIndex" => JetAmbientIndex (fun _ : Fin m => Unit) J

noncomputable def booleanCharacterSiteFactor
    (frequency : JetAmbientIndex jets J → ℤ)
    (g : Finset α → (siteIndex → UnitAddCircle) → ℂ)
    (s : Finset α) (z : siteIndex → UnitAddCircle) : ℂ :=
  ambientIntegerCharacter (booleanSiteAmbientFrequency frequency s) z * g s z

theorem booleanCharacterSiteFactor_norm
    (frequency : JetAmbientIndex jets J → ℤ)
    (g : Finset α → (siteIndex → UnitAddCircle) → ℂ)
    (hg : ∀ s z, ‖g s z‖ ≤ 1) (s : Finset α) (z : siteIndex → UnitAddCircle) :
    ‖booleanCharacterSiteFactor frequency g s z‖ ≤ 1 := by
  simpa only [booleanCharacterSiteFactor, norm_mul, ambientIntegerCharacter_norm, one_mul] using hg s z

theorem booleanCharacterSiteFactor_lipschitz
    (frequency : JetAmbientIndex jets J → ℤ)
    (g : Finset α → (siteIndex → UnitAddCircle) → ℂ)
    (L C D : ℝ≥0) (hf : ∀ a, |(frequency a : ℝ)| ≤ C)
    (hD : ∀ j, (Fintype.card (jets j) : ℝ) ≤ D)
    (hg : ∀ s, LipschitzWith L (g s)) (hunit : ∀ s z, ‖g s z‖ ≤ 1)
    (s : Finset α) :
    LipschitzWith (L + Fintype.card siteIndex * (CircleFourier.characterLipConstant * (D * C)))
      (booleanCharacterSiteFactor frequency g s) := by
  have hfreq (a : siteIndex) : |(booleanSiteAmbientFrequency frequency s a : ℝ)| ≤ (D * C : ℝ≥0) :=
    (booleanSiteAmbientFrequency_bound frequency C.coe_nonneg hf s a).trans
      (mul_le_mul_of_nonneg_right (hD a.1) C.coe_nonneg)
  have hchar := ambientIntegerCharacter_lipschitz (booleanSiteAmbientFrequency frequency s) (D * C) hfreq
  have h := lipschitz_mul_of_bounds (ambientIntegerCharacter (booleanSiteAmbientFrequency frequency s)) (g s)
      (Bf := 1) (Bg := 1) hchar (hg s)
      (fun z => (ambientIntegerCharacter_norm _ z).le) (hunit s)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [one_mul, booleanCharacterSiteFactor] using h.dist_le_mul x y

theorem booleanCharacterSiteFactor_product
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ)
    (frequency : JetAmbientIndex jets J → ℤ)
    (g : Finset α → (siteIndex → UnitAddCircle) → ℂ) (y : EuclideanJetLayers U jets) :
    ambientIntegerCharacter frequency (coveredJetAmbientTorus U d y) *
      (∏ s, g s (coveredJetAmbientTorus U d (coveredBooleanSiteValue U y s))) =
      ∏ s, booleanCharacterSiteFactor frequency g s
        (coveredJetAmbientTorus U d (coveredBooleanSiteValue U y s)) := by
  rw [ambientJetCharacter_site_factorization]
  simp only [booleanCharacterSiteFactor, Finset.prod_mul_distrib]

theorem booleanCharacterSiteFactor_expansion {F : Type*} [Fintype F]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ)
    (frequency : F → JetAmbientIndex jets J → ℤ) (c : F → ℂ)
    (g : Finset α → (siteIndex → UnitAddCircle) → ℂ) (R : ℂ) (y : EuclideanJetLayers U jets) :
    (∑ a, c a * ambientIntegerCharacter (frequency a) (coveredJetAmbientTorus U d y) * R) *
      (∏ s, g s (coveredJetAmbientTorus U d (coveredBooleanSiteValue U y s))) =
      ∑ a, c a * (R * ∏ s, booleanCharacterSiteFactor (frequency a) g s
        (coveredJetAmbientTorus U d (coveredBooleanSiteValue U y s))) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [← booleanCharacterSiteFactor_product U d (frequency a) g y]
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

private noncomputable def singleSiteEuclideanRow {D : Type*} [Fintype D]
    (U : Submodule ℝ (D → ℝ)) (a : D → ℤ) : euclideanSubspace U →ₗ[ℝ] ℝ :=
  (integerRowLinear a).comp (U.subtype.comp
    ((LinearMap.proj ()).comp (euclideanSubspaceArrayEquiv U).toLinearMap))

private theorem singleSiteEuclideanRow_apply {D : Type*} [Fintype D]
    (U : Submodule ℝ (D → ℝ)) (a : D → ℤ) (x : euclideanSubspace U) :
    singleSiteEuclideanRow U a x = ∑ i, (a i : ℝ) * x.val i := by
  change integerRowLinear a (fun i => x.val i) = _
  exact integerRowLinear_apply a _

private theorem singleSiteEuclideanRow_integral {D : Type*} [Fintype D]
    (U : Submodule ℝ (D → ℝ)) (a : D → ℤ) (x : euclideanSubspace U)
    (hx : x ∈ (latticeSection (standardEuclideanLattice D)
      (euclideanSubspace U)).toAddSubgroup) :
    ∃ n : ℤ, singleSiteEuclideanRow U a x = n := by
  have h := (euclideanSubspaceArrayEquiv_mem_lattice U x).mpr hx
  choose z hz using fun i => h () i
  refine ⟨∑ i, a i * z i, ?_⟩
  rw [singleSiteEuclideanRow_apply]
  simp only [euclideanSubspaceArrayEquiv_apply] at hz
  simp only [hz, Int.cast_sum, Int.cast_mul]

private theorem singleSiteEuclideanRow_eq_zero {D : Type*} [Fintype D]
    (U : Submodule ℝ (D → ℝ)) (a : D → ℤ) :
    singleSiteEuclideanRow U a = 0 ↔ U ≤ LinearMap.ker (integerRowLinear a) := by
  constructor
  · intro h x hx
    have he := LinearMap.congr_fun h
      ((euclideanSubspaceArrayEquiv U).symm (fun _ => ⟨x, hx⟩))
    change integerRowLinear a
      ((euclideanSubspaceArrayEquiv U
        ((euclideanSubspaceArrayEquiv U).symm (fun _ => ⟨x, hx⟩))) ()).val = 0 at he
    rw [ContinuousLinearEquiv.apply_symm_apply] at he
    exact he
  · intro h
    ext x
    exact h ((euclideanSubspaceArrayEquiv U x ()).property)

private theorem singleSiteEuclideanRow_character {D : Type*} [Fintype D]
    (U : Submodule ℝ (D → ℝ)) (a : D → ℤ)
    (y : euclideanSubspace U ⧸
      (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup) :
    (∏ i, CircleFourier.character
      (a i • subspaceAmbientTorus U (euclideanSubspaceTorusEquiv U y) i)) =
      quotientLinearCharacter _ (singleSiteEuclideanRow U a)
        (singleSiteEuclideanRow_integral U a) y := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ y
  rw [euclideanSubspaceTorusEquiv_mk, quotientLinearCharacter_mk,
    singleSiteEuclideanRow_apply, character_real_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [subspaceAmbientTorus_mk, euclideanSubspaceArrayEquiv_apply,
    ← AddCircle.coe_zsmul, zsmul_eq_mul]

theorem singleSiteHaar_ambientIntegerCharacter_integral
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j))
        (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (a : (Σ j, J j) → ℤ) :
    (∫ y, ambientIntegerCharacter a
      (fun i => coveredJetAmbientTorus U 1 y ⟨i.1, (), i.2⟩)
      ∂Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))) =
      if ∀ j, U j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩))
      then 1 else 0 := by
  let : ∀ j, SigmaFinite (ν j) := fun _ => inferInstance
  let : ∀ j, SigmaFinite (Measure.pi (fun _ : Unit => ν j)) := fun _ => inferInstance
  have he (y : EuclideanJetLayers U (fun _ => Unit)) :
      ambientIntegerCharacter a
        (fun i => coveredJetAmbientTorus U 1 y ⟨i.1, (), i.2⟩) =
      ∏ j, ∏ u : Unit, quotientLinearCharacter _
        (singleSiteEuclideanRow (U j) (fun i => a ⟨j, i⟩))
        (singleSiteEuclideanRow_integral (U j) (fun i => a ⟨j, i⟩)) (y j u) := by
    simp only [ambientIntegerCharacter, Fintype.prod_sigma, Fintype.prod_unique,
      coveredJetAmbientTorus, quotientIntegerCover, nsmulAddMonoidHom_apply, one_nsmul]
    apply Finset.prod_congr rfl
    intro j _
    exact singleSiteEuclideanRow_character (U j) (fun i => a ⟨j, i⟩) (y j ())
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (fun j (v : Unit → _) =>
    ∏ u : Unit, quotientLinearCharacter _
      (singleSiteEuclideanRow (U j) (fun i => a ⟨j, i⟩))
      (singleSiteEuclideanRow_integral (U j) (fun i => a ⟨j, i⟩)) (v u))]
  simp_rw [integral_fintype_prod_eq_prod]
  simp_rw [quotientLinearCharacter_integral, singleSiteEuclideanRow_eq_zero]
  simp only [Fintype.prod_unique]
  split_ifs with h
  · simp only [h, ite_true, Finset.prod_const_one]
  · obtain ⟨j, hj⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

theorem singleSiteHaar_ambientIntegerCharacter_integrable
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j))
        (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, IsProbabilityMeasure (ν j)]
    (a : (Σ j, J j) → ℤ) :
    Integrable (fun y => ambientIntegerCharacter a
      (fun i => coveredJetAmbientTorus U 1 y ⟨i.1, (), i.2⟩))
      (Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))) := by
  have : ∀ j, IsProbabilityMeasure (Measure.pi (fun _ : Unit => ν j)) :=
    fun _ => Measure.pi.instIsProbabilityMeasure _
  have : IsProbabilityMeasure
      (Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))) :=
    Measure.pi.instIsProbabilityMeasure _
  apply Integrable.of_bound _ 1
    (ae_of_all _ (fun _ => (ambientIntegerCharacter_norm a _).le))
  apply Continuous.aestronglyMeasurable
  let C : ℝ≥0 := ⟨∑ i, |(a i : ℝ)|, Finset.sum_nonneg (fun i _ => abs_nonneg _)⟩
  have hc : Continuous (ambientIntegerCharacter a) :=
    (ambientIntegerCharacter_lipschitz a C (fun i =>
      Finset.single_le_sum (fun j _ => abs_nonneg (a j : ℝ)) (Finset.mem_univ i))).continuous
  apply hc.comp
  apply continuous_pi
  intro i
  exact (continuous_apply (⟨i.1, (), i.2⟩ : JetAmbientIndex (fun _ : Fin m => Unit) J)).comp
    (coveredJetAmbientTorus_continuous (O := fun _ : Fin m => Unit) U 1)

end Erdos3.VectorPolynomial

end

end OAI
