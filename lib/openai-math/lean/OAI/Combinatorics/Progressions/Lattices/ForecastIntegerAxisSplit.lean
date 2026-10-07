/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Prod
import OAI.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleQuadratureUniformBounds

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

def AllocatedActiveIntegerAxis (L : ℕ) :=
  {a : Σ j : Fin m, Fin (n j) // L ^ (a.1.val + 1) < basisAxisScale (basis a.1) a.2}

noncomputable instance (L : ℕ) : Fintype (AllocatedActiveIntegerAxis U basis L) :=
  inferInstanceAs (Fintype {a : Σ j : Fin m, Fin (n j) //
    L ^ (a.1.val + 1) < basisAxisScale (basis a.1) a.2})

noncomputable def allocatedActiveIntegerGridScale (R : Fin m → ℝ) (L : ℕ)
    (a : AllocatedActiveIntegerAxis U basis L) : ℝ :=
  R a.val.1 * (basisAxisScale (basis a.val.1) a.val.2 : ℝ)

theorem allocatedActiveIntegerGridScale_pos {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
    (L : ℕ) (a : AllocatedActiveIntegerAxis U basis L) :
    0 < allocatedActiveIntegerGridScale U basis R L a :=
  mul_pos (hR a.val.1) (Nat.cast_pos.mpr (basisAxisScale_pos _ _))

theorem allocatedActiveIntegerGridScale_mesh {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
    {L : ℕ} (hL : 0 < L) {H q : ℝ} (hq : 0 ≤ q) (hRinv : ∀ j, (R j)⁻¹ ≤ H)
    (a : AllocatedActiveIntegerAxis U basis L) :
    q / allocatedActiveIntegerGridScale U basis R L a ≤ q * H / L := by
  have hLR : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hpow : L ≤ L ^ (a.val.1.val + 1) :=
    Nat.le_self_pow (by omega) L
  have hscale : (L : ℝ) ≤ basisAxisScale (basis a.val.1) a.val.2 := by
    exact_mod_cast hpow.trans a.property.le
  have hqR : 0 ≤ q / R a.val.1 := div_nonneg hq (hR _).le
  calc
    q / allocatedActiveIntegerGridScale U basis R L a =
        (q / R a.val.1) / basisAxisScale (basis a.val.1) a.val.2 := by
      simp only [allocatedActiveIntegerGridScale, div_div]
    _ ≤ (q / R a.val.1) / L := div_le_div_of_nonneg_left hqR hLR hscale
    _ ≤ q * H / L := by
      apply div_le_div_of_nonneg_right _ hLR.le
      simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left (hRinv _) hq

variable {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

theorem allocatedActiveIntegerGrid_complex_quadrature
    (hR : ∀ j, 0 < R j) {H q radius : ℝ} (hH : 0 ≤ H) (hq : 0 < q)
    (hRinv : ∀ j, (R j)⁻¹ ≤ H) (hradius : 0 ≤ radius)
    (hmesh : q * H / S.value ≤ 1)
    (f : (AllocatedActiveIntegerAxis U basis S.value → ℝ) → ℂ) {K : ℝ≥0}
    (hLip : LipschitzWith K f) (c : AllocatedActiveIntegerAxis U basis S.value → ℝ)
    (hsupport : ∀ x, radius < ‖x‖ → f x = 0) :
    ‖((q ^ Fintype.card (AllocatedActiveIntegerAxis U basis S.value) /
          (∏ a, allocatedActiveIntegerGridScale U basis R S.value a) : ℝ) : ℂ) *
        (∑' z : AllocatedActiveIntegerAxis U basis S.value → ℤ,
          f (fun a => (c a + q * z a) /
            allocatedActiveIntegerGridScale U basis R S.value a)) - ∫ x, f x‖ ≤
      2 * (2 * radius + 2) ^ Fintype.card (AllocatedActiveIntegerAxis U basis S.value) *
        (K : ℝ) * (q * H / S.value) := by
  apply scaledRectangular_complex_quadrature f hLip c
    (allocatedActiveIntegerGridScale U basis R S.value) hq
    (allocatedActiveIntegerGridScale_pos U basis hR S.value) hradius
    (div_nonneg (mul_nonneg hq.le hH) (Nat.cast_nonneg _)) hmesh
    (fun a => allocatedActiveIntegerGridScale_mesh U basis hR S.positive hq.le hRinv a)
    hsupport

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

noncomputable def forecastIntegerAxisMerge
    (short : AllocatedShortIntegerAxis U basis L → ℤ)
    (active : AllocatedActiveIntegerAxis U basis L → ℤ)
    (a : Σ j : Fin m, Fin (n j)) : ℤ :=
  if h : basisAxisScale (basis a.1) a.2 ≤ L ^ (a.1.val + 1)
    then short ⟨a, h⟩ else active ⟨a, Nat.lt_of_not_ge h⟩

theorem forecastIntegerAxisMerge_short
    (short : AllocatedShortIntegerAxis U basis L → ℤ)
    (active : AllocatedActiveIntegerAxis U basis L → ℤ)
    (a : AllocatedShortIntegerAxis U basis L) :
    forecastIntegerAxisMerge U basis L short active a.val = short a := by
  rw [forecastIntegerAxisMerge, dite_eq_left a.property]
  rfl

theorem forecastIntegerAxisMerge_active
    (short : AllocatedShortIntegerAxis U basis L → ℤ)
    (active : AllocatedActiveIntegerAxis U basis L → ℤ)
    (a : AllocatedActiveIntegerAxis U basis L) :
    forecastIntegerAxisMerge U basis L short active a.val = active a := by
  rw [forecastIntegerAxisMerge, dite_eq_right (Nat.not_le.mpr a.property)]
  rfl

noncomputable def forecastIntegerAxisSplit :
    ((Σ j : Fin m, Fin (n j)) → ℤ) ≃ᵐ
      ((AllocatedShortIntegerAxis U basis L → ℤ) ×
        (AllocatedActiveIntegerAxis U basis L → ℤ)) where
  toFun z := (fun a => z a.val, fun a => z a.val)
  invFun z := forecastIntegerAxisMerge U basis L z.1 z.2
  left_inv z := by
    funext a
    dsimp only [forecastIntegerAxisMerge]
    split <;> rfl
  right_inv z := by
    apply Prod.ext
    · funext a
      exact forecastIntegerAxisMerge_short U basis L z.1 z.2 a
    · funext a
      exact forecastIntegerAxisMerge_active U basis L z.1 z.2 a
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

theorem forecastIntegerAxisSplit_measurePreserving :
    MeasurePreserving (forecastIntegerAxisSplit U basis L) Measure.count
      (Measure.count.prod Measure.count) := by
  refine ⟨(forecastIntegerAxisSplit U basis L).measurable, ?_⟩
  apply Measure.ext_of_singleton
  intro z
  rw [Measure.map_apply (forecastIntegerAxisSplit U basis L).measurable
    (measurableSet_singleton z)]
  have he : (forecastIntegerAxisSplit U basis L) ⁻¹' {z} =
      {(forecastIntegerAxisSplit U basis L).symm z} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      apply (forecastIntegerAxisSplit U basis L).injective
      rw [hx, MeasurableEquiv.apply_symm_apply]
    · intro hx
      rw [hx, MeasurableEquiv.apply_symm_apply]
  rw [he, Measure.count_singleton, ← Set.singleton_prod_singleton,
    Measure.prod_prod, Measure.count_singleton, Measure.count_singleton, one_mul]

theorem forecastIntegerAxisSplit_integrable_iff
    (f : ((Σ j : Fin m, Fin (n j)) → ℤ) → ℂ) :
    Integrable (fun z => f (forecastIntegerAxisMerge U basis L z.1 z.2))
        (Measure.count.prod Measure.count) ↔ Integrable f Measure.count := by
  exact ((forecastIntegerAxisSplit_measurePreserving U basis L).symm
    (forecastIntegerAxisSplit U basis L)).integrable_comp_emb
      (forecastIntegerAxisSplit U basis L).symm.measurableEmbedding

theorem forecastIntegerAxisSplit_integral
    (f : ((Σ j : Fin m, Fin (n j)) → ℤ) → ℂ) :
    (∫ z, f z ∂Measure.count) =
      ∫ z, f (forecastIntegerAxisMerge U basis L z.1 z.2)
        ∂Measure.count.prod Measure.count := by
  exact (((forecastIntegerAxisSplit_measurePreserving U basis L).symm
    (forecastIntegerAxisSplit U basis L)).integral_comp
      (forecastIntegerAxisSplit U basis L).symm.measurableEmbedding f).symm

theorem forecastIntegerAxisSplit_integral_tsum
    (f : ((Σ j : Fin m, Fin (n j)) → ℤ) → ℂ)
    (hf : Integrable f Measure.count) :
    (∫ z, f z ∂Measure.count) =
      ∑' short : AllocatedShortIntegerAxis U basis L → ℤ,
        ∑' active : AllocatedActiveIntegerAxis U basis L → ℤ,
          f (forecastIntegerAxisMerge U basis L short active) := by
  have hi := (forecastIntegerAxisSplit_integrable_iff U basis L f).mpr hf
  rw [forecastIntegerAxisSplit_integral U basis L f, integral_prod _ hi,
    integral_countable hi.integral_prod_left]
  simp only [count_real_singleton, one_smul]
  apply tsum_congr
  intro short
  have hrow := Measure.ae_count_iff.mp hi.prod_right_ae short
  simpa only [count_real_singleton, one_smul] using integral_countable hrow

end Erdos3.VectorPolynomial

end

end OAI
