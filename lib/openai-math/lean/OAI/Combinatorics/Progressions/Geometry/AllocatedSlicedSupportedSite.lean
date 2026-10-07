/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Isometry
import OAI.Combinatorics.Progressions.Estimates.AllocatedSlicedBooleanSite
import OAI.Combinatorics.Progressions.Estimates.PreparedScalarStructuralBasePower

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

theorem exists_allocatedSlicedIdeal_supported_site_expansion
    [∀ j, DecidableEq (I j)]
    (O : ℕ) (hO : Fintype.card Row ≤ O)
    (hB : ∀ a : {a // ¬grid a}, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (degree a.val) → ℝ)
    {a δ P ε : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hP : 0 ≤ P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (radius : ℝ≥0) (hradius : 0 < radius) (hε : 0 < ε)
    (hHP : 2 * (radius : ℝ) ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    let Q := slicedJointDensityLogBudget O m P + P
    let C : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * radius)
    ∃ χ : (LayerSamplerAxis I n → ℝ) → ℝ,
      (∀ v, (∀ d, |v d| ≤ (radius : ℝ)) → χ v = 1) ∧
    ∃ z : ℕ, (z : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      ∃ (c : (Finset (Fin 1) × LayerSamplerAxis I n → Fin z) → ℂ)
        (f : (Finset (Fin 1) × LayerSamplerAxis I n → Fin z) → Finset (Fin 1) → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ k, ‖c k‖) ≤ Real.exp ((2 * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q) ∧
        (∀ k s x, ‖f k s x‖ ≤ 1) ∧
        (∀ k s, LipschitzWith (NNReal.mk (Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12)) (Real.exp_nonneg _) + C) (f k s)) ∧
        (∀ k s v, (∃ d, 2 * (radius : ℝ) < |v d|) → f k s v = 0) ∧
        ∀ x : Finset (Fin 1) → LayerSamplerAxis I n → ℝ,
          ‖(∏ s, (χ (x s) : ℂ)) * (allocatedSlicedAveragedIdealDensity B U basis S hB lower width
              (oneCubeSiteRestriction grid x) : ℂ) - ∑ k, c k * ∏ s, f k s (x s)‖ ≤ ε := by
  intro Q C
  obtain ⟨χ, _, _, hχ, hone, hsupport, hLip⟩ :=
    exists_normalized_site_cutoff (D := LayerSamplerAxis I n) radius hradius
  have hχC : LipschitzWith C (fun v => (χ v : ℂ)) := by
    simpa only [one_mul, Function.comp_def] using Complex.isometry_ofReal.lipschitzWith.comp hLip
  have hχ1 (s : Finset (Fin 1)) (v) : ‖(χ v : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ v).1] using (hχ v).2
  obtain ⟨z, hz, c, f, hc, hf, hLf, herr⟩ :=
    exists_allocatedSlicedIdeal_boolean_site_expansion B U basis S O hO hB lower width
      ha hδ hP haP hδP hprincipal hw hl (mul_pos (by norm_num) hradius) hε hHP hεP
  let g := bufferedSiteFactor (fun (_ : Finset (Fin 1)) (v : LayerSamplerAxis I n → ℝ) => v)
    (fun _ v => (χ v : ℂ)) f
  refine ⟨χ, hone, z, hz, c, g, hc, ?_, ?_, ?_, ?_⟩
  · exact bufferedSiteFactor_bound _ _ f hχ1 hf
  · intro k s
    have he := bufferedSiteFactor_lipschitz _ _ f
      (K := NNReal.mk (Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12)) (Real.exp_nonneg _))
      (L := 1) (C := C) (fun _ => LipschitzWith.id) (fun _ => hχC) hLf hχ1 hf k s
    rw [mul_one] at he
    convert he using 1
    rfl
  · intro k s v hv
    have hzero : χ v = 0 := by
      by_contra hn
      obtain ⟨d, hd⟩ := hv
      exact (not_lt_of_ge (hsupport v hn d)) hd
    simp only [g, bufferedSiteFactor, hzero, Complex.ofReal_zero, zero_mul]
  · intro x
    apply bufferedSiteExpansion_error _ _ _ c f hε.le hχ1
      (fun _ v hv d => hsupport v (by exact_mod_cast hv) d) herr x

end Erdos3.VectorPolynomial

end

end OAI
