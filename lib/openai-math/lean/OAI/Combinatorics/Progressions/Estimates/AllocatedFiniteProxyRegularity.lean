import OAI.Combinatorics.Progressions.Geometry.AllocatedProxyOutputSupport

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m,
  fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "bound" => NNReal.mk (Real.exp (allocatedDensityLog (G := G) B α O P))
  (le_of_lt (Real.exp_pos _))
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)
local notation "lip" => (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap

local notation "input" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬grid a)
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "radius" => Real.exp (allocatedJetSupportLog (G := G) B α O P)

include hR hσ hM hi hP hMP hRP hRi hσi hcount in
theorem allocatedFiniteLongJetDensity_regularity (hσ1 : ∀ j, σ j ≤ 1)
    {Ω : Type*} [Fintype Ω] (weights : FiniteProbabilityWeights Ω) (F : Ω → (input → ℝ))
    (hF : ∀ v, weights.weight v ≠ 0 → ‖F v‖ ≤ 1) :
    let density := fun z : output → ℝ => weights.mean
      (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA (F v) z)
    (∀ z, |density z| ≤ cap) ∧ LipschitzWith lip density ∧
      (∀ z, radius < ‖z‖ → density z = 0) ∧ Integrable density := by
  intro density
  have hb (v) := allocatedNormalizedLongJetDensity_output_bounds B U basis hR hσ S x
    rows s hA hM hi hP hMP hRP hRi hσi hcount u hσ1 (F v)
  refine ⟨?_, weights.mean_lipschitz _ (fun v _ => (hb v).2), ?_, ?_⟩
  · intro z
    apply weights.abs_mean_le_on_support
    intro v _
    rw [abs_of_nonneg ((hb v).1 z).1]
    exact ((hb v).1 z).2
  · intro z hz
    apply Finset.sum_eq_zero
    intro v _
    by_cases hv : weights.weight v = 0
    · simp only [hv, zero_mul]
    · have he := allocatedNormalizedLongJetDensity_zero_off_ball B U basis hR hσ S x
        rows s hA hM hi hP hMP hRP hRi hσi hcount u hσ1 (F v) (hF v hv) z hz
      exact mul_eq_zero_of_right _ he
  · apply integrable_finsetSum
    intro v _
    exact ((allocatedNormalizedLongJetDensity_probability B U basis hR hσ S x u
      rows s hA hσ1 (F v)).2.1).const_mul (weights.weight v)

end Erdos3.VectorPolynomial

end

end OAI
