import OAI.Combinatorics.Progressions.Estimates.AllocatedProxyOutputBounds
import OAI.Combinatorics.Progressions.Linear.AllocatedKernelSupport

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [dG : DecidableEq G]
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
local notation "radius" => Real.exp (allocatedJetSupportLog (G := G) B α O P)
local notation "input" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬grid a)
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

include hR hσ hM hi hP hMP hRP hRi hσi hcount

theorem allocatedNormalizedLongJetFactor_zero_off_ball (hσ1 : ∀ j, σ j ≤ 1)
    (y : input → ℝ) (hy : ‖y‖ ≤ 1) (a : {a // ¬grid a})
    (z : O a.val.1 → ℝ) (hz : radius < ‖z‖) :
    allocatedNormalizedLongJetFactor B U basis S x u rows s hA y a z = 0 := by
  cases Subsingleton.elim dG (Classical.decEq G)
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i =>
    exact allocatedContinuousKernelDensity_zero_off_box B U basis hR hσ S x rows s hA
      hM hi hP hMP hRP hRi hσi hcount u hσ1 j i y hy z hz
  | inr i =>
    have hr := allocatedKernelRadius_bound B U basis hR hσ S x rows s hA
      hM hi hP hMP hRP hRi hσi hcount j
      (Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i))
    exact allocatedIntegerKernelDensity_support_data B U basis hR hσ S j x u
      (rows j) (s j) (hA j) i (hσ1 j) y hy z (hr.trans_lt hz)

theorem allocatedNormalizedLongJetDensity_zero_off_ball (hσ1 : ∀ j, σ j ≤ 1)
    (y : input → ℝ) (hy : ‖y‖ ≤ 1) (v : output → ℝ) (hv : radius < ‖v‖) :
    allocatedNormalizedLongJetDensity B U basis S x u rows s hA y v = 0 :=
  sigmaAxisWeight_zero_outside _ (Real.exp_pos _).le
    (allocatedNormalizedLongJetFactor_zero_off_ball B U basis hR hσ S x rows s hA
      hM hi hP hMP hRP hRi hσi hcount u hσ1 y hy) v hv

theorem allocatedContinuousLongJetProxy_zero_off_ball (hσ1 : ∀ j, σ j ≤ 1)
    (v : output → ℝ) (hv : radius < ‖v‖) :
    allocatedContinuousLongJetProxy B U basis S x u rows s hA v = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [jointBooleanSource_ae_closedBall (fun a : {a // ¬grid a} => B a.val)
    (fun a => layerSamplerDegree I n a.val)] with y hy
  exact allocatedNormalizedLongJetDensity_zero_off_ball B U basis hR hσ S x rows s hA
    hM hi hP hMP hRP hRi hσi hcount u hσ1 y
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hy) v hv

end Erdos3.VectorPolynomial

end

end OAI
