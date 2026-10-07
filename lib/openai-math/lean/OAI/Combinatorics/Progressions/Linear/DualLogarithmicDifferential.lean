import Mathlib.Algebra.Module.LinearMap.Rat
import OAI.Combinatorics.Progressions.Linear.DualIdealSteps

namespace OAI

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

private theorem base_lift_congr (f g : X → DualLieAlgebra L)
    (hb : ∀ x, dualBaseLinear (f x) = dualBaseLinear (g x)) (p : FreeLieAlgebra ℚ X) :
    dualBaseLinear (FreeLieAlgebra.lift ℚ f p) = dualBaseLinear (FreeLieAlgebra.lift ℚ g p) := by
  change dualBaseLie (FreeLieAlgebra.lift ℚ f p) = dualBaseLie (FreeLieAlgebra.lift ℚ g p)
  rw [map_freeLie_lift, map_freeLie_lift]
  exact congrArg (fun a : X → L => FreeLieAlgebra.lift ℚ a p) (funext hb)

theorem dualTangentLinear_lift_add (f g k : X → DualLieAlgebra L)
    (hfg : ∀ x, dualBaseLinear (f x) = dualBaseLinear (g x))
    (hfk : ∀ x, dualBaseLinear (f x) = dualBaseLinear (k x))
    (ht : ∀ x, dualTangentLinear (f x) = dualTangentLinear (g x) + dualTangentLinear (k x))
    (p : FreeLieAlgebra ℚ X) :
    dualTangentLinear (FreeLieAlgebra.lift ℚ f p) =
      dualTangentLinear (FreeLieAlgebra.lift ℚ g p) +
        dualTangentLinear (FreeLieAlgebra.lift ℚ k p) := by
  have hbr (u v : FreeLieAlgebra ℚ X)
      (hu : dualTangentLinear (FreeLieAlgebra.lift ℚ f u) =
        dualTangentLinear (FreeLieAlgebra.lift ℚ g u) + dualTangentLinear (FreeLieAlgebra.lift ℚ k u))
      (hv : dualTangentLinear (FreeLieAlgebra.lift ℚ f v) =
        dualTangentLinear (FreeLieAlgebra.lift ℚ g v) + dualTangentLinear (FreeLieAlgebra.lift ℚ k v)) :
      dualTangentLinear (FreeLieAlgebra.lift ℚ f ⁅u, v⁆) =
        dualTangentLinear (FreeLieAlgebra.lift ℚ g ⁅u, v⁆) +
          dualTangentLinear (FreeLieAlgebra.lift ℚ k ⁅u, v⁆) := by
    simp only [LieHom.map_lie, dualTangentLinear_lie, hu, hv,
      ← base_lift_congr f g hfg, ← base_lift_congr f k hfk,
      LieRing.lie_add, LieRing.add_lie]
    abel
  apply freeLie_linear_induction (fun q =>
    dualTangentLinear (FreeLieAlgebra.lift ℚ f q) =
      dualTangentLinear (FreeLieAlgebra.lift ℚ g q) +
        dualTangentLinear (FreeLieAlgebra.lift ℚ k q))
  · simp only [map_zero, add_zero]
  · intro u v hu hv
    simp only [map_add, hu, hv]
    abel
  · intro r q hq
    simp only [map_smul, hq, smul_add]
  · intro t
    induction t with
    | ih1 x => simpa only [lieTreeEval, FreeLieAlgebra.lift_of_apply] using ht x
    | ih2 u v hu hv => exact hbr _ _ hu hv

theorem dualTangentLinear_bch_add (s : ℕ) (a a₁ a₂ b b₁ b₂ : DualLieAlgebra L)
    (ha₁ : dualBaseLinear a = dualBaseLinear a₁)
    (ha₂ : dualBaseLinear a = dualBaseLinear a₂)
    (hb₁ : dualBaseLinear b = dualBaseLinear b₁)
    (hb₂ : dualBaseLinear b = dualBaseLinear b₂)
    (hat : dualTangentLinear a = dualTangentLinear a₁ + dualTangentLinear a₂)
    (hbt : dualTangentLinear b = dualTangentLinear b₁ + dualTangentLinear b₂) :
    dualTangentLinear (lieBCH s a b) =
      dualTangentLinear (lieBCH s a₁ b₁) + dualTangentLinear (lieBCH s a₂ b₂) := by
  apply dualTangentLinear_lift_add ![a, b] ![a₁, b₁] ![a₂, b₂]
  · intro i; fin_cases i <;> assumption
  · intro i; fin_cases i <;> assumption
  · intro i; fin_cases i <;> assumption

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualLogDerivative_value_tangent (x y : L) :
    dualLogDerivative (hnil := hnil) ⟨dualConstantLie x + dualInfinitesimal y⟩ =
      dualTangentLinear (lieBCH s (dualConstantLie x + dualInfinitesimal y) (-dualConstantLie x)) := by
  change dualTangentLinear (lieBCH s (dualConstantLie x + dualInfinitesimal y)
    (-dualConstantLie (dualBaseLinear (dualConstantLie x + dualInfinitesimal y)))) = _
  rw [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero]

theorem dualLogDerivative_tangent_add (x y z : L) :
    dualLogDerivative (hnil := hnil) ⟨dualConstantLie x + dualInfinitesimal (y + z)⟩ =
      dualLogDerivative (hnil := hnil) ⟨dualConstantLie x + dualInfinitesimal y⟩ +
        dualLogDerivative (hnil := hnil) ⟨dualConstantLie x + dualInfinitesimal z⟩ := by
  simp only [dualLogDerivative_value_tangent]
  apply dualTangentLinear_bch_add <;>
    simp only [map_add, map_neg, dualBaseLinear_constant, dualBaseLinear_infinitesimal,
      dualTangentLinear_constant, dualTangentLinear_infinitesimal, add_zero, zero_add, neg_zero]

noncomputable def dualLogarithmicDifferential (x : L) : L →ₗ[ℚ] L :=
  (AddMonoidHom.mk'
    (fun y => dualLogDerivative (hnil := hnil) ⟨dualConstantLie x + dualInfinitesimal y⟩)
    (dualLogDerivative_tangent_add x)).toRatLinearMap

@[simp] theorem dualLogarithmicDifferential_apply (x y : L) :
    dualLogarithmicDifferential (hnil := hnil) x y =
      dualLogDerivative (hnil := hnil) ⟨dualConstantLie x + dualInfinitesimal y⟩ := rfl

theorem dualLogDerivative_eq_differential (z : DualGroup hnil) :
    dualLogDerivative z =
      dualLogarithmicDifferential (hnil := hnil) (dualBaseLinear z.coord) (dualTangentLinear z.coord) := by
  apply congrArg (dualLogDerivative (hnil := hnil))
  apply NilpotentLieBCHGroup.ext
  exact dualLie_decomposition z.coord

theorem dualLogarithmicDifferential_smul_real [LieAlgebra ℝ L] (x y : L) (r : ℝ) :
    dualLogarithmicDifferential (hnil := hnil) x (r • y) =
      r • dualLogarithmicDifferential (hnil := hnil) x y := by
  let T : L →ₗ[ℚ] L := r • LinearMap.id
  have hT : ∀ a b : L, b ∈ (⊤ : LieIdeal ℚ L) →
      T ⁅a, b⁆ = ⁅(LieHom.id : L →ₗ⁅ℚ⁆ L) a, T b⁆ := by
    intro a b _
    change r • ⁅a, b⁆ = ⁅a, r • b⁆
    exact (lie_smul r a b).symm
  have he := dualLinearLift_logDerivative_eq (hL := hnil) hnil ⊤ LieHom.id T hT
    (⟨dualConstantLie x + dualInfinitesimal y⟩ : DualGroup hnil) (by trivial)
    (⟨dualConstantLie x + dualInfinitesimal (r • y)⟩ : DualGroup hnil)
    (by simp only [map_add, dualLinearLift_constant, dualLinearLift_infinitesimal]; rfl)
  exact he.symm

noncomputable def dualRealLogarithmicDifferential [LieAlgebra ℝ L] (x : L) : L →ₗ[ℝ] L where
  toFun := dualLogarithmicDifferential (hnil := hnil) x
  map_add' := (dualLogarithmicDifferential x).map_add
  map_smul' r y := dualLogarithmicDifferential_smul_real x y r

end Erdos3.NilpotentLieBCHGroup

end

end OAI
