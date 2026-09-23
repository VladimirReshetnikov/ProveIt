import Surreal.Surcomplex.CircleChords
import Surreal.Surcomplex.TrigonometricOrder

/-!
# Ptolemy equality for actual cyclic quadrilaterals

Cyclic order is witnessed by strictly increasing finite angle
representatives within one full turn. The exact chord formula and a
finite trigonometric identity prove the equality clause of
`trigonometry:thm:ptolemy` and `trigonometry:eq:ptolemy` at every positive
surreal radius. No motion or continuity of an ordinary real parameter
is used to define cyclic order.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- The sine addition identity underlying Ptolemy equality, for arbitrary actual finite angles. -/
theorem finiteSin_ptolemy_identity (α β γ : SignSequence.FiniteElement.{u}) :
    finiteSin (α + β) * finiteSin (β + γ) =
      finiteSin α * finiteSin γ + finiteSin β * finiteSin (α + β + γ) := by
  simp only [finiteSin_add, finiteCos_add]
  linear_combination finiteSin α * finiteSin γ * finiteCos_sq_add_finiteSin_sq β

/-- Four finite representatives in strict cyclic order, without passing through a full turn. -/
def CyclicAngleOrder (θ₁ θ₂ θ₃ θ₄ : SignSequence.FiniteElement.{u}) : Prop :=
  θ₁.val < θ₂.val ∧ θ₂.val < θ₃.val ∧ θ₃.val < θ₄.val ∧
    θ₄.val < θ₁.val + SignSequence.ofReal (2 * Real.pi)

/-- A strictly positive representative difference below one full turn has positive half-angle sine. -/
theorem finiteSin_half_sub_pos_of_lt (α β : SignSequence.FiniteElement.{u})
    (hlt : α.val < β.val)
    (hfull : β.val < α.val + SignSequence.ofReal (2 * Real.pi)) :
    0 < finiteSin (finiteHalf (β - α)) := by
  apply finiteSin_pos_of_mem_Ioo
  rw [val_finiteHalf]
  change 0 < (β.val - α.val) / 2 ∧
    (β.val - α.val) / 2 < SignSequence.ofReal Real.pi
  rw [map_mul, map_ofNat] at hfull
  constructor <;> linarith only [hlt, hfull]

/-- The chord between increasing representatives uses the positive half-angle sine. -/
theorem modulus_circlePoint_sub_of_lt (O : Surcomplex.{u}) (R : SignSequence.{u})
    (hR : 0 ≤ R) (α β : SignSequence.FiniteElement.{u})
    (hlt : α.val < β.val)
    (hfull : β.val < α.val + SignSequence.ofReal (2 * Real.pi)) :
    modulus (circlePoint O R α - circlePoint O R β) =
      2 * R * finiteSin (finiteHalf (β - α)) := by
  rw [← neg_sub (circlePoint O R β) (circlePoint O R α), modulus_neg,
    modulus_circlePoint_sub O R hR β α,
    abs_of_pos (finiteSin_half_sub_pos_of_lt α β hlt hfull)]

/-- Distinct representatives separated by less than one turn yield distinct points at positive radius. -/
theorem circlePoint_ne_of_lt (O : Surcomplex.{u}) (R : SignSequence.{u})
    (hR : 0 < R) (α β : SignSequence.FiniteElement.{u})
    (hlt : α.val < β.val)
    (hfull : β.val < α.val + SignSequence.ofReal (2 * Real.pi)) :
    circlePoint O R α ≠ circlePoint O R β := by
  have hp : 0 < modulus (circlePoint O R α - circlePoint O R β) := by
    rw [modulus_circlePoint_sub_of_lt O R hR.le α β hlt hfull]
    exact mul_pos (mul_pos (by norm_num) hR)
      (finiteSin_half_sub_pos_of_lt α β hlt hfull)
  intro he
  rw [he, sub_self, modulus_zero] at hp
  exact lt_irrefl _ hp

/-- Strict cyclic order certifies all six pairwise inequalities of the four circle points. -/
theorem circlePoints_distinct_of_cyclicAngleOrder (O : Surcomplex.{u})
    (R : SignSequence.{u}) (hR : 0 < R)
    (θ₁ θ₂ θ₃ θ₄ : SignSequence.FiniteElement.{u})
    (h : CyclicAngleOrder θ₁ θ₂ θ₃ θ₄) :
    circlePoint O R θ₁ ≠ circlePoint O R θ₂ ∧
      circlePoint O R θ₁ ≠ circlePoint O R θ₃ ∧
      circlePoint O R θ₁ ≠ circlePoint O R θ₄ ∧
      circlePoint O R θ₂ ≠ circlePoint O R θ₃ ∧
      circlePoint O R θ₂ ≠ circlePoint O R θ₄ ∧
      circlePoint O R θ₃ ≠ circlePoint O R θ₄ := by
  obtain ⟨h12, h23, h34, h41⟩ := h
  refine ⟨circlePoint_ne_of_lt O R hR θ₁ θ₂ h12 (by linarith),
    circlePoint_ne_of_lt O R hR θ₁ θ₃ (by linarith) (by linarith),
    circlePoint_ne_of_lt O R hR θ₁ θ₄ (by linarith) h41,
    circlePoint_ne_of_lt O R hR θ₂ θ₃ h23 (by linarith),
    circlePoint_ne_of_lt O R hR θ₂ θ₄ (by linarith) (by linarith),
    circlePoint_ne_of_lt O R hR θ₃ θ₄ h34 (by linarith)⟩

private theorem half_sub_add_half_sub (α β γ : SignSequence.FiniteElement.{u}) :
    finiteHalf (β - α) + finiteHalf (γ - β) = finiteHalf (γ - α) := by
  unfold finiteHalf
  ring

/-- Ptolemy equality for finite representatives in cyclic order at every positive surreal radius. -/
theorem ptolemy_eq_of_cyclicAngleOrder (O : Surcomplex.{u}) (R : SignSequence.{u})
    (hR : 0 < R) (θ₁ θ₂ θ₃ θ₄ : SignSequence.FiniteElement.{u})
    (h : CyclicAngleOrder θ₁ θ₂ θ₃ θ₄) :
    modulus (circlePoint O R θ₁ - circlePoint O R θ₃) *
        modulus (circlePoint O R θ₂ - circlePoint O R θ₄) =
      modulus (circlePoint O R θ₁ - circlePoint O R θ₂) *
          modulus (circlePoint O R θ₃ - circlePoint O R θ₄) +
        modulus (circlePoint O R θ₁ - circlePoint O R θ₄) *
          modulus (circlePoint O R θ₂ - circlePoint O R θ₃) := by
  obtain ⟨h12, h23, h34, h41⟩ := h
  rw [modulus_circlePoint_sub_of_lt O R hR.le θ₁ θ₃ (by linarith) (by linarith),
    modulus_circlePoint_sub_of_lt O R hR.le θ₂ θ₄ (by linarith) (by linarith),
    modulus_circlePoint_sub_of_lt O R hR.le θ₁ θ₂ h12 (by linarith),
    modulus_circlePoint_sub_of_lt O R hR.le θ₃ θ₄ h34 (by linarith),
    modulus_circlePoint_sub_of_lt O R hR.le θ₁ θ₄ (by linarith) h41,
    modulus_circlePoint_sub_of_lt O R hR.le θ₂ θ₃ h23 (by linarith)]
  have hs := finiteSin_ptolemy_identity (finiteHalf (θ₂ - θ₁))
    (finiteHalf (θ₃ - θ₂)) (finiteHalf (θ₄ - θ₃))
  rw [half_sub_add_half_sub θ₁ θ₂ θ₃, half_sub_add_half_sub θ₂ θ₃ θ₄,
    half_sub_add_half_sub θ₁ θ₃ θ₄] at hs
  linear_combination 4 * R ^ 2 * hs

/-- Cyclic order on an actual positive-radius circle is witnessed by finite angle representatives. -/
def CyclicallyOrderedOnCircle (O : Surcomplex.{u}) (R : SignSequence.{u})
    (z₁ z₂ z₃ z₄ : Surcomplex.{u}) : Prop :=
  0 < R ∧ ∃ θ₁ θ₂ θ₃ θ₄ : SignSequence.FiniteElement.{u},
    CyclicAngleOrder θ₁ θ₂ θ₃ θ₄ ∧ z₁ = circlePoint O R θ₁ ∧
      z₂ = circlePoint O R θ₂ ∧ z₃ = circlePoint O R θ₃ ∧ z₄ = circlePoint O R θ₄

/-- The finite-lift cyclic-order predicate guarantees four distinct actual points. -/
theorem distinct_of_cyclicallyOrderedOnCircle (O : Surcomplex.{u}) (R : SignSequence.{u})
    (z₁ z₂ z₃ z₄ : Surcomplex.{u}) (h : CyclicallyOrderedOnCircle O R z₁ z₂ z₃ z₄) :
    z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₁ ≠ z₄ ∧ z₂ ≠ z₃ ∧ z₂ ≠ z₄ ∧ z₃ ≠ z₄ := by
  obtain ⟨hR, θ₁, θ₂, θ₃, θ₄, ho, rfl, rfl, rfl, rfl⟩ := h
  exact circlePoints_distinct_of_cyclicAngleOrder O R hR θ₁ θ₂ θ₃ θ₄ ho

/-- Ptolemy equality for any four actual points witnessed to be cyclically ordered on a circle. -/
theorem ptolemy_eq_of_cyclicallyOrderedOnCircle (O : Surcomplex.{u}) (R : SignSequence.{u})
    (z₁ z₂ z₃ z₄ : Surcomplex.{u}) (h : CyclicallyOrderedOnCircle O R z₁ z₂ z₃ z₄) :
    modulus (z₁ - z₃) * modulus (z₂ - z₄) =
      modulus (z₁ - z₂) * modulus (z₃ - z₄) + modulus (z₁ - z₄) * modulus (z₂ - z₃) := by
  obtain ⟨hR, θ₁, θ₂, θ₃, θ₄, ho, rfl, rfl, rfl, rfl⟩ := h
  exact ptolemy_eq_of_cyclicAngleOrder O R hR θ₁ θ₂ θ₃ θ₄ ho

end
end Surreal.Surcomplex
