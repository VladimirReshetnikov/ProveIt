import GRHArticle.SingularModuli.ReducedForms
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Order discriminants and the two inert-prime congruence conditions

A positive discriminant magnitude occurs among the primitive reduced forms
exactly when it is 0 or 3 modulo 4. The index `n` represents magnitude `n+1`.
-/

namespace GRHArticle.SingularModuli

/-- Every negative integer congruent to 0 or 1 modulo 4 has a primitive
reduced representative with leading coefficient 1. -/
theorem reducedForms_nonempty_iff_residue (D : ℕ+) :
    (reducedForms D).Nonempty ↔ (D : ℕ)%4 = 0 ∨ (D : ℕ)%4 = 3 := by
  constructor
  · rintro ⟨f,hf⟩
    have hd := ((mem_reducedForms_iff D f).mp hf).1
    have hpar : f.b%2 = 0 ∨ f.b%2 = 1 := by omega
    rcases hpar with h | h
    · have he : f.b^2 = 4 * (f.b/2)^2 := by
        have := Int.emod_add_mul_ediv f.b 2
        rw [h,zero_add] at this
        conv_lhs => rw [← this]
        ring
      rw [he] at hd
      left
      have hd' : (D:ℤ) = 4*((f.a:ℤ)*f.c-(f.b/2)^2) := by linarith only [hd]
      omega
    · have he : f.b^2 = 1 + 4 * ((f.b/2)^2 + f.b/2) := by
        have := Int.emod_add_mul_ediv f.b 2
        rw [h] at this
        conv_lhs => rw [← this]
        ring
      rw [he] at hd
      right
      have hd' : (D:ℤ) = 4*((f.a:ℤ)*f.c-((f.b/2)^2+f.b/2))-1 := by linarith only [hd]
      omega
  · intro h
    have hp := D.pos
    rcases h with h | h
    · let c : ℤ := (D:ℤ)/4
      refine ⟨⟨1,0,c⟩,(mem_reducedForms_iff D _).mpr ?_⟩
      simp [IsPrimitiveReducedForm, c]; omega
    · let c : ℤ := ((D:ℤ)+1)/4
      refine ⟨⟨1,1,c⟩,(mem_reducedForms_iff D _).mpr ?_⟩
      simp [IsPrimitiveReducedForm, c]; omega

/-- At index `n`, test whether the magnitude `n+1` gives an order discriminant. -/
def orderDiscriminantIndex (n : ℕ) : Prop := (n+1)%4 = 0 ∨ (n+1)%4 = 3

instance decidableOrderDiscriminantIndex : DecidablePred orderDiscriminantIndex := fun n ↦ by
  unfold orderDiscriminantIndex
  infer_instance

/-- Either 7 or 13 is a quadratic nonresidue test for the negative discriminant. -/
def nearFullDiscriminantIndex (n : ℕ) : Prop :=
  orderDiscriminantIndex n ∧
    ((¬∃ a : ZMod 7, -((n+1:ℕ) : ZMod 7) = a*a) ∨
     (¬∃ a : ZMod 13, -((n+1:ℕ) : ZMod 13) = a*a))

instance decidableNearFullDiscriminantIndex : DecidablePred nearFullDiscriminantIndex := fun n ↦ by
  unfold nearFullDiscriminantIndex
  infer_instance

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

/-- The executable congruence test uses the actual Legendre symbols of the
negative discriminant. -/
theorem nearFullDiscriminantIndex_iff (n : ℕ) :
    nearFullDiscriminantIndex n ↔ (reducedForms n.succPNat).Nonempty ∧
      (legendreSym 7 (-((n+1:ℕ) : ℤ)) = -1 ∨ legendreSym 13 (-((n+1:ℕ) : ℤ)) = -1) := by
  rw [reducedForms_nonempty_iff_residue, legendreSym.eq_neg_one_iff, legendreSym.eq_neg_one_iff]
  simp only [nearFullDiscriminantIndex, orderDiscriminantIndex, IsSquare, Int.cast_neg,
    Int.cast_natCast, Nat.succPNat_coe]

theorem orderDiscriminantIndex_periodic : Function.Periodic orderDiscriminantIndex 364 :=
  fun n ↦ propext (by unfold orderDiscriminantIndex; omega)

theorem nearFullDiscriminantIndex_periodic : Function.Periodic nearFullDiscriminantIndex 364 := by
  intro n
  apply propext
  have h (p : ℕ) [NeZero p] (hp : (364:ZMod p) = 0) :
      ((n+364+1:ℕ):ZMod p) = ((n+1:ℕ):ZMod p) := by push_cast; rw [hp, add_zero]
  simp only [nearFullDiscriminantIndex, orderDiscriminantIndex_periodic n,
    h 7 (by decide), h 13 (by decide)]

/-- There are 182 order discriminants and 126 members of the specified
congruence families in each period of length 364. -/
theorem nearFullDiscriminantIndex_period_counts :
    Nat.count orderDiscriminantIndex 364 = 182 ∧ Nat.count nearFullDiscriminantIndex 364 = 126 := by
  decide +kernel

end GRHArticle.SingularModuli
