import OAI.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def scalarUnitEquiv (A : Type*) : A ≃ (Unit → A) where
  toFun a _ := a
  invFun f := f ()
  left_inv _ := rfl
  right_inv f := by
    funext u
    cases u
    rfl

theorem unitIntervalBox_eq_image (a : ℤ) (len : ℕ) :
    translatedIntegerBox (fun _ : Unit => a) (fun _ => len) =
      (Finset.Ico a (a + len)).image (scalarUnitEquiv ℤ) := by
  ext x
  rw [mem_translatedIntegerBox, Finset.mem_image]
  constructor
  · intro hx
    exact ⟨x (), Finset.mem_Ico.mpr (hx ()), (scalarUnitEquiv ℤ).apply_symm_apply x⟩
  · rintro ⟨n, hn, rfl⟩ u
    exact Finset.mem_Ico.mp hn

theorem unitIntervalBox_expect (a : ℤ) (len : ℕ) (f : (Unit → ℤ) → ℂ) :
    (𝔼 x ∈ translatedIntegerBox (fun _ : Unit => a) (fun _ => len), f x) =
      𝔼 n ∈ Finset.Ico a (a + len), f (fun _ => n) := by
  rw [unitIntervalBox_eq_image]
  exact Finset.expect_image (scalarUnitEquiv ℤ).injective.injOn

end Erdos3

end

end OAI
