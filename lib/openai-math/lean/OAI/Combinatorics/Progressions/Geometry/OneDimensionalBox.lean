import OAI.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice

namespace OAI

section

namespace Erdos3

def scalarPiOneEquiv (A : Type*) [AddCommGroup A] : A ≃+ (Fin 1 → A) where
  toFun a _ := a
  invFun f := f 0
  left_inv _ := rfl
  right_inv f := by
    funext i
    exact congrArg f (Subsingleton.elim _ _)
  map_add' _ _ := rfl

theorem oneDimensionalBox_eq_image (a : ℤ) (L : ℕ) :
    translatedIntegerBox (fun _ : Fin 1 => a) (fun _ => L) =
      (Finset.Ico a (a + L)).image (scalarPiOneEquiv ℤ) := by
  ext x
  rw [mem_translatedIntegerBox, Finset.mem_image]
  constructor
  · intro hx
    refine ⟨x 0, Finset.mem_Ico.mpr (hx 0), ?_⟩
    exact (scalarPiOneEquiv ℤ).apply_symm_apply x
  · rintro ⟨y, hy, rfl⟩ i
    exact Finset.mem_Ico.mp hy

theorem oneDimensionalBox_norm (j : ℕ) (a : ℤ) (L : ℕ) (f : (Fin 1 → ℤ) → ℂ) :
    finiteSupportGowersNorm j (translatedIntegerBox (fun _ : Fin 1 => a) (fun _ => L)) f =
      finiteSupportGowersNorm j (Finset.Ico a (a + L)) (fun x => f (fun _ => x)) := by
  rw [oneDimensionalBox_eq_image]
  exact finiteSupportGowersNorm_addEquiv (scalarPiOneEquiv ℤ) j _ f

theorem oneDimensionalBox_correlation (a : ℤ) (L : ℕ) (f g : (Fin 1 → ℤ) → ℂ) :
    finiteCorrelation (translatedIntegerBox (fun _ : Fin 1 => a) (fun _ => L)) f g =
      finiteCorrelation (Finset.Ico a (a + L)) (fun x => f (fun _ => x)) (fun x => g (fun _ => x)) := by
  rw [oneDimensionalBox_eq_image]
  exact finiteCorrelation_addEquiv (scalarPiOneEquiv ℤ) _ f g

theorem integerInterval_cubeCount_bounds (a : ℤ) (L : ℕ) [NeZero L] (j : ℕ) :
    ((1 : ℝ) / ((j : ℝ) + 1) ^ (j + 1)) * (L : ℝ) ^ (j + 1) ≤
      Nat.card (SupportedCube j (Finset.Ico a (a + L) : Set ℤ)) ∧
    (Nat.card (SupportedCube j (Finset.Ico a (a + L) : Set ℤ)) : ℝ) ≤ (L : ℝ) ^ (j + 1) := by
  have h := translatedIntegerBox_cubeCount_bounds (fun _ : Fin 1 => L) (fun _ => a) j
  rw [oneDimensionalBox_eq_image] at h
  have he := reflectsPairSums_of_addEquiv (scalarPiOneEquiv ℤ) (Finset.Ico a (a + L) : Set ℤ)
  have hcount : Nat.card (SupportedCube j
      (((Finset.Ico a (a + L)).image (scalarPiOneEquiv ℤ)) : Set (Fin 1 → ℤ))) =
      Nat.card (SupportedCube j (Finset.Ico a (a + L) : Set ℤ)) :=
    card_supportedCube_image_eq he j
  rw [hcount, Finset.card_image_of_injective _ (scalarPiOneEquiv ℤ).injective] at h
  simpa only [Fintype.card_fin, pow_one, Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast] using h

end Erdos3

end

end OAI
