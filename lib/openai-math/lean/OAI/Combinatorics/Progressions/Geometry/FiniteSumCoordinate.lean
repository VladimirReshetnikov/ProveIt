import OAI.Combinatorics.Progressions.Polynomial.WeightedPolynomialRestriction

namespace OAI

section

namespace Erdos3

variable {σ : Type*} [DecidableEq σ]

def coordinateAdditionInputs (i : σ) (x : Option σ → ℤ) : Fin 3 → σ → ℤ :=
  ![Function.update (fun j => x (some j)) i (x (some i) + x none),
    fun j => x (some j), Function.update (fun j => x (some j)) i (x none)]

@[simp] theorem coordinateAdditionInputs_sum (i : σ) (x : Option σ → ℤ) :
    coordinateAdditionInputs i x 0 =
      Function.update (fun j => x (some j)) i (x (some i) + x none) := rfl

@[simp] theorem coordinateAdditionInputs_left (i : σ) (x : Option σ → ℤ) :
    coordinateAdditionInputs i x 1 = (fun j => x (some j)) := rfl

@[simp] theorem coordinateAdditionInputs_right (i : σ) (x : Option σ → ℤ) :
    coordinateAdditionInputs i x 2 = Function.update (fun j => x (some j)) i (x none) := rfl

noncomputable def coordinateAdditionProduct {I : Type*} (f : I → (σ → ℤ) → ℂ)
    (a : Fin 3 → I) (i : σ) (x : Option σ → ℤ) : ℂ :=
  f (a 0) (coordinateAdditionInputs i x 0) * star (f (a 1) (coordinateAdditionInputs i x 1)) *
    star (f (a 2) (coordinateAdditionInputs i x 2))

end Erdos3

end

section

namespace Erdos3

variable {σ : Type*} [DecidableEq σ]

def coordinateConstantInput (i : σ) (h n : ℤ) : σ → ℤ :=
  Function.update (fun _ => n) i h

def coordinatePairInput (i : σ) (a b n : ℤ) : Option σ → ℤ
  | none => b
  | some j => coordinateConstantInput i a n j

theorem coordinatePairInput_sum (i : σ) (a b n : ℤ) :
    coordinateAdditionInputs i (coordinatePairInput i a b n) 0 =
      coordinateConstantInput i (a + b) n := by
  simp [coordinateAdditionInputs, coordinatePairInput, coordinateConstantInput]

theorem coordinatePairInput_left (i : σ) (a b n : ℤ) :
    coordinateAdditionInputs i (coordinatePairInput i a b n) 1 = coordinateConstantInput i a n := rfl

theorem coordinatePairInput_right (i : σ) (a b n : ℤ) :
    coordinateAdditionInputs i (coordinatePairInput i a b n) 2 = coordinateConstantInput i b n := by
  simp [coordinateAdditionInputs, coordinatePairInput, coordinateConstantInput]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} [DecidableEq σ] {n : ℕ}

def finiteSumCoordinateInput (i : σ) (x : (σ ⊕ Fin n) → ℤ) : σ → ℤ :=
  Function.update (fun j => x (Sum.inl j)) i (∑ a : Fin n, x (Sum.inr a))

def finiteTermCoordinateInput (i : σ) (a : Fin n) (x : (σ ⊕ Fin n) → ℤ) : σ → ℤ :=
  Function.update (fun j => x (Sum.inl j)) i (x (Sum.inr a))

def finiteSumCoordinateHom (i j : σ) : (((σ ⊕ Fin n) → ℤ) →+ ℤ) where
  toFun x := finiteSumCoordinateInput i x j
  map_zero' := by simp [finiteSumCoordinateInput]
  map_add' x y := by
    simp only [finiteSumCoordinateInput, Function.update_apply, Pi.add_apply,
      Finset.sum_add_distrib]
    split_ifs <;> rfl

def finiteTermCoordinateHom (i : σ) (a : Fin n) (j : σ) : (((σ ⊕ Fin n) → ℤ) →+ ℤ) where
  toFun x := finiteTermCoordinateInput i a x j
  map_zero' := by simp [finiteTermCoordinateInput]
  map_add' x y := by
    simp only [finiteTermCoordinateInput, Function.update_apply, Pi.add_apply]
    split_ifs <;> rfl

theorem finiteSumCoordinateInput_one (i : σ) (x : (σ ⊕ Fin 1) → ℤ) :
    finiteSumCoordinateInput i x = finiteTermCoordinateInput i 0 x := by
  simp only [finiteSumCoordinateInput, finiteTermCoordinateInput, Fin.sum_univ_one]

end Erdos3

end

end OAI
