/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Lattices.NativeIntegerSelfEquivalence

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def BinaryTensorIndex (I : Type*) : ℕ → Type _
  | 0 => I
  | n + 1 => BinaryTensorIndex I n × BinaryTensorIndex I n

instance BinaryTensorIndex.fintype (I : Type*) [Fintype I] (n : ℕ) : Fintype (BinaryTensorIndex I n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype I)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (BinaryTensorIndex I n × BinaryTensorIndex I n))

variable {σ I : Type*} [DecidableEq σ]

def coordinateTranslatedInput (l : List σ) (x : Option σ → ℤ) (i : σ) : ℤ :=
  x (some i) + if i ∈ l then x none else 0

def coordinateTranslationHom (l : List σ) (j : Option σ) : ((Option σ → ℤ) →+ ℤ) where
  toFun x := match j with
    | none => x none
    | some i => coordinateTranslatedInput l x i
  map_zero' := by cases j <;> simp [coordinateTranslatedInput]
  map_add' x y := by
    cases j with
    | none => rfl
    | some i =>
      simp only [coordinateTranslatedInput, Pi.add_apply]
      split_ifs <;> ring

def coordinateReplaceIndex (i : σ) (j : Option σ) : Option σ :=
  if j = some i then none else j

def coordinateReplaceInput (i : σ) (x : Option σ → ℤ) : Option σ → ℤ :=
  fun j => x (coordinateReplaceIndex i j)

theorem coordinateTranslation_sum (l : List σ) (i : σ) (hi : i ∉ l) (x : Option σ → ℤ) :
    coordinateAdditionInputs i (fun j => coordinateTranslationHom l j x) 0 =
      coordinateTranslatedInput (i :: l) x := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [coordinateAdditionInputs, coordinateTranslationHom, coordinateTranslatedInput, hi]
  · simp [coordinateAdditionInputs, coordinateTranslationHom, coordinateTranslatedInput, hj]

theorem coordinateTranslation_left (l : List σ) (i : σ) (x : Option σ → ℤ) :
    coordinateAdditionInputs i (fun j => coordinateTranslationHom l j x) 1 =
      coordinateTranslatedInput l x := rfl

theorem coordinateTranslation_right (l : List σ) (i : σ) (hi : i ∉ l) (x : Option σ → ℤ) :
    coordinateAdditionInputs i (fun j => coordinateTranslationHom l j x) 2 =
      coordinateTranslatedInput l (coordinateReplaceInput i x) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [coordinateAdditionInputs, coordinateTranslationHom, coordinateTranslatedInput,
      coordinateReplaceInput, coordinateReplaceIndex, hi]
  · simp [coordinateAdditionInputs, coordinateTranslationHom, coordinateTranslatedInput,
      coordinateReplaceInput, coordinateReplaceIndex, hj]

noncomputable def coordinateTranslationExpansion (f : I → (σ → ℤ) → ℂ) :
    (l : List σ) → BinaryTensorIndex I l.length → (Option σ → ℤ) → ℂ
  | [], a, x => f a (fun j => x (some j))
  | i :: l, a, x => coordinateTranslationExpansion f l a.1 x *
      coordinateTranslationExpansion f l a.2 (coordinateReplaceInput i x)

theorem coordinateTranslationExpansion_unit [Fintype I] (f : I → (σ → ℤ) → ℂ)
    (hunit : ∀ x, ∑ i, ‖f i x‖ ^ 2 = 1) (l : List σ) (x : Option σ → ℤ) :
    ∑ a : BinaryTensorIndex I l.length, ‖coordinateTranslationExpansion f l a x‖ ^ 2 = 1 := by
  induction l generalizing x with
  | nil => exact hunit _
  | cons i l ih =>
    change (∑ a : BinaryTensorIndex I l.length × BinaryTensorIndex I l.length,
      ‖coordinateTranslationExpansion f l a.1 x *
        coordinateTranslationExpansion f l a.2 (coordinateReplaceInput i x)‖ ^ 2) = 1
    simp only [Fintype.sum_prod_type, norm_mul, mul_pow, ← Finset.mul_sum, ih, mul_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def TernaryTensorIndex (I : Type*) : ℕ → Type _
  | 0 => I
  | n + 1 => TernaryTensorIndex I n × (TernaryTensorIndex I n × TernaryTensorIndex I n)

instance TernaryTensorIndex.fintype (I : Type*) [Fintype I] (n : ℕ) : Fintype (TernaryTensorIndex I n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype I)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (TernaryTensorIndex I n ×
      (TernaryTensorIndex I n × TernaryTensorIndex I n)))

variable {σ I : Type*} [DecidableEq σ]

def ternaryCoordinateInput (l : List σ) (x : (Fin 3 × σ) → ℤ) (j : σ) : ℤ :=
  if j ∈ l then ∑ a : Fin 3, x (a, j) else x (0, j)

def ternaryCoordinateHom (l : List σ) (j : σ) : (((Fin 3 × σ) → ℤ) →+ ℤ) where
  toFun x := ternaryCoordinateInput l x j
  map_zero' := by simp [ternaryCoordinateInput]
  map_add' x y := by
    simp only [ternaryCoordinateInput, Pi.add_apply, Finset.sum_add_distrib]
    split_ifs <;> rfl

def ternaryReplaceIndex (i : σ) (a : Fin 3) (j : Fin 3 × σ) : Fin 3 × σ :=
  if j = (0, i) then (a, i) else j

def ternaryReplaceInput (i : σ) (a : Fin 3) (x : (Fin 3 × σ) → ℤ) : (Fin 3 × σ) → ℤ :=
  fun j => x (ternaryReplaceIndex i a j)

theorem ternaryCoordinateInput_replace (l : List σ) (i : σ) (hi : i ∉ l)
    (a : Fin 3) (x : (Fin 3 × σ) → ℤ) :
    ternaryCoordinateInput l (ternaryReplaceInput i a x) =
      Function.update (ternaryCoordinateInput l x) i (x (a, i)) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [ternaryCoordinateInput, ternaryReplaceInput, ternaryReplaceIndex, hi]
  · simp [ternaryCoordinateInput, ternaryReplaceInput, ternaryReplaceIndex, hj]

theorem ternaryCoordinateInput_cons (l : List σ) (i : σ)
    (x : (Fin 3 × σ) → ℤ) :
    ternaryCoordinateInput (i :: l) x = Function.update (ternaryCoordinateInput l x) i
      (x (0, i) + (x (1, i) + x (2, i))) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [ternaryCoordinateInput, Fin.sum_univ_three, add_assoc]
  · simp [ternaryCoordinateInput, hj]

noncomputable def ternaryCoordinateExpansion (f : I → (σ → ℤ) → ℂ) :
    (l : List σ) → TernaryTensorIndex I l.length → (((Fin 3 × σ) → ℤ) → ℂ)
  | [], a, x => f a (fun j => x (0, j))
  | i :: l, a, x => ternaryCoordinateExpansion f l a.1 x *
    (ternaryCoordinateExpansion f l a.2.1 (ternaryReplaceInput i 1 x) *
      ternaryCoordinateExpansion f l a.2.2 (ternaryReplaceInput i 2 x))

theorem ternaryCoordinateExpansion_unit [Fintype I] (f : I → (σ → ℤ) → ℂ)
    (hf : ∀ x, ∑ a, ‖f a x‖ ^ 2 = 1) (l : List σ) (x : (Fin 3 × σ) → ℤ) :
    ∑ a : TernaryTensorIndex I l.length, ‖ternaryCoordinateExpansion f l a x‖ ^ 2 = 1 := by
  induction l generalizing x with
  | nil => exact hf _
  | cons i l ih =>
    change (∑ a : TernaryTensorIndex I l.length ×
      (TernaryTensorIndex I l.length × TernaryTensorIndex I l.length),
      ‖ternaryCoordinateExpansion f l a.1 x *
        (ternaryCoordinateExpansion f l a.2.1 (ternaryReplaceInput i 1 x) *
          ternaryCoordinateExpansion f l a.2.2 (ternaryReplaceInput i 2 x))‖ ^ 2) = 1
    simp only [Fintype.sum_prod_type, norm_mul, mul_pow, ← Finset.mul_sum, ih, mul_one]

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

theorem exists_coordinate_translation_equivalence {σ : Type*} [Fintype σ] [DecidableEq σ] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : σ => 1) p)
      (l : List σ) (i : σ), i ∉ l →
      NativeIntegerVectorEquivalence (Fintype.card σ - 1) ((p + C) ^ C)
        (fun k x => W.eval k (coordinateTranslatedInput (i :: l) x))
        (fun k : Fin W.outputDim × Fin W.outputDim => fun x =>
          W.eval k.1 (coordinateTranslatedInput l x) *
            W.eval k.2 (coordinateTranslatedInput l (coordinateReplaceInput i x))) := by
  obtain ⟨C, hC, hadd⟩ := exists_multilinearity_equivalence (σ := σ)
  refine ⟨C, hC, ?_⟩
  intro p W l i hi
  have E := (hadd W i).linearPullbackHom (coordinateTranslationHom l)
  simpa only [coordinateSumVector, coordinateTensorVector,
    coordinateTranslation_sum l i hi, coordinateTranslation_left,
    coordinateTranslation_right l i hi] using E

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_ternary_coordinate_equivalence {σ : Type*}
    [Fintype σ] [DecidableEq σ] [Nonempty σ] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : σ => 1) p)
      (l : List σ) (i : σ), i ∉ l →
      NativeIntegerVectorEquivalence (Fintype.card σ - 1) ((p + C) ^ C)
        (fun j x => W.eval j (ternaryCoordinateInput (i :: l) x))
        (fun a : Fin W.outputDim × (Fin W.outputDim × Fin W.outputDim) => fun x =>
          W.eval a.1 (ternaryCoordinateInput l x) *
            (W.eval a.2.1 (ternaryCoordinateInput l (ternaryReplaceInput i 1 x)) *
              W.eval a.2.2 (ternaryCoordinateInput l (ternaryReplaceInput i 2 x)))) := by
  obtain ⟨A, _, hadd⟩ := exists_multilinearity_equivalence (σ := σ)
  obtain ⟨B, _, hself⟩ := exists_integer_self_equivalence (σ := σ)
  obtain ⟨D, _, htensor⟩ := NativeIntegerVectorEquivalence.exists_tensor_budget
  obtain ⟨F, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B
  let V := (U + Polynomial.C D) ^ D
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((U + V + Polynomial.C F) ^ F)
  refine ⟨C, hC, ?_⟩
  intro p W l i hi
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let u := (p + A) ^ A + (p + B) ^ B
  let v := (u + D) ^ D
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hAu : (p + A) ^ A ≤ u := le_add_of_nonneg_right (by positivity)
  have hBu : (p + B) ^ B ≤ u := le_add_of_nonneg_left (by positivity)
  let leftMap : Option σ → (((Fin 3 × σ) → ℤ) →+ ℤ) := fun j => match j with
    | none => { toFun := fun x => x (1, i) + x (2, i)
                map_zero' := by simp
                map_add' := fun x y => by simp only [Pi.add_apply]; ring }
    | some j => ternaryCoordinateHom l j
  let rightMap : Option σ → (((Fin 3 × σ) → ℤ) →+ ℤ) := fun j => match j with
    | none => { toFun := fun x => x (2, i), map_zero' := rfl, map_add' := fun _ _ => rfl }
    | some j => if j = i then
        { toFun := fun x => x (1, i), map_zero' := rfl, map_add' := fun _ _ => rfl }
      else ternaryCoordinateHom l j
  let middle (x : (Fin 3 × σ) → ℤ) :=
    Function.update (ternaryCoordinateInput l x) i (x (1, i) + x (2, i))
  have hleft0 (x : (Fin 3 × σ) → ℤ) :
      coordinateAdditionInputs i (fun j => leftMap j x) 0 = ternaryCoordinateInput (i :: l) x := by
    rw [ternaryCoordinateInput_cons l i]
    change Function.update (ternaryCoordinateInput l x) i
      (ternaryCoordinateInput l x i + (x (1, i) + x (2, i))) = _
    simp only [ternaryCoordinateInput, ite_eq_right hi]
  have hleft1 (x : (Fin 3 × σ) → ℤ) :
      coordinateAdditionInputs i (fun j => leftMap j x) 1 = ternaryCoordinateInput l x := rfl
  have hleft2 (x : (Fin 3 × σ) → ℤ) :
      coordinateAdditionInputs i (fun j => leftMap j x) 2 = middle x := rfl
  have hrightBase (x : (Fin 3 × σ) → ℤ) :
      (fun j => rightMap (some j) x) = Function.update (ternaryCoordinateInput l x) i (x (1, i)) := by
    funext j
    by_cases hj : j = i <;> simp [rightMap, hj, ternaryCoordinateHom]
  have hright0 (x : (Fin 3 × σ) → ℤ) :
      coordinateAdditionInputs i (fun j => rightMap j x) 0 = middle x := by
    rw [coordinateAdditionInputs_sum, hrightBase]
    simp [rightMap, middle]
  have hright1 (x : (Fin 3 × σ) → ℤ) :
      coordinateAdditionInputs i (fun j => rightMap j x) 1 =
        ternaryCoordinateInput l (ternaryReplaceInput i 1 x) := by
    rw [coordinateAdditionInputs_left, hrightBase, ternaryCoordinateInput_replace l i hi]
  have hright2 (x : (Fin 3 × σ) → ℤ) :
      coordinateAdditionInputs i (fun j => rightMap j x) 2 =
        ternaryCoordinateInput l (ternaryReplaceInput i 2 x) := by
    rw [coordinateAdditionInputs_right, hrightBase, ternaryCoordinateInput_replace l i hi]
    simp [rightMap]
  have E₀ : NativeIntegerVectorEquivalence (Fintype.card σ - 1) u
      (fun j x => W.eval j (ternaryCoordinateInput (i :: l) x))
      (fun a : Fin W.outputDim × Fin W.outputDim => fun x =>
        W.eval a.1 (ternaryCoordinateInput l x) * W.eval a.2 (middle x)) := by
    have E := ((hadd W i).linearPullbackHom leftMap).mono hAu
    simpa only [coordinateSumVector, coordinateTensorVector, hleft0, hleft1, hleft2] using E
  have E₁ : NativeIntegerVectorEquivalence (Fintype.card σ - 1) u
      (fun j x => W.eval j (middle x))
      (fun a : Fin W.outputDim × Fin W.outputDim => fun x =>
        W.eval a.1 (ternaryCoordinateInput l (ternaryReplaceInput i 1 x)) *
          W.eval a.2 (ternaryCoordinateInput l (ternaryReplaceInput i 2 x))) := by
    have E := ((hadd W i).linearPullbackHom rightMap).mono hAu
    simpa only [coordinateSumVector, coordinateTensorVector, hright0, hright1, hright2] using E
  have Eself := ((hself W).linearPullbackHom (ternaryCoordinateHom l)).mono hBu
  have E₂ := htensor hu Eself E₁
  have Emid (x : (Fin 3 × σ) → ℤ) :
      ∑ a : Fin W.outputDim × Fin W.outputDim,
        ‖W.eval a.1 (ternaryCoordinateInput l x) * W.eval a.2 (middle x)‖ ^ 2 = 1 := by
    simp only [Fintype.sum_prod_type, norm_mul, mul_pow, ← Finset.mul_sum, W.unit_eval, mul_one]
  have E := htrans (add_nonneg hu hv) (E₀.mono (le_add_of_nonneg_right hv))
    (E₂.mono (le_add_of_nonneg_left hu)) Emid
  have hcost : (u + v + F) ^ F ≤ (p + C) ^ C := by
    simpa [X, U, V, u, v, Polynomial.eval₂_pow] using hbudget p hp
  exact E.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
