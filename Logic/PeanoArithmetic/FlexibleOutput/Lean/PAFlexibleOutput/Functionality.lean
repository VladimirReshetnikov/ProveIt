import PAFlexibleOutput.Statement
import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic

/-!
# The halting formula is functional in every model of `𝗣𝗔⁻`

Foundation represents a partial recursive function by the formula `code c` attached to a
code `c : Nat.ArithPart₁.Code k`. Its first variable is the output and the remaining `k`
variables are the arguments. This module proves that `code c` defines a partial *function* in
every model of `𝗣𝗔⁻`, nonstandard arguments included: two outputs for the same arguments are
equal (`code_uniq`).

The proof is an induction on the code. Every case is immediate from the shape of the formula
except minimisation, where the formula says "the value at `z` is `0`, and at every `x < z` there
is a nonzero value". Two candidates `z < z'` would give a zero and a nonzero value at `z`, and
the induction hypothesis identifies them. This uses that the order of the model is linear,
which is why the statement is about `𝗣𝗔⁻` and not about `𝗥₀`.

`PAFlexibleOutput.universalGraph` is `code c` for a code `c` chosen by `Classical.epsilon`, so
the functionality of the halting formula in models of `𝗣𝗔` (`functionalityInPAModels`) follows
without any information about which code was chosen.
-/

set_option autoImplicit false

namespace PAFlexibleOutput

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

section

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

/-- The free-variable form of the representing formula has at most one output. -/
lemma codeAux_uniq {k : ℕ} (c : Nat.ArithPart₁.Code k) {v : Fin k → M} {z z' : M} :
    (codeAux c).Evalf (z :> v) → (codeAux c).Evalf (z' :> v) → z = z' := by
  induction c generalizing z z'
  case zero => simp [codeAux]; rintro rfl rfl; rfl
  case one => simp [codeAux]; rintro rfl rfl; rfl
  case add => simp [codeAux]; rintro rfl rfl; rfl
  case mul => simp [codeAux]; rintro rfl rfl; rfl
  case proj => simp [codeAux]; rintro rfl rfl; rfl
  case equal i j =>
    by_cases hv : v i = v j <;> simp [codeAux, hv]
    · rintro rfl rfl; rfl
    · rintro rfl rfl; rfl
  case lt i j =>
    by_cases hv : v i < v j <;> simp [codeAux, hv, -not_lt]
    · rintro rfl rfl; rfl
    · rintro rfl rfl; rfl
  case comp m n c d ihc ihd =>
    simp only [codeAux, Semiformula.eval_exsClosure, LogicalConnective.HomClass.map_and,
      LogicalConnective.Prop.and_eq, Semiformula.eval_rew, Function.comp_def]
    rintro ⟨w₁, hc₁, hd₁⟩ ⟨w₂, hc₂, hd₂⟩
    have hd₁' : ∀ i, (codeAux (d i)).Evalf (w₁ i :> v) := by
      simpa [Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq,
        Matrix.comp_vecCons'] using hd₁
    have hd₂' : ∀ i, (codeAux (d i)).Evalf (w₂ i :> v) := by
      simpa [Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq,
        Matrix.comp_vecCons'] using hd₂
    have : w₁ = w₂ := funext fun i => ihd i (hd₁' i) (hd₂' i)
    rcases this with rfl
    have hc₁' : (codeAux c).Evalf (z :> w₁) := by
      simpa [Function.comp_def, Matrix.empty_eq, Matrix.comp_vecCons'] using hc₁
    have hc₂' : (codeAux c).Evalf (z' :> w₁) := by
      simpa [Function.comp_def, Matrix.empty_eq, Matrix.comp_vecCons'] using hc₂
    exact ihc hc₁' hc₂'
  case rfind k c ih =>
    have key : ∀ {a b : M}, (codeAux (Nat.ArithPart₁.Code.rfind c)).Evalf (a :> v) →
        (codeAux (Nat.ArithPart₁.Code.rfind c)).Evalf (b :> v) → ¬ a < b := by
      intro a b ha hb hab
      have ha0 : (codeAux c).Evalf ((0 : M) :> a :> v) := by
        have := ha
        simp [codeAux, Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq,
          Matrix.comp_vecCons'] at this
        exact this.1
      have hbm : ∀ x < b, ∃ w : M, w ≠ 0 ∧ (codeAux c).Evalf (w :> x :> v) := by
        have := hb
        simp [codeAux, Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq,
          Matrix.comp_vecCons'] at this
        exact this.2
      rcases hbm a hab with ⟨w, hw, hwa⟩
      exact hw (ih hwa ha0)
    intro h₁ h₂
    rcases lt_trichotomy z z' with (h | h | h)
    · exact absurd h (key h₁ h₂)
    · exact h
    · exact absurd h (key h₂ h₁)

/-- The representing formula `code c` has at most one output for given arguments, in every
model of `𝗣𝗔⁻`. -/
theorem code_uniq {k : ℕ} (c : Nat.ArithPart₁.Code k) {v : Fin k → M} {z z' : M} :
    (code c).Evalb (z :> v) → (code c).Evalb (z' :> v) → z = z' := by
  intro h₁ h₂
  refine codeAux_uniq c (v := v) ?_ ?_
  · simpa [code, Semiformula.eval_rew, Matrix.empty_eq, Function.comp_def,
      Matrix.comp_vecCons'] using h₁
  · simpa [code, Semiformula.eval_rew, Matrix.empty_eq, Function.comp_def,
      Matrix.comp_vecCons'] using h₂

/-- Every formula `codeOfPartrec' f` is functional in every model of `𝗣𝗔⁻`, whether or not `f`
is partial recursive. -/
theorem codeOfPartrec'_uniq {k : ℕ} (f : List.Vector ℕ k →. ℕ) {v : Fin k → M} {z z' : M} :
    (codeOfPartrec' f).Evalb (z :> v) → (codeOfPartrec' f).Evalb (z' :> v) → z = z' :=
  code_uniq _

/-- The halting formula has at most one output for a given program and input, in every model
of `𝗣𝗔⁻`. Program and input range over the whole model. -/
theorem universalGraph_uniq {program input y z : M} :
    (M ⊧/![y, program, input] universalGraph) → (M ⊧/![z, program, input] universalGraph) →
      y = z := by
  intro h₁ h₂
  have e : ∀ a : M, (![a, program, input] : Fin 3 → M) = a :> ![program, input] := fun _ => rfl
  rw [e] at h₁ h₂
  exact codeOfPartrec'_uniq universalEval h₁ h₂

end

/-- `Statement.FunctionalityInPAModels`: the halting formula is functional in every model of
`𝗣𝗔`. -/
theorem functionalityInPAModels : FunctionalityInPAModels := by
  intro M _ _ _ program input y z h₁ h₂
  haveI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  exact universalGraph_uniq h₁ h₂

#print axioms functionalityInPAModels

end PAFlexibleOutput
