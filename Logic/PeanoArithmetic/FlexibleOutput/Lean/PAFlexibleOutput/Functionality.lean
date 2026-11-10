import PAFlexibleOutput.Halting
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

`universalGraph` is `code c` for a code `c` chosen by `Classical.epsilon`, so its functionality
(`universalGraph_uniq`) follows without any information about which code was chosen.
-/

set_option autoImplicit false

namespace PAFlexibleOutput

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

/-- The free-variable form of the representing formula has at most one output. -/
lemma codeAux_uniq {k : ℕ} (c : Nat.ArithPart₁.Code k) {v : Fin k → M} {z z' : M} :
    (codeAux c).Evalf (z :> v) → (codeAux c).Evalf (z' :> v) → z = z' := by
  induction c generalizing z z'
  case zero | one | add | mul | proj => simp [codeAux]; rintro rfl rfl; rfl
  case equal i j => by_cases hv : v i = v j <;> simp [codeAux, hv] <;> rintro rfl rfl <;> rfl
  case lt i j => by_cases hv : v i < v j <;> simp [codeAux, hv, -not_lt] <;> rintro rfl rfl <;> rfl
  case comp m n c d ihc ihd =>
    simp only [codeAux, Semiformula.eval_exsClosure, LogicalConnective.HomClass.map_and,
      LogicalConnective.Prop.and_eq, Semiformula.eval_rew, Function.comp_def]
    rintro ⟨w₁, hc₁, hd₁⟩ ⟨w₂, hc₂, hd₂⟩
    simp [Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq, Matrix.comp_vecCons']
      at hc₁ hd₁ hc₂ hd₂
    obtain rfl : w₁ = w₂ := funext fun i => ihd i (hd₁ i) (hd₂ i)
    exact ihc hc₁ hc₂
  case rfind k c ih =>
    have key : ∀ {a b : M}, (codeAux c.rfind).Evalf (a :> v) →
        (codeAux c.rfind).Evalf (b :> v) → ¬ a < b := by
      intro a b ha hb hab
      simp [codeAux, Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq,
        Matrix.comp_vecCons'] at ha hb
      obtain ⟨w, hw, hwa⟩ := hb.2 a hab
      exact hw (ih hwa ha.1)
    exact fun h₁ h₂ => le_antisymm (not_lt.1 (key h₂ h₁)) (not_lt.1 (key h₁ h₂))

/-- The representing formula `code c` has at most one output for given arguments, in every
model of `𝗣𝗔⁻`. -/
theorem code_uniq {k : ℕ} (c : Nat.ArithPart₁.Code k) {v : Fin k → M} {z z' : M}
    (h₁ : (code c).Evalb (z :> v)) (h₂ : (code c).Evalb (z' :> v)) : z = z' := by
  simp [code, Semiformula.eval_rew, Matrix.empty_eq, Function.comp_def] at h₁ h₂
  exact codeAux_uniq c h₁ h₂

/-- The halting formula has at most one output for a given program and input, in every model
of `𝗣𝗔⁻`. Program and input range over the whole model. -/
theorem universalGraph_uniq {program input y z : M}
    (h₁ : M ⊧/![y, program, input] universalGraph)
    (h₂ : M ⊧/![z, program, input] universalGraph) : y = z :=
  code_uniq _ h₁ h₂

/-- A model of `𝗣𝗔⁻` that satisfies the halting sentence with output `n` computes the value
`n`: the numeral `n` is its only output. -/
theorem valueIn_of_models {c : Code} {x n : ℕ} (h : M↓[ℒₒᵣ] ⊧ haltSentence c x n) :
    ValueIn M c x (some n) := fun _ =>
  ⟨fun hy => universalGraph_uniq hy (models_haltSentence.mp h),
    fun hy => hy ▸ models_haltSentence.mp h⟩

#print axioms valueIn_of_models

end PAFlexibleOutput
