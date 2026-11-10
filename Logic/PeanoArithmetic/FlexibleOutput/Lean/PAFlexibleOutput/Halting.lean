import Mathlib.Computability.PartrecCode
import Foundation.FirstOrder.Arithmetic.R0.Representation

/-!
# The halting formula

One fixed arithmetical formula `universalGraph(y, c, x)` says "program `c` halts on input `x`
with output `y`". It is Foundation's representing formula of the universal partial recursive
function of Mathlib's `Nat.Partrec.Code`.

* `haltSentence c x y` is the sentence obtained by substituting numerals.
* `OutputIn M c x y` reads the formula in a structure `M`, for an output `y : M`.
* `ValueIn M c x o` says that the value of program `c` on input `x`, computed inside `M`, is
  `o : Option ℕ`: the numeral `n` is the only output if `o = some n`, and there is no output if
  `o = none`.
* `standardCorrectness`, `outputIn_nat`: in the standard model the formula says exactly
  `y ∈ Nat.Partrec.Code.eval c x`.
* `universalGraph_sigma_one`: the formula is `𝚺₁`.
-/

set_option autoImplicit false

namespace PAFlexibleOutput

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-- Programs: Mathlib's codes of partial recursive functions. -/
abbrev Code := Nat.Partrec.Code

/-- The universal partial recursive function: a program code and an input. -/
def universalEval : List.Vector ℕ 2 →. ℕ :=
  fun v => Nat.Partrec.Code.eval (Denumerable.ofNat Code (v.get 0)) (v.get 1)

theorem universalEval_partrec : Nat.Partrec' universalEval :=
  Nat.Partrec'.of_part <| Nat.Partrec.Code.eval_part.comp
    ((Computable.ofNat Code).comp (Computable.vector_get.comp .id (.const 0)))
    (Computable.vector_get.comp .id (.const 1))

/-- The halting formula. Its variables are output, program code, input. -/
noncomputable def universalGraph : ArithmeticSemisentence 3 :=
  codeOfPartrec' universalEval

/-- The sentence "program `c` halts on input `x` with output `y`". -/
noncomputable def haltSentence (c : Code) (x y : ℕ) : ArithmeticSentence :=
  universalGraph/[↑y, ↑(Encodable.encode c), ↑x]

/-- `y` is an output of program `c` on input `x`, computed inside the structure `M`. -/
def OutputIn (M : Type*) [ORingStructure M] (c : Code) (x : ℕ) (y : M) : Prop :=
  M ⊧/![y, ORingStructure.numeral (Encodable.encode c), ORingStructure.numeral x] universalGraph

/-- The value of program `c` on input `x`, computed inside `M`, is `o`: for `o = some n` the
numeral `n` is the unique output, and for `o = none` there is no output. -/
def ValueIn (M : Type*) [ORingStructure M] (c : Code) (x : ℕ) : Option ℕ → Prop
  | some n => ∀ y : M, OutputIn M c x y ↔ y = ORingStructure.numeral n
  | none => ∀ y : M, ¬ OutputIn M c x y

/-- A structure satisfies the halting sentence iff the numeral is an output. -/
theorem models_haltSentence {M : Type*} [ORingStructure M] {c : Code} {x y : ℕ} :
    M↓[ℒₒᵣ] ⊧ haltSentence c x y ↔ OutputIn M c x (ORingStructure.numeral y) := by
  simp [haltSentence, OutputIn, models_iff, Semiformula.eval_substs]

/-- In the standard model the outputs are the real outputs. -/
theorem outputIn_nat {c : Code} {x y : ℕ} : OutputIn ℕ c x y ↔ y ∈ Nat.Partrec.Code.eval c x := by
  simpa [OutputIn, universalGraph, universalEval] using
    codeOfPartrec'_spec universalEval_partrec (y := y) (v := ![Encodable.encode c, x])

/-- In the standard model the halting sentence says that the program really halts with the
given output. -/
theorem standardCorrectness (c : Code) (x y : ℕ) :
    ℕ↓[ℒₒᵣ] ⊧ haltSentence c x y ↔ y ∈ Nat.Partrec.Code.eval c x := by
  rw [models_haltSentence, Nat.numeral_eq, outputIn_nat]

/-- The halting formula is `𝚺₁`. -/
theorem universalGraph_sigma_one : Hierarchy 𝚺 1 universalGraph := by
  simp [universalGraph, codeOfPartrec']

#print axioms standardCorrectness

end PAFlexibleOutput
