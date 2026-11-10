import Mathlib.Computability.PartrecCode
import Foundation.FirstOrder.Arithmetic.R0.Representation

/-!
# The halting formula and the value of a program inside a structure

One fixed arithmetical formula `universalGraph(y, c, x)` says "program `c` halts on input `x`
with output `y`". It is Foundation's representing formula of the universal partial recursive
function of Mathlib's `Nat.Partrec.Code`.

* `OutputIn M c x y` reads the formula in a structure `M`, for an output `y : M`.
* `ValueIn M c x o` says that the value of program `c` on input `x`, computed inside `M`, is
  `o : Option ℕ`: the numeral `n` is the only output if `o = some n`, and there is no output if
  `o = none`.
* `outputIn_nat`, `valueIn_nat`: in the standard model the outputs and the value are the real
  ones.
* `valueGraph(y, c, x)` is the formula "`y` is the only output of program `c` on input `x`".
  A structure satisfies its instance at numerals iff the value computed inside it is that
  numeral (`models_not_valueGraph`, stated for the negation, which is the form the main proof
  uses).
* `universalGraph_sigma_one`: the halting formula is `𝚺₁`.
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

/-- `y` is an output of program `c` on input `x`, computed inside the structure `M`. -/
def OutputIn (M : Type*) [ORingStructure M] (c : Code) (x : ℕ) (y : M) : Prop :=
  M ⊧/![y, ORingStructure.numeral (Encodable.encode c), ORingStructure.numeral x] universalGraph

/-- The value of program `c` on input `x`, computed inside `M`, is `o`: for `o = some n` the
numeral `n` is the unique output, and for `o = none` there is no output. -/
def ValueIn (M : Type*) [ORingStructure M] (c : Code) (x : ℕ) : Option ℕ → Prop
  | some n => ∀ y : M, OutputIn M c x y ↔ y = ORingStructure.numeral n
  | none => ∀ y : M, ¬ OutputIn M c x y

/-- In the standard model the outputs are the real outputs. -/
theorem outputIn_nat {c : Code} {x y : ℕ} : OutputIn ℕ c x y ↔ y ∈ Nat.Partrec.Code.eval c x := by
  simpa [OutputIn, universalGraph, universalEval] using
    codeOfPartrec'_spec universalEval_partrec (y := y) (v := ![Encodable.encode c, x])

/-- In the standard model the value is the real value. -/
theorem valueIn_nat {c : Code} {x : ℕ} {o : Option ℕ} :
    ValueIn ℕ c x o ↔ Nat.Partrec.Code.eval c x = (o : Part ℕ) := by
  cases o with
  | none => simp [ValueIn, outputIn_nat, Part.eq_none_iff]
  | some n =>
    simp only [ValueIn, outputIn_nat, Nat.numeral_eq, Part.coe_some, Part.eq_some_iff]
    exact ⟨fun h => (h n).2 rfl, fun h y => ⟨fun hy => Part.mem_unique hy h, fun hy => hy ▸ h⟩⟩

/-- The value formula "`y` is the only output of program `c` on input `x`". Its variables are
value, program code, input. -/
noncomputable def valueGraph : ArithmeticSemisentence 3 :=
  “y c x. ∀ z, !universalGraph z c x ↔ z = y”

/-- A structure satisfies the negated value sentence iff the value computed inside it is not
the given numeral. Nothing is assumed about the structure. -/
theorem models_not_valueGraph {M : Type*} [ORingStructure M] {c : Code} {x n : ℕ} :
    M↓[ℒₒᵣ] ⊧ (∼valueGraph)/[↑n, ↑(Encodable.encode c), ↑x] ↔ ¬ValueIn M c x (some n) := by
  have hv : ∀ y c x : M, M ⊧/![y, c, x] valueGraph ↔
      ∀ z, M ⊧/![z, c, x] universalGraph ↔ z = y := by
    simp [valueGraph, Semiformula.eval_substs]
  simp [models_iff, Semiformula.eval_substs, ValueIn, OutputIn, hv]

/-- The halting formula is `𝚺₁`. -/
theorem universalGraph_sigma_one : Hierarchy 𝚺 1 universalGraph := by
  simp [universalGraph, codeOfPartrec']

#print axioms valueIn_nat
#print axioms models_not_valueGraph

end PAFlexibleOutput
