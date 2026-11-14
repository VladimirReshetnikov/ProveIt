import PA194CodeGraph
/-! Specialization of uniform Code graphs to one variable and two model parameters. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194CodeInstance
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PA194CodeGraph
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- Fixing two model elements preserves Σ₁ definability. -/
theorem unary_of_three [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (c : Code 3) (a b : M) :
    𝚺₁-Function₁ (fun t : M => F c ![t,a,b]) := by
  have hg : 𝚺₁.DefinableFunction (fun v : Fin 3 → M => F c v) :=
    HierarchySymbol.Defined.to_definable (graph c) (modelGraph c)
  have hi : ∀ j : Fin 3, 𝚺₁.DefinableFunction (fun v : Fin 1 → M => ![v 0,a,b] j) := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact HierarchySymbol.DefinableFunction.var 0
    · refine Fin.cases ?_ (fun l => ?_) k
      · exact HierarchySymbol.DefinableFunction.const a
      · exact Fin.cases (HierarchySymbol.DefinableFunction.const b) (fun x => Fin.elim0 x) l
  have h := HierarchySymbol.DefinableFunction.substitution hg hi
  simpa using h
#print axioms unary_of_three
end models
end PA194CodeInstance
