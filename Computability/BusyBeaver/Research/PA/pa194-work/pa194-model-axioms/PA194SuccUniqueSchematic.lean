import PA194Schematic
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
namespace PA194SuccUniqueSchematic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping PA194Schematic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
inductive Pred | value | equiv | succ deriving DecidableEq

def arity : Pred → ℕ | .value => 1 | .equiv => 2 | .succ => 2
abbrev L := boxL arity

def valueRel : L.Rel 1 := BoxRel.box (ar := arity) Pred.value
def equivRel : L.Rel 2 := BoxRel.box (ar := arity) Pred.equiv
def succRel : L.Rel 2 := BoxRel.box (ar := arity) Pred.succ

def V {n : ℕ} (i : Fin n) : Semiformula L Empty n := .rel valueRel ![.bvar i]
def E {n : ℕ} (i j : Fin n) : Semiformula L Empty n := .rel equivRel ![.bvar i,.bvar j]
def S {n : ℕ} (i j : Fin n) : Semiformula L Empty n := .rel succRel ![.bvar i,.bvar j]

def uniqueValue : Sentence L := ∀⁰ (∀⁰ ((V 1 ⋏ V 0) 🡒 E 1 0))
def successorCoherent : Sentence L := ∀⁰ (∀⁰ (∀⁰ (∀⁰ ((E 3 2 ⋏ (S 3 1 ⋏ S 2 0)) 🡒 E 1 0))))
def successorUnique : Sentence L := ∀⁰ (∀⁰ (((∃⁰ (V 0 ⋏ S 0 2)) ⋏ (∃⁰ (V 0 ⋏ S 0 1))) 🡒 E 1 0))
def schema : Sentence L := uniqueValue 🡒 (successorCoherent 🡒 successorUnique)

@[simp] theorem map_vec2 {α β : Type} (f : α → β) (a b : α) :
    f ∘ ![a,b] = ![f a,f b] := by
  funext i
  fin_cases i <;> simp

@[simp] theorem map_vec1 {α β : Type} (f : α → β) (a : α) :
    f ∘ ![a] = ![f a] := by
  funext i
  fin_cases i <;> simp

theorem schema_valid (M : Type) [Nonempty M] [Structure L M] : M↓[L] ⊧ schema := by
  change (Semiformula.Eval (L := L) (M := M) ![] Empty.elim) schema
  simp [schema,uniqueValue,successorCoherent,successorUnique,V,E,S,Semantics.Models,Semiformula.eval_all,Semiformula.eval_ex,Semiformula.eval_rel]
  intro huniq hcoh b b' a ha hR a' ha' hR'
  exact hcoh a a' b b' (huniq a a' ha ha') hR hR'

/-- Every internal instance of the logical successor-uniqueness scheme is provable. -/
theorem certificate {W : Type} [ORingStructure W] [W↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {K : Language} [K.Encodable] [K.LORDefinable]
    (σ : (i : Pred) → Bootstrapping.Semiformula W K (arity i)) (T : Theory K) [T.Δ₁] :
    T.internalize W ⊢ PA194Schematic.instS σ schema :=
  PA194Schematic.instS_provable_of_valid σ T schema schema_valid

#print axioms schema_valid
#print axioms certificate

end PA194SuccUniqueSchematic
