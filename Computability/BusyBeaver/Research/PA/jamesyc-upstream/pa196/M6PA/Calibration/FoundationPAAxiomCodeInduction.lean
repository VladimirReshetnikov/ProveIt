module
public import Foundation.FirstOrder.Incompleteness.Definability
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Basic
public import M6PA.Theory
@[expose] public section

/-!
# Numeric annotations for the pinned PA induction axiom predicate

These annotations retain model-valued parameter counts and formula codes. They
are not restricted to quotations of standard formulas. `Valid` is exactly the
induction branch of Foundation's chosen `Peano.Δ₁Class`; this file neither
changes the provability predicate nor extracts executable data from a Prop.
-/
namespace M6.PA.FoundationAxiomCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic

/-- Raw data only: parameter count, universally closed body, induction formula. -/
structure InductionData (V : Type*) where
  parameters : V
  closedBody : V
  formula : V

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The exact numeric conditions in the pinned induction recognition graph. -/
def InductionData.Valid (a : InductionData V) (p : V) : Prop :=
  a.parameters ≤ p ∧ a.closedBody ≤ p ∧
  p = qqAlls a.closedBody a.parameters ∧
  IsUFormula ℒₒᵣ a.closedBody ∧ shift ℒₒᵣ a.closedBody = a.closedBody ∧
  bv ℒₒᵣ a.closedBody = a.parameters ∧
  a.formula ≤ subst ℒₒᵣ (fvarVec a.parameters) a.closedBody ∧
  IsSemiformula ℒₒᵣ 1 a.formula ∧
  subst ℒₒᵣ (fvarVec a.parameters) a.closedBody = indBodyVal a.formula

theorem inductionData_iff (p : V) :
    (∃ a : InductionData V, a.Valid p) ↔ InductionR (fun _ => True) p := by
  constructor
  · rintro ⟨⟨m,b,k⟩, hm,hb,hp,hu,hs,hv,hk,hf,he⟩
    exact ⟨m,hm,b,hb,hp,hu,hs,hv,k,hk,hf,True.intro,he⟩
  · rintro ⟨m,hm,b,hb,hp,hu,hs,hv,k,hk,hf,_,he⟩
    exact ⟨⟨m,b,k⟩,hm,hb,hp,hu,hs,hv,hk,hf,he⟩

/-- Exact all-model decomposition; the finite branch is intentionally unchanged. -/
theorem axiom_iff (p : V) :
    p ∈ theory.Δ₁Class ↔ p ∈ PeanoMinus.Δ₁Class ∨
      ∃ a : InductionData V, a.Valid p := by
  rw [Peano.mem_Δ₁Class_iff, inductionData_iff]

theorem InductionData.mem {p : V} (a : InductionData V) (h : a.Valid p) :
    p ∈ theory.Δ₁Class :=
  (axiom_iff p).mpr (Or.inr ⟨a,h⟩)

/-- Erasure enters the actual pinned derivation's axiom constructor. -/
theorem InductionData.derivation {s p : V} (a : InductionData V)
    (h : a.Valid p) (hs : IsFormulaSet ℒₒᵣ s) (hp : p ∈ s) :
    Derivation theory (Bootstrapping.axm s p) :=
  Derivation.axm hs hp (a.mem h)

#print axioms inductionData_iff
#print axioms axiom_iff
#print axioms InductionData.mem
#print axioms InductionData.derivation
end M6.PA.FoundationAxiomCode

