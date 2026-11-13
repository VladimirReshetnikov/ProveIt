module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateLookup
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
noncomputable def boundIndexGraph (i : Nat) : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “out b f. ∃ index, index=↑i ∧ !nthDef out b index”
noncomputable def freeIndexGraph (i : Nat) : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “out b f. ∃ index, index=↑i ∧ !nthDef out f index”
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] nthDef
theorem boundIndex_graph (i : Nat) (out b f : V) :
    (boundIndexGraph i).val.Evalb ![out,b,f] ↔ out=nth b (i:V) := by
  simp [boundIndexGraph,lookup_correct,numeral_eq_natCast]
theorem freeIndex_graph (i : Nat) (out b f : V) :
    (freeIndexGraph i).val.Evalb ![out,b,f] ↔ out=nth f (i:V) := by
  simp [freeIndexGraph,lookup_correct,numeral_eq_natCast]
#print axioms boundIndex_graph
#print axioms freeIndex_graph
end M6.PA.RelationalPredicateTemplate
