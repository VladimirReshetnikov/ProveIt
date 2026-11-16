module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateTermValidity
@[expose] public section
/-! Re-derived predicate-template atoms. The hole is an arbitrary target
formula with one bound argument and may retain arbitrary free parameters. -/
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def atomValue {n k : Nat} (r : Relation k) (ts : Fin k → Term n) (P b f : V) : V :=
  match r with
  | .eq => qqRel 2 0 (termValue (ts 0) b f ∷ (termValue (ts 1) b f ∷ 0))
  | .mem => qqRel 2 1 (termValue (ts 0) b f ∷ (termValue (ts 1) b f ∷ 0))
  | .predicate => substs1 RelationalSource.language (termValue (ts 0) b f) P
attribute [local irreducible] termGraph
noncomputable def atomGraph {n k : Nat} (r : Relation k) (ts : Fin k → Term n) : 𝚺ᴬ₁.Semisentence 4 :=
  match r with
  | .eq => .mkSigma “out P b f. ∃ x y ys args,
      !(termGraph (ts 0)) x b f ∧ !(termGraph (ts 1)) y b f ∧
      !adjoinDef ys y 0 ∧ !adjoinDef args x ys ∧ !qqRelDef out 2 0 args”
  | .mem => .mkSigma “out P b f. ∃ x y ys args,
      !(termGraph (ts 0)) x b f ∧ !(termGraph (ts 1)) y b f ∧
      !adjoinDef ys y 0 ∧ !adjoinDef args x ys ∧ !qqRelDef out 2 1 args”
  | .predicate => .mkSigma “out P b f. ∃ x, !(termGraph (ts 0)) x b f ∧
      !(substs1Graph RelationalSource.language) out x P”
theorem atom_graph {n k : Nat} (r : Relation k) (ts : Fin k → Term n) (out P b f : V) :
    (atomGraph r ts).val.Evalb ![out,P,b,f] ↔ out=atomValue r ts P b f := by
  cases r <;> simp [atomGraph,atomValue,term_graph,Matrix.comp_vecCons'']
theorem atomValue_isSemiformula {s k : Nat} {n P b f : V}
    (r : Relation k) (ts : Fin k → Term s)
    (hP : IsSemiformula RelationalSource.language 1 P)
    (h : EnvironmentsValid (s:V) n b f)
    (hf : ∀j i,(ts j).FVar? i→(i:V)<len f) :
    IsSemiformula RelationalSource.language n (atomValue r ts P b f) := by
  cases r with
  | eq => simp [atomValue,termValue_isSemiterm _ h (hf 0),termValue_isSemiterm _ h (hf 1)]
  | mem => simp [atomValue,termValue_isSemiterm _ h (hf 0),termValue_isSemiterm _ h (hf 1)]
  | predicate => exact IsSemiformula.substs1 (termValue_isSemiterm _ h (hf 0)) hP
#print axioms atom_graph
#print axioms atomValue_isSemiformula
end M6.PA.RelationalPredicateTemplate

