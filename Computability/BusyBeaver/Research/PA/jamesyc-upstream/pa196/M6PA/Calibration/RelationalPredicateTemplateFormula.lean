module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateBinders
@[expose] public section
/-! Finite host template instantiation into arbitrary model-valued relational
syntax. Under a bound quantifier the unary hole itself is unchanged. -/
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def formulaValue : {s : Nat} → Formula s → V → V → V → V
  | _, .verum, _, _, _ => qqVerum
  | _, .falsum, _, _, _ => qqFalsum
  | _, .rel r ts, P,b,f => atomValue r ts P b f
  | _, .nrel r ts, P,b,f => neg RelationalSource.language (atomValue r ts P b f)
  | _, .and p q, P,b,f => qqAnd (formulaValue p P b f) (formulaValue q P b f)
  | _, .or p q, P,b,f => qqOr (formulaValue p P b f) (formulaValue q P b f)
  | _, .all p, P,b,f => qqAll (formulaValue p P (bindBound b) (bindFree f))
  | _, .exs p, P,b,f => qqExs (formulaValue p P (bindBound b) (bindFree f))
attribute [local irreducible] atomGraph bindBoundGraph bindFreeGraph
noncomputable def formulaGraph : {s : Nat} → Formula s → 𝚺ᴬ₁.Semisentence 4
  | _, .verum => .mkSigma “out P b f. !qqVerumDef out”
  | _, .falsum => .mkSigma “out P b f. !qqFalsumDef out”
  | _, .rel r ts => atomGraph r ts
  | _, .nrel r ts => .mkSigma “out P b f. ∃ a, !(atomGraph r ts) a P b f ∧ !(negGraph RelationalSource.language) out a”
  | _, .and p q => .mkSigma “out P b f. ∃ a c, !(formulaGraph p) a P b f ∧ !(formulaGraph q) c P b f ∧ !qqAndDef out a c”
  | _, .or p q => .mkSigma “out P b f. ∃ a c, !(formulaGraph p) a P b f ∧ !(formulaGraph q) c P b f ∧ !qqOrDef out a c”
  | _, .all p => .mkSigma “out P b f. ∃ bs fs a, !bindBoundGraph bs b ∧ !bindFreeGraph fs f ∧ !(formulaGraph p) a P bs fs ∧ !qqAllDef out a”
  | _, .exs p => .mkSigma “out P b f. ∃ bs fs a, !bindBoundGraph bs b ∧ !bindFreeGraph fs f ∧ !(formulaGraph p) a P bs fs ∧ !qqExsDef out a”
theorem formula_graph {s : Nat} (p : Formula s) (out P b f : V) :
    (formulaGraph p).val.Evalb ![out,P,b,f] ↔ out=formulaValue p P b f := by
  induction p generalizing out P b f <;>
    simp_all [formulaGraph,formulaValue,atom_graph,bindBound_graph,bindFree_graph,Matrix.comp_vecCons'']
#print axioms formula_graph
end M6.PA.RelationalPredicateTemplate

