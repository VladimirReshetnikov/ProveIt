module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateBinaryTemplates
@[expose] public section
namespace M6.PA.RelationalPredicateBinary
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language

theorem multiplication_closure : totality (domain (V:=V)) multiplication=
    ⌜RelationalSource.PairGraph.mulUniversalOutput⌝ := by
  change totality (domain (V:=V)) multiplication=⌜∀¹
    (RelationalSource.Ordinal.domain (.bvar 0) 🡒 ∀¹
      (RelationalSource.Ordinal.domain (.bvar 0) 🡒 ∃¹
        (RelationalSource.Ordinal.domain (.bvar 0) ⋏
          RelationalSource.PairGraph.mulResult (.bvar 2) (.bvar 1) (.bvar 0))))⌝
  simp [totality,outputAt,←FFL.FirstOrder.Semiterm.typed_quote_bShift,
    ←FFL.FirstOrder.Semiterm.typed_quote_bvar,Rew.bShift]

theorem addition_host_closure : RelationalSource.PairGraph.addClosedResult=
    ∀¹ (RelationalSource.Ordinal.domain (.bvar 0) 🡒 ∀¹
      (RelationalSource.Ordinal.domain (.bvar 0) 🡒 ∃¹
        (RelationalSource.Ordinal.domain (.bvar 0) ⋏
          RelationalSource.PairGraph.addResult (.bvar 1) (.bvar 2) (.bvar 0)))) := by
  simp only [RelationalSource.PairGraph.addClosedResult,RelationalSource.closeParameter,
    RelationalSource.PairGraph.addTotalStatement,RelationalSource.PairGraph.addOutputConclusion,
    RelationalSource.PairGraph.addOutput,FFL.FirstOrder.Semiformula.rewAux,
    FFL.FirstOrder.Semiformula.imp_eq,FFL.FirstOrder.Semiformula.neg_eq,
    FFL.FirstOrder.Semiformula.rewAux_neg,RelationalSource.Ordinal.domain_rew,
    RelationalSource.PairGraph.addResult_rew]
  simp only [←FFL.FirstOrder.Semiformula.neg_eq,FFL.FirstOrder.Semiformula.rewAux_neg,
    RelationalSource.Ordinal.domain_rew]
  rfl

theorem addition_closure : totalityReverse (domain (V:=V)) addition=
    ⌜RelationalSource.PairGraph.addClosedResult⌝ := by
  rw [addition_host_closure]
  simp [totalityReverse,outputAt,←FFL.FirstOrder.Semiterm.typed_quote_bShift,
    ←FFL.FirstOrder.Semiterm.typed_quote_bvar,Rew.bShift]

#print axioms addition_host_closure
#print axioms addition_closure
#print axioms multiplication_closure
end M6.PA.RelationalPredicateBinary
