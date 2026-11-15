import PA194PAeqFullyClosed
import PA194PAeqTargetInventory
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def zeroCode : V := ^func 0 0 0
noncomputable def succVarCode : V := ^func 1 1 (?[ ^#(0 : V)] : V)
noncomputable def inductionBody (p : V) : V :=
  imp PA194PAeq.language (substs1 PA194PAeq.language zeroCode p)
    (imp PA194PAeq.language (^∀ (imp PA194PAeq.language p (substs1 PA194PAeq.language succVarCode p))) (^∀ p))
noncomputable def inductionBodyGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out p. ∃ z b a vec sv nxt st stAll concl tail,
    !qqFuncDef z 0 0 0 ∧ !(substs1Graph PA194PAeq.language) b z p ∧
    !qqBvarDef a 0 ∧ !adjoinDef vec a 0 ∧ !qqFuncDef sv 1 1 vec ∧
    !(substs1Graph PA194PAeq.language) nxt sv p ∧ !(impGraph PA194PAeq.language) st p nxt ∧
    !qqAllDef stAll st ∧ !qqAllDef concl p ∧ !(impGraph PA194PAeq.language) tail stAll concl ∧
    !(impGraph PA194PAeq.language) out b tail”
theorem inductionBody_graph (out p : V) : inductionBodyGraph.val.Evalb ![out,p] ↔ out = inductionBody p := by
  simp [inductionBodyGraph,inductionBody,zeroCode,succVarCode,Matrix.comp_vecCons'']
instance inductionBody_defined : 𝚺₁-Function₁ (inductionBody : V → V) via inductionBodyGraph := .mk fun v => by
  change inductionBodyGraph.val.Evalb v ↔ v 0 = inductionBody (v 1)
  have hv : ![v 0,v 1] = v := by funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  simpa only [hv] using inductionBody_graph (v 0) (v 1)

theorem inductionBody_scope {p : V} (hp : IsSemiformula PA194PAeq.language 1 p) :
    IsSemiformula PA194PAeq.language 0 (inductionBody p) := by
  have hz : IsSemiterm PA194PAeq.language 0 (zeroCode : V) := by simp [zeroCode]
  have hs : IsSemiterm PA194PAeq.language 1 (succVarCode : V) := by simp [succVarCode]
  have hp' : IsSemiformula PA194PAeq.language ((0 : V)+1) p := by simpa using hp
  have hs' : IsSemiterm PA194PAeq.language ((0 : V)+1) (succVarCode : V) := by simpa using hs
  unfold inductionBody
  apply IsSemiformula.imp.mpr
  refine ⟨IsSemiformula.substs1 hz hp, IsSemiformula.imp.mpr ⟨?_,IsSemiformula.all.mpr hp'⟩⟩
  exact IsSemiformula.all.mpr (IsSemiformula.imp.mpr ⟨hp',IsSemiformula.substs1 hs' hp⟩)

theorem paeq_quote_neg {n : Nat} (p : Semiproposition PA194PAeq.language n) :
    (⌜∼p⌝ : V) = neg PA194PAeq.language (⌜p⌝ : V) := by
  change ((Semiformula.typedQuote V (∼p)).val : V) = neg PA194PAeq.language (Semiformula.typedQuote V p).val
  rw [Semiformula.typedQuote_neg]
  rfl
theorem paeq_quote_substs1 {n : Nat} (p : Semiproposition PA194PAeq.language 1)
    (t : SyntacticSemiterm PA194PAeq.language n) :
    (⌜p ⇜ ![t]⌝ : V) = substs1 PA194PAeq.language (⌜t⌝ : V) (⌜p⌝ : V) := by
  simp only [substs1,Semiformula.quote_def,Semiformula.typed_quote_substs]
  rfl
theorem inductionBody_quote (p : Semiproposition PA194PAeq.language 1) :
    inductionBody (⌜p⌝ : V) = (⌜PA194PAeq.inductionFormula p⌝ : V) := by
  have hz : (⌜(PA194PAeq.zero : SyntacticSemiterm PA194PAeq.language 0)⌝ : V) = zeroCode := by simp [zeroCode,PA194PAeq.quote_zero]
  have hs : (⌜(PA194PAeq.succ (.bvar 0) : SyntacticSemiterm PA194PAeq.language 1)⌝ : V) = succVarCode := by
    simp [succVarCode,PA194PAeq.quote_successor]
  unfold inductionBody
  rw [← hz,← hs,← paeq_quote_substs1,← paeq_quote_substs1]
  change imp PA194PAeq.language (⌜p ⇜ ![PA194PAeq.zero]⌝ : V)
    (imp PA194PAeq.language (^∀ (imp PA194PAeq.language (⌜p⌝ : V) (⌜p ⇜ ![PA194PAeq.succ (.bvar 0)]⌝ : V))) (^∀ (⌜p⌝ : V))) = _
  simp only [imp]
  change (neg PA194PAeq.language (⌜p ⇜ ![PA194PAeq.zero]⌝ : V) ^⋎
    (neg PA194PAeq.language (^∀ (neg PA194PAeq.language (⌜p⌝ : V) ^⋎ (⌜p ⇜ ![PA194PAeq.succ (.bvar 0)]⌝ : V))) ^⋎ ^∀ (⌜p⌝ : V))) = _
  simp only [← paeq_quote_neg,← Semiformula.quote_or,← Semiformula.quote_all]
  rfl
#print axioms inductionBody_graph
#print axioms inductionBody_scope
#print axioms inductionBody_quote
end generic
end PA194PAeqBind
