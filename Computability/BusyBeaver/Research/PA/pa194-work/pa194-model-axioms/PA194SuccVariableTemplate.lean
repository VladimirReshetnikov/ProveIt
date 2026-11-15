import PA194SuccVariableDispatcher
import PA194ForwardSuccValueAt
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194SuccVariableTemplate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194SuccVariableDispatcher PA194ForwardSuccValueAt
open M6.PA.RelationalSource M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def translatedSuccExpansion : Semiproposition M6.PA.RelationalSource.language 2 :=
  (PA194PAeqOrdinalValues.domainTemplate ⇜ ![#1]) ⋏
    (∃⁰ (((PA194PAeqOrdinalValues.domainTemplate ⇜ ![#0]) ⋏
      (PA194PAeqOrdinalValues.equalityTemplate ⇜ ![#0,#1])) ⋏
      (PA194PAeqOrdinalValues.successorTemplate ⇜ ![#0,#2])))

theorem translatedSuccExpansion_eq : translatedSuccValue2 = translatedSuccExpansion := by
  simp only [translatedSuccValue2,translatedSuccExpansion,PA194ForwardTyped.value,PA194PAeq.succ,PA194ForwardTyped.shiftEnv]
  simp only [PA194PAeqOrdinalValues.domainTemplate, PA194PAeqOrdinalValues.equalityTemplate,
    PA194PAeqOrdinalValues.successorTemplate,Rewriting.subst,app_eq_rewAux,domain_rew,successor_rew]
  isoSyntax

theorem translatedSuccTemplate_value (x z : V) :
    ((⌜translatedSuccValue2⌝ : Semiformula V SourceL 2).subst ![Semiterm.fvar x,Semiterm.fvar z] : Formula V SourceL).val =
      successorValue (^&z) (variableValue (^#(0 : V)) (^&x)) := by
  let D : Semiformula V SourceL 1 := ⌜PA194PAeqOrdinalValues.domainTemplate⌝
  let E : Semiformula V SourceL 2 := ⌜PA194PAeqOrdinalValues.equalityTemplate⌝
  let S : Semiformula V SourceL 2 := ⌜PA194PAeqOrdinalValues.successorTemplate⌝
  have d1 : (⌜((PA194PAeqOrdinalValues.domainTemplate ⇜ ![#1]) : Semiproposition M6.PA.RelationalSource.language 2)⌝ : Semiformula V SourceL 2) = D.subst ![Semiterm.bvar 1] := by
    rw [Semiformula.typed_quote_substs]
    congr 1
    funext i
    fin_cases i <;> simp [D]
  have d0 : (⌜((PA194PAeqOrdinalValues.domainTemplate ⇜ ![#0]) : Semiproposition M6.PA.RelationalSource.language 3)⌝ : Semiformula V SourceL 3) = D.subst ![Semiterm.bvar 0] := by
    rw [Semiformula.typed_quote_substs]
    congr 1
    funext i
    fin_cases i <;> simp [D]
  have e : (⌜((PA194PAeqOrdinalValues.equalityTemplate ⇜ ![#0,#1]) : Semiproposition M6.PA.RelationalSource.language 3)⌝ : Semiformula V SourceL 3) = E.subst ![Semiterm.bvar 0,Semiterm.bvar 1] := by
    rw [Semiformula.typed_quote_substs]
    congr 1
    funext i
    fin_cases i <;> simp [E]
  have ss : (⌜((PA194PAeqOrdinalValues.successorTemplate ⇜ ![#0,#2]) : Semiproposition M6.PA.RelationalSource.language 3)⌝ : Semiformula V SourceL 3) = S.subst ![Semiterm.bvar 0,Semiterm.bvar 2] := by
    rw [Semiformula.typed_quote_substs]
    congr 1
    funext i
    fin_cases i <;> simp [S]
  have hsyn : (⌜translatedSuccValue2⌝ : Semiformula V SourceL 2) =
      D.subst ![Semiterm.bvar 1] ⋏ (∃⁰ (((D.subst ![Semiterm.bvar 0]) ⋏
      (E.subst ![Semiterm.bvar 0,Semiterm.bvar 1])) ⋏ (S.subst ![Semiterm.bvar 0,Semiterm.bvar 2]))) := by
    rw [translatedSuccExpansion_eq]
    change Semiformula.typedQuote V translatedSuccExpansion = _
    simp only [translatedSuccExpansion,Semiformula.typedQuote]
    change Semiformula.typedQuote V (PA194PAeqOrdinalValues.domainTemplate ⇜ ![#1]) = _ at d1
    change Semiformula.typedQuote V (PA194PAeqOrdinalValues.domainTemplate ⇜ ![#0]) = _ at d0
    change Semiformula.typedQuote V (PA194PAeqOrdinalValues.equalityTemplate ⇜ ![#0,#1]) = _ at e
    change Semiformula.typedQuote V (PA194PAeqOrdinalValues.successorTemplate ⇜ ![#0,#2]) = _ at ss
    rw [d1,d0,e,ss]
  have he : ((⌜translatedSuccValue2⌝ : Semiformula V SourceL 2).subst ![Semiterm.fvar x,Semiterm.fvar z] : Formula V SourceL) =
      D.subst ![Semiterm.fvar z] ⋏ (∃⁰ (((D.subst ![Semiterm.bvar 0]) ⋏
      (E.subst ![Semiterm.bvar 0,Semiterm.fvar x])) ⋏ (S.subst ![Semiterm.bvar 0,Semiterm.fvar z]))) := by
    rw [hsyn]
    simp [Semiformula.substs_substs,SemitermVec.q]
  have hD := congrArg Semiformula.val (Semiformula.subst_eq_self₁ D)
  change subst SourceL (?[ ^#(0 : V)] : V) (⌜PA194PAeqOrdinalValues.domainTemplate⌝ : Semiformula V SourceL 1).val = (⌜PA194PAeqOrdinalValues.domainTemplate⌝ : Semiformula V SourceL 1).val at hD
  have hv := congrArg Semiformula.val he
  simpa [D,E,S,successorValue,variableValue,domainCode,equalityCode,successorCode,templateOne,templateTwo,
    substs1,SemitermVec.val_succ,Semiformula.quote_def,hD] using hv

theorem numericalDispatcher_eq_template (x z : V) :
    translate (succVariablePacket x z) (^func (1 : V) 1 (?[ ^#(0 : V)] : V)) =
      ((⌜translatedSuccValue2⌝ : Semiformula V SourceL 2).subst ![Semiterm.fvar x,Semiterm.fvar z] : Formula V SourceL).val :=
  (translate_succVariable x z).trans (translatedSuccTemplate_value x z).symm

#print axioms numericalDispatcher_eq_template
#print axioms translatedSuccTemplate_value
#print axioms translatedSuccExpansion_eq
end generic
end PA194SuccVariableTemplate
