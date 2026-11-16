module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCompilerRuleExpression
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualCompilerRuleExpression
open ActualWordExpression ActualWordCoding NativeCalculus.ActualBasis.Code
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
attribute [local irreducible] mp gen leaf1 leaf2 leaf3 leaf4 leaf5 leaf6 leaf7 leaf8 rawBundle

theorem rule_standard (rows : List (List Nat)) (tag payload : Nat) :
    eval rule (encodeRows rows) tag payload=encode (ruleCompileAtoms (fun i => rows.getD i []) tag payload) := by
  by_cases ht : tag<11
  · have hc : tag=0 ∨ tag=1 ∨ tag=2 ∨ tag=3 ∨ tag=4 ∨ tag=5 ∨ tag=6 ∨ tag=7 ∨ tag=8 ∨ tag=9 ∨ tag=10 := by omega
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simpa [rule,eval,ActualCheckExpression.eval,ruleCompileAtoms] using mp_standard rows 0 payload
    · simpa [rule,eval,ActualCheckExpression.eval,ruleCompileAtoms] using gen_standard rows 1 payload
    · simpa [rule,eval,ActualCheckExpression.eval,ruleCompileAtoms] using leaf1_standard (encodeRows rows) 2 payload
    · simpa [rule,eval,ActualCheckExpression.eval,ruleCompileAtoms] using leaf2_standard (encodeRows rows) 3 payload
    · simpa [rule,eval,ActualCheckExpression.eval,ruleCompileAtoms] using leaf3_standard (encodeRows rows) 4 payload
    · simpa [rule,eval,ActualCheckExpression.eval,ruleCompileAtoms] using leaf4_standard (encodeRows rows) 5 payload
    · simpa [rule,eval,ActualCheckExpression.eval,ruleCompileAtoms] using leaf5_standard (encodeRows rows) 6 payload
    · simpa [rule,eval,ActualCheckExpression.eval,ruleCompileAtoms] using leaf6_standard (encodeRows rows) 7 payload
    · simpa [rule,eval,ActualCheckExpression.eval,ruleCompileAtoms] using leaf7_standard (encodeRows rows) 8 payload
    · simpa [rule,eval,ActualCheckExpression.eval,ruleCompileAtoms] using leaf8_standard (encodeRows rows) 9 payload
    · simpa [rule,eval,ActualCheckExpression.eval,ruleCompileAtoms] using bundle_standard (encodeRows rows) 10 payload
  · obtain ⟨n,rfl⟩ : ∃ n,tag=n+11 := ⟨tag-11,by omega⟩
    simp [rule,eval,ActualCheckExpression.eval,ruleCompileAtoms]

noncomputable def ruleGraph : 𝚺ᴬ₁.Semisentence 4 := graph rule
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def ruleValue (previous tag payload : V) : V := eval rule previous tag payload

theorem rule_graph (z previous tag payload : V) :
    ruleGraph.val.Evalb ![z,previous,tag,payload] ↔ z=ruleValue previous tag payload := graph_correct _ _ _ _ _

theorem ruleGraph_total (previous tag payload : V) :
    ∃! z,ruleGraph.val.Evalb ![z,previous,tag,payload] := total_unique _ _ _ _
instance ruleValue_defined : 𝚺ᴬ₁-Function₃ (ruleValue : V → V → V → V) via ruleGraph := .mk fun v => by
  have hv : v=![v 0,v 1,v 2,v 3] := by
    funext ⟨i,hi⟩
    have he : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases he with rfl|rfl|rfl|rfl <;> rfl
  rw [hv]
  exact graph_correct _ _ _ _ _
instance ruleValue_definable : 𝚺ᴬ₁-Function₃ (ruleValue : V → V → V → V) := ruleValue_defined.to_definable

#print axioms rule_standard
#print axioms ruleGraph_total
end M6.PA.ActualCompilerRuleExpression

