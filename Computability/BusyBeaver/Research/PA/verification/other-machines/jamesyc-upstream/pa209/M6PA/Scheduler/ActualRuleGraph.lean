module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualRuleExpression
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualRuleExpression
open ActualCheckExpression ActualTableCoding NativeCalculus.ActualBasis.Code
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

theorem rule_standard (xs : List (Option Nat)) (tag payload : Nat) :
    eval rule (encodeTable xs) tag payload =
      optionCode (ruleCheck (fun i => xs.getD i none) tag payload) := by
  by_cases ht : tag<11
  · have hcases : tag=0 ∨ tag=1 ∨ tag=2 ∨ tag=3 ∨ tag=4 ∨ tag=5 ∨
      tag=6 ∨ tag=7 ∨ tag=8 ∨ tag=9 ∨ tag=10 := by omega
    rcases hcases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simpa [rule,eval,ruleCheck] using mp_standard xs 0 payload
    · simpa [rule,eval,ruleCheck] using gen_standard xs 1 payload
    · simpa [rule,eval,ruleCheck] using leaf1_standard (encodeTable xs) 2 payload
    · simpa [rule,eval,ruleCheck] using leaf2_standard (encodeTable xs) 3 payload
    · simpa [rule,eval,ruleCheck] using leaf3_standard (encodeTable xs) 4 payload
    · simpa [rule,eval,ruleCheck] using leaf4_standard (encodeTable xs) 5 payload
    · simpa [rule,eval,ruleCheck] using leaf5_standard (encodeTable xs) 6 payload
    · simpa [rule,eval,ruleCheck] using leaf6_standard (encodeTable xs) 7 payload
    · simpa [rule,eval,ruleCheck] using leaf7_standard (encodeTable xs) 8 payload
    · simpa [rule,eval,ruleCheck] using leaf8_standard (encodeTable xs) 9 payload
    · simpa [rule,eval,ruleCheck] using bundle_standard (encodeTable xs) 10 payload
  · obtain ⟨n,rfl⟩ : ∃ n,tag=n+11 := ⟨tag-11,by omega⟩
    simp [rule,eval,ruleCheck,optionCode]
    rfl

/-- Fixed Sigma-1 syntax for the exact rule evaluator. The result uses zero
for rejection and a+1 for a successful conclusion a. -/
noncomputable def ruleGraph : 𝚺ᴬ₁.Semisentence 4 := graph rule

theorem ruleGraph_standard (xs : List (Option Nat)) (tag payload z : Nat) :
    ruleGraph.val.Evalb ![z,encodeTable xs,tag,payload] ↔
      z=optionCode (ruleCheck (fun i => xs.getD i none) tag payload) := by
  rw [ruleGraph,graph_correct,rule_standard]

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem ruleGraph_total (previous tag payload : V) :
    ∃! z,ruleGraph.val.Evalb ![z,previous,tag,payload] := total_unique _ _ _ _

noncomputable def ruleValue (previous tag payload : V) : V := eval rule previous tag payload
instance ruleValue_defined : 𝚺ᴬ₁-Function₃ (ruleValue : V → V → V → V) via ruleGraph := .mk fun v => by
  have hv : v = ![v 0,v 1,v 2,v 3] := by
    funext ⟨i,hi⟩
    have he : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases he with rfl|rfl|rfl|rfl <;> rfl
  rw [hv]
  exact graph_correct _ _ _ _ _
instance ruleValue_definable : 𝚺ᴬ₁-Function₃ (ruleValue : V → V → V → V) := ruleValue_defined.to_definable

#print axioms rule_standard
#print axioms ruleGraph_standard
#print axioms ruleGraph_total
end M6.PA.ActualRuleExpression

