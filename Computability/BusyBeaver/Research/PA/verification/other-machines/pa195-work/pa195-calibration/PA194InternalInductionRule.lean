import PA194FullInternalInduction
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace PA194InternalInductionRule
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem induction_rule (K : Bootstrapping.Semiformula V ℒₒᵣ 1)
    (hbase : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ K.subst ![⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝])
    (hstep : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
      ∀⁰ (K 🡒 K.subst ![⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝])) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ ∀⁰ K := by
  have hK : IsSemiformula ℒₒᵣ 1 K.val := by simpa using K.isSemiformula
  have hp := PA194FullInternalInduction.internal_induction_body K.val hK
  rw [indBodyVal_eq] at hp
  have h : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ indBody K := (tprovable_iff_provable).mpr hp
  exact ⟨h.some ⨀ hbase.some ⨀ hstep.some⟩
#print axioms induction_rule
end PA194InternalInductionRule
