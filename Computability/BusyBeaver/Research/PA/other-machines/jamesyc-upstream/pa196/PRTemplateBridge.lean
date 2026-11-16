module
public import PRTemplateCore
public import FixTemplateBridge
@[expose] public section
namespace PalomarPA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

theorem prTerm_to_mul (t u : Term ξ n) :
 (Term.mul t u).toFoundation = (‘!!t.toFoundation * !!u.toFoundation’ : Semiterm ℒₒᵣ ξ n) := by
 rw [← Term.to_from (‘!!t.toFoundation * !!u.toFoundation’ : Semiterm ℒₒᵣ ξ n)]
 simp only [fromMul,Term.from_to]

theorem prSub1_to (p : Formula Empty 1) (a : Term Empty n) :
 (prSub1 p a).toFoundation = p.toFoundation/[a.toFoundation] := by
 rw [prSub1,substClosed_to]
 congr 1
 apply Rew.ext
 · intro i; fin_cases i; rfl
 · intro x; exact Empty.elim x

theorem prSub2_to (p : Formula Empty 2) (a b : Term Empty n) :
 (prSub2 p a b).toFoundation = p.toFoundation/[a.toFoundation,b.toFoundation] :=
 substClosed_to2 p a b

theorem prSub3_to (p : Formula Empty 3) (a b c : Term Empty n) :
 (prSub3 p a b c).toFoundation = p.toFoundation/[a.toFoundation,b.toFoundation,c.toFoundation] := by
 rw [prSub3,substClosed_to]
 congr 1
 apply Rew.ext
 · intro i; fin_cases i <;> rfl
 · intro x; exact Empty.elim x

def standardPRCSeq (zero seq : ArithmeticSemisentence 1) (succ edge : ArithmeticSemisentence 3)
 (length : ArithmeticSemisentence 2) : ArithmeticSemisentence 1 :=
 “s. !seq s ∧ (∃ z < s, !zero z ∧ !edge 0 s z) ∧
   (∀ i < 2*s, (∃ l <⁺ 2*s, !length l s ∧ i+1 < l) →
     ∀ z < s, !edge i s z → ∃ u < s, !succ u z i ∧ !edge (i+1) s u)”
def standardPRResult (cseq : ArithmeticSemisentence 1) (edge : ArithmeticSemisentence 3) :
 ArithmeticSemisentence 2 := “z u. ∃ s, !cseq s ∧ !edge u s z”

theorem prResultTemplate_to (cseq : Formula Empty 1) (edge : Formula Empty 3) :
 (prResultTemplate cseq edge).toFoundation = standardPRResult cseq.toFoundation edge.toFoundation := by
 simp only [prResultTemplate,Formula.toFoundation,prSub1_to,prSub3_to,Term.to_bvar]
 rfl

theorem prCSeqTemplate_to (zero seq : Formula Empty 1) (succ edge : Formula Empty 3)
 (length : Formula Empty 2) :
 (prCSeqTemplate zero seq succ edge length).toFoundation =
 standardPRCSeq zero.toFoundation seq.toFoundation succ.toFoundation edge.toFoundation length.toFoundation := by
 simp only [prCSeqTemplate,Formula.toFoundation,Formula.to_neg,prSub1_to,prSub2_to,prSub3_to,
  Term.to_add,prTerm_to_mul,Term.to_zero,Term.to_one,Term.to_bvar]
 unfold standardPRCSeq
 simp only [Semiformula.ballLT,Semiformula.ball_eq,Semiformula.bexsLT,Semiformula.bexs_eq,
  Semiformula.bexsLTSucc,Semiformula.imp_eq]
 congr! 30 <;> try rfl
 · apply Function.LeftInverse.injective Formula.to_from
   with_unfolding_all decide +kernel
 · apply Function.LeftInverse.injective Term.to_from
   with_unfolding_all decide +kernel
#print axioms prResultTemplate_to
#print axioms prCSeqTemplate_to
end PalomarPA
