module
public import SeqTemplateCore
public import PRTemplateBridge
@[expose] public section
namespace PalomarPA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

def standardSeq (mapping : ArithmeticSemisentence 1) (domain under : ArithmeticSemisentence 2) :
 ArithmeticSemisentence 1 :=
 “s. !mapping s ∧ ∃ l <⁺ 2*s, ∃ d <⁺ 2*s, !domain d s ∧ !under d l”
def standardSeqLength (seq : ArithmeticSemisentence 1) (domain under : ArithmeticSemisentence 2) :
 ArithmeticSemisentence 2 :=
 “l s. (!seq s → ∃ d <⁺ 2*s, !domain d s ∧ !under d l) ∧ (¬!seq s → l=0)”

theorem seqTemplate_to (mapping : Formula Empty 1) (domain under : Formula Empty 2) :
 (seqTemplate mapping domain under).toFoundation = standardSeq mapping.toFoundation domain.toFoundation under.toFoundation := by
 simp only [seqTemplate,Formula.toFoundation,prSub1_to,prSub2_to,
  Term.to_add,prTerm_to_mul,Term.to_zero,Term.to_one,Term.to_bvar]
 unfold standardSeq
 simp only [Semiformula.bexsLTSucc,Semiformula.bexsLT,Semiformula.bexs_eq]
 congr! 25 <;> try rfl
 all_goals
  apply Function.LeftInverse.injective Term.to_from
  with_unfolding_all decide +kernel

theorem seqLengthTemplate_to (seq : Formula Empty 1) (domain under : Formula Empty 2) :
 (seqLengthTemplate seq domain under).toFoundation = standardSeqLength seq.toFoundation domain.toFoundation under.toFoundation := by
 simp only [seqLengthTemplate,Formula.toFoundation,Formula.to_neg,prSub1_to,prSub2_to,
  Term.to_add,prTerm_to_mul,Term.to_zero,Term.to_one,Term.to_bvar]
 unfold standardSeqLength
 simp only [Semiformula.bexsLTSucc,Semiformula.bexsLT,Semiformula.bexs_eq,Semiformula.imp_eq]
 congr! 25 <;> try rfl
 all_goals
  apply Function.LeftInverse.injective Term.to_from
  with_unfolding_all decide +kernel
#print axioms seqTemplate_to
#print axioms seqLengthTemplate_to
end PalomarPA
