module
public import MappingTemplateCore
public import PRTemplateBridge
@[expose] public section
namespace PalomarPA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

def standardMapping (domain member : ArithmeticSemisentence 2) (edge : ArithmeticSemisentence 3) :
 ArithmeticSemisentence 1 :=
 “m. ∃ d <⁺ 2*m, !domain d m ∧ ∀ x < d, !member x d →
   ∃ y < m, !edge m x y ∧ ∀ y' < m, !edge m x y' → y'=y”

theorem mappingTemplate_to (domain member : Formula Empty 2) (edge : Formula Empty 3) :
 (mappingTemplate domain member edge).toFoundation =
 standardMapping domain.toFoundation member.toFoundation edge.toFoundation := by
 simp only [mappingTemplate,Formula.toFoundation,Formula.to_neg,prSub2_to,prSub3_to,
  Term.to_add,prTerm_to_mul,Term.to_one,Term.to_bvar]
 unfold standardMapping
 simp only [Semiformula.ballLT,Semiformula.ball_eq,Semiformula.bexsLT,Semiformula.bexs_eq,
  Semiformula.bexsLTSucc,Semiformula.imp_eq]
 congr! 40 <;> try rfl
 all_goals first
  | (apply Function.LeftInverse.injective Formula.to_from; with_unfolding_all decide +kernel)
  | (apply Function.LeftInverse.injective Term.to_from; with_unfolding_all decide +kernel)
#print axioms mappingTemplate_to
end PalomarPA
