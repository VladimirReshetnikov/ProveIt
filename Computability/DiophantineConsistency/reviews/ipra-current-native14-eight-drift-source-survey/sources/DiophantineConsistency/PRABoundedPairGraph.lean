import DiophantineConsistency.PRAPairBoundConversion
set_option autoImplicit false
namespace DiophantineConsistency.PRABoundedPairGraph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAModelIOpenPairing PRAPairBoundConversion
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
/-- A pair exists, determines its components, and bounds both strictly by
its value plus one in every candidate-PRA model. -/
theorem modelPairGraphBounded (a b : M) :
    ∃ t : M,
      (Semiformula.lMap embedding pairDef.val).Eval ![t,a,b] Empty.elim ∧
      (∀ a' b', (Semiformula.lMap embedding pairDef.val).Eval ![t,a',b'] Empty.elim → a' = a ∧ b' = b) ∧
      Structure.rel (L := language) Language.ORing.Rel.lt
        ![a,Structure.func (L := language) addCode ![t,Structure.func (L := language) oneCode Fin.elim0]] ∧
      Structure.rel (L := language) Language.ORing.Rel.lt
        ![b,Structure.func (L := language) addCode ![t,Structure.func (L := language) oneCode Fin.elim0]] := by
  obtain ⟨t,hgraph,hunique,ha,hb⟩ := modelPairGraph a b
  exact ⟨t,hgraph,hunique,modelBoundSucc t a ha,modelBoundSucc t b hb⟩
end models
end DiophantineConsistency.PRABoundedPairGraph
