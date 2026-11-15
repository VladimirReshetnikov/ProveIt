import PA194ForwardSuccInjectiveProvable
import PA194ForwardRootQuote
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194ForwardSuccInjective
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194BindSource PA194QuotedInduction PA194StandardOrdinalReduction PA194OrdinalSuppliers
open PA194StandardEqualitySuppliers PA194EmptySourceProof PA194CongruenceSourceProof
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph M6.PA.RelationalSource.Ordinal
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance succInjectiveRootZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance succInjectiveRootOne : One M := ⟨F oneCode Fin.elim0⟩
local instance succInjectiveRootAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance succInjectiveRootMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance succInjectiveRootLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance succInjectiveRootIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194FormulaDispatcher PA194ForwardTyped
attribute [local irreducible] target

theorem typed_succInjective_closed :
    (Rewriting.emb PA194PAeq.succInjective.univCl : SourceFormula 0) = PA194PAeq.succInjective := by
  change (PA194PAeq.succInjective.univCl : Proposition PA194PAeq.language) = PA194PAeq.succInjective
  rw [Semiformula.coe_univCl_eq_univCl']
  exact Semiformula.univCl'_eq_self_of _ (by decide)

theorem root_succInjective_provable (d : M)
    (hlen : (⌜PA194PAeq.succInjective.univCl⌝ : M) < len (nth (rootParameters d) 1)) :
    letI := adjunctiveFullSepTheoryDelta
    Provable adjunctiveFullSepTheory
      (translateFormula (rootParameters d) (⌜PA194PAeq.succInjective.univCl⌝ : M)) := by
  letI := adjunctiveFullSepTheoryDelta
  have hquote : (⌜PA194PAeq.succInjective⌝ : M) = (⌜PA194PAeq.succInjective.univCl⌝ : M) := by
    rw [Sentence.quote_def,typed_succInjective_closed]
  have heq := root_translate_quote PA194PAeq.succInjective d (by simpa [hquote] using hlen)
  rw [hquote] at heq
  rw [heq]
  simpa only [target] using (source_provable (M := M))
#print axioms typed_succInjective_closed
#print axioms root_succInjective_provable
end models
end PA194ForwardSuccInjective
