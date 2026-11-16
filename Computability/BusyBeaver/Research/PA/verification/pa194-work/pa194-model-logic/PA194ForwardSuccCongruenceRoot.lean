import PA194ForwardSuccCongruenceProvable
import PA194ForwardRootQuote
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194ForwardSuccCongruence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194BindSource PA194QuotedInduction PA194StandardOrdinalReduction PA194OrdinalSuppliers
open PA194StandardEqualitySuppliers PA194EmptySourceProof PA194CongruenceSourceProof PA194StandardOrdinalProof
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph M6.PA.RelationalSource.Ordinal
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance succCongruenceRootZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance succCongruenceRootOne : One M := ⟨F oneCode Fin.elim0⟩
local instance succCongruenceRootAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance succCongruenceRootMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance succCongruenceRootLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance succCongruenceRootIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194FormulaDispatcher PA194ForwardTyped
attribute [local irreducible] target

theorem typed_succCongruence_closed :
    (Rewriting.emb PA194PAeq.succCongruence.univCl : SourceFormula 0) = PA194PAeq.succCongruence := by
  change (PA194PAeq.succCongruence.univCl : Proposition PA194PAeq.language) = PA194PAeq.succCongruence
  rw [Semiformula.coe_univCl_eq_univCl']
  exact Semiformula.univCl'_eq_self_of _ (by decide)

theorem root_succCongruence_provable (d : M)
    (hlen : (⌜PA194PAeq.succCongruence.univCl⌝ : M) < len (nth (rootParameters d) 1)) :
    letI := adjunctiveFullSepTheoryDelta
    Provable adjunctiveFullSepTheory
      (translateFormula (rootParameters d) (⌜PA194PAeq.succCongruence.univCl⌝ : M)) := by
  letI := adjunctiveFullSepTheoryDelta
  have hquote : (⌜PA194PAeq.succCongruence⌝ : M) = (⌜PA194PAeq.succCongruence.univCl⌝ : M) := by
    rw [Sentence.quote_def,typed_succCongruence_closed]
  have heq := root_translate_quote PA194PAeq.succCongruence d (by simpa [hquote] using hlen)
  rw [hquote] at heq
  rw [heq]
  simpa only [target] using (source_provable (M := M))
#print axioms typed_succCongruence_closed
#print axioms root_succCongruence_provable
end models
end PA194ForwardSuccCongruence
