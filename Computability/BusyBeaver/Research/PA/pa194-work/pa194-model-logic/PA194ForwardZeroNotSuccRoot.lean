import PA194ForwardZeroNotSuccProvable
import PA194ForwardRootQuote
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194ForwardZeroSucc
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194BindSource PA194QuotedInduction PA194StandardOrdinalReduction PA194OrdinalSuppliers
open PA194StandardEqualitySuppliers PA194EmptySourceProof PA194CongruenceSourceProof PA194StandardOrdinalProof
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph M6.PA.RelationalSource.Ordinal
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance zeroSuccRootZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance zeroSuccRootOne : One M := ⟨F oneCode Fin.elim0⟩
local instance zeroSuccRootAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance zeroSuccRootMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance zeroSuccRootLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance zeroSuccRootIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194FormulaDispatcher PA194ForwardTyped
attribute [local irreducible] target

theorem typed_zeroNotSucc_closed :
    (Rewriting.emb PA194PAeq.zeroNotSucc.univCl : SourceFormula 0) = PA194PAeq.zeroNotSucc := by
  change (PA194PAeq.zeroNotSucc.univCl : Proposition PA194PAeq.language) = PA194PAeq.zeroNotSucc
  rw [Semiformula.coe_univCl_eq_univCl']
  exact Semiformula.univCl'_eq_self_of _ (by decide)

theorem root_zeroNotSucc_provable (d : M)
    (hlen : (⌜PA194PAeq.zeroNotSucc.univCl⌝ : M) < len (nth (rootParameters d) 1)) :
    letI := adjunctiveFullSepTheoryDelta
    Provable adjunctiveFullSepTheory
      (translateFormula (rootParameters d) (⌜PA194PAeq.zeroNotSucc.univCl⌝ : M)) := by
  letI := adjunctiveFullSepTheoryDelta
  have hquote : (⌜PA194PAeq.zeroNotSucc⌝ : M) = (⌜PA194PAeq.zeroNotSucc.univCl⌝ : M) := by
    rw [Sentence.quote_def,typed_zeroNotSucc_closed]
  have heq := root_translate_quote PA194PAeq.zeroNotSucc d (by simpa [hquote] using hlen)
  rw [hquote] at heq
  rw [heq]
  simpa only [target] using (source_provable (M := M))
#print axioms typed_zeroNotSucc_closed
#print axioms root_zeroNotSucc_provable
end models
end PA194ForwardZeroSucc
