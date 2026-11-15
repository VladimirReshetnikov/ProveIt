import PA194ForwardSymmetryProvable
import PA194ForwardRootQuote
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194ForwardSymmetry
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194BindSource PA194QuotedInduction PA194StandardOrdinalReduction PA194OrdinalSuppliers
open PA194StandardEqualitySuppliers PA194EmptySourceProof PA194CongruenceSourceProof PA194StandardOrdinalProof
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph M6.PA.RelationalSource.Ordinal
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance symmetryRootZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance symmetryRootOne : One M := ⟨F oneCode Fin.elim0⟩
local instance symmetryRootAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance symmetryRootMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance symmetryRootLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance symmetryRootIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194FormulaDispatcher PA194ForwardTyped
attribute [local irreducible] target

theorem typed_symmetry_closed :
    (Rewriting.emb PA194PAeq.symmetry.univCl : SourceFormula 0) = PA194PAeq.symmetry := by
  change (PA194PAeq.symmetry.univCl : Proposition PA194PAeq.language) = PA194PAeq.symmetry
  rw [Semiformula.coe_univCl_eq_univCl']
  exact Semiformula.univCl'_eq_self_of _ (by decide)

theorem root_symmetry_provable (d : M)
    (hlen : (⌜PA194PAeq.symmetry.univCl⌝ : M) < len (nth (rootParameters d) 1)) :
    letI := adjunctiveFullSepTheoryDelta
    Provable adjunctiveFullSepTheory
      (translateFormula (rootParameters d) (⌜PA194PAeq.symmetry.univCl⌝ : M)) := by
  letI := adjunctiveFullSepTheoryDelta
  have hquote : (⌜PA194PAeq.symmetry⌝ : M) = (⌜PA194PAeq.symmetry.univCl⌝ : M) := by
    rw [Sentence.quote_def,typed_symmetry_closed]
  have heq := root_translate_quote PA194PAeq.symmetry d (by simpa [hquote] using hlen)
  rw [hquote] at heq
  rw [heq]
  simpa only [target] using (source_provable (M := M))
#print axioms typed_symmetry_closed
#print axioms root_symmetry_provable
end models
end PA194ForwardSymmetry
