import PA194ForwardIdentityQuote
import PA194ForwardReflRoot
import PA194ForwardZeroNotSuccRoot
import PA194ForwardAddZeroRoot
import PA194ForwardMulZeroRoot
import PA194ForwardSymmetryRoot
import PA194ForwardRootQuote
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194IdentityFixedSuppliers
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194BindSource PA194QuotedInduction PA194StandardOrdinalReduction PA194OrdinalSuppliers
open PA194StandardEqualitySuppliers PA194EmptySourceProof PA194CongruenceSourceProof PA194StandardOrdinalProof
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph M6.PA.RelationalSource.Ordinal
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance identityFixedZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance identityFixedOne : One M := ⟨F oneCode Fin.elim0⟩
local instance identityFixedAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance identityFixedMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance identityFixedLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance identityFixedIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194ForwardIdentityQuote PA194FormulaDispatcher PA194ForwardTyped

theorem identity_reflexivity_provable (param : M) (hid : NormalizedIdentityPacket param)
    (hlen : (⌜PA194PAeq.reflexivity.univCl⌝ : M) < len (nth param 1)) :
    letI := adjunctiveFullSepTheoryDelta
    Provable adjunctiveFullSepTheory
      (translateFormula param (⌜PA194PAeq.reflexivity.univCl⌝ : M)) := by
  letI := adjunctiveFullSepTheoryDelta
  have hquote : (⌜PA194PAeq.reflexivity⌝ : M) = (⌜PA194PAeq.reflexivity.univCl⌝ : M) := by
    rw [Sentence.quote_def,PA194ForwardReflProof.typed_reflexivity_closed]
  have heq := identity_translate_quote PA194PAeq.reflexivity hid (by simpa [hquote] using hlen)
  rw [hquote] at heq
  rw [heq,reflexivity_env]
  simpa only [PA194ForwardReflProof.target] using (PA194ForwardReflProof.source_provable (M := M))
#print axioms identity_reflexivity_provable

theorem identity_zeroNotSucc_provable (param : M) (hid : NormalizedIdentityPacket param)
    (hlen : (⌜PA194PAeq.zeroNotSucc.univCl⌝ : M) < len (nth param 1)) :
    letI := adjunctiveFullSepTheoryDelta
    Provable adjunctiveFullSepTheory
      (translateFormula param (⌜PA194PAeq.zeroNotSucc.univCl⌝ : M)) := by
  letI := adjunctiveFullSepTheoryDelta
  have hquote : (⌜PA194PAeq.zeroNotSucc⌝ : M) = (⌜PA194PAeq.zeroNotSucc.univCl⌝ : M) := by
    rw [Sentence.quote_def,PA194ForwardZeroSucc.typed_zeroNotSucc_closed]
  have heq := identity_translate_quote PA194PAeq.zeroNotSucc hid (by simpa [hquote] using hlen)
  rw [hquote] at heq
  rw [heq,zeroNotSucc_env]
  simpa only [PA194ForwardZeroSucc.target] using (PA194ForwardZeroSucc.source_provable (M := M))
#print axioms identity_zeroNotSucc_provable

theorem identity_addZero_provable (param : M) (hid : NormalizedIdentityPacket param)
    (hlen : (⌜PA194PAeq.addZero.univCl⌝ : M) < len (nth param 1)) :
    letI := adjunctiveFullSepTheoryDelta
    Provable adjunctiveFullSepTheory
      (translateFormula param (⌜PA194PAeq.addZero.univCl⌝ : M)) := by
  letI := adjunctiveFullSepTheoryDelta
  have hquote : (⌜PA194PAeq.addZero⌝ : M) = (⌜PA194PAeq.addZero.univCl⌝ : M) := by
    rw [Sentence.quote_def,PA194ForwardAddZero.typed_addZero_closed]
  have heq := identity_translate_quote PA194PAeq.addZero hid (by simpa [hquote] using hlen)
  rw [hquote] at heq
  rw [heq,addZero_env]
  simpa only [PA194ForwardAddZero.target] using (PA194ForwardAddZero.source_provable (M := M))
#print axioms identity_addZero_provable

theorem identity_mulZero_provable (param : M) (hid : NormalizedIdentityPacket param)
    (hlen : (⌜PA194PAeq.mulZero.univCl⌝ : M) < len (nth param 1)) :
    letI := adjunctiveFullSepTheoryDelta
    Provable adjunctiveFullSepTheory
      (translateFormula param (⌜PA194PAeq.mulZero.univCl⌝ : M)) := by
  letI := adjunctiveFullSepTheoryDelta
  have hquote : (⌜PA194PAeq.mulZero⌝ : M) = (⌜PA194PAeq.mulZero.univCl⌝ : M) := by
    rw [Sentence.quote_def,PA194ForwardMulZero.typed_mulZero_closed]
  have heq := identity_translate_quote PA194PAeq.mulZero hid (by simpa [hquote] using hlen)
  rw [hquote] at heq
  rw [heq,mulZero_env]
  simpa only [PA194ForwardMulZero.target] using (PA194ForwardMulZero.source_provable (M := M))
#print axioms identity_mulZero_provable

theorem identity_symmetry_provable (param : M) (hid : NormalizedIdentityPacket param)
    (hlen : (⌜PA194PAeq.symmetry.univCl⌝ : M) < len (nth param 1)) :
    letI := adjunctiveFullSepTheoryDelta
    Provable adjunctiveFullSepTheory
      (translateFormula param (⌜PA194PAeq.symmetry.univCl⌝ : M)) := by
  letI := adjunctiveFullSepTheoryDelta
  have hquote : (⌜PA194PAeq.symmetry⌝ : M) = (⌜PA194PAeq.symmetry.univCl⌝ : M) := by
    rw [Sentence.quote_def,PA194ForwardSymmetry.typed_symmetry_closed]
  have heq := identity_translate_quote PA194PAeq.symmetry hid (by simpa [hquote] using hlen)
  rw [hquote] at heq
  rw [heq,symmetry_env]
  simpa only [PA194ForwardSymmetry.target] using (PA194ForwardSymmetry.source_provable (M := M))
#print axioms identity_symmetry_provable
end models
end PA194IdentityFixedSuppliers
