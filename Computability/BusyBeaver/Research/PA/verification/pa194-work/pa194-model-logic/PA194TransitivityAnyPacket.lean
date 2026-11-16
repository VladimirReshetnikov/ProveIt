import PA194ForwardTransitivityRoot
import PA194ClosedSentenceEnvironment
import PA194PAeqStandardNoFree
import PA194ForwardRootQuote
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194TransitivityAnyPacket
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194BindSource PA194QuotedInduction PA194StandardOrdinalReduction PA194OrdinalSuppliers
open PA194StandardEqualitySuppliers PA194EmptySourceProof PA194CongruenceSourceProof PA194StandardOrdinalProof
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph M6.PA.RelationalSource.Ordinal
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance transitivityAnyPacketZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance transitivityAnyPacketOne : One M := ⟨F oneCode Fin.elim0⟩
local instance transitivityAnyPacketAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance transitivityAnyPacketMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance transitivityAnyPacketLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance transitivityAnyPacketIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194FormulaDispatcher PA194ForwardTyped PA194ClosedEnvironment PA194PAeqBind PA194PAeqOrdinalValues PA194TermDispatcher

theorem transitivity_any_packet {param : M} (hparam : ParametersValid 0 0 param) :
    letI := adjunctiveFullSepTheoryDelta
    Provable adjunctiveFullSepTheory
      (translateFormula param (⌜PA194PAeq.transitivity.univCl⌝ : M)) := by
  letI := adjunctiveFullSepTheoryDelta
  let p : M := ⌜PA194PAeq.transitivity.univCl⌝
  have hquote : (⌜PA194PAeq.transitivity⌝ : M) = p := by
    dsimp [p]
    rw [Sentence.quote_def,PA194ForwardTransitivity.typed_transitivity_closed]
  have hp : IsUFormula PA194PAeq.language p := by
    rw [←hquote]
    exact (Semiformula.quote_isSemiformula₀ PA194PAeq.transitivity).isUFormula
  have hs : shift PA194PAeq.language p = p := by
    rw [←hquote,←Semiformula.quote_shift]
    rw [PA194PAeqBind.syntactic_noFree_shift_fixed 0 PA194PAeq.transitivity (by decide)]
  have heq := sentence_root_packet hp hs hparam (d := p)
  have hr := PA194ForwardTransitivity.root_transitivity_provable p (rootParameters_length p)
  rw [heq] at hr
  exact hr
#print axioms transitivity_any_packet
end models
end PA194TransitivityAnyPacket
