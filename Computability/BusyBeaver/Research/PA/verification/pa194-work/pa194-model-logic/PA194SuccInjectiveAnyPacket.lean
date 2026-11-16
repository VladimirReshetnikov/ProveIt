import PA194ForwardSuccInjectiveRoot
import PA194ClosedSentenceEnvironment
import PA194PAeqStandardNoFree
import PA194ForwardRootQuote
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194SuccInjectiveAnyPacket
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194BindSource PA194QuotedInduction PA194StandardOrdinalReduction PA194OrdinalSuppliers
open PA194StandardEqualitySuppliers PA194EmptySourceProof PA194CongruenceSourceProof
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph M6.PA.RelationalSource.Ordinal
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance succInjectiveAnyPacketZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance succInjectiveAnyPacketOne : One M := ⟨F oneCode Fin.elim0⟩
local instance succInjectiveAnyPacketAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance succInjectiveAnyPacketMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance succInjectiveAnyPacketLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance succInjectiveAnyPacketIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194FormulaDispatcher PA194ForwardTyped PA194ClosedEnvironment PA194PAeqBind PA194PAeqOrdinalValues PA194TermDispatcher

theorem succInjective_any_packet {param : M} (hparam : ParametersValid 0 0 param) :
    letI := adjunctiveFullSepTheoryDelta
    Provable adjunctiveFullSepTheory
      (translateFormula param (⌜PA194PAeq.succInjective.univCl⌝ : M)) := by
  letI := adjunctiveFullSepTheoryDelta
  let p : M := ⌜PA194PAeq.succInjective.univCl⌝
  have hquote : (⌜PA194PAeq.succInjective⌝ : M) = p := by
    dsimp [p]
    rw [Sentence.quote_def,PA194ForwardSuccInjective.typed_succInjective_closed]
  have hp : IsUFormula PA194PAeq.language p := by
    rw [←hquote]
    exact (Semiformula.quote_isSemiformula₀ PA194PAeq.succInjective).isUFormula
  have hs : shift PA194PAeq.language p = p := by
    rw [←hquote,←Semiformula.quote_shift]
    rw [PA194PAeqBind.syntactic_noFree_shift_fixed 0 PA194PAeq.succInjective (by decide)]
  have heq := sentence_root_packet hp hs hparam (d := p)
  have hr := PA194ForwardSuccInjective.root_succInjective_provable p (rootParameters_length p)
  rw [heq] at hr
  exact hr
#print axioms succInjective_any_packet
end models
end PA194SuccInjectiveAnyPacket
