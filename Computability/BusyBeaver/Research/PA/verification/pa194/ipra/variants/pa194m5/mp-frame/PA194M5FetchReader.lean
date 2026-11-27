import PA194M5FetchAgree
import PA194ProgramReader
import PA194ModelAXReader
import PA194PausedReach
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
namespace PA194M5FetchReader
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open PA194SourceControllerCode PA194SourceRegisters PA194SourceRegisterRelation PA194SchedulerFetchPositive
open PA194ModelMPDrain PA194ModelCantorWalker PA194MachineProjections PA194ModelAXReader
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

theorem rows : PA194ProgramReader.ReaderRows PA194M5Program.program 34 8 3 := by
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,by decide,by decide,by decide,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first | rw [PA194M5Program.programLength]; decide | decide +kernel

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def output (a : Fin 11 → M) : Fin 11 → M :=
  Function.update (Function.update a 8 (F fixedSecond ![a 8])) 3 (a 3 + F fixedFirst ![a 8])

theorem reader (a : Fin 11 → M) (tail : M) (hx : a 6 = 0) (hy : a 7 = 0) :
    PA194PausedReach.Reaches (PA194ProgramDrain.step PA194M5Program.program) (sourceState 34 a tail) (sourceState 48 (output a) tail) := by
  have h := (PA194ProgramReader.reader PA194M5Program.program 34 8 3 rows a tail).reaches
  have hz : cantor (0 : M) 0 = 0 := by simp [cantor,triangle]
  rw [hx,hy,hz,zero_add] at h
  have ho : argsAfter (argsAfter (argsAt 8 a (F fixedFirst ![a 8]) (F fixedSecond ![a 8]) 0) 7 [8]
      ((argsAt 8 a (F fixedFirst ![a 8]) (F fixedSecond ![a 8]) 0) 7)) 6 [3]
      ((argsAfter (argsAt 8 a (F fixedFirst ![a 8]) (F fixedSecond ![a 8]) 0) 7 [8]
      ((argsAt 8 a (F fixedFirst ![a 8]) (F fixedSecond ![a 8]) 0) 7)) 6) = output a := by
    funext i
    fin_cases i <;> simp [argsAfter,argsAt,PA194ModelCantorWalker.write,location,tally,output,hx,hy,subSelf,PA194StateOne.modelNumeralOne,
      show modelNumeral M 0 = (0:M) from rfl]
  exact ho ▸ h
#print axioms rows
#print axioms reader
end models
end PA194M5FetchReader
