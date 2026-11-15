import PA194SchedulerDispatchOpen
import PA194DispatchTag
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194SchedulerBranchesOpen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SchedulerCode PA194SchedulerIteration
open PA194IteratedSimulation PA194SchedulerDispatchOpen PA194DispatchTag
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem fetchDecodeBranches (scheduler : M) (initial : Fin 11 → M) (tail : M)
    (hn : F fN ![scheduler] = initial 0) (hl : F fL ![scheduler] = initial 8)
    (hx : initial 6 = (0 : M)) (hy : initial 7 = (0 : M)) (h3 : initial 3 = (0 : M)) :
    ∃ (clock : M) (out : Fin 11 → M),
      F PA194SourceControllerCode.run ![clock,sourceState 25 initial tail] = sourceState 48 out tail ∧
      F (PA194SchedulerCode.tail fN fL) ![scheduler] = out 8 ∧
      F fN ![F PA194SchedulerIteration.step ![scheduler]] = out 0 ∧
      out 6 = 0 ∧ out 7 = 0 ∧
      (F (head fN fL) ![scheduler] = 0 →
        F PA194SourceControllerCode.run ![clock+1,sourceState 25 initial tail] = sourceState 3661 out tail) ∧
      (F (head fN fL) ![scheduler] = 1 →
        F PA194SourceControllerCode.run ![(clock+1)+1,sourceState 25 initial tail] = sourceState 3554 (Function.update out 3 0) tail) ∧
      (∀ c : M, F (head fN fL) ![scheduler] = (c+1)+1 →
        F PA194SourceControllerCode.run ![(clock+1)+1,sourceState 25 initial tail] = sourceState 50 (Function.update out 3 c) tail) := by
  obtain ⟨clock,out,hprefix,hhead,htail,hN,h6,h7⟩ := fetchDecodeDispatch scheduler initial tail hn hl hx hy h3
  refine ⟨clock,out,hprefix,htail,hN,h6,h7,?_,?_,?_⟩
  · intro hz
    have htag : out 3 = (0 : M) := hhead.symm.trans hz
    have hstep := shiftTag out tail htag
    change F (iterate PA194SourceControllerCode.step) ![clock+1,sourceState 25 initial tail] = _
    rw [PA194DiagonalIteration.iterSucc]
    change F PA194SourceControllerCode.step ![F PA194SourceControllerCode.run ![clock,sourceState 25 initial tail]] = _
    rw [hprefix,hstep]
  · intro h1
    have htag : out 3 = (1 : M) := hhead.symm.trans h1
    have hstep := mpTag out tail htag
    change F (iterate PA194SourceControllerCode.step) ![(clock+1)+1,sourceState 25 initial tail] = _
    rw [PA194DiagonalIteration.iterSucc,PA194DiagonalIteration.iterSucc]
    change F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![F PA194SourceControllerCode.run ![clock,sourceState 25 initial tail]]] = _
    rw [hprefix,hstep]
  · intro c hc
    have htag : out 3 = (c+1)+1 := hhead.symm.trans hc
    have hstep := axTag out tail c htag
    change F (iterate PA194SourceControllerCode.step) ![(clock+1)+1,sourceState 25 initial tail] = _
    rw [PA194DiagonalIteration.iterSucc,PA194DiagonalIteration.iterSucc]
    change F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![F PA194SourceControllerCode.run ![clock,sourceState 25 initial tail]]] = _
    rw [hprefix,hstep]
#print axioms fetchDecodeBranches
end models
end PA194SchedulerBranchesOpen
