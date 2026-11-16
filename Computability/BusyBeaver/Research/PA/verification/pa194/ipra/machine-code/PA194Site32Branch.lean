import PA194Site32To4
import PA194Site27BranchRows
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site32Branch
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns PA194FiniteControls PA194StateOne PRAModelIOpenPairing PA194Path27Header
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def entry (k : M) (args : Fin 11 → M) : M :=
  let z := F zeros ![k,F sourceFileCode args+F sourceFileCode args+1]
  F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),modelWord (PA194SourceProgram.path 32) ((z+z)+(z+z))]]

theorem zeroTo5 (k : M) (args : Fin 11 → M) (hz : args 6 = (0 : M)) :
    let v := physicalArgs args
    let t := F ones ![v 9+1,v 10]
    ∃ clock z : M, F PA194Stepper.stepper ![clock,entry k args] =
      F pairCode ![modelNumeral M 5,F pairCode ![(z+z)+(z+z)+1,t]] := by
  dsimp only
  let v := physicalArgs args
  let tail := F (fileCode 1) ![v 9,v 10]
  let t := F ones ![v 9+1,v 10]
  have ht : tail = t+t := by
    dsimp only [tail,t]
    rw [modelFileSucc,modelBlock]
    change F ones ![v 9+1,F (fileCode 0) ![v 10]]+F ones ![v 9+1,F (fileCode 0) ![v 10]] = _
    rw [modelFileZero]
  have hv : v 8 = (0 : M) := hz
  let ev : Fin 9 → M := fun i => v i.succ.succ
  let ev6 : Fin 3 → M := fun i => ev i.succ.succ.succ.succ.succ.succ
  have htail : (fun i : Fin 2 => ev6 i.succ) = ![v 9,v 10] := by
    funext i; fin_cases i <;> rfl
  have hq : F ones ![ev6 0,F (fileCode 1) (fun i => ev6 i.succ)] = F ones ![v 8,tail] := by
    rw [htail]
    rfl
  have h := PA194Site32To4.to4 k args
  dsimp only at h
  change F PA194Stepper.stepper ![_,entry k args] =
    F pairCode ![modelNumeral M 4,F pairCode ![_,F ones ![ev6 0,F (fileCode 1) (fun i => ev6 i.succ)]]] at h
  rw [hq] at h
  obtain ⟨clock,z,h⟩ : ∃ clock z : M, F PA194Stepper.stepper ![clock,entry k args] =
      F pairCode ![modelNumeral M 4,F pairCode ![z+z,F ones ![v 8,tail]]] := by
    exact ⟨_,_,h⟩
  rw [hv,ht] at h
  refine ⟨F addCode ![clock,modelNumeral M 1],z,?_⟩
  rw [PA194StepperCompose.modelStepperCompose,h]
  exact PA194Site27BranchRows.zeroRow z t

theorem positiveTo6 (k : M) (args : Fin 11 → M) (m : M) (hm : args 6 = m+1) :
    let v := physicalArgs args
    let tail := F (fileCode 1) ![v 9,v 10]
    let r := F ones ![m,tail]
    ∃ clock z : M, F PA194Stepper.stepper ![clock,entry k args] =
      F pairCode ![modelNumeral M 6,F pairCode ![z,(r+r+1)+(r+r+1)]] := by
  dsimp only
  let v := physicalArgs args
  let tail := F (fileCode 1) ![v 9,v 10]
  have hv : v 8 = m+1 := hm
  let ev : Fin 9 → M := fun i => v i.succ.succ
  let ev6 : Fin 3 → M := fun i => ev i.succ.succ.succ.succ.succ.succ
  have htail : (fun i : Fin 2 => ev6 i.succ) = ![v 9,v 10] := by
    funext i; fin_cases i <;> rfl
  have hq : F ones ![ev6 0,F (fileCode 1) (fun i => ev6 i.succ)] = F ones ![v 8,tail] := by
    rw [htail]
    rfl
  have h := PA194Site32To4.to4 k args
  dsimp only at h
  change F PA194Stepper.stepper ![_,entry k args] =
    F pairCode ![modelNumeral M 4,F pairCode ![_,F ones ![ev6 0,F (fileCode 1) (fun i => ev6 i.succ)]]] at h
  rw [hq] at h
  obtain ⟨clock,z,h⟩ : ∃ clock z : M, F PA194Stepper.stepper ![clock,entry k args] =
      F pairCode ![modelNumeral M 4,F pairCode ![z+z,F ones ![v 8,tail]]] := by
    exact ⟨_,_,h⟩
  rw [hv] at h
  refine ⟨F addCode ![clock,modelNumeral M 1],z,?_⟩
  rw [PA194StepperCompose.modelStepperCompose,h]
  exact PA194Site27BranchRows.positiveRow z m tail
#print axioms zeroTo5
#print axioms positiveTo6
end models
end PA194Site32Branch
