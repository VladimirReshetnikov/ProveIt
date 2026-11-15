import PA194Site32ZeroTo24Exact
import PA194Path34Header
import PA194SourceSite31Physical
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site32ZeroPathExact
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns PA194Path27Header PA194Path34Header
open BinaryTapeCodes PRAModelIOpenPairing PA194BinaryDouble PA194Site32ZeroRollback
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem zerosSucc (n x : M) : F zeros ![n+1,x] = F zeros ![n,x]+F zeros ![n,x] := by
  change F zeros ![F addCode ![n,F oneCode Fin.elim0],x] = _
  rw [modelAddOne,modelZerosSucc]

theorem entryFrame (k : M) (args : Fin 11 → M) :
    PA194Site32Branch.entry k args = PA194SourceSite31Physical.physicalFrame 32 ((k+1)+1) args := by
  let f := F sourceFileCode args
  have heq : (1 : M)+(f+f) = f+f+1 := by simp only [add_assoc,add_comm,add_left_comm]
  dsimp only [PA194Site32Branch.entry,PA194SourceSite31Physical.physicalFrame]
  rw [heq,zerosSucc,zerosSucc]

theorem zeroPath (k : M) (args : Fin 11 → M) (hz : args 6 = (0 : M)) :
    F PA194Stepper.stepper ![PA194Site32ZeroTo24Exact.clock k args,PA194SourceSite31Physical.physicalFrame 32 ((k+1)+1) args] =
      PA194SourceSite31Physical.physicalFrame 34 (((k+1)+1)+1) args := by
  let f := F sourceFileCode args
  let n := ((k+1)+1)+1
  let z := F zeros ![n,(1 : M)+f+f]
  let d := z+z
  let r := (d+d)+(d+d)
  let s := (1+1)+(r+r)+(r+r)
  let b := (s+s)+(s+s)+1
  have hp := PA194Path34Header.path34Word z
  dsimp only at hp
  change modelWord (PA194SourceProgram.path 34) z = b at hp
  have h := PA194Site32ZeroTo24Exact.zeroTo24 k args hz
  dsimp only at h
  have hz1 := zerosSucc n ((1 : M)+f+f)
  change F zeros ![n+1,(1 : M)+f+f] = d at hz1
  rw [hz1] at h
  rw [←entryFrame]
  have hsum : (1 : M)+(f+f) = (1 : M)+f+f := by simp only [add_assoc]
  dsimp only [PA194SourceSite31Physical.physicalFrame]
  rw [hsum,hp]
  exact h
#print axioms entryFrame
#print axioms zeroPath
end models
end PA194Site32ZeroPathExact
