import PA194Path33Header
import PA194Site32PositiveTo24Exact
import PA194Site32ZeroPath
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site32PositivePathExact
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns PA194Path27Header PA194Path33Header PA194Site32ZeroPath
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

theorem positivePath (k m : M) (args : Fin 11 → M) (hm : args 6 = m+1) :
    F PA194Stepper.stepper ![PA194Site32PositiveTo24Exact.clock k args,PA194SourceSite31Physical.physicalFrame 32 ((k+1)+1) args] =
      PA194SourceSite31Physical.physicalFrame 33 (((k+1)+1)+1) (Function.update args 6 m) := by
  let updated := Function.update args 6 m
  let f := F sourceFileCode updated
  let z := F zeros ![k+1,(1 : M)+f+f]
  let r := (z+z)+(z+z)
  let r1 := (1 : M)+r+r
  let r2 := r1+r1+1
  let r3 := r2+r2+1
  let t := (1 : M)+r3+r3
  let t1 := t+t
  let t2 := t1+t1
  let t3 := t2+t2
  let t4 := t3+t3
  have hp := PA194Path33Header.path33Word z
  dsimp only at hp
  change modelWord (PA194SourceProgram.path 33) r = t4+1 at hp
  have h := PA194Site32PositiveTo24Exact.positiveTo24 k m args hm
  dsimp only at h
  have hsum : (1 : M)+(f+f) = (1 : M)+f+f := by simp only [add_assoc]
  have hzeros : F zeros ![((k+1)+1)+1,(1 : M)+f+f] = r := by
    dsimp only [r,z]
    rw [zerosSucc,zerosSucc]
  rw [←entryFrame]
  dsimp only [PA194SourceSite31Physical.physicalFrame]
  rw [hsum,hzeros,hp]
  exact h
#print axioms positivePath
end models
end PA194Site32PositivePathExact
