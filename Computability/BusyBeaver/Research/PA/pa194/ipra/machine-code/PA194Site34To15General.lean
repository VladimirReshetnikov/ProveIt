import PA194Site34PrefixGeneral
import PA194EightyFourScan
import PA194Site32ZeroPath
import PA194Path34Header
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site34To15General
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem to15 (k : M) (args : Fin 11 → M) :
    let n := (k+1)+1
    let a := F ones ![n,modelNumeral M 200]
    let f := F sourceFileCode args
    F PA194Stepper.stepper ![F addCode ![modelNumeral M 13,n+1],
      PA194SourceSite31Physical.physicalFrame 34 n args] =
      F pairCode ![modelNumeral M 15,F pairCode ![F halfCode (fun _ => a),
        F parityCode (fun _ => a)+(1+1)+(f+f)+(f+f)]] := by
  dsimp only
  let n := (k+1)+1
  let f := F sourceFileCode args
  let t := (1 : M)+(f+f)
  let z := F zeros ![k,t]
  have ht : t = f+f+1 := by dsimp [t]; simp only [add_assoc,add_comm,add_left_comm]
  have hz : F zeros ![n,t] = modelWord [false,false] z := by
    dsimp only [n,z]
    rw [PA194Site32ZeroPath.zerosSucc,PA194Site32ZeroPath.zerosSucc]
    simp only [modelWord,Bool.false_eq_true,↓reduceIte]
  have hprefix := PA194Site34PrefixGeneral.prefixWord z
  simp only [modelNumeralOne] at hprefix
  have hinput : modelWord (PA194SourceProgram.path 34) (F zeros ![n,t]) =
      modelWord [true,false,false,true,false,false,false,false,false] z := by
    rw [PA194Path34Header.path34,hz]
    simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false]
  rw [←hz] at hprefix
  have hscan := PA194EightyFourScan.scanExit n (modelNumeral M 200) f
  dsimp only at hscan
  rw [←ht] at hscan
  dsimp only [PA194SourceSite31Physical.physicalFrame]
  rw [hinput,PA194StepperCompose.modelStepperCompose,hprefix,hscan]
#print axioms to15
end models
end PA194Site34To15General
