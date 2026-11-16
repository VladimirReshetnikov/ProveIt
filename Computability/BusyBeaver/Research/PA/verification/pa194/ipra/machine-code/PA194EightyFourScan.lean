import PA194GenericZeroToOneScan
import PA194EightyFourExit
import PA194RightRows
import PA194HeaderController
import PA194BinaryDouble
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194EightyFourScan
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194RightRows PA194EightyFourExit
open PackedIterationModel ConfigurationStep PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem packedExit (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 84,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 15,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(1+1)+(r+r)+(r+r)]] := by
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![modelNumeral M 84,l,r+r+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![modelNumeral M 84,l,r+r+1],F nextL ![modelNumeral M 84,l,r+r+1],
    F nextR ![modelNumeral M 84,l,r+r+1]) = stepSem (modelNumeral M 84) l (r+r+1) at hm
  rw [←hm,modelEightyFourOdd]
/-- Read zeros as ones, for every model length, then read the first one and
enter state 15. -/
theorem scanExit (n l r : M) :
    let a := F ones ![n,l]
    F PA194Stepper.stepper ![n+1,F pairCode ![modelNumeral M 84,
      F pairCode ![l,F zeros ![n,r+r+1]]]] =
    F pairCode ![modelNumeral M 15,F pairCode ![F halfCode (fun _ => a),
      F parityCode (fun _ => a)+(1+1)+(r+r)+(r+r)]] := by
  have hl (a b : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 84,F pairCode ![a,b+b]]) =
      F pairCode ![modelNumeral M 84,F pairCode ![a+a+1,b]] := by
    have h := rightZero 84 1 84 (by decide) (by decide +kernel) a b
    simpa only [PA194StateOne.modelNumeralOne] using h
  have hs := PA194GenericZeroToOneScan.modelFullScan 84 hl n l (r+r+1)
  dsimp only
  change F PA194Stepper.stepper ![F addCode ![n,F oneCode Fin.elim0],_] = _
  rw [modelAddOne,PA194Stepper.modelStepperSucc,hs,packedExit]
/-- The exact two-zero-prefixed returned file is scanned with a model-valued
clock. The suffix r is the half of the updated remaining file. -/
theorem returnedFileScan (k l r : M) :
    let t := (1 : M)+(r+r)+(r+r)
    let a := F ones ![k+1,l]
    F PA194Stepper.stepper ![((k+1)+1)+1,F pairCode ![modelNumeral M 84,
      F pairCode ![l,F zeros ![modelNumeral M 2,F zeros ![k,t]]]]] =
    F pairCode ![modelNumeral M 15,F pairCode ![a,(1 : M)+(1+1)+((r+r)+(r+r))+((r+r)+(r+r))]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let t := (1 : M)+(r+r)+(r+r)
  have ht : t = (r+r)+(r+r)+1 := by dsimp [t]; simp only [add_assoc,add_comm]
  have hz : F zeros ![modelNumeral M 2,F zeros ![k,t]] = F zeros ![(k+1)+1,t] := by
    rw [PA194HeaderController.zerosTwo]
    change _ = F zeros ![F addCode ![k+1,F oneCode Fin.elim0],t]
    rw [modelAddOne,modelZerosSucc]
    have hs : F zeros ![k+1,t] = F zeros ![k,t]+F zeros ![k,t] := by
      change F zeros ![F addCode ![k,F oneCode Fin.elim0],t] = _
      rw [modelAddOne,modelZerosSucc]
    simp only [hs]
  let a := F ones ![k+1,l]
  have ho : F ones ![(k+1)+1,l] = a+a+1 := by
    change F ones ![F addCode ![k+1,F oneCode Fin.elim0],l] = _
    rw [modelAddOne,modelOnesSucc]
  have h := scanExit ((k+1)+1) l (r+r)
  dsimp only at h
  rw [←ht,←hz,ho,(PA194BinaryDouble.modelOdd a).1,(PA194BinaryDouble.modelOdd a).2] at h
  exact h
#print axioms returnedFileScan
#print axioms scanExit
end models
end PA194EightyFourScan
