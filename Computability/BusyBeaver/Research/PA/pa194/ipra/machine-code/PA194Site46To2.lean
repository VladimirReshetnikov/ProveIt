import PA194Site46SecondPass
import PA194Site46ThirdPrefix
import PA194Site46SecondTo17
import PA194Site46SecondReturn
import PA194Site46SecondTo14
import PA194FourteenOddTo16
import PA194Site35SixteenSixRuns
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site46To2
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194Path27Header PA194RegisterPermutation PA194RegisterFile BinaryTapeCodes TableDispatch PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem to2 (k : M) (args : Fin 11 → M) :
    let e := physicalArgs args
    let out := PA194Site46SecondTo17.output k args
    F PA194Stepper.stepper ![modelNumeral M 9,
      F PA194Stepper.stepper ![modelNumeral M 24,
        F PA194Stepper.stepper ![((k+1)+1)+1,
          F PA194Stepper.stepper ![PA194Site46SecondTo17.fourCost args,
            F PA194Stepper.stepper ![modelNumeral M 3,
              F PA194Stepper.stepper ![PA194Site46SecondTo17.clock14 k args,
                PA194SourceSite31Physical.physicalFrame 46 ((k+1)+1) args]]]]]] =
      F pairCode ![modelNumeral M 2,F pairCode ![modelNumeral M 824,F halfCode (fun _ => out)]] := by
  dsimp only
  let out := PA194Site46SecondTo17.output k args
  have hod (z : M) : ∃ p : M, F ones ![k+1,z] = p+p+1 := by
    refine ⟨F ones ![k,z],?_⟩
    change F ones ![F addCode ![k,F oneCode Fin.elim0],z] = _
    rw [modelAddOne,modelOnesSucc]
  have hodd : ∃ p : M, out = p+p+1 := by
    dsimp only [out,PA194Site46SecondTo17.output]
    exact hod _
  obtain ⟨p,hp⟩ := hodd
  have hhalf : F halfCode (fun _ => out) = p := by rw [hp,(modelOdd p).2]
  have h := PA194Site46SecondPass.secondPass k args
  dsimp only at h
  change _ = F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),modelWord (PA194SourceProgram.path 46) (out+out)]] at h
  rw [PA194Site46To109.path46,hp] at h
  have hpref := PA194Site46ThirdPrefix.prefixWord p
  simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false,modelNumeralOne] at hpref
  simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false] at h
  rw [h,hpref,hhalf]
#print axioms to2
end models
end PA194Site46To2
