import PA194Site35SecondPass
import PA194Site35ThirdPrefix
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site35To2
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PRAModelIOpenPairing
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
    let out := PA194Site35SecondTo17.output k args
    let c := F addCode ![F addCode ![F addCode ![PA194Site35To14.clock k args,modelNumeral M 3],PA194Site35SecondTo17.backCost k args],modelNumeral M 25]
    F PA194Stepper.stepper ![F addCode ![c,modelNumeral M 10],
      PA194SourceSite31Physical.physicalFrame 35 ((k+1)+1) args] =
      F pairCode ![modelNumeral M 2,F pairCode ![modelNumeral M 1608,F halfCode (fun _ => out)]] := by
  dsimp only
  let out := PA194Site35SecondTo17.output k args
  have hod (z : M) : ∃ p : M, F ones ![k+1,z] = p+p+1 := by
    refine ⟨F ones ![k,z],?_⟩
    change F ones ![F addCode ![k,F oneCode Fin.elim0],z] = _
    rw [modelAddOne,modelOnesSucc]
  have hodd : ∃ p : M, out = p+p+1 := by
    dsimp only [out,PA194Site35SecondTo17.output]
    exact hod _
  obtain ⟨p,hp⟩ := hodd
  have hhalf : F halfCode (fun _ => out) = p := by rw [hp,(modelOdd p).2]
  have h := PA194Site35SecondPass.secondPass k args
  dsimp only at h
  change _ = F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),modelWord (PA194SourceProgram.path 35) (out+out)]] at h
  rw [PA194Site34PositivePath.path35,hp] at h
  have hpref := PA194Site35ThirdPrefix.prefixWord p
  simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false,modelNumeralOne] at hpref
  simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false] at h
  rw [PA194StepperCompose.modelStepperCompose,h,hpref,hhalf]
#print axioms to2
end models
end PA194Site35To2
