import PA194State61Odd
import PA194RightRows
import PA194GenericRightScan
import PA194StepperCompose
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194State61OddRoute
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194BinaryDouble PA194RightRows PA194State61Odd
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
theorem packed61Odd (a b : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 61,F pairCode ![a+a,b+b+1]]) =
    F pairCode ![modelNumeral M 86,F pairCode ![a,((b+b)+1)+((b+b)+1)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![modelNumeral M 61,a+a,b+b+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![modelNumeral M 61,a+a,b+b+1],F nextL ![modelNumeral M 61,a+a,b+b+1],
    F nextR ![modelNumeral M 61,a+a,b+b+1]) = stepSem (modelNumeral M 61) (a+a) (b+b+1) at hm
  rw [←hm,modelState61Odd,(modelDouble a).1,(modelDouble a).2,zero_add]
  simp only [add_assoc,add_comm,add_left_comm]

theorem threeTo85 (a b : M) :
    F PA194Stepper.stepper ![modelNumeral M 3,F pairCode ![modelNumeral M 61,F pairCode ![a+a,b+b+1]]] =
    F pairCode ![modelNumeral M 85,F pairCode ![(a+a)+(a+a),b]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 2),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,PA194Stepper.modelStepperZero,packed61Odd]
  have h1 := rightZero 86 0 73 (by decide) (by decide +kernel) a (b+b+1)
  simp only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] at h1
  have h2 := rightOne 73 0 85 (by decide) (by decide +kernel) (a+a) b
  simp only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] at h2
  rw [h1,h2]

theorem oddTo106 (k a r : M) :
    let s0 := (r+r)+(r+r)+1
    let s := s0+s0+1
    let b := F ones ![k,s]
    let l := F ones ![k,(a+a)+(a+a)]
    let l1 := l+l+1
    let l2 := l1+l1+1
    F PA194Stepper.stepper ![(modelNumeral M 3+k)+modelNumeral M 3,
      F pairCode ![modelNumeral M 61,F pairCode ![a+a,b+b+1]]] =
    F pairCode ![modelNumeral M 106,F pairCode ![l2+l2,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let s0 := (r+r)+(r+r)+1
  let s := s0+s0+1
  let b := F ones ![k,s]
  let l := F ones ![k,(a+a)+(a+a)]
  have hloop (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 85,F pairCode ![x,y+y+1]]) =
      F pairCode ![modelNumeral M 85,F pairCode ![x+x+1,y]] := by
    have h := rightOne 85 1 85 (by decide) (by decide +kernel) x y
    simpa only [PA194StateOne.modelNumeralOne] using h
  have hs := PA194GenericRightScan.modelFullScan 85 hloop k ((a+a)+(a+a)) s
  have hfinish : F PA194Stepper.stepper ![modelNumeral M 3,F pairCode ![modelNumeral M 85,F pairCode ![l,s]]] =
      F pairCode ![modelNumeral M 106,F pairCode ![((l+l+1)+(l+l+1)+1)+((l+l+1)+(l+l+1)+1),r]] := by
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 2),_] = _
    rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,PA194Stepper.modelStepperZero]
    rw [hloop l s0,hloop (l+l+1) (r+r)]
    have he := rightZero 85 0 106 (by decide) (by decide +kernel) ((l+l+1)+(l+l+1)+1) r
    simp only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] at he
    exact he
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 3+k,modelNumeral M 3],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![modelNumeral M 3,F PA194Stepper.stepper ![F addCode ![modelNumeral M 3,k],_]] = _
  rw [PA194StepperCompose.modelStepperCompose,threeTo85,hs,hfinish]
#print axioms oddTo106
#print axioms threeTo85
end models
end PA194State61OddRoute
