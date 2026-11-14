import PA194StateOne
import PA194BinaryDouble
import PA194RightRows
import PA194RegisterEngine
import PA194StepperCompose
set_option autoImplicit false
namespace PA194SevenReturnController
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PRABooleanOps PRAIsZero
open BinaryTapeCodes TableDispatch TableModelSemantics ConfigurationStep PackedRootModel PA194FiniteControls PA194StateOne PA194BinaryDouble

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelSevenEven (l r : M) :
    (F nextQ ![modelNumeral M 7,l,r+r], F nextL ![modelNumeral M 7,l,r+r],
      F nextR ![modelNumeral M 7,l,r+r]) = (modelNumeral M 9,F halfCode (fun _ => l),F parityCode (fun _ => l)+(r+r)+(r+r)) := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hq : modelNumeral M 7 < modelNumeral M 194 := modelNumeralStrict 7 194 (by decide)
  have hactive : F ltBitCode ![modelNumeral M 7,modelNumeral M 194] ≠ F (Code.zero 0) Fin.elim0 := by
    intro hz
    exact ((modelLtZero _ _).mp hz) hq
  have hr := modelDouble r
  have ha : modelNumeral M 7 + modelNumeral M 7 + F parityCode (fun _ => r+r) = modelNumeral M 14 := by
    rw [hr.1]
    simp only [add_zero]
    rw [←modelNumeralAdd]
  have hw : lookupSem 0 writes (modelNumeral M 14) = (0 : M) := by
    rw [←modelLookupAll]
    change F writeCode (fun _ => modelNumeral M 14) = _
    rw [modelWriteNumeral]
    rfl
  have hd : lookupSem 0 directions (modelNumeral M 14) = (0 : M) := by
    rw [←modelLookupAll]
    change F directionCode (fun _ => modelNumeral M 14) = _
    rw [modelDirectionNumeral]
    rfl
  have ht : lookupSem 194 targets (modelNumeral M 14) = modelNumeral M 9 := by
    rw [←modelLookupAll]
    change F targetCode (fun _ => modelNumeral M 14) = _
    rw [modelTargetNumeral]
    rfl
  have hn := modelNext (![modelNumeral M 7,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hn
  change (F nextQ ![modelNumeral M 7,l,r+r],F nextL ![modelNumeral M 7,l,r+r],
    F nextR ![modelNumeral M 7,l,r+r]) = stepSem (modelNumeral M 7) l (r+r) at hn
  rw [hn]
  simp only [stepSem]
  have hadd (a b : M) : F addCode ![a,b] = a+b := rfl
  simp only [hadd,ha,hw,hd,ht,hactive,ite_false,hr.2,zero_add]
  have hz : (0 : M) = F (Code.zero 0) Fin.elim0 := rfl
  simp only [hz,ite_true]
  simp only [add_assoc]
theorem packed7zero (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 7,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M 9,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+(r+r)+(r+r)]] := by
  rw [PackedIterationModel.modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![modelNumeral M 7,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![modelNumeral M 7,l,r+r],F nextL ![modelNumeral M 7,l,r+r],
    F nextR ![modelNumeral M 7,l,r+r]) = stepSem (modelNumeral M 7) l (r+r) at hm
  rw [←hm,modelSevenEven]

theorem sevenToTwelve (a p : M) :
    F PA194Stepper.stepper ![modelNumeral M 2,F pairCode ![modelNumeral M 7,F pairCode ![a+a,p+p]]] =
    F pairCode ![modelNumeral M 12,F pairCode ![(a+a)+1,p+p]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 1),_] = _
  rw [PA194Stepper.modelStepperSucc,
    show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
    PA194Stepper.modelStepperSucc,
    show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
    PA194Stepper.modelStepperZero,packed7zero,(modelDouble a).1,(modelDouble a).2,zero_add]
  have h := PA194RightRows.rightZero 9 1 12 (by decide) (by decide +kernel) a (p+p)
  rw [h,PA194StateOne.modelNumeralOne]
theorem sevenToBlock (a p : M) :
    F PA194Stepper.stepper ![modelNumeral M 3,F pairCode ![modelNumeral M 7,F pairCode ![a+a,p+p]]] =
    F pairCode ![modelNumeral M 12,F pairCode ![((a+a)+1)+((a+a)+1),p]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 2),_] = _
  rw [PA194Stepper.modelStepperSucc,sevenToTwelve]
  have h := PA194RightRows.rightZero 12 0 12 (by decide) (by decide +kernel) ((a+a)+1) p
  simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h
/-- The returned first block is then consumed by the state-12 scanner;
its m bits move left as zeros while the updated remaining file stays intact. -/
theorem sevenThroughFirst (m a p : M) :
    let b := F PA194RegisterFile.block ![m,p]
    let l := ((a+a)+1)+((a+a)+1)
    F PA194Stepper.stepper ![modelNumeral M 3+(((1 : M)+1)+m),
      F pairCode ![modelNumeral M 7,F pairCode ![a+a,b+b]]] =
    F pairCode ![modelNumeral M 13,F pairCode ![F PA194ZeroRuns.zeros ![m,(l+l)+(l+l)],p]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let b := F PA194RegisterFile.block ![m,p]
  let l := ((a+a)+1)+((a+a)+1)
  have hr := PA194RegisterEngine.modelFirstRegister 0 ![m,p] l
  simp only [Matrix.cons_val_zero,PA194RegisterFile.modelFileSucc] at hr
  rw [PA194RegisterFile.fileCode,modelProjection] at hr
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 3,((1 : M)+1)+m],_] = _
  rw [PA194StepperCompose.modelStepperCompose,sevenToBlock]
  exact hr
/-- Compose an existing state-7 return with the new controller and scan. -/
theorem continueThroughFirst (m a p time start : M)
    (hrun : F PA194Stepper.stepper ![time,start] =
      F pairCode ![modelNumeral M 7,F pairCode ![a+a,
        F PA194RegisterFile.block ![m,p]+F PA194RegisterFile.block ![m,p]]]) :
    let l := ((a+a)+1)+((a+a)+1)
    F PA194Stepper.stepper ![time+(modelNumeral M 3+(((1 : M)+1)+m)),start] =
      F pairCode ![modelNumeral M 13,F pairCode ![F PA194ZeroRuns.zeros ![m,(l+l)+(l+l)],p]] := by
  dsimp only
  change F PA194Stepper.stepper ![F addCode ![time,_],start] = _
  rw [PA194StepperCompose.modelStepperCompose,hrun]
  exact sevenThroughFirst m a p
#print axioms continueThroughFirst
#print axioms sevenThroughFirst
#print axioms sevenToBlock
#print axioms sevenToTwelve
#print axioms modelSevenEven
end models
end PA194SevenReturnController
