import PA194ReturnSeven
import PA194OnesCommute
import PA194SixBoundaryComposition
import PA194SixScanInvariant
import PA194UnaryRuns
import PA194StepperCompose
set_option autoImplicit false
namespace PA194ReturnCell
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194ReturnSeven PA194OnesCommute PA194SixBoundaryComposition BinaryTapeCodes PA194BinaryDouble PA194StateSix PA194StateSixEven PA194StateSixBoundary PA194SixScanInvariant PA194UnaryRuns PackedIterationModel ConfigurationStep PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem modelPackedBoundary (l r : M) :
    F PackedClock.encodedStep
      (fun _ => F pairCode ![TableDispatch.modelNumeral M 6,F pairCode ![l+l,r+r+1]]) =
    F pairCode ![TableDispatch.modelNumeral M 6,F pairCode ![l,(r+r+1)+(r+r+1)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 6,l+l,r+r+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 6,l+l,r+r+1],F nextL ![TableDispatch.modelNumeral M 6,l+l,r+r+1],
    F nextR ![TableDispatch.modelNumeral M 6,l+l,r+r+1]) = stepSem (TableDispatch.modelNumeral M 6) (l+l) (r+r+1) at hm
  rw [←hm,modelStateSixOddEven]

theorem modelPackedReturnSeven (l r : M) :
    F PackedClock.encodedStep
      (fun _ => F pairCode ![TableDispatch.modelNumeral M 7,F pairCode ![l,r+r+1]]) =
    F pairCode ![TableDispatch.modelNumeral M 6,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+(1+1)+(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 7,l,r+r+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 7,l,r+r+1],F nextL ![TableDispatch.modelNumeral M 7,l,r+r+1],
    F nextR ![TableDispatch.modelNumeral M 7,l,r+r+1]) = stepSem (TableDispatch.modelNumeral M 7) l (r+r+1) at hm
  rw [←hm,modelReturnSeven]

/-- Return one unary register block, preserving arbitrary model tape tails. -/
theorem modelReturnCell (n l t : M) :
    let a := F ones ![n,(1 : M)+t+t]
    F PA194Stepper.stepper ![(n+1)+1,F pairCode ![TableDispatch.modelNumeral M 7,
      F pairCode ![F ones ![n,l+l],t+t+1]]] =
    F pairCode ![TableDispatch.modelNumeral M 7,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(a+a)+(a+a)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have exhaust := PRAExhaustion.modelZeroOrSuccPred n
  change n = (0 : M) ∨ F Code.succ (fun _ => F predCode (fun _ => n)) = n at exhaust
  rcases exhaust with hn | hn
  · subst n
    have hs (x : M) : F PA194Stepper.stepper ![x+1,F pairCode ![TableDispatch.modelNumeral M 7,
        F pairCode ![l+l,t+t+1]]] = F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![x,
          F pairCode ![TableDispatch.modelNumeral M 7,F pairCode ![l+l,t+t+1]]]) := by
      change F PA194Stepper.stepper ![F addCode ![x,F oneCode Fin.elim0],_] = _
      rw [modelAddOne,PA194Stepper.modelStepperSucc]
    rw [modelOnesZero,modelOnesZero]
    simp only [zero_add]
    have hs0 := hs (0 : M)
    simp only [zero_add] at hs0
    have hzero := PA194Stepper.modelStepperZero (F pairCode ![TableDispatch.modelNumeral M 7,F pairCode ![l+l,t+t+1]])
    change F PA194Stepper.stepper ![(0 : M),_] = _ at hzero
    rw [hs,hs0,hzero,modelPackedReturnSeven]
    rw [(modelDouble l).1,(modelDouble l).2]
    simp only [zero_add]
    have hdouble : (1 : M)+1+(t+t)+(t+t) = ((1 : M)+t+t)+((1 : M)+t+t) := by
      simp only [add_assoc,add_comm,add_left_comm]
    rw [hdouble,modelPackedExit]
  · have hn' : ∃ k : M, n = k+1 := by
      let k := F predCode (fun _ => n)
      have hh : F Code.succ (fun _ => k) = k+1 := (modelAddOne k).symm
      exact ⟨k,hn.symm.trans hh⟩
    rcases hn' with ⟨k,rfl⟩
    let w := F ones ![k,l+l]
    let r := (1 : M)+t+t
    have hleft : F ones ![k+1,l+l] = w+w+1 := by
      change F ones ![F addCode ![k,F oneCode Fin.elim0],_] = _
      rw [modelAddOne,modelOnesSucc]
    have hright : (1 : M)+(1+1)+(t+t)+(t+t) = r+r+1 := by
      dsimp [r]
      simp only [add_assoc,add_comm,add_left_comm]
    have hfirst : F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 7,
        F pairCode ![F ones ![k+1,l+l],t+t+1]]) =
        F pairCode ![TableDispatch.modelNumeral M 6,F pairCode ![F ones ![k,l+l],r+r+1]] := by
      rw [hleft,modelPackedReturnSeven,(modelOdd w).1,(modelOdd w).2]
      rw [hright]
    let init := F pairCode ![TableDispatch.modelNumeral M 7,F pairCode ![F ones ![k+1,l+l],t+t+1]]
    have hs : F PA194Stepper.stepper ![(0 : M)+1,init] = F PackedClock.encodedStep (fun _ => init) := by
      change F PA194Stepper.stepper ![F addCode ![(0 : M),F oneCode Fin.elim0],init] = _
      rw [modelAddOne,PA194Stepper.modelStepperSucc]
      have hzero := PA194Stepper.modelStepperZero init
      change F PA194Stepper.stepper ![(0 : M),init] = _ at hzero
      rw [hzero]
    have htime : (k+1)+1+1 = (1 : M)+(k+1+1) := by simp only [add_comm,add_left_comm]
    rw [htime]
    change F PA194Stepper.stepper ![F addCode ![(1 : M),k+1+1],init] = _
    have hs1 : F PA194Stepper.stepper ![(1 : M),init] = F PackedClock.encodedStep (fun _ => init) := by
      simpa only [zero_add] using hs
    rw [PA194StepperCompose.modelStepperCompose,hs1,hfirst,modelScanExit]
#print axioms modelReturnCell
#print axioms modelPackedReturnSeven
end models
end PA194ReturnCell
