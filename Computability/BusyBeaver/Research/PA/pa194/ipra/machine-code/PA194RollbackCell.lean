import PA194RollbackBoundary
import PA194RollbackScanInvariant
import PA194DecrementZeroCell
import PA194StepperCompose
set_option autoImplicit false
namespace PA194RollbackCell
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PA194UnaryRuns PA194BinaryDouble PA194RollbackBoundary PA194RollbackScanInvariant PA194DecrementZeroCell BinaryTapeCodes PackedIterationModel ConfigurationStep
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
    F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 11,F pairCode ![l+l,r+r+1]]) =
    F pairCode ![TableDispatch.modelNumeral M 11,F pairCode ![l,(r+r+1)+(r+r+1)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 11,l+l,r+r+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 11,l+l,r+r+1],F nextL ![TableDispatch.modelNumeral M 11,l+l,r+r+1],
    F nextR ![TableDispatch.modelNumeral M 11,l+l,r+r+1]) = stepSem (TableDispatch.modelNumeral M 11) (l+l) (r+r+1) at hm
  rw [←hm,modelRollbackOddEven]

theorem modelRollbackBoundary (n l r : M) :
    F PA194Stepper.stepper ![n+1,F pairCode ![TableDispatch.modelNumeral M 11,
      F pairCode ![F ones ![n,l+l],r+r+1]]] =
    F pairCode ![TableDispatch.modelNumeral M 11,F pairCode ![l,F ones ![n+1,r]+F ones ![n+1,r]]] := by
  have hstep : F PA194Stepper.stepper ![n+1,F pairCode ![TableDispatch.modelNumeral M 11,
      F pairCode ![F ones ![n,l+l],r+r+1]]] =
      F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![n,F pairCode ![TableDispatch.modelNumeral M 11,
        F pairCode ![F ones ![n,l+l],r+r+1]]]) := by
    change F PA194Stepper.stepper ![F addCode ![n,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,PA194Stepper.modelStepperSucc]
  have hscan := PA194RollbackScanInvariant.modelFullScan n (l+l) r
  have hodd : F ones ![n+1,r] = F ones ![n,r]+F ones ![n,r]+1 := by
    change F ones ![F addCode ![n,F oneCode Fin.elim0],r] = _
    rw [modelAddOne,modelOnesSucc]
  rw [hstep,hscan,hodd,modelPackedBoundary,←hodd]

theorem modelAfterBoundary (l u : M) :
    let a := u+u+1
    F PA194Stepper.stepper ![TableDispatch.modelNumeral M 2,F pairCode ![TableDispatch.modelNumeral M 11,
      F pairCode ![l+l+1,u+u]]] =
    F pairCode ![TableDispatch.modelNumeral M 11,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(a+a)+(a+a)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let a := u+u+1
  have h1 : F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 11,F pairCode ![l+l+1,u+u]]) =
      F pairCode ![TableDispatch.modelNumeral M 8,F pairCode ![l,(a+a)+1]] := by
    rw [packedEleven,(modelOdd l).1,(modelOdd l).2]
    dsimp [a]
    simp only [add_assoc,add_comm,add_left_comm]
  have h2 : F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 8,F pairCode ![l,(a+a)+1]]) =
      F pairCode ![TableDispatch.modelNumeral M 11,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+(a+a)+(a+a)]] := packedEight l a
  have stepNum (k : Nat) (c : M) : F PA194Stepper.stepper ![TableDispatch.modelNumeral M (k+1),c] = F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![TableDispatch.modelNumeral M k,c]) := by
    rw [PA194FiniteControls.modelNumeralSucc]
    change F PA194Stepper.stepper ![F addCode ![TableDispatch.modelNumeral M k,F oneCode Fin.elim0],c] = _
    rw [modelAddOne,PA194Stepper.modelStepperSucc]
  dsimp only
  repeat rw [stepNum]
  have hz : TableDispatch.modelNumeral M 0 = F (Code.zero 0) Fin.elim0 := rfl
  rw [hz,PA194Stepper.modelStepperZero,h1,h2]
theorem modelRollbackCell (n l t : M) :
    let x := F ones ![n,(l+l+1)+(l+l+1)]
    let a := F ones ![n+1,t]
    F PA194Stepper.stepper ![(n+1)+1,F pairCode ![TableDispatch.modelNumeral M 11,
      F pairCode ![F halfCode (fun _ => x),F parityCode (fun _ => x)+t+t]]] =
    F pairCode ![TableDispatch.modelNumeral M 11,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(a+a)+(a+a)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have exhaust := PRAExhaustion.modelZeroOrSuccPred n
  change n = (0 : M) ∨ F Code.succ (fun _ => F predCode (fun _ => n)) = n at exhaust
  rcases exhaust with hn | hn
  · subst n
    dsimp only
    rw [modelOnesZero]
    rw [(modelDouble (l+l+1)).1,(modelDouble (l+l+1)).2]
    simp only [zero_add]
    have hone : F ones ![(1 : M),t] = t+t+1 := by
      have h := modelOnesSucc (0 : M) t
      have hs : F Code.succ (fun _ => (0 : M)) = (1 : M) := by
        have hh := (modelAddOne (0 : M)).symm
        change F Code.succ (fun _ => (0 : M)) = (0 : M)+1 at hh
        simpa using hh
      rw [hs,modelOnesZero] at h
      exact h
    rw [hone]
    have h2 : (1 : M)+1 = TableDispatch.modelNumeral M 2 := by
      rw [←PA194StateOne.modelNumeralOne,←PA194FiniteControls.modelNumeralAdd]
    rw [h2]
    exact modelAfterBoundary l t
  · have hn' : ∃ k : M, n = k+1 := by
      let k := F predCode (fun _ => n)
      have hh : F Code.succ (fun _ => k) = k+1 := (modelAddOne k).symm
      exact ⟨k,hn.symm.trans hh⟩
    rcases hn' with ⟨k,rfl⟩
    dsimp only
    let x := F ones ![k,(l+l+1)+(l+l+1)]
    have hx : F ones ![k+1,(l+l+1)+(l+l+1)] = x+x+1 := by
      change F ones ![F addCode ![k,F oneCode Fin.elim0],_] = _
      rw [modelAddOne,modelOnesSucc]
    rw [hx,(modelOdd x).1,(modelOdd x).2]
    have ht : ((k+1)+1)+1 = (k+1)+TableDispatch.modelNumeral M 2 := by
      have htwo : TableDispatch.modelNumeral M 2 = (1 : M)+1 := by
        rw [←PA194StateOne.modelNumeralOne,←PA194FiniteControls.modelNumeralAdd]
      rw [htwo]
      simp only [add_assoc]
    rw [ht]
    change F PA194Stepper.stepper ![F addCode ![k+1,TableDispatch.modelNumeral M 2],_] = _
    rw [PA194StepperCompose.modelStepperCompose]
    have hscan := modelRollbackBoundary k (l+l+1) t
    have hright : (1 : M)+t+t = t+t+1 := by simp only [add_assoc,add_comm,add_left_comm]
    rw [hright,hscan,modelAfterBoundary]
    have hon : F ones ![(k+1)+1,t] = F ones ![k+1,t]+F ones ![k+1,t]+1 := by
      change F ones ![F addCode ![k+1,F oneCode Fin.elim0],t] = _
      rw [modelAddOne,modelOnesSucc]
    rw [hon]
#print axioms modelRollbackCell
#print axioms modelRollbackBoundary
#print axioms modelAfterBoundary
end models
end PA194RollbackCell
