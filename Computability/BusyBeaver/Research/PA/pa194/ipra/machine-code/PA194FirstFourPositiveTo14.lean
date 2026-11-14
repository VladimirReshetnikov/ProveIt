import PA194FirstFourPositiveTo13
import PA194ThirteenExitComposition
import PA194OnesCommute
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FirstFourPositiveTo14
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194FirstFourPositiveTo13 PA194FirstFourPositiveReturn PA194FirstFourPositiveSelected PA194SevenReturnController PA194ReturnCell PA194ReturnFile PA194OnesCommute
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194RegisterFile PA194MarkerScan PA194BinaryDouble
open PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem returnEven (n : Nat) (e : Fin (n+2) → M) (t : M) (ht : e 0 = t+t) :
    ∃ q : M, F (returnCode n) e = q+q := by
  cases n with
  | zero =>
    refine ⟨t,?_⟩
    rw [modelReturnCodeZero,ht]
  | succ n =>
    rw [modelReturnCodeSucc]
    exact ⟨_,rfl⟩

theorem returnBlockEven (n : Nat) (e : Fin (n+3) → M) (t : M) (ht : e 0 = t+t) :
    ∃ m q : M, F (returnCode (n+1)) e = F block ![m,q+q] := by
  let p := F (returnCode n) (Fin.cases (e 0) (fun i => e i.succ.succ))
  obtain ⟨q,hq⟩ := returnEven n (Fin.cases (e 0) (fun i => e i.succ.succ)) t (by simpa using ht)
  refine ⟨e 1,q,?_⟩
  have hs : F ones ![e 1+1,p] = F ones ![e 1,p]+F ones ![e 1,p]+1 := by
    change F ones ![F addCode ![e 1,F oneCode Fin.elim0],p] = _
    rw [modelAddOne,modelOnesSucc]
  have hb : F (returnCode (n+1)) e = F block ![e 1,p] := by
    rw [modelReturnCodeSucc,modelOnesCommute,modelBlock,hs]
  exact hb.trans (congrArg (fun z => F block ![e 1,z]) hq)

theorem selectedEven (k a m q : M) :
    let ret := F block ![m,q+q]
    let l := ((a+a)+(a+a))+((a+a)+(a+a))
    let scanned := F ones ![k,l]
    ∃ time left right : M, F PA194Stepper.stepper ![time,F pairCode ![modelNumeral M 7,
      F pairCode ![F halfCode (fun _ => scanned),F parityCode (fun _ => scanned)+ret+ret]]] =
    F pairCode ![modelNumeral M 13,F pairCode ![left,right+right]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  have he := PRAExhaustion.modelZeroOrSuccPred k
  change k = (0 : M) ∨ F Code.succ (fun _ => F predCode (fun _ => k)) = k at he
  rcases he with hk | hk
  · subst k
    obtain ⟨time,left,h⟩ := selectedZero a m (q+q)
    exact ⟨time,left,q,h⟩
  · let j := F predCode (fun _ => k)
    have hk' : k=j+1 := by
      have hs : F Code.succ (fun _ => j) = j+1 := (modelAddOne j).symm
      exact hk.symm.trans hs
    rw [hk']
    obtain ⟨time,left,h⟩ := selectedSucc j a (F block ![m,q+q])
    refine ⟨time,left,F ones ![m+1,q+q],?_⟩
    simpa only [modelBlock] using h

theorem markerFirstFourPositiveBlankTo14 (n : Nat) (e : Fin 2 → M) (rest : Fin (n+2) → M)
    (u k : M)
    (ht : e (Fin.last 1) =
      let t := F ones ![k+1,F (fileCode (n+1)) rest]; (t+t+1)+(t+t+1))
    (hfirst : e 0 = modelNumeral M 4)
    (hblank : rest (Fin.last (n+1)) = (0 : M)) :
    let z := u+u
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let l64 := z4+z4
    let x := ((l64+l64)+(l64+l64))+((l64+l64)+(l64+l64))+1
    ∃ time left right : M, F PA194Stepper.stepper ![time,
      F pairCode ![modelNumeral M (markerControl ⟨1,by decide⟩),F pairCode ![x+x+1,F (fileCode 1) e]]] =
    F pairCode ![modelNumeral M 14,F pairCode ![left,right]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let a0 := ll+ll+1
  let a1 := a0+a0+1
  let a2 := a1+a1+1
  let a3 := a2+a2+1
  let six := ((1 : M)+1+1)+((1 : M)+1+1)
  let w := F ones ![(1 : M),six+six+1]
  let ret := F (PA194ReturnFile.returnCode (n+1)) (Fin.cases (w+w) rest)
  obtain ⟨time,hreturn⟩ := markerFirstFourPositiveBlankReturn n e rest u k ht hfirst hblank
  obtain ⟨m,q,hblock⟩ := returnBlockEven (M := M) n (Fin.cases (w+w) rest) w rfl
  obtain ⟨more,left,right,hselected⟩ := selectedEven k a3 m q
  rw [←hblock] at hselected
  refine ⟨(time+more)+1,F halfCode (fun _ => left),
    F parityCode (fun _ => left)+(right+right)+(right+right),?_⟩
  change F PA194Stepper.stepper ![F addCode ![time+more,F oneCode Fin.elim0],_] = _
  rw [modelAddOne,PA194Stepper.modelStepperSucc]
  change F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![F addCode ![time,more],_]) = _
  rw [PA194StepperCompose.modelStepperCompose,hreturn,hselected]
  exact PA194ThirteenExitComposition.modelPackedThirteenExit left right
#print axioms markerFirstFourPositiveBlankTo14
#print axioms returnEven
#print axioms returnBlockEven
#print axioms selectedEven
end models
end PA194FirstFourPositiveTo14
