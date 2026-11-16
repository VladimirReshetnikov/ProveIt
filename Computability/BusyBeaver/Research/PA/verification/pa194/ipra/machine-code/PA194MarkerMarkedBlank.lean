import PA194PositiveMarkCycle
import PA194ReturnedDecrement
import PA194DecrementFirstReturn
import PA194MarkedCycleDecrement
import PA194SevenToSixteen
import PA194ReturnedUpdatedEven
import PA194MarkerPositiveReturn
import PA194SixteenHeaderReturn
import PA194MarkerPositiveSixteen
import PA194MarkerHeaderRecurrence
import PA194HeaderTo84
import PA194EightyFourTo17
import PA194MarkerTo84
import PA194Second17Return
import PA194MarkerSecond17
import PA194OddHeaderTo106
import PA194UpdatedSevenMatch
import PA194UpdatedSevenOdd
import PA194UpdatedSevenBlank
import PA194SevenRewind
import PA194FileTraversal
import PA194MarkerTo106
import PA194MarkerThird17
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194MarkerMarkedBlank
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble
open PA194PositiveMarkCycle PA194ReturnedDecrement PA194ReturnFileMeaning
open PA194MarkedCycleDecrement PA194DecrementFirstReturn PA194MarkerPositiveReturn
open PA194SevenToSixteen PA194ReturnedUpdatedEven PA194MarkerPositiveSixteen PA194SixteenHeaderReturn
open PA194MarkerHeaderRecurrence PA194HeaderTo84 PA194IncrementDispatch PA194HeaderController
open PA194UpdatedSevenOdd PA194UpdatedSevenBlank PA194SevenRewind
open PA194MarkerTo84 PA194EightyFourTo17 PA194MarkerSecond17 PA194Second17Return
open PA194MarkerThird17 PA194OddHeaderTo106 PA194MarkerTo106 PA194UpdatedSevenMatch
open PA194MarkAll PA194CarryFile PA194RegisterFile PA194ReturnFile PA194MarkerScan PA194MarkedFile
open PRAModelIOpenPairing TableDispatch
open PA194UpdatedSevenOdd PA194UpdatedSevenBlank PA194SevenRewind
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem markerMarkedBlank (idx n : Nat) (bound : idx+1 < 9)
    (hn : idx+n=7)
    (e : Fin (idx+2) → M) (rest : Fin (n+2) → M) (v u k : M)
    (ht : e (Fin.last (idx+1)) =
      let t := F ones ![v,F (fileCode (n+1)) rest]; (t+t+1)+(t+t+1))
    (hblank : rest (Fin.last (n+1)) = (0 : M))
    (hfirst : e 0 = ((((((k+1)+1)+1)+1)+1)+1)+1)
    (hv : v ≠ (0 : M)) :
    letI : DecidableEq M := Classical.decEq M
    let tail := F (fileCode (n+1)) rest
    let z := u+u
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let l64 := z4+z4
    let x := ((l64+l64)+(l64+l64))+((l64+l64)+(l64+l64))+1
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let a0 := ll+ll+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let a3 := a2+a2+1
    let ep := replaceLast idx (fun i : Fin (idx+1) => e i.succ) (F markedBlock ![v,tail])
    let cost := F (costCode idx) ep
    let pred := F predCode (fun _ => v)
    let p := F (fileCode idx) (replaceLast idx (fun i : Fin (idx+1) => e i.succ) (F block ![pred,tail]))
    let isZero := v = (0 : M)
    let markClock := (F (costCode (idx+1)) e+modelNumeral M 3)+F (costCode (idx+1)) e
    let headerClock := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    let c1 := modelNumeral M 6+((modelNumeral M 3+1)+1)
    let cycleClock := (((c1+headerClock)+modelNumeral M 3)+modelNumeral M 3)+1
    let phaseClock := ((markClock+headerClock)+modelNumeral M 3)+cycleClock
    let decrementClock := (modelNumeral M 2+(k+1))+((cost+(if isZero then modelNumeral M 7 else modelNumeral M 4))+cost)
    let nn := modelNumeral M 2
    let c := (((((((nn+1)+(k+1))+1)+1)+k)+nn)+1)+1
    ∃ (r : M) (file : Fin 8 → M) (t s next spare : M), p = r+r ∧ p = F (fileCode 7) file ∧ file (Fin.last 7) = t+t ∧ t=s+s+1 ∧ s=F ones ![next,F (fileCode 1) ![spare,(0 : M)]] ∧
      let controllerClock := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
      let l := F ones ![k,(a3+a3)+(a3+a3)]
      let l1 := l+l+1
      let l2 := l1+l1+1
      let rev : Fin 7 → M := ![file 5,file 4,file 3,file 2,file 1,file 0,l2+l2]
      let marked := F (markedFile 1) ![next,spare,(0 : M)]
      let ep := replaceLast 7 file marked
      let rewound := F (fileCode 7) ep
      F PA194Stepper.stepper ![((((((((phaseClock+decrementClock)+(((k+1)+1)+1))+(modelNumeral M 2+c))+
          ((modelNumeral M 3+1)+1))+(((controllerClock+modelNumeral M 3)+modelNumeral M 4)+1+modelNumeral M 10))+
          (((((k+1)+1)+1)+1)+((k+1)+1))+((modelNumeral M 4+1)+1))+
          ((((controllerClock+modelNumeral M 3)+modelNumeral M 4)+1)+((modelNumeral M 3+k)+modelNumeral M 3)))+F (costCode 7) file)+((modelNumeral M 2+((file 6+1)+1))+F (costCode 6) rev),
        F pairCode ![modelNumeral M (markerControl ⟨idx+1,bound⟩),F pairCode ![x+x+1,F (fileCode (idx+1)) e]]] =
      F pairCode ![modelNumeral M 17,F pairCode ![l1,(1 : M)+rewound+rewound]] := by
  classical
  dsimp only
  have hm := markerTo106 idx n bound e rest v u k ht hfirst hv
  dsimp only at hm
  simp only [hv,if_false] at hm ⊢
  obtain ⟨r,hr,hm⟩ := hm
  obtain ⟨file,t,s,next,spare,hfile,htail,hs,hones⟩ := matchSevenBlank idx n hn e rest (F predCode (fun _ => v)) hblank
  refine ⟨r,file,t,s,next,spare,hr,hfile,htail,hs,hones,?_⟩
  have hh : F halfCode (fun _ => F (fileCode 7) file) = r := by
    rw [←hfile,hr,(PA194BinaryDouble.modelDouble r).2]
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let a0 := ll+ll+1
  let a1 := a0+a0+1
  let a2 := a1+a1+1
  let a3 := a2+a2+1
  let l := F ones ![k,(a3+a3)+(a3+a3)]
  let l1 := l+l+1
  let l2 := l1+l1+1
  have hscan := PA194FileTraversal.scanSeven file (l2+l2) t htail
  rw [hh,hs] at hscan
  have hrew := sevenTo17 file l1 s
  dsimp only at hrew
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![F addCode ![_,F (costCode 7) file],_]] = _
  rw [PA194StepperCompose.modelStepperCompose,hm,hscan,hrew]
  have hmarked : F (markedFile 1) ![next,spare,(0 : M)] = (s+s)+(s+s) := by
    rw [modelMarkedFile]
    have hv : (fun i : Fin 2 => (![next,spare,(0 : M)] : Fin 3 → M) i.succ) = ![spare,(0 : M)] := by
      funext i
      fin_cases i <;> rfl
    simp only [Matrix.cons_val_zero,hv,modelMarkedBlock,←hones]
  rw [hmarked]
  have hvec : replaceLast 7 file ((s+s)+(s+s)) =
      ![file 0,file 1,file 2,file 3,file 4,file 5,file 6,(s+s)+(s+s)] := by
    funext i
    fin_cases i <;> simp [replaceLast,Fin.snoc]
  rw [hvec]
#print axioms markerMarkedBlank
end models
end PA194MarkerMarkedBlank
