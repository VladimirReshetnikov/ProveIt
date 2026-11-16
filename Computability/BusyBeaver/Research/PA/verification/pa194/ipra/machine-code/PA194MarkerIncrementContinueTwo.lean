import PA194IncrementContinueTwo
import PA194MarkerToIncrement
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194MarkerIncrementContinueTwo
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
open PA194MarkerMarkedBlank PA194MarkedExitIncrement
open PA194MarkerTo84 PA194EightyFourTo17 PA194MarkerSecond17 PA194Second17Return
open PA194MarkerToIncrement PA194IncrementContinueTwo
open PA194MarkerThird17 PA194OddHeaderTo106 PA194MarkerTo106 PA194UpdatedSevenMatch
open PA194MarkAll PA194CarryFile PA194RegisterFile PA194ReturnFile PA194MarkerScan PA194MarkedFile
open PRAModelIOpenPairing TableDispatch
open PA194UpdatedSevenOdd PA194UpdatedSevenBlank PA194SevenRewind
open PA194MarkerMarkedBlank PA194MarkedExitIncrement
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem markerToContinueTarget (idx n : Nat) (bound : idx+1 < 9)
    (hn : idx+n=7)
    (e : Fin (idx+2) → M) (rest : Fin (n+2) → M) (v u k j : M)
    (ht : e (Fin.last (idx+1)) =
      let t := F ones ![v,F (fileCode (n+1)) rest]; (t+t+1)+(t+t+1))
    (hblank : rest (Fin.last (n+1)) = (0 : M))
    (hfirst : e 0 = ((((((k+1)+1)+1)+1)+1)+1)+1)
    (hv : v ≠ (0 : M)) (hk : k = j+1) :
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
      let g2 := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
      let h2 := g2+g2+1
      let xx2 := h2+h2+1
      let ll2 := (xx2+xx2)+(xx2+xx2)+1
      let b0 := ll2+ll2+1
      let b1 := b0+b0+1
      let b2 := b1+b1+1
      let b3 := b2+b2+1
      let tailArgs : Fin 3 → M := ![next,spare,(0 : M)]
      let prefixCost := F (costCode 7) ep
      let front := (((1 : M)+1)+next)+F (costCode 1) (fun i => tailArgs i.succ)
      let incCost := ((front+modelNumeral M 6)+F (costCode 1) (fun i => tailArgs i.succ))+((next+1)+1+1)
      let triple := ((1 : M)+1)+1
      let six := triple+triple
      let endFile := F (fileCode 1) (replaceLast 1 (fun i => tailArgs i.succ) six)
      let result := F block ![next+1,endFile]
      let out := F (returnCode 7) (Fin.cases result ep)
      let retClock := (prefixCost+incCost)+prefixCost
      let cdispatch1 := ((((k+1)+1)+1)+1)+1+((modelNumeral M 3+1)+1)
      let cdispatch2 := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
      let dispatch := (cdispatch1+(((cdispatch2+modelNumeral M 3)+modelNumeral M 4)+1))+modelNumeral M 10
      F PA194Stepper.stepper ![(((((((((phaseClock+decrementClock)+(((k+1)+1)+1))+(modelNumeral M 2+c))+
          ((modelNumeral M 3+1)+1))+(((controllerClock+modelNumeral M 3)+modelNumeral M 4)+1+modelNumeral M 10))+
          (((((k+1)+1)+1)+1)+((k+1)+1))+((modelNumeral M 4+1)+1))+
          ((((controllerClock+modelNumeral M 3)+modelNumeral M 4)+1)+((modelNumeral M 3+k)+modelNumeral M 3)))+F (costCode 7) file)+((modelNumeral M 2+((file 6+1)+1))+F (costCode 6) rev))+(dispatch+(((k+1)+retClock)+((k+1)+1))),
        F pairCode ![modelNumeral M (markerControl ⟨idx+1,bound⟩),F pairCode ![x+x+1,F (fileCode (idx+1)) e]]] =
      F pairCode ![modelNumeral M 7,F pairCode ![b3+b3,F block ![k,out]+F block ![k,out]]] ∧
      ∃ rr : M, out = rr+rr ∧
        let zz := F zeros ![modelNumeral M 2,F zeros ![j,1+(rr+rr)+(rr+rr)]]
        let rrr := zz+zz
        let ttt := (rrr+rrr)+(rrr+rrr)
        let ww := F ones ![modelNumeral M 3,1+ttt+ttt]
        ∃ endClock : M, F PA194Stepper.stepper ![endClock,
          F pairCode ![modelNumeral M (markerControl ⟨idx+1,bound⟩),F pairCode ![x+x+1,F (fileCode (idx+1)) e]]] =
          F pairCode ![modelNumeral M 24,F pairCode ![h,1+(ww+ww)+(ww+ww)]] := by
  classical
  dsimp only
  have hm := markerToIncrement idx n bound hn e rest v u k ht hblank hfirst hv
  dsimp only at hm
  simp only [hv,if_false] at hm ⊢
  obtain ⟨r,file,t,s,next,spare,hr,hfile,htail,hs,hones,hm⟩ := hm
  refine ⟨r,file,t,s,next,spare,hr,hfile,htail,hs,hones,hm,?_⟩
  rw [hk] at hm
  have hc := incrementToContinueTarget u j file next spare _ _ hm
  dsimp only at hc
  obtain ⟨rr,hrr,hc⟩ := hc
  refine ⟨rr,hrr,_,hc⟩
#print axioms markerToContinueTarget
end models
end PA194MarkerIncrementContinueTwo
