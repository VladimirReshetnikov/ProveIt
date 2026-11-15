import PA194Site28ReturnKick
import PA194Site28ReturnCarry
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site28CarryRoundTrip
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterFile PA194Site28CarryCell PA194Site28CarryFile PA194Site28CarryCodes PA194Site28BlankExit PA194Site28ReturnKick PA194Site28ReturnCarry PA194CarryFile PA194ReturnFile PA194UnaryRuns PA194BinaryDouble PA194StateOne PRAModelIOpenPairing BinaryTapeCodes
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem carryLeftOdd (n : Nat) (e : Fin (n+2) → M) (l : M)
    (hl : F parityCode (fun _ => l) = (1 : M)) :
    F parityCode (fun _ => carryLeft n l e) = (1 : M) := by
  induction n generalizing l with
  | zero => exact hl
  | succ n ih =>
    let next := F ones ![e 0+1,l+l]
    have hs : next = F ones ![e 0,l+l]+F ones ![e 0,l+l]+1 := by
      dsimp only [next]
      change F ones ![F addCode ![e 0,F oneCode Fin.elim0],_] = _
      rw [modelAddOne,modelOnesSucc]
    have ho : F parityCode (fun _ => next) = (1 : M) := by rw [hs,(modelOdd _).1]
    exact ih (fun i => e i.succ) next ho

theorem roundTrip (n : Nat) (e : Fin (n+2) → M) (l : M)
    (hl : F parityCode (fun _ => l) = (1 : M))
    (he : e (Fin.last (n+1)) = (0 : M)) :
    let v := e ⟨n,by omega⟩
    let a := carryLeft n l e
    let z := F ones ![v+1,a+a]
    let s := ((1 : M)+1)+1
    let q := s+s
    let w := F ones ![v,(1 : M)+q+q]
    let t := w+w
    let vals : Fin (n+1) → M := fun i => e i.castSucc
    let out := F (PA194ReturnFile.returnCode n) (Fin.cases t vals)
    F PA194Stepper.stepper ![F (PA194CarryFile.costCode n) vals,
      F PA194Stepper.stepper ![modelNumeral M 2+((v+1)+1),
        F PA194Stepper.stepper ![modelNumeral M 3,
          F PA194Stepper.stepper ![(1 : M)+(v+1),
            F PA194Stepper.stepper ![F (timeCode n) e,
              F pairCode ![modelNumeral M 3,F pairCode ![l,F ones ![e 0+1,F (fileCode n) (fun i => e i.succ)]]]]]]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => l),out+out+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let v := e ⟨n,by omega⟩
  let a := carryLeft n l e
  let z := F ones ![v+1,a+a]
  let s := ((1 : M)+1)+1
  let q := s+s
  let w := F ones ![v,(1 : M)+q+q]
  let t := w+w
  let vals : Fin (n+1) → M := fun i => e i.castSucc
  have ho : F parityCode (fun _ => a) = (1 : M) := carryLeftOdd n e l hl
  have hf := PA194Site28CarryCodes.carryFileCoded (M := M) n e l
  rw [PA194Site28CarryCodes.modelLeft,he] at hf
  have hc := PA194Site28CarryCell.carryCell (M := M) v a (0 : M)
  simp only [zero_add,add_zero] at hc
  have hb := PA194Site28BlankExit.blankExit (M := M) z
  have hs : (1 : M)+(1+1) = s := by dsimp only [s]; simp only [add_assoc]
  rw [hs] at hb
  have hk := PA194Site28ReturnKick.kickReturn (M := M) v a (1 : M)
  dsimp only at hk
  rw [ho] at hk
  change F PA194Stepper.stepper ![modelNumeral M 2+((v+1)+1),
    F pairCode ![modelNumeral M 7,F pairCode ![z+z,s]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => a),(1 : M)+(w+w)+(w+w)]] at hk
  have hright : (1 : M)+(w+w)+(w+w) = t+t+1 := by
    dsimp only [t]; simp only [add_assoc,add_comm,add_left_comm]
  rw [hright] at hk
  have hr := PA194Site28ReturnCarry.returnCarry (M := M) n e l t hl
  dsimp only at hr
  rw [hf,hc,hb,hk,hr]
#print axioms roundTrip
#print axioms carryLeftOdd
end models
end PA194Site28CarryRoundTrip
