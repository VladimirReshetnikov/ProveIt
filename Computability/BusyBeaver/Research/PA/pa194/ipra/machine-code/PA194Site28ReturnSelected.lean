import PA194ReturnCell
import PA194OnesCommute
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site28ReturnSelected
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194ReturnCell PA194OnesCommute PA194UnaryRuns PA194BinaryDouble PA194StateOne PRAModelIOpenPairing BinaryTapeCodes
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem returnSelected (n v k l t : M) :
    let d0 := F ones ![k,(l+l)+(l+l)]
    let d1 := d0+d0+1
    let d2 := d1+d1
    let d3 := d2+d2+1
    let d4 := F ones ![v,d3]
    let left := (d4+d4)+(d4+d4)+1
    let marked := F ones ![n+1,left]
    let w1 := F ones ![n+1,(1 : M)+t+t]
    let t1 := w1+w1
    let w2 := F ones ![v,(1 : M)+t1+t1]
    let t2 := w2+w2
    let w3 := F ones ![k,(1 : M)+t2+t2]
    F PA194Stepper.stepper ![(k+1)+1,
      F PA194Stepper.stepper ![(v+1)+1,
        F PA194Stepper.stepper ![((n+1)+1)+1,
          F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => marked),t+t+1]]]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![l,(w3+w3)+(w3+w3)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let d0 := F ones ![k,(l+l)+(l+l)]
  let d1 := d0+d0+1
  let d2 := d1+d1
  let d3 := d2+d2+1
  let d4 := F ones ![v,d3]
  let left := (d4+d4)+(d4+d4)+1
  let marked := F ones ![n+1,left]
  let w1 := F ones ![n+1,(1 : M)+t+t]
  let t1 := w1+w1
  let w2 := F ones ![v,(1 : M)+t1+t1]
  let t2 := w2+w2
  have hm : F halfCode (fun _ => marked) = F ones ![n+1,d4+d4] := by
    have hs : marked = F ones ![n,left]+F ones ![n,left]+1 := by
      dsimp only [marked]
      change F ones ![F addCode ![n,F oneCode Fin.elim0],_] = _
      rw [modelAddOne,modelOnesSucc]
    rw [hs,(modelOdd _).2]
    have hc := modelOnesCommute n (d4+d4)
    change F ones ![n,left] = F ones ![n,d4+d4]+F ones ![n,d4+d4]+1 at hc
    rw [hc]
    change _ = F ones ![F addCode ![n,F oneCode Fin.elim0],_]
    rw [modelAddOne,modelOnesSucc]
  have hd4 : d4 = F ones ![v,d2]+F ones ![v,d2]+1 := by
    dsimp only [d4,d3]
    exact modelOnesCommute v d2
  have hd4odd : F parityCode (fun _ => d4) = (1 : M) := by rw [hd4,(modelOdd _).1]
  have hd4half : F halfCode (fun _ => d4) = F ones ![v,d2] := by rw [hd4,(modelOdd _).2]
  have hd1odd : F parityCode (fun _ => d1) = (1 : M) := (modelOdd d0).1
  have hd1half : F halfCode (fun _ => d1) = d0 := (modelOdd d0).2
  have h1 := modelReturnCell (n+1) d4 t
  dsimp only at h1
  rw [hd4odd,hd4half] at h1
  have h2 := modelReturnCell v d1 t1
  dsimp only at h2
  rw [hd1odd,hd1half] at h2
  have h3 := modelReturnCell k (l+l) t2
  dsimp only at h3
  rw [(modelDouble l).1,(modelDouble l).2,zero_add] at h3
  rw [hm]
  have heq1 : (1 : M)+(w1+w1)+(w1+w1) = t1+t1+1 := by dsimp only [t1]; simp only [add_assoc,add_comm,add_left_comm]
  have heq2 : (1 : M)+(w2+w2)+(w2+w2) = t2+t2+1 := by dsimp only [t2]; simp only [add_assoc,add_comm,add_left_comm]
  rw [heq1] at h1
  rw [heq2] at h2
  rw [h1,h2,h3]
#print axioms returnSelected
end models
end PA194Site28ReturnSelected
