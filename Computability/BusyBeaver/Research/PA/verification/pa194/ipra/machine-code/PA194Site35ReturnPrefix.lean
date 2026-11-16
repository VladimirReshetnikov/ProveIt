import PA194PrefixReturn
import PA194OnesCommute
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site35ReturnPrefix
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterFile PA194CarryFile PA194UnaryRuns PA194OnesCommute PA194PrefixReturn PA194ReturnFile PA194ReturnCell PA194BinaryDouble PA194StateOne PRAModelIOpenPairing
open BinaryTapeCodes TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

/-- Return over a fixed number of preceding registers and the model-valued header gap;
the exact right tape is retained as a named primitive-recursive expression. -/
theorem returnPrefix (n : Nat) (k d t : M) (ep : Fin (n+1) → M) :
    let l := d+d
    let x := F (PA194PrefixFile.leftCode n) (Fin.cases (F ones ![k+1,l]) ep)
    let out := F (returnCode n) (Fin.cases t ep)
    let a := F ones ![k,(1 : M)+out+out]
    F PA194Stepper.stepper ![(k+1)+1,
      F PA194Stepper.stepper ![F (costCode n) ep,
        F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => x),
          F parityCode (fun _ => x)+(t+t)]]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => d),
      F parityCode (fun _ => d)+(a+a)+(a+a)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let l := d+d
  let out := F (returnCode n) (Fin.cases t ep)
  let a := F ones ![k,(1 : M)+out+out]
  have hp := modelReturnPrefixFile n ep (F ones ![k+1,l]) t
  dsimp only at hp
  have ho : F ones ![k+1,l] = F ones ![k,l]+F ones ![k,l]+1 := by
    change F ones ![F addCode ![k,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  rw [ho,(modelOdd _).1,(modelOdd _).2] at hp
  have hc := modelReturnCell k d out
  dsimp only at hc
  have hright : (1 : M)+out+out = out+out+1 := by simp only [add_assoc,add_comm,add_left_comm]
  rw [hright] at hc
  have hres : (1 : M)+out+out = out+out+1 := hright
  rw [ho]
  simp only [add_assoc] at hp ⊢
  rw [hp]
  simp only [←add_assoc]
  have hin : (1 : M)+out+out = out+out+1 := hright
  rw [hin,hc]
  simp only [add_assoc]
#print axioms returnPrefix
end models
end PA194Site35ReturnPrefix
