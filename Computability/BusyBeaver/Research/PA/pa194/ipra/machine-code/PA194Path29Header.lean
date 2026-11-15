import PA194Site28ReturnHeader
import PA194Path28Header
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Path29Header
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Path27Header PA194Path28Header PA194HeaderController PA194ZeroRuns PRAModelIOpenPairing

theorem path29 : PA194SourceProgram.path 29 = [true,false,false,false,true,false,true,true,false] := by decide +kernel
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem resultIsPath29 (k p : M) :
    let z := F zeros ![k,(1 : M)+(p+p)+(p+p)]
    let r := (z+z)+(z+z)
    let r1 := (1 : M)+r+r
    let x := (1+1)+(r1+r1)+(r1+r1)
    let t := (1 : M)+x+x
    let t1 := t+t
    let t2 := t1+t1
    let t3 := t2+t2
    let t4 := t3+t3
    t4+1 = PA194Path27Header.modelWord (PA194SourceProgram.path 29)
      (F zeros ![k+1,(1 : M)+(p+p)+(p+p)]) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let z := F zeros ![k,(1 : M)+(p+p)+(p+p)]
  let r := (z+z)+(z+z)
  have hz1 := modelZerosSucc (M := M) k ((1 : M)+(p+p)+(p+p))
  change F zeros ![F Code.succ (fun _ => k),_] = _ at hz1
  rw [←modelAddOne] at hz1
  change F zeros ![k+1,(1 : M)+(p+p)+(p+p)] = z+z at hz1
  rw [hz1,path29]
  simp only [PA194Path27Header.modelWord,Bool.false_eq_true,↓reduceIte]
  ring
#print axioms path29
#print axioms resultIsPath29
end models
end PA194Path29Header
