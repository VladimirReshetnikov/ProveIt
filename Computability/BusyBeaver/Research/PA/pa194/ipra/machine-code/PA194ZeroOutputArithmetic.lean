import PA194ZeroOutputFile
import PA194ZeroRuns
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ZeroOutputArithmetic
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194ZeroOutputFile PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem outputArithmetic (k f out : M) (hf : f = ((out+out)+(out+out))+1+1) :
    let q := out+out+1
    let z := F zeros ![k+1,(1 : M)+(q+q)+(q+q)]
    let r := (z+z)+(z+z)
    let t := (1 : M)+r+r
    let t1 := t+t
    let t2 := t1+t1
    let t3 := t2+t2
    let t4 := t3+t3
    let y := F zeros ![k+1,f+f+1]
    let y1 := y+y
    let y2 := y1+y1
    let y3 := y2+y2
    let y4 := y3+y3
    let y5 := y4+y4
    let y6 := y5+y5
    let y7 := y6+y6
    let o2 := (1 : M)+1
    let o4 := o2+o2
    let o8 := o4+o4
    let o16 := o8+o8
    t4+1 = y7+o16+1 := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  have hkey : (1 : M)+(out+out+1+(out+out+1))+(out+out+1+(out+out+1)) = f+f+1 := by
    rw [hf]
    simp only [add_assoc,add_comm,add_left_comm]
  rw [hkey]
  simp only [add_assoc,add_comm,add_left_comm]
#print axioms outputArithmetic
end models
end PA194ZeroOutputArithmetic
