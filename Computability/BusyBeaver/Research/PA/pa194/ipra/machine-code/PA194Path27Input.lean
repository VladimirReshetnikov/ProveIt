import PA194Path27Header
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Path27Input
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194Path27Header PA194ZeroRuns PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem site27Input (k f : M) :
    let r := F zeros ![k,f+f+1]
    let s := r+r
    let u0 := s+s
    let u1 := u0+u0
    let u2 := u1+u1
    let u3 := u2+u2+1
    let u4 := u3+u3
    let u5 := u4+u4
    let u6 := u5+u5
    u6+u6+1 = modelWord (PA194SourceProgram.path 27)
      (F zeros ![(k+1)+1,1+(f+f)]) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  have harg : (1 : M)+(f+f)=f+f+1 := by simp only [add_comm]
  rw [harg]
  have hz1 := modelZerosSucc (M := M) k (f+f+1)
  have hz2 := modelZerosSucc (M := M) (k+1) (f+f+1)
  change F zeros ![F Code.succ (fun _ => k),f+f+1] = _ at hz1
  change F zeros ![F Code.succ (fun _ => k+1),f+f+1] = _ at hz2
  rw [←modelAddOne] at hz1 hz2
  change F zeros ![(k+1)+1,f+f+1] = _ at hz2
  change F zeros ![k+1,f+f+1] = _ at hz1
  rw [hz2,hz1,path27]
  simp only [modelWord,Bool.false_eq_true,↓reduceIte]
#print axioms site27Input
end models
end PA194Path27Input
