import PA194SecondHeaderPass
import PA194OnesCommute
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SecondHeaderFile
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194OnesCommute
open PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem headerFile (n : Nat) (v : Fin (n+1) → M) (k : M) :
  let f := F (fileCode n) v
  let r := F ones ![k,(f+f+1)+(f+f+1)+1]
  let e : Fin (n+2) → M := Fin.cases (k+1) v
  F (fileCode (n+1)) e = r+r := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  rw [modelFileSucc,modelBlock]
  simp only [Fin.cases_zero,Fin.cases_succ]
  rw [show k+1 = F Code.succ (fun _ => k) from (modelAddOne k)]
  rw [show F Code.succ (fun _ => k)+1 = F Code.succ (fun _ => F Code.succ (fun _ => k)) from modelAddOne _]
  rw [modelOnesSucc,modelOnesSucc]
  rw [modelOnesCommute,modelOnesCommute]
theorem sourceFirstPassShape (k : M) (e : Fin 11 → M) :
  let v := physicalArgs e
  let f := F sourceFileCode e
  let p := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
  let t := (1 : M)+(1+1)+((p+p)+(p+p))+((p+p)+(p+p))
  let r := F ones ![k,t]
  let ext : Fin 12 → M := Fin.cases (k+1) v
  F (fileCode 11) ext = r+r ∧ F ones ![k+1,t] = r+r+1 := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let v := physicalArgs e
  let p := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
  have hf : F (fileCode 10) v = p+p := by rw [modelFileSucc,modelBlock]
  have h := headerFile 10 v k
  dsimp only at h
  rw [hf] at h
  dsimp [p,v] at h
  constructor
  · convert h using 1 <;> simp only [add_assoc,add_comm,add_left_comm]
  · rw [show k+1 = F Code.succ (fun _ => k) from modelAddOne k,modelOnesSucc]
#print axioms sourceFirstPassShape
#print axioms headerFile
end models
end PA194SecondHeaderFile
