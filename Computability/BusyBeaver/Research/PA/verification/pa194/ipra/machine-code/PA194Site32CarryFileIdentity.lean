import PA194Site32CarryTo4
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site32CarryFileIdentity
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194StateOne PA194UnaryRuns PA194OnesCommute PA194RegisterFile PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem carryFile (v : Fin 11 → M) (q : M) :
    let out := F (fileCode 6) ![v 2,v 3,v 4,v 5,v 6,v 7,(q+q)+(q+q)]
    let aR1 := F ones ![v 1,(1 : M)+out+out]
    let aR2 := F ones ![v 0,(1 : M)+(aR1+aR1)+(aR1+aR1)]
    let vec : Fin 9 → M := ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,(q+q)+(q+q)]
    F (fileCode 8) vec = aR2+aR2 := by
  dsimp only
  let vec : Fin 9 → M := ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,(q+q)+(q+q)]
  let vec7 : Fin 8 → M := fun i => vec i.succ
  let out := F (fileCode 6) ![v 2,v 3,v 4,v 5,v 6,v 7,(q+q)+(q+q)]
  let aR1 := F ones ![v 1,(1 : M)+out+out]
  let aR2 := F ones ![v 0,(1 : M)+(aR1+aR1)+(aR1+aR1)]
  have htail : (fun i : Fin 7 => vec7 i.succ) = ![v 2,v 3,v 4,v 5,v 6,v 7,(q+q)+(q+q)] := by
    funext i; fin_cases i <;> rfl
  have hone (n x : M) : F ones ![n+1,x] = F ones ![n,(1 : M)+x+x] := by
    change F ones ![F addCode ![n,F oneCode Fin.elim0],x] = _
    rw [modelAddOne,modelOnesSucc]
    have hx : (1 : M)+x+x = x+x+1 := by ac_rfl
    rw [hx,modelOnesCommute]
  have h7 : F (fileCode 7) vec7 = aR1+aR1 := by
    rw [modelFileSucc,modelBlock,htail]
    change F ones ![v 1+1,out]+F ones ![v 1+1,out] = aR1+aR1
    rw [hone]
  have h8 : F (fileCode 8) vec = aR2+aR2 := by
    rw [modelFileSucc,modelBlock]
    change F ones ![v 0+1,F (fileCode 7) vec7]+F ones ![v 0+1,F (fileCode 7) vec7] = aR2+aR2
    rw [h7,hone]
  exact h8
#print axioms carryFile
end models
end PA194Site32CarryFileIdentity
