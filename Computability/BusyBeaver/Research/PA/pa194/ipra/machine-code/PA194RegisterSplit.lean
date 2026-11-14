import PA194DecrementChoice
import PA194ReturnFileMeaning
set_option autoImplicit false
set_option maxRecDepth 2048
namespace PA194RegisterSplit
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterFile PA194MarkedFile PA194ReturnFile PA194ReturnFileMeaning
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
def tailArgs (p : Fin 9) (a : Fin 11 → M) : Fin (8-p.val+2) → M := fun i => a ⟨p.val+1+i.val,by have := p.isLt; have := i.isLt; omega⟩
def frontArgs (p : Fin 9) (a : Fin 11 → M) (marked : M) : Fin (p.val+1) → M :=
  Fin.snoc (fun i => a ⟨i.val,by have := p.isLt; have := i.isLt; omega⟩) marked

/-- Restoring an arbitrary physical prefix and replacing its selected block
changes exactly that physical slot; the tail contains the spare register. -/
theorem splitFile (p : Fin 9) (a : Fin 11 → M) (z marked : M) :
    F (returnCode p.val) (Fin.cases (F block ![z,F (fileCode (8-p.val+1)) (tailArgs p a)]) (frontArgs p a marked)) =
      F (fileCode 10) (Function.update a ⟨p.val,by have := p.isLt; omega⟩ z) := by
  rw [modelReturnMeaning]
  rcases p with ⟨p,hp⟩
  have hs : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 := by omega
  rcases hs with h | h | h | h | h | h | h | h | h <;> subst p <;>
    simp only [modelFileSucc] <;>
    simp [tailArgs,frontArgs,replaceLast,Fin.snoc,Function.update,show ∀ e : Fin 1 → M, F (fileCode 0) e = e 0 from fun e => modelProjection 0 e]

#print axioms splitFile
end models
end PA194RegisterSplit
