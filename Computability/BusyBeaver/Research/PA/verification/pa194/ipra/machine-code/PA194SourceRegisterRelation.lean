import PA194SourceRegisters
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SourceRegisterRelation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PA194SourceRegisters
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

def Encodes (file : M) (regs : Fin 9 → M) : Prop :=
  ∀ r, getSem r.val file = regs r

noncomputable def pack (e : Fin 9 → M) (tail : M) : M :=
  pair (e 0) (pair (e 1) (pair (e 2) (pair (e 3) (pair (e 4)
    (pair (e 5) (pair (e 6) (pair (e 7) (pair (e 8) tail))))))))

theorem packEncodes (e : Fin 9 → M) (tail : M) : Encodes (pack e tail) e := by
  intro r
  fin_cases r <;> simp [pack,getSem,pi₁_pair,pi₂_pair]

theorem updateEncodes (file : M) (regs : Fin 9 → M) (h : Encodes file regs)
    (r : Fin 9) (v : M) : Encodes (putSem r.val file v) (Function.update regs r v) := by
  intro j
  by_cases hj : j = r
  · subst j
    rw [readAfterWrite,Function.update_self]
  · have hv : j.val ≠ r.val := by
      intro he
      exact hj (Fin.ext he)
    rw [readOtherAfterWrite r.val j.val file v hv,Function.update_of_ne hj,h j]
#print axioms packEncodes
#print axioms updateEncodes
end models
end PA194SourceRegisterRelation
