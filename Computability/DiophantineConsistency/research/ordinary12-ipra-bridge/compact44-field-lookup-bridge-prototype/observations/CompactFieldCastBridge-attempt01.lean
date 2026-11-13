import DiophantineConsistency.FixedGraphAnchoredMatch
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactFieldCastBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
abbrev Quad := ℕ × ℕ × ℕ × ℕ

theorem lookup_row (f : Quad → ℕ) (lookup : V → V)
    (hlookup : ∀ m : ℕ, lookup (m:V)=((f (Compact943Data.rows.toArray[m]?.getD (0,0,0,0))):V))
    (i : Fin 943) : lookup (i.val:V)=((f (Compact943Data.row i)):V) := by
  rw [hlookup]
  have hi : i.val<Compact943Data.rows.length := by simpa only [Compact943Data.rows_length] using i.isLt
  simp only [List.getElem?_toArray, List.getElem?_pos _ _ hi, Option.getD_some]
  rfl
#print axioms CompactFieldCastBridge.lookup_row
end CompactFieldCastBridge
