import DiophantineConsistency.CompactRowComplete
import DiophantineConsistency.CompactForbidden
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
noncomputable section
namespace CompactNoExtra
open DiophantineConsistency CompactRowTransport
open DiophantineConsistency.ArithmeticWangTable
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem no_east_five_model {i : V} (hi : i < 943) :
    compactField (fun t => t.2.2.1) i ≠ 5 := by
  obtain ⟨m,hm,rfl⟩ := standard_of_lt (n := 943) (by simpa using hi)
  have hn := CompactForbidden.no_east_five ⟨m,hm⟩
  rw [compactField_cast _ rfl]
  simp only [Compact943Data.row, List.getElem?_toArray, getElem?_pos _ _ hm, Option.getD_some] at *
  exact_mod_cast hn

theorem extra_west_five : compactField (fun t => t.1) (1 : V) = 5 := by
  change compactField (fun t => t.1) ((1 : ℕ) : V) = 5
  rw [compactField_cast _ rfl]
  norm_num [Compact943Data.rows]

theorem extra_forbidden_with_left {left current : V} (hl : left < 943)
    (hmatch : compactField (fun t => t.2.2.1) left = compactField (fun t => t.1) current) :
    current ≠ 1 := by
  intro h
  subst current
  exact (no_east_five_model hl) (hmatch.trans extra_west_five)
#print axioms CompactNoExtra.extra_forbidden_with_left
end CompactNoExtra
