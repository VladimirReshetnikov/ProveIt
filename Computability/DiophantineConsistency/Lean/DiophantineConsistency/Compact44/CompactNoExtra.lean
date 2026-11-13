import DiophantineConsistency.Compact44.CompactRowComplete
import DiophantineConsistency.Compact44.CompactForbidden
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
  simp only [Compact943Data.row, List.getElem?_toArray, getElem?_pos Compact943Data.rows m (by simpa only [Compact943Data.rows_length] using hm), Option.getD_some] at *
  exact_mod_cast hn

theorem extra_west_five : compactField (fun t => t.1) (1 : V) = 5 := by
  have h : compactField (fun t => t.1) ((1 : ℕ) : V) = (5 : V) := by
    rw [compactField_cast _ rfl]
    norm_num [Compact943Data.rows]
  simpa using h

theorem extra_forbidden_with_left {left current : V} (hl : left < 943)
    (hmatch : compactField (fun t => t.2.2.1) left = compactField (fun t => t.1) current) :
    current ≠ 1 := by
  intro h
  subst current
  exact (no_east_five_model hl) (hmatch.trans extra_west_five)
#print axioms CompactNoExtra.extra_forbidden_with_left
end CompactNoExtra
namespace CompactNoExtra
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem cyclic_excludes_extra (b : V → V) {N : V} (hpos : 0 < N)
    (hbound : ∀ j < N, b j < 943)
    (heast : ∀ j < N, ∀ j' < N, (j' + 1) % N = j →
      CompactRowTransport.compactField (fun t => t.2.2.1) (b j) =
        CompactRowTransport.compactField (fun t => t.1) (b j')) :
    ∀ j < N, b j ≠ 1 := by
  intro j hj
  let left := (j + 1) % N
  have hl : left < N := mod_lt _ hpos
  apply extra_forbidden_with_left (hbound left hl)
  exact heast left hl j hj rfl
#print axioms CompactNoExtra.cyclic_excludes_extra
end CompactNoExtra
