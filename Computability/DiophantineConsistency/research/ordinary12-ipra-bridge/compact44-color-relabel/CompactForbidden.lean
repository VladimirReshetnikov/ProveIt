import DiophantineConsistency.Compact943Data
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace CompactForbidden
open Compact943Data

theorem no_east_five_all : rows.all (fun t => decide (t.2.2.1 ≠ 5)) = true := by decide

theorem west_five_extra_all : rows.all (fun t => decide (t.1 = 5 → t = (5,0,0,0))) = true := by decide

theorem no_east_five (i : Fin 943) : (row i).2.2.1 ≠ 5 := by
  have hm : row i ∈ rows := List.get_mem rows _
  exact of_decide_eq_true ((List.all_eq_true.mp no_east_five_all) (row i) hm)

theorem west_five_extra (i : Fin 943) : (row i).1 = 5 → row i = (5,0,0,0) := by
  have hm : row i ∈ rows := List.get_mem rows _
  exact of_decide_eq_true ((List.all_eq_true.mp west_five_extra_all) (row i) hm)

theorem five_cannot_have_left (left current : Fin 943)
    (hmatch : (row left).2.2.1 = (row current).1) : (row current).1 ≠ 5 := by
  intro h
  exact no_east_five left (hmatch.trans h)
end CompactForbidden
#print axioms CompactForbidden.no_east_five_all
#print axioms CompactForbidden.west_five_extra_all
#print axioms CompactForbidden.no_east_five
#print axioms CompactForbidden.west_five_extra
#print axioms CompactForbidden.five_cannot_have_left
