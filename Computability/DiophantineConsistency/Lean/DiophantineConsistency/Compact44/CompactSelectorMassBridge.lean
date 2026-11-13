import DiophantineConsistency.Compact44.CompactCoefficientMass
import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit false
set_option Elab.async false
noncomputable section
attribute [local irreducible] Compact943Data.rows
namespace CompactSelectorMassBridge
open scoped BigOperators
/-- This generic list lemma hides the concrete table from elaboration. -/
theorem ofFn_get_cast {α : Type*} (l : List α) {n : ℕ} (hl : l.length=n) :
    List.ofFn (fun i : Fin n => l.get ⟨i.val, by simpa only [hl] using i.isLt⟩) = l := by
  subst n
  exact List.ofFn_get l

theorem rows_ofFn : List.ofFn Compact943Data.row = Compact943Data.rows := by
  unfold Compact943Data.row
  exact ofFn_get_cast Compact943Data.rows Compact943Data.rows_length

theorem selector_fin_mass :
    (∑ i : Fin 943, CompactCoefficientMass.selector (Compact943Data.row i)) =
      CompactCoefficientMass.selectorMass := by
  rw [← Fin.sum_ofFn]
  rw [List.ofFn_comp', rows_ofFn]
  rfl

theorem copy_fin_mass :
    (∑ j : Fin 41, 2^(10+j.val) : ℕ) = CompactCoefficientMass.copyMass := by
  rw [CompactCoefficientMass.copy_mass_exact]
  decide

#print axioms CompactSelectorMassBridge.ofFn_get_cast
#print axioms CompactSelectorMassBridge.rows_ofFn
#print axioms CompactSelectorMassBridge.selector_fin_mass
#print axioms CompactSelectorMassBridge.copy_fin_mass
end CompactSelectorMassBridge
