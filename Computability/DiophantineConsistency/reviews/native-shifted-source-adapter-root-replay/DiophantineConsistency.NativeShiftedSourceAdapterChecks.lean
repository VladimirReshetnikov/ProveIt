import DiophantineConsistency.NativeShiftedSourceAdapter

namespace DiophantineConsistency.NativeShiftedSourceAdapterChecks

open NativeShiftedSourceAdapter NativeOrdinarySourceConstruction

set_option Elab.async false

theorem all_ring_rows {R : Type*} [CommRing R] (p : Fin 4 → R)
    (x : Fin 31 → R) :
    (∀ j, SplitCertificate59.sourceRows p (toOld x) j =
      NativeQuadraticParent.sourceRows p x j) ∧
    (∀ j, NativeQuadraticParent.sourceRows p (toNew x) j =
      SplitCertificate59.sourceRows p x j) :=
  ⟨rows_toOld p x, rows_toNew p x⟩

theorem all_other_coordinates {R : Type*} [CommRing R] (x : Fin 31 → R) :
    ∀ i, i ≠ 3 → toOld x i = x i ∧ toNew x i = x i :=
  fun i hi => ⟨toOld_other x i hi, toNew_other x i hi⟩

/-- Positivity of the inverse cannot be claimed for arbitrary positive input. -/
theorem inverse_boundary : toNew (fun _ : Fin 31 => (1 : ℤ)) 3 = 0 := by
  rw [toNew_three]; norm_num

theorem strict_source_bound (p : Fin 4 → ℤ) {d MC MF : ℕ}
    (hi : NativeSourceMask.Interface p d MC MF)
    (n : Fin 31 → ℕ) (hn : ∀ i, 0 < n i)
    (hs : ∀ j, SplitCertificate59.sourceRows p (fun i => (n i : ℤ)) j = 0) :
    1 < n 3 ∧ ∀ i, 0 < toNew (fun j => (n j : ℤ)) i := by
  have hz := source_old_z_gt_one p hi n hn hs
  exact ⟨hz, toNew_positive _ (fun i => by exact_mod_cast hn i) (by exact_mod_cast hz)⟩

theorem actual_external_endpoint :
    CurrentPositiveShiftedSource ↔ ¬ DiophantineConsistency.ConZFC :=
  current_shifted_iff_not_conZFC

#print axioms all_ring_rows
#print axioms all_other_coordinates
#print axioms toOld_toNew
#print axioms toNew_toOld
#print axioms inverse_boundary
#print axioms strict_source_bound
#print axioms shifted_to_old
#print axioms old_to_shifted
#print axioms positive_shifted_iff_source
#print axioms current_shifted_iff_positive_zero
#print axioms actual_external_endpoint
#print axioms no_current_shifted_iff_conZFC

end DiophantineConsistency.NativeShiftedSourceAdapterChecks
