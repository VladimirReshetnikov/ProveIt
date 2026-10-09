import GowersSzemeredi.Proofs16EvenCoreAnchorCompatibility

/-! The length-eight core relation has exactly the signs required by
the four column differences, after reversing the last two endpoint pairs. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem mem_bohr_columnTupleFrequencies {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (v : Fin 8 → ZMod N) {r : Real} {y : ZMod N}
    (hy : y ∈ bohr (columnTupleFrequencies T v) r) : ∀ i, y ∈ bohr (T (v i)) r := by
  have hp := (mem_bohr_family_union (fun j : Fin 4 => columnDifferenceSpectrum T (columnTuplePairs v j)) r y).mp hy
  have hm (j : Fin 4) : y ∈ bohr (T (columnTuplePairs v j).1) r ∧
      y ∈ bohr (T (columnTuplePairs v j).2) r := by
    simpa only [columnDifferenceSpectrum,bohr_union,Finset.mem_inter] using hp j
  intro i
  fin_cases i
  · exact (hm 0).1
  · exact (hm 0).2
  · exact (hm 1).1
  · exact (hm 1).2
  · exact (hm 2).1
  · exact (hm 2).2
  · exact (hm 3).1
  · exact (hm 3).2

theorem even_core_column_tuple_respected {N : Nat} [NeZero N]
    (P Gamma : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {r : Real} (hr : 0 ≤ r)
    (hrel : EvenColumnCoreRelations P Gamma T L r 4)
    {v : Fin 8 → ZMod N} (hv : v ∈ supportedColumnTuples P) :
    ColumnTupleRespected (coreColumnSpectrum P Gamma T) (coreColumnMap P L) r v := by
  obtain ⟨hvP,hadd⟩ := Finset.mem_filter.mp hv
  have hP := Fintype.mem_piFinset.mp hvP
  intro y hy
  have hmem := mem_bohr_columnTupleFrequencies (coreColumnSpectrum P Gamma T) v hy
  have hcore (i : Fin 8) : y ∈ bohr Gamma r ∧ y ∈ bohr (T (v i)) r := by
    have h := (coreColumnSpectrum_mem P Gamma T (hP i)).mp (hmem i)
    exact ⟨bohr_mono_radius _ (by linarith : r/4 ≤ r) h.1,
      bohr_mono_radius _ (by linarith : r/4 ≤ r) h.2⟩
  have h := hrel 4 (by omega) [v 0,v 1,v 2,v 3,v 5,v 4,v 7,v 6] (by rfl)
    (by simpa only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] using
      And.intro (hP 0) (And.intro (hP 1) (And.intro (hP 2) (And.intro (hP 3)
        (And.intro (hP 5) (And.intro (hP 4) (And.intro (hP 7) (hP 6))))))))
    (by dsimp [columnAnchorEval]; linear_combination hadd) y (hcore 0).1
    (by simpa only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] using
      And.intro (hcore 0).2 (And.intro (hcore 1).2 (And.intro (hcore 2).2 (And.intro (hcore 3).2
        (And.intro (hcore 5).2 (And.intro (hcore 4).2 (And.intro (hcore 7).2 (hcore 6).2)))))))
  dsimp [columnAnchorEval] at h
  dsimp [ColumnDifferenceQuadruple,columnDifferenceMap,columnTuplePairs]
  simp only [coreColumnMap,if_pos (hP 0),if_pos (hP 1),if_pos (hP 2),if_pos (hP 3),
    if_pos (hP 4),if_pos (hP 5),if_pos (hP 6),if_pos (hP 7)]
  linear_combination h

theorem even_core_column_tuple_failures_empty {N : Nat} [NeZero N]
    (P Gamma : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {r : Real} (hr : 0 ≤ r)
    (hrel : EvenColumnCoreRelations P Gamma T L r 4) :
    columnTupleFailures (supportedColumnTuples P)
      (coreColumnSpectrum P Gamma T) (coreColumnMap P L) r = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨hv,hn⟩ := Finset.mem_filter.mp hv
  exact hn (even_core_column_tuple_respected P Gamma T L hr hrel hv)

end LeanProofs.GowersSzemeredi
