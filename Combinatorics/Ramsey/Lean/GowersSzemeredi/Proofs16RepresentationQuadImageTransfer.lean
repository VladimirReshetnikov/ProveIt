import GowersSzemeredi.Proofs16RepresentationColumnMaps

/-! A good original 16-tuple controls the normalized chosen-map quadruple
on its actual common domain. The reference map cancels in values, while
its frequencies remain in every normalized map domain. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem mem_bohr_flattened_representations {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (b : Fin 4 → FourRepresentationTuple N)
    (sigma : Real) (y : ZMod N)
    (hy : ∀ j, y ∈ bohr (representationColumnSpectrum T (b j)) sigma) :
    y ∈ bohr (columnListSpectrum T (columnAnchorList (flattenFourRepresentations b))) sigma := by
  have hs : ∀ j, y ∈ bohr (T (b j).1) sigma ∧ y ∈ bohr (T (b j).2.1) sigma ∧
      y ∈ bohr (T (b j).2.2.1) sigma ∧ y ∈ bohr (T (b j).2.2.2) sigma := by
    intro j
    have h := (mem_columnListSpectrum_bohr T (representationColumnEntries (b j)) sigma y).mp (hy j)
    simpa only [representationColumnEntries, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] using h
  apply (mem_columnListSpectrum_bohr T _ sigma y).mpr
  simp only [flattenFourRepresentations, columnAnchorList, List.ofFn_succ, List.ofFn_zero,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨(hs 0).1, (hs 0).2.1, (hs 0).2.2.1, (hs 0).2.2.2,
    (hs 1).2.1, (hs 1).1, (hs 1).2.2.2, (hs 1).2.2.1,
    (hs 2).1, (hs 2).2.1, (hs 2).2.2.1, (hs 2).2.2.2,
    (hs 3).2.1, (hs 3).1, (hs 3).2.2.2, (hs 3).2.2.1⟩

theorem normalized_quad_defect_eq_flattened {N : Nat}
    (L : ZMod N → ZMod N → ZMod N) (f : ZMod N → FourRepresentationTuple N)
    (q : Fin 4 → ZMod N) (y : ZMod N) :
    columnQuadDefect (normalizedRepresentationMap L f) (q 0) (q 1) (q 3) (q 2) y =
      columnAnchorEval (fun x => L x y) (columnAnchorList (flattenFourRepresentations (fun j => f (q j)))) := by
  rw [flattenFourRepresentations_eval]
  simp only [columnQuadDefect, normalizedRepresentationMap, representationColumnMap_eq]
  ring

/-- The normalized common domain is contained in the original sixteen
column domain; therefore its defect image cannot be larger. -/
theorem normalized_quad_image_transfer {N K : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (f : ZMod N → FourRepresentationTuple N) (q : Fin 4 → ZMod N) (sigma : Real)
    (himage : ((bohr (columnListSpectrum T (columnAnchorList
      (flattenFourRepresentations (fun j => f (q j))))) sigma).image
        (fun y => columnAnchorEval (fun x => L x y)
          (columnAnchorList (flattenFourRepresentations (fun j => f (q j)))))).card ≤ K) :
    ColumnQuadImageRelation (normalizedRepresentationSpectrum T f) (normalizedRepresentationMap L f)
      sigma K (q 0) (q 1) (q 3) (q 2) := by
  apply (image_card_le_of_eq_on_subset _ _ _ _ ?_
    (fun y _ => normalized_quad_defect_eq_flattened L f q y)).trans himage
  intro y hy
  obtain ⟨_, h0, h1, h3, h2⟩ := Finset.mem_filter.mp hy
  apply mem_bohr_flattened_representations T (fun j => f (q j)) sigma y
  intro j
  have hown : ∀ x : ZMod N, y ∈ bohr (normalizedRepresentationSpectrum T f x) sigma →
      y ∈ bohr (representationColumnSpectrum T (f x)) sigma := by
    intro x hx
    rw [normalizedRepresentationSpectrum, bohr_union] at hx
    exact (Finset.mem_inter.mp hx).1
  fin_cases j
  · exact hown _ h0
  · exact hown _ h1
  · exact hown _ h2
  · exact hown _ h3

end LeanProofs.GowersSzemeredi
