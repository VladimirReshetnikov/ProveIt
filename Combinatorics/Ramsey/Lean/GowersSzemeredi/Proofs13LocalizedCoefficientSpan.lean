import GowersSzemeredi.Proofs13SpanFullLength

/-! Full-target coefficient localization retaining the actual integer span. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Weighted coefficient localization works for any certified partition
into parents of the column step, bounded above by the column length. -/
theorem bilinear_cell_of_short_parent_partition_full_length {N : Nat} [Fact N.Prime]
    (S Q : ModAP N) (J : Finset (ZMod N)) (C : Finset (Pair N))
    (y : ZMod N) (phi : Pair N → ZMod N) (b c : ZMod N → ZMod N) (delta : Real)
    (hS : S.IsProper) (hSstep : S.step != 0) (hSpos : 8 ≤ S.length) (hQ : Q.IsProper)
    (hQpos : 0 < Q.length) (M : Nat) (T : Fin M → ModAP N)
    (hpart : IsPartition (fun j => (T j).carrier) Q.carrier)
    (hcell : ∀ j, (T j).IsProper ∧ 0 < (T j).length ∧ S.length / 2 ≤ (T j).length ∧
      (T j).length ≤ S.length ∧ (T j).step = S.step)
    (hδ : 0 < delta) (hδone : delta ≤ 1) (hJ : J ⊆ Q.carrier)
    (hsupport : ∀ z ∈ C, z.1 ∈ S.carrier ∧ z.2 - y ∈ J)
    (hmass : delta * S.length * Q.length ≤ C.card)
    (hrow : ∀ z ∈ C, phi z = b (z.2 - y) + c (z.2 - y) * z.1)
    (hb : FreimanHom 8 J b) (hc : FreimanHom 8 J c) :
    ∃ U : ModAP N, ∃ t : Nat, U.step != 0 ∧ U.IsProper ∧ U.carrier ⊆ Q.carrier ∧
      (S.length : Real) ^ cor711Exponent delta 1 ≤ U.length ∧
      delta * S.length * U.length ≤ (C.filter fun z ↦ z.2 - y ∈ U.carrier).card ∧
      BilinearOn (C.filter fun z ↦ z.2 - y ∈ U.carrier) phi ∧
      0 < t ∧ U.step = (t : ZMod N) * S.step ∧ t * (U.length - 1) < S.length := by
  classical
  have hQcard : Q.carrier.card = Q.length := hQ
  have hQne : Q.carrier.Nonempty := Finset.card_pos.mp (by simpa only [hQcard] using hQpos)
  obtain ⟨j, hj⟩ := exists_coordinate_filter_cell C Q.carrier (fun z => z.2 - y)
    (fun j => (T j).carrier) hQne hpart (fun z hz => hJ (hsupport z hz).2)
    (b := delta * S.length) (by simpa only [hQcard] using hmass)
  let J' := J ∩ (T j).carrier
  let C' := C.filter fun z => z.2 - y ∈ (T j).carrier
  have hJsub : J' ⊆ J := Finset.inter_subset_left
  have hJparent : J' ⊆ (T j).carrier := Finset.inter_subset_right
  have hCsub : C' ⊆ C := Finset.filter_subset _ _
  have hCsupport : ∀ z ∈ C', z.1 ∈ S.carrier ∧ z.2 - y ∈ J' := by
    intro z hz
    obtain ⟨hzC, hzT⟩ := Finset.mem_filter.mp hz
    exact ⟨(hsupport z hzC).1, Finset.mem_inter.mpr ⟨(hsupport z hzC).2, hzT⟩⟩
  have hCmass : delta * S.length * (T j).length ≤ C'.card := by
    simpa only [show (T j).carrier.card = (T j).length from (hcell j).1] using hj
  have hb' : FreimanHom 8 J' b :=
    IsAddFreimanHom.subset hJsub hb (Set.mapsTo_univ _ _)
  have hc' : FreimanHom 8 J' c :=
    IsAddFreimanHom.subset hJsub hc (Set.mapsTo_univ _ _)
  have hshort : (T j).length ≤ S.length := (hcell j).2.2.2.1
  have hlong : S.length / 2 ≤ (T j).length := (hcell j).2.2.1
  have hparent : S.length ≤ 3 * (T j).length := by omega
  have hfour : 4 ≤ (T j).length := by omega
  have hScard : S.carrier.card = S.length := hS
  obtain ⟨U, t, hUs, hU, hUsub, hUl, hmassU, hbilinear, ht, hstepU, hspan⟩ :=
    extract_bilinear_cell_short_parent_with_step_span (T j) S.carrier J' C' y phi b c delta
      (hcell j).1 (by simpa only [(hcell j).2.2.2.2] using hSstep) hfour S.length hparent
      (Finset.card_pos.mp (by rw [hScard]; omega)) hδ hδone hJparent hCsupport
      (by simpa only [hScard] using hCmass) (fun z hz ↦ hrow z (hCsub hz)) hb' hc'
  have hfilter : C'.filter (fun z ↦ z.2 - y ∈ U.carrier) =
      C.filter (fun z ↦ z.2 - y ∈ U.carrier) := by
    ext z
    simp only [C', Finset.mem_filter]
    exact ⟨fun ⟨⟨hc, _⟩, hu⟩ ↦ ⟨hc, hu⟩,
      fun ⟨hc, hu⟩ ↦ ⟨⟨hc, hUsub hu⟩, hu⟩⟩
  rw [hfilter] at hmassU hbilinear
  exact ⟨U, t, hUs, hU, hUsub.trans (hpart.cell_subset j), hUl,
    by simpa only [hScard] using hmassU, hbilinear, ht,
    by simpa only [(hcell j).2.2.2.2] using hstepU, hspan.trans_le hshort⟩

end LeanProofs.GowersSzemeredi
