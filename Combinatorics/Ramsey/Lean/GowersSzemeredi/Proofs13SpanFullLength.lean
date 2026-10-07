import GowersSzemeredi.Proofs13SpanLocalization
import GowersSzemeredi.Proofs13ShortParentFullLength

/-! Integer-span localization with the original power-length target. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Weighted coefficient localization works for any certified partition
into parents of the column step, bounded above by the column length. -/
theorem bilinear_square_of_short_parent_partition_full_length {N : Nat} [Fact N.Prime]
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
    ∃ V W : ModAP N, ∃ E : Finset (Pair N),
      V.step != 0 ∧ V.step = W.step ∧ V.IsProper ∧ W.IsProper ∧ V.length = W.length ∧
      (S.length : Real) ^ (cor711Exponent delta 1 / 2) - 1 ≤ V.length ∧
      E ⊆ C ∧ E ⊆ V.carrier.product W.carrier ∧
      delta / 4 * V.length * W.length ≤ E.card ∧ BilinearOn E phi := by
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
  obtain ⟨V, W, E, hVs, hstepVW, hV, hW, hVl, hwidth, hEC, hbox, hEmass, hbil⟩ :=
    bilinear_square_from_short_parent_full_length S (T j) J' C' y phi b c delta
      hS hSstep (by omega) (hcell j).1 hfour hparent (hcell j).2.2.2.2 hshort
      hδ hδone hJparent hCsupport hCmass (fun z hz => hrow z (hCsub hz)) hb' hc'
  exact ⟨V, W, E, hVs, hstepVW, hV, hW, hVl, hwidth,
    hEC.trans hCsub, hbox, hEmass, hbil⟩

/-- Construct the bilinear square using only the integer span geometry,
retaining the full column-length target at every scale above seven. The density loss is exactly 1/4. -/
theorem bilinear_square_of_span_full_length {N : Nat} [Fact N.Prime]
    (S Q : ModAP N) (J : Finset (ZMod N)) (C : Finset (Pair N))
    (y : ZMod N) (phi : Pair N → ZMod N) (b c : ZMod N → ZMod N) (delta : Real)
    (hS : S.IsProper) (hSstep : S.step != 0) (hSlength : 8 ≤ S.length) (hQ : Q.IsProper)
    (a : Nat) (ha : 0 < a) (hstep : S.step = (a : ZMod N) * Q.step)
    (hspan : a * (S.length - 1) < Q.length)
    (hδ : 0 < delta) (hδone : delta ≤ 1) (hJ : J ⊆ Q.carrier)
    (hsupport : ∀ z ∈ C, z.1 ∈ S.carrier ∧ z.2 - y ∈ J)
    (hmass : delta * S.length * Q.length ≤ C.card)
    (hrow : ∀ z ∈ C, phi z = b (z.2 - y) + c (z.2 - y) * z.1)
    (hb : FreimanHom 8 J b) (hc : FreimanHom 8 J c) :
    ∃ V W : ModAP N, ∃ E : Finset (Pair N),
      V.step != 0 ∧ V.step = W.step ∧ V.IsProper ∧ W.IsProper ∧ V.length = W.length ∧
      (S.length : Real) ^ (cor711Exponent delta 1 / 2) - 1 ≤ V.length ∧
      E ⊆ C ∧ E ⊆ V.carrier.product W.carrier ∧
      delta / 4 * V.length * W.length ≤ E.card ∧ BilinearOn E phi := by
  obtain ⟨M, T, hpart, hcell⟩ := section13_parent_partition_of_span S Q hQ (by omega) a ha hstep hspan
  exact bilinear_square_of_short_parent_partition_full_length S Q J C y phi b c delta
    hS hSstep hSlength hQ (by omega) M T hpart hcell hδ hδone hJ hsupport hmass hrow hb hc


end LeanProofs.GowersSzemeredi
