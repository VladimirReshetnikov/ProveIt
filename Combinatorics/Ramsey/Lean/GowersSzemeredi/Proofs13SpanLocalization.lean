import GowersSzemeredi.Proofs13IndexedCoefficientPartition
import GowersSzemeredi.Proofs13ShortParentChunks

/-! Short-parent localization under the actual integer span condition,
without the earlier quadratic parent-size budget. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Weighted coefficient localization works for any certified partition
into parents of the column step, bounded above by the column length. -/
theorem bilinear_square_of_short_parent_partition {N : Nat} [Fact N.Prime]
    (S Q : ModAP N) (J : Finset (ZMod N)) (C : Finset (Pair N))
    (y : ZMod N) (phi : Pair N → ZMod N) (b c : ZMod N → ZMod N) (delta : Real)
    (hS : S.IsProper) (hSpos : 0 < S.length) (hQ : Q.IsProper)
    (hQpos : 0 < Q.length) (M L : Nat) (T : Fin M → ModAP N)
    (hpart : IsPartition (fun j => (T j).carrier) Q.carrier)
    (hcell : ∀ j, (T j).IsProper ∧ 0 < (T j).length ∧ L ≤ (T j).length ∧
      (T j).length ≤ S.length ∧ (T j).step = S.step)
    (hδ : 0 < delta) (hδone : delta ≤ 1) (hJ : J ⊆ Q.carrier)
    (hsupport : ∀ z ∈ C, z.1 ∈ S.carrier ∧ z.2 - y ∈ J)
    (hmass : delta * S.length * Q.length ≤ C.card)
    (hrow : ∀ z ∈ C, phi z = b (z.2 - y) + c (z.2 - y) * z.1)
    (hb : FreimanHom 8 J b) (hc : FreimanHom 8 J c)
    (hlarge : 8 ≤ (L : Real) ^ cor711Exponent delta 1) :
    ∃ V W : ModAP N, ∃ E : Finset (Pair N),
      V.step != 0 ∧ V.step = W.step ∧ V.IsProper ∧ W.IsProper ∧ V.length = W.length ∧
      (L : Real) ^ (cor711Exponent delta 1 / 2) - 1 ≤ V.length ∧
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
  have hlong : L ≤ (T j).length := (hcell j).2.2.1
  have he : 0 < cor711Exponent delta 1 := by unfold cor711Exponent; positivity
  have hlargeT : 8 ≤ ((T j).length : Real) ^ cor711Exponent delta 1 := hlarge.trans
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hlong) he.le)
  obtain ⟨V, W, E, hVs, hstepVW, hV, hW, hVl, hwidth, hEC, hbox, hEmass, hbil⟩ :=
    bilinear_square_from_short_parent S (T j) J' C' y phi b c delta hS hSpos
      (hcell j).1 (hcell j).2.1 (hcell j).2.2.2.2 hshort
      hδ hδone hJparent hCsupport hCmass (fun z hz => hrow z (hCsub hz)) hb' hc' hlargeT
  refine ⟨V, W, E, hVs, hstepVW, hV, hW, hVl, ?_, hEC.trans hCsub, hbox, hEmass, hbil⟩
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg L)
    (show (L : Real) ≤ (T j).length by exact_mod_cast hlong)
    (div_nonneg he.le (by norm_num : (0 : Real) ≤ 2))
  linarith only [hp, hwidth]

/-- The integer span bound suffices to partition heights into parents whose
lengths lie between half the column length and the column length. -/
theorem section13_parent_partition_of_span {N : Nat} [NeZero N]
    (S Q : ModAP N) (hQ : Q.IsProper) (hSlen : 2 ≤ S.length)
    (a : Nat) (ha : 0 < a) (hstep : S.step = (a : ZMod N) * Q.step)
    (hspan : a * (S.length - 1) < Q.length) :
    ∃ M : Nat, ∃ T : Fin M → ModAP N,
      IsPartition (fun j => (T j).carrier) Q.carrier ∧
      ∀ j, (T j).IsProper ∧ 0 < (T j).length ∧ S.length / 2 ≤ (T j).length ∧
        (T j).length ≤ S.length ∧ (T j).step = S.step := by
  have hm : 0 < S.length / 2 := Nat.div_pos hSlen (by omega)
  have hhalf : S.length / 2 ≤ S.length - 1 := by omega
  have hsize : a * (S.length / 2) ≤ Q.length :=
    (Nat.mul_le_mul_left a hhalf).trans hspan.le
  obtain ⟨M, P, _, hpart, hcell⟩ := section13_residue_short_partition
    Q.length a (S.length / 2) ha hm hsize
  refine ⟨M, fun j => section5Transport Q (P j), section5Transport_partition Q P hQ hpart,
    fun j => ⟨section5Transport_isProper Q (P j) hQ (hcell j).1 (hpart.cell_subset j),
      hm.trans_le (hcell j).2.1, (hcell j).2.1, ?_, ?_⟩⟩
  · change (P j).length ≤ S.length
    have hlen := (hcell j).2.2.1
    have hdiv := Nat.div_mul_le_self S.length 2
    omega
  · change ((P j).step : ZMod N) * Q.step = S.step
    rw [(hcell j).2.2.2]
    exact hstep.symm

/-- Construct the bilinear square using only the integer span geometry,
plus the displayed affine-extraction scale. The density loss is exactly 1/4. -/
theorem bilinear_square_of_span_budget {N : Nat} [Fact N.Prime]
    (S Q : ModAP N) (J : Finset (ZMod N)) (C : Finset (Pair N))
    (y : ZMod N) (phi : Pair N → ZMod N) (b c : ZMod N → ZMod N) (delta : Real)
    (hS : S.IsProper) (hSlength : 2 ≤ S.length) (hQ : Q.IsProper)
    (a : Nat) (ha : 0 < a) (hstep : S.step = (a : ZMod N) * Q.step)
    (hspan : a * (S.length - 1) < Q.length)
    (hδ : 0 < delta) (hδone : delta ≤ 1) (hJ : J ⊆ Q.carrier)
    (hsupport : ∀ z ∈ C, z.1 ∈ S.carrier ∧ z.2 - y ∈ J)
    (hmass : delta * S.length * Q.length ≤ C.card)
    (hrow : ∀ z ∈ C, phi z = b (z.2 - y) + c (z.2 - y) * z.1)
    (hb : FreimanHom 8 J b) (hc : FreimanHom 8 J c)
    (hlarge : 8 ≤ ((S.length / 2 : Nat) : Real) ^ cor711Exponent delta 1) :
    ∃ V W : ModAP N, ∃ E : Finset (Pair N),
      V.step != 0 ∧ V.step = W.step ∧ V.IsProper ∧ W.IsProper ∧ V.length = W.length ∧
      ((S.length / 2 : Nat) : Real) ^ (cor711Exponent delta 1 / 2) - 1 ≤ V.length ∧
      E ⊆ C ∧ E ⊆ V.carrier.product W.carrier ∧
      delta / 4 * V.length * W.length ≤ E.card ∧ BilinearOn E phi := by
  obtain ⟨M, T, hpart, hcell⟩ := section13_parent_partition_of_span S Q hQ hSlength a ha hstep hspan
  exact bilinear_square_of_short_parent_partition S Q J C y phi b c delta hS (by omega)
    hQ (by omega) M (S.length / 2) T hpart hcell hδ hδone hJ hsupport hmass hrow hb hc hlarge

end LeanProofs.GowersSzemeredi
