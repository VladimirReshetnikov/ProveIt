import GowersSzemeredi.Proofs13IndexedCoefficientPartition
import GowersSzemeredi.Proofs05ResiduePartition

/-! Localize coefficient extraction to short parents with the column step.
The parent partition is constructed and its density is retained by averaging. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Partition a height progression into short parents with a prescribed
integer multiple of its step. -/
theorem section13_short_parent_partition {N : Nat} [NeZero N]
    (Q : ModAP N) (a v : Nat) (hQ : Q.IsProper) (ha : 0 < a) (hv : 1 ≤ v)
    (hsize : a * v ^ 2 ≤ Q.length) :
    ∃ M : Nat, ∃ T : Fin M → ModAP N,
      IsPartition (fun j => (T j).carrier) Q.carrier ∧
      ∀ j, (T j).IsProper ∧ 0 < (T j).length ∧
        ((T j).length = v - 1 ∨ (T j).length = v) ∧
        (T j).step = (a : ZMod N) * Q.step := by
  obtain ⟨M, P, _, hpart, hcell, hstep⟩ :=
    section5_residue_target_partition Q.length a v ha hv hsize
  refine ⟨M, fun j => section5Transport Q (P j), section5Transport_partition Q P hQ hpart,
    fun j => ⟨section5Transport_isProper Q (P j) hQ (hcell j).1 (hpart.cell_subset j),
      (hcell j).2.1, (hcell j).2.2, ?_⟩⟩
  change ((P j).step : ZMod N) * Q.step = _
  rw [hstep j]

/-- Construct a bilinear square directly from the coefficient data, using
a short-parent partition. The only extra geometric input is the explicit
integer step ratio and its parent-size budget. -/
theorem bilinear_square_of_parent_size_budget {N : Nat} [Fact N.Prime]
    (S Q : ModAP N) (J : Finset (ZMod N)) (C : Finset (Pair N))
    (y : ZMod N) (phi : Pair N → ZMod N) (b c : ZMod N → ZMod N) (delta : Real)
    (hS : S.IsProper) (hSlength : 2 ≤ S.length) (hQ : Q.IsProper)
    (a : Nat) (ha : 0 < a) (hstep : S.step = (a : ZMod N) * Q.step)
    (hsize : a * S.length ^ 2 ≤ Q.length)
    (hδ : 0 < delta) (hδone : delta ≤ 1) (hJ : J ⊆ Q.carrier)
    (hsupport : ∀ z ∈ C, z.1 ∈ S.carrier ∧ z.2 - y ∈ J)
    (hmass : delta * S.length * Q.length ≤ C.card)
    (hrow : ∀ z ∈ C, phi z = b (z.2 - y) + c (z.2 - y) * z.1)
    (hb : FreimanHom 8 J b) (hc : FreimanHom 8 J c)
    (hlarge : 8 ≤ ((S.length - 1 : Nat) : Real) ^ cor711Exponent delta 1) :
    ∃ V W : ModAP N, ∃ E : Finset (Pair N),
      V.step != 0 ∧ V.step = W.step ∧ V.IsProper ∧ W.IsProper ∧ V.length = W.length ∧
      ((S.length - 1 : Nat) : Real) ^ (cor711Exponent delta 1 / 2) - 1 ≤ V.length ∧
      E ⊆ C ∧ E ⊆ V.carrier.product W.carrier ∧
      delta / 4 * V.length * W.length ≤ E.card ∧ BilinearOn E phi := by
  classical
  obtain ⟨M, T, hpart, hcell⟩ := section13_short_parent_partition Q a S.length hQ ha
    (by omega) hsize
  have hQlength : 0 < Q.length := by
    have hs : 0 < a * S.length ^ 2 := Nat.mul_pos ha (pow_pos (by omega) _)
    exact hs.trans_le hsize
  have hQcard : Q.carrier.card = Q.length := hQ
  have hQne : Q.carrier.Nonempty := Finset.card_pos.mp (by simpa only [hQcard] using hQlength)
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
  have hshort : (T j).length ≤ S.length := by rcases (hcell j).2.2.1 with h | h <;> omega
  have hlong : S.length - 1 ≤ (T j).length := by rcases (hcell j).2.2.1 with h | h <;> omega
  have he : 0 < cor711Exponent delta 1 := by unfold cor711Exponent; positivity
  have hlargeT : 8 ≤ ((T j).length : Real) ^ cor711Exponent delta 1 := hlarge.trans
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hlong) he.le)
  obtain ⟨V, W, E, hVs, hstepVW, hV, hW, hVl, hwidth, hEC, hbox, hEmass, hbil⟩ :=
    bilinear_square_from_short_parent S (T j) J' C' y phi b c delta hS (by omega)
      (hcell j).1 (hcell j).2.1 ((hcell j).2.2.2.trans hstep.symm) hshort
      hδ hδone hJparent hCsupport hCmass (fun z hz => hrow z (hCsub hz)) hb' hc' hlargeT
  refine ⟨V, W, E, hVs, hstepVW, hV, hW, hVl, ?_, hEC.trans hCsub, hbox, hEmass, hbil⟩
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg (S.length - 1))
    (show ((S.length - 1 : Nat) : Real) ≤ (T j).length by exact_mod_cast hlong)
    (div_nonneg he.le (by norm_num : (0 : Real) ≤ 2))
  linarith only [hp, hwidth]

end LeanProofs.GowersSzemeredi
