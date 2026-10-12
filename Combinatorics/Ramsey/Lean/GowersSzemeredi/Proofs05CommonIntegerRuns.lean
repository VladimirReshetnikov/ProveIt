import GowersSzemeredi.Proofs05IntegerRefinement

/-! Integer refinements with an explicitly shared positive step. These
certificates permit simultaneous refinement of the axes of a modular square. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem ModAP.integer_partition_with_step {N : Nat} [NeZero N]
    (P : ModAP N) (hP : P.IsProper) (d : Nat) (hd : 0 < d)
    (hstep : (d : ZMod N) = P.step) :
    ∃ M : Nat, ∃ Q : Fin M → NatAP,
      IsPartition (fun j => ((Q j).toModAP N).carrier) P.carrier ∧
      (∀ j, (Q j).IsProper ∧ (Q j).step = d ∧ (Q j).carrier ⊆ Finset.range N) ∧
      M * N < 2 * N + P.length * d := by
  classical
  have heval (i : Nat) : ((P.start.val + i * d : Nat) : ZMod N) = section5IndexPoint P i := by
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val, hstep, section5IndexPoint]
  have hinj : Set.InjOn (fun i : Nat => ((P.start.val + i * d : Nat) : ZMod N))
      (Finset.range P.length : Set Nat) := by
    simpa only [heval] using section5IndexPoint_injective_on_range P hP
  obtain ⟨M, Q, hM, hbudget, hpart, hQ⟩ := integerRun_partition P.start.val d P.length hd hinj
  refine ⟨M, Q, ?_, fun j => ⟨(hQ j).1, (hQ j).2.1, (hQ j).2.2.1⟩, ?_⟩
  · simpa only [heval, ← section5_carrier_eq_image_range] using hpart
  · have ha := ZMod.val_lt P.start
    have hlen := Nat.mul_le_mul_right d (Nat.sub_le P.length 1)
    omega

/-- The common orientation is chosen once from the shared modular step,
not independently for each progression in a family. -/
theorem common_integer_orientation {N : Nat} [NeZero N] (v : ZMod N) (hv : v ≠ 0) :
    ∃ d : Nat, 0 < d ∧ d = centeredAbs v ∧
      ∀ P : ModAP N, P.IsProper → P.step = v →
        ∃ M : Nat, ∃ Q : Fin M → NatAP,
          IsPartition (fun j => ((Q j).toModAP N).carrier) P.carrier ∧
          (∀ j, (Q j).IsProper ∧ (Q j).step = d ∧ (Q j).carrier ⊆ Finset.range N) ∧
          M * N < 2 * N + P.length * d := by
  have hcenter : centeredAbs v = min v.val (N - v.val) := ZMod.valMinAbs_natAbs_eq_min _
  have hval : 0 < v.val := by
    have hn : v.val ≠ 0 := (ZMod.val_eq_zero v).not.mpr hv
    omega
  by_cases hdir : v.val ≤ N - v.val
  · refine ⟨v.val, hval, by rw [hcenter, min_eq_left hdir], ?_⟩
    intro P hP hstep
    exact P.integer_partition_with_step hP v.val hval
      ((ZMod.natCast_zmod_val v).trans hstep.symm)
  · have hnegval : (-v).val = N - v.val := by rw [ZMod.neg_val, if_neg hv]
    have hd : 0 < N - v.val := by have h := ZMod.val_lt v; omega
    refine ⟨N - v.val, hd, by rw [hcenter, min_eq_right (by omega)], ?_⟩
    intro P hP hstep
    have hcast : ((N - v.val : Nat) : ZMod N) = P.reverse.step := by
      rw [← hnegval, ZMod.natCast_zmod_val]
      simpa only [ModAP.reverse, hstep]
    obtain ⟨M, Q, hpart, hQ, hbudget⟩ :=
      P.reverse.integer_partition_with_step ((P.reverse_isProper).mpr hP) _ hd hcast
    exact ⟨M, Q, by simpa only [P.reverse_carrier] using hpart, hQ, hbudget⟩

/-- With a prescribed short multiplier and one shared orientation, every
axis has the same integer step and the same square-root cell-count budget. -/
theorem ModAP.integer_refinement_at_multiplier {N : Nat} [NeZero N]
    (P : ModAP N) (hP : P.IsProper) (t u d : Nat)
    (ht : t = Nat.sqrt P.length) (ht2 : 2 ≤ t) (hu : 0 < u) (hut : u ≤ t)
    (hd : 0 < d) (hsmall : d * t < N)
    (horientation : ∀ S : ModAP N, S.IsProper → S.step = (u : ZMod N) * P.step →
      ∃ M : Nat, ∃ Q : Fin M → NatAP,
        IsPartition (fun j => ((Q j).toModAP N).carrier) S.carrier ∧
        (∀ j, (Q j).IsProper ∧ (Q j).step = d ∧ (Q j).carrier ⊆ Finset.range N) ∧
        M * N < 2 * N + S.length * d) :
    ∃ M : Nat, ∃ Q : Fin M → NatAP,
      IsPartition (fun j => ((Q j).toModAP N).carrier) P.carrier ∧
      (∀ j, (Q j).IsProper ∧ (Q j).step = d ∧ (Q j).carrier ⊆ Finset.range N) ∧
      M ≤ 4 * t := by
  classical
  have ht0 : 0 < t := by omega
  have htsq : t * t ≤ P.length := by rw [ht]; exact Nat.sqrt_le _
  have htL : t < P.length := by nlinarith
  have huL : u ≤ P.length := hut.trans htL.le
  let A := residueNatAP P.length u
  have hApart : IsNatAPPartition A (Finset.range P.length) := residueNatAP_partition hu huL
  let S : Fin u → ModAP N := fun r => section5Transport P (A r)
  have hSpart : IsPartition (fun r => (S r).carrier) P.carrier :=
    section5Transport_partition P A hP hApart
  have hSproper (r : Fin u) : (S r).IsProper :=
    section5Transport_isProper P (A r) hP (residueNatAP_proper hu r) (hApart.cell_subset r)
  have hSstep (r : Fin u) : (S r).step = (u : ZMod N) * P.step := rfl
  have hSlen : ∑ r, (S r).length = P.length := by
    calc
      ∑ r, (S r).length = ∑ r, (A r).carrier.card :=
        Finset.sum_congr rfl (fun r _ => (residueNatAP_proper hu r).2.symm)
      _ = P.length := by simpa only [Finset.card_range] using hApart.sum_card
  choose M Q hQpart hQprops hQbudget using fun r => horientation (S r) (hSproper r) (hSstep r)
  have hsum : (∑ r, M r) * N < 2 * u * N + P.length * d := by
    calc
      _ = ∑ r, M r * N := Finset.sum_mul _ _ _
      _ < ∑ r, (2 * N + (S r).length * d) :=
        Finset.sum_lt_sum_of_nonempty ⟨⟨0, hu⟩, Finset.mem_univ _⟩ (fun r _ => hQbudget r)
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul Finset.univ (fun r : Fin u => (S r).length) d, hSlen]
        simp
        ring
  have hscaled : (∑ r, M r) * t < 2 * u * t + P.length := by
    apply Nat.lt_of_mul_lt_mul_right (a := N)
    calc
      (∑ r, M r) * t * N = ((∑ r, M r) * N) * t := by ring
      _ < (2 * u * N + P.length * d) * t := Nat.mul_lt_mul_of_pos_right hsum ht0
      _ ≤ (2 * u * t + P.length) * N := by
        have h := Nat.mul_le_mul_left P.length hsmall.le
        nlinarith
  have hcount : (∑ r, M r) ≤ 4 * t := by
    have hround : P.length ≤ t * t + t + t := by rw [ht]; exact Nat.sqrt_le_add _
    have humul := Nat.mul_le_mul_right t hut
    nlinarith
  let R : Fin (∑ r, M r) → NatAP := fun j =>
    let z := (section5NatFlattenEquiv M).symm j
    Q z.1 z.2
  refine ⟨∑ r, M r, R, ?_, ?_, hcount⟩
  · exact finsetPartition_flatten M (fun r => (S r).carrier) P.carrier
      (fun r j => ((Q r j).toModAP N).carrier) hSpart hQpart
  · intro j
    let z := (section5NatFlattenEquiv M).symm j
    exact hQprops z.1 z.2

/-- Two equally long proper progressions with the same modular step have
integer refinements with a common positive integer step and at most
`4*floor(sqrt(m))` cells on either axis. -/
theorem common_integer_refinement_pair {N : Nat} [NeZero N]
    (P R : ModAP N) (hP : P.IsProper) (hR : R.IsProper)
    (hlen : P.length = R.length) (hstep : P.step = R.step) (hm : 4 ≤ P.length) :
    ∃ d : Nat, ∃ M L : Nat, ∃ Q : Fin M → NatAP, ∃ T : Fin L → NatAP,
      0 < d ∧ IsPartition (fun j => ((Q j).toModAP N).carrier) P.carrier ∧
      IsPartition (fun j => ((T j).toModAP N).carrier) R.carrier ∧
      (∀ j, (Q j).IsProper ∧ (Q j).step = d ∧ (Q j).carrier ⊆ Finset.range N) ∧
      (∀ j, (T j).IsProper ∧ (T j).step = d ∧ (T j).carrier ⊆ Finset.range N) ∧
      M ≤ 4 * Nat.sqrt P.length ∧ L ≤ 4 * Nat.sqrt P.length := by
  classical
  let t := Nat.sqrt P.length
  have ht2 : 2 ≤ t := Nat.le_sqrt.mpr (by simpa using hm)
  have ht0 : 0 < t := by omega
  have htsq : t * t ≤ P.length := Nat.sqrt_le _
  have htL : t < P.length := by nlinarith
  letI : NeZero t := ⟨by omega⟩
  obtain ⟨u, hu, hut, hsmall⟩ :=
    simultaneous_small_multiplier (N := N) (K := 1) (M := t) (fun _ => P.step)
  have hut' : u ≤ t := by simpa using hut
  let v : ZMod N := (u : ZMod N) * P.step
  have hv : v ≠ 0 := by
    intro hz
    have h := section5IndexPoint_injective_on_range P hP
      (Finset.mem_range.mpr (hut'.trans_lt htL)) (Finset.mem_range.mpr (by omega : 0 < P.length))
      (show section5IndexPoint P u = section5IndexPoint P 0 by
        simp only [section5IndexPoint, Nat.cast_zero, zero_mul, add_zero]
        change P.start + v = P.start
        rw [hz, add_zero])
    omega
  obtain ⟨d, hd, hdc, horientation⟩ := common_integer_orientation v hv
  have hdt : d * t < N := by rw [hdc]; exact hsmall 0
  obtain ⟨M, Q, hQ, hQprops, hM⟩ :=
    P.integer_refinement_at_multiplier hP t u d rfl ht2 hu hut' hd hdt horientation
  obtain ⟨L, T, hT, hTprops, hL⟩ :=
    R.integer_refinement_at_multiplier hR t u d (by rw [← hlen]) ht2 hu hut' hd hdt
      (by simpa only [← hstep] using horientation)
  exact ⟨d, M, L, Q, T, hd, hQ, hT, hQprops, hTprops, hM, hL⟩

end LeanProofs.GowersSzemeredi
