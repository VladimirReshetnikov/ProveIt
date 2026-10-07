import GowersSzemeredi.Proofs13LocalizedCoefficientSpan

/-! A construction of Stage 13.9 retaining the bounded integer step required
for square extraction. The short-column cases are not asserted here. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Above seven columns, localization preserves the full Stage 13.9 length
and density bounds and supplies the missing integer span certificate. -/
theorem lemma_13_9_with_localized_step_span {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (F : Stage136Data N) (G : Stage137Data N) (H : Stage138Data N)
    (h136 : IsStage136Data S D E F)
    (h137 : IsStage137Data S D E F G) (h138 : IsStage138Data S D E G H)
    (hQ : E.Q.IsProper) (hSlength : 8 ≤ G.S.length)
    (a : Nat) (haStep : 0 < a) (hstep : G.S.step = (a : ZMod N) * E.Q.step)
    (hspan : a * (G.S.length - 1) < E.Q.length) :
    ∃ J : Stage139Data N, IsStage139Data S E G H J ∧
      ∃ t : Nat, 0 < t ∧ J.U.step = (t : ZMod N) * G.S.step ∧
        t * (J.U.length - 1) < G.S.length := by
  classical
  have hRne := stage136_progression_nonempty S D E F h136
  have hRcard : F.R.carrier.card = F.R.length := h136.2.2.1
  have hRlen : 0 < F.R.length := by simpa only [hRcard] using hRne.card_pos
  rcases h137.1 with ⟨hSstep, hSproper, hSsub, hSlower, hBsupport, hBmass, hBmass', hBlinear⟩
  have hSlenReal : (0 : Real) < G.S.length :=
    (Real.rpow_pos_of_pos (by exact_mod_cast hRlen) _).trans_le hSlower
  have hSlen : 0 < G.S.length := by exact_mod_cast hSlenReal
  have hScard : G.S.carrier.card = G.S.length := hSproper
  have hSne : G.S.carrier.Nonempty := Finset.card_pos.mp (by simpa only [hScard] using hSlen)
  have hQlen : 0 < E.Q.length := by omega
  have hQstep : E.Q.step != 0 := by rw [← h136.1]; exact h136.2.1
  rcases h138 with ⟨hrow, hJsub, hpair, hCdef, hCmass⟩
  have hCmem (z : Pair N) (hz : z ∈ H.C) : z ∈ G.B ∧ z.2 - G.y ∈ H.J := by
    rw [hCdef] at hz
    exact Finset.mem_filter.mp hz
  have hJQ : H.J ⊆ E.Q.carrier := by
    intro h hh
    exact (Finset.mem_inter.mp (Finset.mem_filter.mp (hJsub hh)).1).1
  have hCsupport : ∀ z ∈ H.C, z.1 ∈ G.S.carrier ∧ z.2 - G.y ∈ H.J := by
    intro z hz
    exact ⟨(Finset.mem_product.mp (hBsupport (hCmem z hz).1)).1, (hCmem z hz).2⟩
  have hCrows : ∀ z ∈ H.C,
      S.phi z = H.a (z.2 - G.y) + H.c (z.2 - G.y) * z.1 := by
    intro z hz
    have h := hrow _ (hJsub (hCmem z hz).2) z.1
      (by simpa using (hCmem z hz).1)
    simpa using h
  have ha : FreimanHom 8 H.J H.a := by
    exact (AddHomClass.isAddFreimanHom (AddMonoidHom.fst (ZMod N) (ZMod N))
      (Set.mapsTo_univ _ _)).comp hpair
  have hc : FreimanHom 8 H.J H.c := by
    exact (AddHomClass.isAddFreimanHom (AddMonoidHom.snd (ZMod N) (ZMod N))
      (Set.mapsTo_univ _ _)).comp hpair
  let delta : Real := (2 : Real) ^ (-(135 : Int)) * S.alpha ^ 704
  have hα := S.alpha_pos
  have hδ : 0 < delta := by dsimp [delta]; positivity
  have hδone : delta ≤ 1 := by
    calc
      _ ≤ (2 : Real) ^ (-(135 : Int)) * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hα.le S.alpha_at_most_one) (by positivity)
      _ ≤ 1 := by norm_num
  have hmass : delta * G.S.length * E.Q.length ≤ H.C.card := by
    dsimp only [delta]
    nlinarith only [hCmass]
  obtain ⟨M, T, hpart, hcell⟩ := section13_parent_partition_of_span
    G.S E.Q hQ (by omega) a haStep hstep hspan
  obtain ⟨U, t, hUs, hUp, hUQ, hUl, hUD, hbilinear, ht, hstepU, hspanU⟩ :=
    bilinear_cell_of_short_parent_partition_full_length G.S E.Q H.J H.C G.y
      S.phi H.a H.c delta hSproper hSstep hSlength hQ hQlen M T hpart hcell
      hδ hδone hJQ hCsupport hmass hCrows ha hc
  let J : Stage139Data N := ⟨U, H.C.filter fun z ↦ z.2 - G.y ∈ U.carrier⟩
  have hD : J.D = H.C.filter (fun z ↦ z.2 - G.y ∈ U.carrier ∩ H.J) := by
    ext z
    simp only [J, Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨hz, hu⟩
      exact ⟨hz, hu, (hCmem z hz).2⟩
    · rintro ⟨hz, hu, _⟩
      exact ⟨hz, hu⟩
  refine ⟨J, ?_, t, ht, hstepU, hspanU⟩
  refine ⟨hUs, hUp, hUQ, ?_, ?_, hD, ?_, hbilinear⟩
  · exact ⟨t, by simpa only [nsmul_eq_mul] using hstepU⟩
  · simpa only [delta, stage139_partition_exponent] using hUl
  · simpa only [delta] using hUD

end LeanProofs.GowersSzemeredi
