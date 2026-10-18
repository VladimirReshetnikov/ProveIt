import GowersSzemeredi.Proofs13CoefficientPartition

/-! Declarations of `Proofs13CoefficientPartition` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- The analytic and averaging step of Lemma 13.9 on a given height
progression. Both coefficient maps retain the one-domain exponent. -/
theorem extract_bilinear_cell {N : Nat} [Fact N.Prime]
    (T : ModAP N) (S J : Finset (ZMod N)) (C : Finset (Pair N))
    (y : ZMod N) (phi : Pair N → ZMod N) (a c : ZMod N → ZMod N) (delta : Real)
    (hT : T.IsProper) (hstep : T.step != 0) (hlen : 0 < T.length)
    (hS : S.Nonempty) (hδ : 0 < delta) (hδone : delta ≤ 1)
    (hJ : J ⊆ T.carrier)
    (hsupport : ∀ z ∈ C, z.1 ∈ S ∧ z.2 - y ∈ J)
    (hmass : delta * S.card * T.length ≤ C.card)
    (hrow : ∀ z ∈ C, phi z = a (z.2 - y) + c (z.2 - y) * z.1)
    (ha : FreimanHom 8 J a) (hc : FreimanHom 8 J c) :
    ∃ U : ModAP N, U.step != 0 ∧ U.IsProper ∧ U.carrier ⊆ T.carrier ∧
      (T.length : Real) ^ cor711Exponent delta 1 ≤ U.length ∧
      delta * S.card * U.length ≤ (C.filter fun z ↦ z.2 - y ∈ U.carrier).card ∧
      BilinearOn (C.filter fun z ↦ z.2 - y ∈ U.carrier) phi := by
  have hcard := translated_row_card_le C S J y hsupport
  have hcardReal : (C.card : Real) ≤ (S.card : Real) * J.card := by exact_mod_cast hcard
  have hSpos : (0 : Real) < S.card := by exact_mod_cast hS.card_pos
  have hJdense : delta * T.length ≤ J.card := by
    apply le_of_mul_le_mul_left (a := (S.card : Real)) _ hSpos
    nlinarith only [hmass, hcardReal]
  obtain ⟨M, P, hP, hcell⟩ := corollary_7_11_pair_modular N T J a c delta
    hT hstep hlen hδ hδone hJ hJdense ha hc
  have hTcard : T.carrier.card = T.length := hT
  have hTne : T.carrier.Nonempty := Finset.card_pos.mp (by simpa only [hTcard] using hlen)
  obtain ⟨j, hj⟩ := exists_coordinate_filter_cell C T.carrier (fun z ↦ z.2 - y)
    (fun j ↦ (P j).carrier) hTne hP (fun z hz ↦ hJ (hsupport z hz).2)
    (b := delta * S.card) (by simpa only [hTcard] using hmass)
  obtain ⟨hs, hp, hl, hla, hlc⟩ := hcell j
  have hPcard : (P j).carrier.card = (P j).length := hp
  refine ⟨P j, hs, hp, hP.cell_subset j, hl, ?_, ?_⟩
  · simpa only [hPcard] using hj
  · apply bilinearOn_of_affine_row_coefficients _
      ((P j).carrier.filter fun x ↦ x ∈ J) y phi a c ?_ ?_ hla hlc
    · intro z hz
      obtain ⟨hzC, hzP⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hzP, (hsupport z hzC).2⟩
    · intro z hz
      exact hrow z (Finset.mem_filter.mp hz).1

/-- Lemma 13.9 follows from the actual preceding extraction data once the
ambient height progression is proper and at least as long as the selected
column progression. These geometric conditions are not in the old catalogue
antecedent and remain explicit. The natural-multiple step statement here is
only the modular statement in `IsStage139Data`; it does not supply the stronger
integer step control needed for the later square-grid construction. -/
theorem lemma_13_9_of_length_comparison {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (F : Stage136Data N) (G : Stage137Data N) (H : Stage138Data N)
    (h136 : IsStage136Data S D E F)
    (h137 : IsStage137Data S D E F G) (h138 : IsStage138Data S D E G H)
    (hQ : E.Q.IsProper) (hlength : G.S.length ≤ E.Q.length) :
    ∃ J : Stage139Data N, IsStage139Data S E G H J := by
  classical
  have hRne := stage136_progression_nonempty S D E F h136
  have hRcard : F.R.carrier.card = F.R.length := h136.2.2.1
  have hRlen : 0 < F.R.length := by simpa only [hRcard] using hRne.card_pos
  rcases h137.1 with ⟨hSstep, hSproper, _, hSlower, hBsupport, _, _, _⟩
  have hSlenReal : (0 : Real) < G.S.length :=
    (Real.rpow_pos_of_pos (by exact_mod_cast hRlen) _).trans_le hSlower
  have hSlen : 0 < G.S.length := by exact_mod_cast hSlenReal
  have hScard : G.S.carrier.card = G.S.length := hSproper
  have hSne : G.S.carrier.Nonempty := Finset.card_pos.mp (by simpa only [hScard] using hSlen)
  have hQlen : 0 < E.Q.length := lt_of_lt_of_le hSlen hlength
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
  have hmass : delta * G.S.carrier.card * E.Q.length ≤ H.C.card := by
    rw [hScard]
    dsimp only [delta]
    nlinarith only [hCmass]
  obtain ⟨U, hUs, hUp, hUQ, hUl, hUD, hbilinear⟩ := extract_bilinear_cell E.Q
    G.S.carrier H.J H.C G.y S.phi H.a H.c delta hQ hQstep hQlen hSne hδ hδone
    hJQ hCsupport hmass hCrows ha hc
  let J : Stage139Data N := ⟨U, H.C.filter fun z ↦ z.2 - G.y ∈ U.carrier⟩
  have hD : J.D = H.C.filter (fun z ↦ z.2 - G.y ∈ U.carrier ∩ H.J) := by
    ext z
    simp only [J, Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨hz, hu⟩
      exact ⟨hz, hu, (hCmem z hz).2⟩
    · rintro ⟨hz, hu, _⟩
      exact ⟨hz, hu⟩
  refine ⟨J, hUs, hUp, hUQ, ?_, ?_, hD, ?_, hbilinear⟩
  · refine ⟨(U.step / G.S.step).val, ?_⟩
    rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
    exact (div_mul_cancel₀ U.step (bne_iff_ne.mp hSstep)).symm
  · have he : 0 < cor711Exponent delta 1 := (cor711_single_exponent_bounds hδ hδone).1
    have hle : (G.S.length : Real) ^ cor711Exponent delta 1 ≤
        (E.Q.length : Real) ^ cor711Exponent delta 1 :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hlength) he.le
    have h := hle.trans hUl
    simpa only [delta, stage139_partition_exponent] using h
  · simpa only [delta, hScard] using hUD

/-- In the full extraction chain, the remaining geometric input is the
printed assertion that the Stage 13.6 progression is no longer than `Q`. -/
theorem lemma_13_9_of_progression_length_bound {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (F : Stage136Data N) (G : Stage137Data N) (H : Stage138Data N)
    (h135 : IsStage135Data S D E) (h136 : IsStage136Data S D E F)
    (h137 : IsStage137Data S D E F G) (h138 : IsStage138Data S D E G H)
    (hRlength : F.R.length ≤ E.Q.length) :
    ∃ J : Stage139Data N, IsStage139Data S E G H J := by
  have hScard : G.S.carrier.card = G.S.length := h137.1.2.1
  have hRcard : F.R.carrier.card = F.R.length := h136.2.2.1
  have hSR : G.S.length ≤ F.R.length := by
    rw [← hScard, ← hRcard]
    exact Finset.card_le_card h137.1.2.2.1
  exact lemma_13_9_of_length_comparison S D E F G H h136 h137 h138 h135.2.1
    (hSR.trans hRlength)

/-- Every Stage 13.9 conclusion forces enough distinct height positions in
`Q`; this requirement cannot be replaced by its formal progression length. -/
theorem stage139_height_card_lower {N : Nat} [NeZero N]
    (S : Section13Context N) (E : Stage135Data N) (G : Stage137Data N)
    (H : Stage138Data N) (J : Stage139Data N)
    (h139 : IsStage139Data S E G H J) :
    (G.S.length : Real) ^ ((2 : Real) ^ (-(284 : Int)) * S.alpha ^ 1408) ≤
      E.Q.carrier.card := by
  have hcard : J.U.carrier.card = J.U.length := h139.2.1
  have hle : J.U.length ≤ E.Q.carrier.card := by
    rw [← hcard]
    exact Finset.card_le_card h139.2.2.1
  exact h139.2.2.2.2.1.trans (by exact_mod_cast hle)

end LeanProofs.GowersSzemeredi
