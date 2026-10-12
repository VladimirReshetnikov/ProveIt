import GowersSzemeredi.Proofs13LocalizedCoefficientSpan
import GowersSzemeredi.Proofs13TinyCoefficientCells
import GowersSzemeredi.Proofs13PrintedCoefficientBounds

/-! The original contextual numerical bounds of Lemma 13.9, together with
proved integer step and span controls for the following square construction.
The stronger upstream extraction is not assumed to follow from its weaker
catalogue companion. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def IsStage139DataPrinted {N : Nat} [NeZero N] (S : Section13Context N)
    (E : Stage135Data N) (G : Stage137Data N) (H : Stage138Data N)
    (J : Stage139Data N) : Prop :=
  J.U.step != 0 ∧ J.U.IsProper ∧ J.U.carrier ⊆ E.Q.carrier ∧
  (∃ t : Nat, J.U.step = t • G.S.step) ∧
  (G.S.length : Real) ^
      ((2 : Real) ^ (-(182 : Int)) * S.alpha ^ 832) ≤ J.U.length ∧
  J.D = H.C.filter (fun z => z.2 - G.y ∈ J.U.carrier ∩ H.J) ∧
  (2 : Real) ^ (-(84 : Int)) * S.alpha ^ 416 * G.S.length * J.U.length ≤
    J.D.card ∧
  BilinearOn J.D S.phi

set_option exponentiation.threshold 512 in
/-- The printed Stage 13.8 density yields the printed Stage 13.9 exponent,
without a factor-two loss for the two coefficient maps. -/
theorem stage139Printed_partition_exponent (alpha : Real) :
    cor711Exponent ((2 : Real) ^ (-(84 : Int)) * alpha ^ 416) 1 =
      (2 : Real) ^ (-(182 : Int)) * alpha ^ 832 := by
  unfold cor711Exponent
  norm_num [Real.rpow_neg, zpow_neg]
  ring

/-- Above seven columns, localization preserves the full Stage 13.9 length
and density bounds and supplies the missing integer span certificate. -/
theorem lemma_13_9_printed_with_localized_step_span {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (F : Stage136Data N) (G : Stage137Data N) (H : Stage138Data N)
    (h136 : IsStage136DataPrinted S D E F)
    (h137 : IsStage137DataPrinted S D E F G) (h138 : IsStage138DataPrinted S D E G H)
    (hQ : E.Q.IsProper) (hSlength : 8 ≤ G.S.length)
    (a : Nat) (haStep : 0 < a) (hstep : G.S.step = (a : ZMod N) * E.Q.step)
    (hspan : a * (G.S.length - 1) < E.Q.length) :
    ∃ J : Stage139Data N, IsStage139DataPrinted S E G H J ∧
      ∃ t : Nat, 0 < t ∧ J.U.step = (t : ZMod N) * G.S.step ∧
        t * (J.U.length - 1) < G.S.length := by
  classical
  have hRne := stage136_progression_nonempty S D E F h136.to_encoded
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
  let delta : Real := (2 : Real) ^ (-(84 : Int)) * S.alpha ^ 416
  have hα := S.alpha_pos
  have hδ : 0 < delta := by dsimp [delta]; positivity
  have hδone : delta ≤ 1 := by
    calc
      _ ≤ (2 : Real) ^ (-(84 : Int)) * 1 :=
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
  · simpa only [delta, stage139Printed_partition_exponent] using hUl
  · simpa only [delta] using hUD

/-- Short columns permit a Stage 13.9 cell of at most three heights. -/
theorem lemma_13_9_printed_small_columns {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (F : Stage136Data N) (G : Stage137Data N) (H : Stage138Data N)
    (h136 : IsStage136DataPrinted S D E F)
    (h137 : IsStage137DataPrinted S D E F G) (h138 : IsStage138DataPrinted S D E G H)
    (hQ : E.Q.IsProper) (hlength : G.S.length ≤ E.Q.length) (hsmall : G.S.length ≤ 7) :
    ∃ J : Stage139Data N, IsStage139DataPrinted S E G H J ∧ J.U.length ≤ 3 := by
  classical
  have hRne := stage136_progression_nonempty S D E F h136.to_encoded
  have hRcard : F.R.carrier.card = F.R.length := h136.2.2.1
  have hRlen : 0 < F.R.length := by simpa only [hRcard] using hRne.card_pos
  rcases h137.1 with ⟨hSstep, hSproper, hSsub, hSlower, hBsupport, hBmass, hBmass', hBlinear⟩
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
  let delta : Real := (2 : Real) ^ (-(84 : Int)) * S.alpha ^ 416
  have hα := S.alpha_pos
  have hδ : 0 < delta := by dsimp [delta]; positivity
  have hδone : delta ≤ 1 := by
    calc
      _ ≤ (2 : Real) ^ (-(84 : Int)) * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hα.le S.alpha_at_most_one) (by positivity)
      _ ≤ 1 := by norm_num
  have hmass : delta * G.S.carrier.card * E.Q.length ≤ H.C.card := by
    rw [hScard]
    dsimp only [delta]
    nlinarith only [hCmass]
  have he := cor711_single_exponent_bounds hδ hδone
  have htarget : (G.S.length : Real) ^ cor711Exponent delta 1 ≤ 2 := by
    calc
      _ ≤ (8 : Real) ^ cor711Exponent delta 1 :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (show G.S.length ≤ 8 by omega)) he.1.le
      _ = (2 : Real) ^ (3 * cor711Exponent delta 1) := by
        rw [Real.rpow_mul (by norm_num)]
        norm_num
      _ ≤ (2 : Real) ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [he.2])
      _ = 2 := Real.rpow_one _
  have htargetQ : (G.S.length : Real) ^ cor711Exponent delta 1 ≤ E.Q.length :=
    (Real.rpow_le_self_of_one_le (by exact_mod_cast hSlen) (by linarith [he.2])).trans
      (Nat.cast_le.mpr hlength)
  obtain ⟨U, hUs, hUp, hUQ, hUl, hUupper, hUD, hbilinear⟩ :=
    extract_bilinear_cell_small_target E.Q G.S.carrier H.J H.C G.y S.phi H.a H.c delta
      _ htarget htargetQ hQ hQstep hQlen hSne hJQ hCsupport hmass hCrows ha hc
  let J : Stage139Data N := ⟨U, H.C.filter fun z ↦ z.2 - G.y ∈ U.carrier⟩
  have hD : J.D = H.C.filter (fun z ↦ z.2 - G.y ∈ U.carrier ∩ H.J) := by
    ext z
    simp only [J, Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨hz, hu⟩
      exact ⟨hz, hu, (hCmem z hz).2⟩
    · rintro ⟨hz, hu, _⟩
      exact ⟨hz, hu⟩
  refine ⟨J, ?_, hUupper⟩
  refine ⟨hUs, hUp, hUQ, ?_, ?_, hD, ?_, hbilinear⟩
  · refine ⟨(U.step / G.S.step).val, ?_⟩
    rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
    exact (div_mul_cancel₀ U.step (bne_iff_ne.mp hSstep)).symm
  · simpa only [delta, stage139Printed_partition_exponent] using hUl
  · simpa only [delta, hScard] using hUD

/-- Retain the geometry needed for square extraction at every column scale.
Small columns yield a height cell of length at most three; all other columns
yield a bounded positive integer step. -/
theorem lemma_13_9_printed_all_scales_with_geometry {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (F : Stage136Data N) (G : Stage137Data N) (H : Stage138Data N)
    (h135 : IsStage135Data S D E) (h136 : IsStage136DataPrinted S D E F)
    (h137 : IsStage137DataPrinted S D E F G) (h138 : IsStage138DataPrinted S D E G H)
    (hRlength : F.R.length ≤ E.Q.length)
    (a : Nat) (ha : 0 < a) (hstep : G.S.step = (a : ZMod N) * F.R.step)
    (hspan : a * (G.S.length - 1) < F.R.length) :
    ∃ J : Stage139Data N, IsStage139DataPrinted S E G H J ∧
      (J.U.length ≤ 3 ∨ ∃ t : Nat, 0 < t ∧
        J.U.step = (t : ZMod N) * G.S.step ∧ t * (J.U.length - 1) < G.S.length) := by
  by_cases hlarge : 8 ≤ G.S.length
  · obtain ⟨J, hJ, hgeom⟩ := lemma_13_9_printed_with_localized_step_span
      S D E F G H h136 h137 h138 h135.2.1 hlarge a ha
      (by simpa only [h136.1] using hstep) (hspan.trans_le hRlength)
    exact ⟨J, hJ, Or.inr hgeom⟩
  · have hScard : G.S.carrier.card = G.S.length := h137.1.2.1
    have hRcard : F.R.carrier.card = F.R.length := h136.2.2.1
    have hSR : G.S.length ≤ F.R.length := by
      rw [← hScard, ← hRcard]
      exact Finset.card_le_card h137.1.2.2.1
    obtain ⟨J, hJ, hsmall⟩ := lemma_13_9_printed_small_columns
      S D E F G H h136 h137 h138 h135.2.1 (hSR.trans hRlength) (by omega)
    exact ⟨J, hJ, Or.inl hsmall⟩

/-- The support relation omitted from `IsStage139DataPrinted` is recovered from the
actual Stage 13.7 and Stage 13.8 conclusions. -/
theorem stage139Printed_support_of_stage137_stage138 {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (F : Stage136Data N) (G : Stage137Data N) (H : Stage138Data N)
    (J : Stage139Data N)
    (h137 : IsStage137DataPrinted S D E F G)
    (h138 : IsStage138DataPrinted S D E G H)
    (h139 : IsStage139DataPrinted S E G H J) :
    J.D ⊆ G.S.carrier.product (translateFinset J.U.carrier G.y) := by
  classical
  rcases h137.1 with
    ⟨_hSstep, _hSproper, _hSsub, _hSlower, hBsupport,
      _hBlargeOne, _hBlargeTwo, _hlinear⟩
  rcases h138 with
    ⟨_hrows, _hJsub, _hfreiman, hCdef, _hClarge⟩
  rcases h139 with
    ⟨_hUstep, _hUproper, _hUsub, _hstepMultiple, _hUlower,
      hDdef, _hDlarge, _hbilinear⟩
  intro z hz
  rw [hDdef] at hz
  have hzD := Finset.mem_filter.mp hz
  have hzC : z ∈ H.C := hzD.1
  rw [hCdef] at hzC
  have hzB : z ∈ G.B := (Finset.mem_filter.mp hzC).1
  have hzProduct := Finset.mem_product.mp (hBsupport hzB)
  apply Finset.mem_product.mpr
  refine ⟨hzProduct.1, ?_⟩
  unfold translateFinset
  rw [Finset.mem_image]
  refine ⟨z.2 - G.y, (Finset.mem_inter.mp hzD.2).1, ?_⟩
  abel

/-- The original contextual Lemma 13.9 with the geometry supplied by
its preceding constructions, retaining all printed numerical bounds. -/
def lemma_13_9_printed_bounds : Prop :=
  ∀ (N : Nat) [Fact N.Prime] (S : Section13Context N) (D : Stage134Data N)
      (E : Stage135Data N) (F : Stage136Data N) (G : Stage137Data N) (H : Stage138Data N),
    IsStage135Data S D E → IsStage136DataPrinted S D E F →
    IsStage137DataPrinted S D E F G → Stage137StepSpan F G →
    IsStage138DataPrinted S D E G H → F.R.length ≤ E.Q.length →
    ∃ J : Stage139Data N, IsStage139DataPrinted S E G H J ∧
      Stage139ConstructionGeometry G J

theorem lemma_13_9_printed_bounds_holds : lemma_13_9_printed_bounds := by
  intro N _ S D E F G H h135 h136 h137 hspan h138 hlength
  obtain ⟨a, ha, hstep, hspan⟩ := hspan
  obtain ⟨J, h139, hgeom⟩ := lemma_13_9_printed_all_scales_with_geometry
    S D E F G H h135 h136 h137 h138 hlength a ha hstep hspan
  have hRne := stage136_progression_nonempty S D E F h136.to_encoded
  have hRcard : F.R.carrier.card = F.R.length := h136.2.2.1
  have hRpos : 0 < F.R.length := by simpa only [hRcard] using hRne.card_pos
  have hGpos : 0 < G.S.length := by
    have hpos : (0 : Real) < G.S.length :=
      (Real.rpow_pos_of_pos (by exact_mod_cast hRpos) _).trans_le h137.1.2.2.2.1
    exact_mod_cast hpos
  exact ⟨J, h139, h137.1.2.1, hGpos,
    stage139Printed_support_of_stage137_stage138 S D E F G H J h137 h138 h139, hgeom⟩

end LeanProofs.GowersSzemeredi
