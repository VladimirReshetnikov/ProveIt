import GowersSzemeredi.Proofs13SpanLocalization
import GowersSzemeredi.Proofs13IndexedRowExtraction
import GowersSzemeredi.Proofs13CoefficientExtraction

/-! A direct square extraction from the Section 13 coefficient data.
Integer span geometry is constructed and retained through the row selection. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The full coefficient data and an actual integer span yield a bilinear
square contained in the original domain, with no grid hypothesis. -/
theorem section13_square_of_indexed_coefficients {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (F : Stage136Data N) (G : Stage137Data N) (H : Stage138Data N)
    (h137 : IsStage137Data S D E F G) (h138 : IsStage138Data S D E G H)
    (hQ : E.Q.IsProper) (hSlen : 2 ≤ G.S.length)
    (t : Nat) (ht : 0 < t) (hstep : G.S.step = (t : ZMod N) * E.Q.step)
    (hspan : t * (G.S.length - 1) < E.Q.length)
    (hlarge : 8 ≤ ((G.S.length / 2 : Nat) : Real) ^
      cor711Exponent ((2 : Real) ^ (-(135 : Int)) * S.alpha ^ 704) 1) :
    ∃ V W : ModAP N, ∃ B : Finset (Pair N),
      V.step != 0 ∧ V.step = W.step ∧ V.IsProper ∧ W.IsProper ∧ V.length = W.length ∧
      ((G.S.length / 2 : Nat) : Real) ^
        (cor711Exponent ((2 : Real) ^ (-(135 : Int)) * S.alpha ^ 704) 1 / 2) - 1 ≤ V.length ∧
      B ⊆ S.A ∧ B ⊆ V.carrier.product W.carrier ∧
      (2 : Real) ^ (-(137 : Int)) * S.alpha ^ 704 * V.length * W.length ≤ B.card ∧
      BilinearOn B S.phi := by
  classical
  rcases h138 with ⟨hrow, hJsub, hpair, hCdef, hCmass⟩
  have hCmem (z : Pair N) (hz : z ∈ H.C) : z ∈ G.B ∧ z.2 - G.y ∈ H.J := by
    rw [hCdef] at hz
    exact Finset.mem_filter.mp hz
  have hJQ : H.J ⊆ E.Q.carrier := by
    intro h hh
    exact (Finset.mem_inter.mp (Finset.mem_filter.mp (hJsub hh)).1).1
  have hCsupport : ∀ z ∈ H.C, z.1 ∈ G.S.carrier ∧ z.2 - G.y ∈ H.J := by
    intro z hz
    exact ⟨(Finset.mem_product.mp (h137.1.2.2.2.2.1 (hCmem z hz).1)).1, (hCmem z hz).2⟩
  have hCrows : ∀ z ∈ H.C,
      S.phi z = H.a (z.2 - G.y) + H.c (z.2 - G.y) * z.1 := by
    intro z hz
    have h := hrow _ (hJsub (hCmem z hz).2) z.1 (by simpa using (hCmem z hz).1)
    simpa using h
  have ha : FreimanHom 8 H.J H.a :=
    (AddHomClass.isAddFreimanHom (AddMonoidHom.fst (ZMod N) (ZMod N))
      (Set.mapsTo_univ _ _)).comp hpair
  have hc : FreimanHom 8 H.J H.c :=
    (AddHomClass.isAddFreimanHom (AddMonoidHom.snd (ZMod N) (ZMod N))
      (Set.mapsTo_univ _ _)).comp hpair
  let delta : Real := (2 : Real) ^ (-(135 : Int)) * S.alpha ^ 704
  have hα := S.alpha_pos
  have hδ : 0 < delta := mul_pos (zpow_pos (by norm_num) _) (pow_pos hα _)
  have hδone : delta ≤ 1 := by
    calc
      _ ≤ (2 : Real) ^ (-(135 : Int)) * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hα.le S.alpha_at_most_one) (by positivity)
      _ ≤ 1 := by norm_num
  have hmass : delta * G.S.length * E.Q.length ≤ H.C.card := by
    dsimp [delta]
    nlinarith only [hCmass]
  obtain ⟨V, W, B, hVs, hVW, hV, hW, hVl, hwidth, hBC, hbox, hmassB, hbil⟩ :=
    bilinear_square_of_span_budget G.S E.Q H.J H.C G.y S.phi H.a H.c delta
      h137.1.2.1 hSlen hQ t ht hstep hspan hδ hδone hJQ hCsupport hmass hCrows ha hc hlarge
  refine ⟨V, W, B, hVs, hVW, hV, hW, hVl, hwidth, ?_, hbox, ?_, hbil⟩
  · exact fun z hz => h137.2 (hCmem z (hBC hz)).1
  · have hδeq : delta / 4 = (2 : Real) ^ (-(137 : Int)) * S.alpha ^ 704 := by
      dsimp [delta]
      norm_num [zpow_neg]
      ring
    rwa [hδeq] at hmassB

/-- Starting from Stage 13.6, all row, coefficient, parent, and square data
are constructed. Only the three displayed scale inequalities remain. -/
theorem section13_square_extraction_of_scales {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N) (F : Stage136Data N)
    (h135 : IsStage135Data S D E) (h136 : IsStage136Data S D E F)
    (hRupper : F.R.length ≤ E.Q.length)
    (hlarge : 8 ≤ (F.R.length : Real) ^ ((2 : Real) ^ (-(100 : Int)) * S.alpha ^ 448))
    (hwidth : (2 : Real) ^ 135 * S.alpha ^ (-(704 : Int)) ≤
      (F.R.length : Real) ^ ((2 : Real) ^ (-(100 : Int)) * S.alpha ^ 448))
    (hscale : 8 ≤ ((Nat.floor ((F.R.length : Real) ^
      ((2 : Real) ^ (-(100 : Int)) * S.alpha ^ 448)) / 2 : Nat) : Real) ^
        cor711Exponent ((2 : Real) ^ (-(135 : Int)) * S.alpha ^ 704) 1) :
    ∃ V W : ModAP N, ∃ B : Finset (Pair N),
      V.step != 0 ∧ V.step = W.step ∧ V.IsProper ∧ W.IsProper ∧ V.length = W.length ∧
      ((Nat.floor ((F.R.length : Real) ^
        ((2 : Real) ^ (-(100 : Int)) * S.alpha ^ 448)) / 2 : Nat) : Real) ^
        (cor711Exponent ((2 : Real) ^ (-(135 : Int)) * S.alpha ^ 704) 1 / 2) - 1 ≤ V.length ∧
      B ⊆ S.A ∧ B ⊆ V.carrier.product W.carrier ∧
      (2 : Real) ^ (-(137 : Int)) * S.alpha ^ 704 * V.length * W.length ≤ B.card ∧
      BilinearOn B S.phi := by
  have hRne := stage136_progression_nonempty S D E F h136
  have hRlen : 0 < F.R.length := by
    simpa only [show F.R.carrier.card = F.R.length from h136.2.2.1] using hRne.card_pos
  have hQlen : (0 : Real) < E.Q.length := by exact_mod_cast hRlen.trans_le hRupper
  have hI : (criticalHeights S D E).Nonempty := by
    apply Finset.card_pos.mp
    have hpos : (0 : Real) < (criticalHeights S D E).card :=
      (div_pos (mul_pos (pow_pos S.alpha_pos _) hQlen) (by norm_num)).trans_le h135.2.2.2.2.2
    exact_mod_cast hpos
  obtain ⟨G, hG, t, ht, hstep, hspan⟩ := lemma_13_7_with_step_span S D E F h136 hI hlarge
  have hGlen := hG.1.2.2.2.1
  have hGtwo : 2 ≤ G.S.length := by
    have h : (8 : Real) ≤ G.S.length := hlarge.trans hGlen
    have : 8 ≤ G.S.length := by exact_mod_cast h
    omega
  obtain ⟨H, hH⟩ := lemma_13_8_holds N S D E F G hG (hwidth.trans hGlen)
  have hfloor : Nat.floor ((F.R.length : Real) ^
      ((2 : Real) ^ (-(100 : Int)) * S.alpha ^ 448)) / 2 ≤ G.S.length / 2 :=
    Nat.div_le_div_right (Nat.floor_le_of_le hGlen)
  have he : 0 < cor711Exponent ((2 : Real) ^ (-(135 : Int)) * S.alpha ^ 704) 1 := by
    have hα := S.alpha_pos
    unfold cor711Exponent
    positivity
  have hGscale := hscale.trans (Real.rpow_le_rpow (Nat.cast_nonneg _)
    (show ((Nat.floor ((F.R.length : Real) ^
      ((2 : Real) ^ (-(100 : Int)) * S.alpha ^ 448)) / 2 : Nat) : Real) ≤ ((G.S.length / 2 : Nat) : Real) from by
        exact_mod_cast hfloor) he.le)
  obtain ⟨V, W, B, hVs, hVW, hV, hW, hVl, hsize, hBA, hbox, hmass, hbil⟩ :=
    section13_square_of_indexed_coefficients S D E F G H hG hH h135.2.1 hGtwo
      t ht (by simpa only [h136.1] using hstep) (hspan.trans_le hRupper) hGscale
  refine ⟨V, W, B, hVs, hVW, hV, hW, hVl, ?_, hBA, hbox, hmass, hbil⟩
  have hfloorR : ((Nat.floor ((F.R.length : Real) ^
      ((2 : Real) ^ (-(100 : Int)) * S.alpha ^ 448)) / 2 : Nat) : Real) ≤
      ((G.S.length / 2 : Nat) : Real) := by exact_mod_cast hfloor
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg _) hfloorR
    (div_nonneg he.le (by norm_num : (0 : Real) ≤ 2))
  linarith only [hp, hsize]

end LeanProofs.GowersSzemeredi
