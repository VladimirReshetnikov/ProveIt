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
  have hCmem (z : Pair N) (hz : z ∈ H.C) : z ∈ G.B ∧ z.2 - G.y ∈ H.J :=
    Finset.mem_filter.mp (hCdef ▸ hz)
  let delta : Real := (2 : Real) ^ (-(135 : Int)) * S.alpha ^ 704
  have hα := S.alpha_pos
  obtain ⟨V, W, B, hVs, hVW, hV, hW, hVl, hwidth, hBC, hbox, hmassB, hbil⟩ :=
    bilinear_square_of_span_budget G.S E.Q H.J H.C G.y S.phi H.a H.c delta h137.1.2.1 hSlen hQ t
      ht hstep hspan (by positivity)
      (mul_le_one₀ (by norm_num) (by positivity) (pow_le_one₀ hα.le S.alpha_at_most_one))
      (hJsub.trans ((Finset.filter_subset _ _).trans Finset.inter_subset_left))
      (fun z hz => ⟨(Finset.mem_product.mp (h137.1.2.2.2.2.1 (hCmem z hz).1)).1, (hCmem z hz).2⟩)
      (by linarith)
      (fun z hz => by
        simpa using hrow _ (hJsub (hCmem z hz).2) z.1 (by simpa using (hCmem z hz).1))
      ((AddHomClass.isAddFreimanHom (AddMonoidHom.fst (ZMod N) (ZMod N))
        (Set.mapsTo_univ _ _)).comp hpair)
      ((AddHomClass.isAddFreimanHom (AddMonoidHom.snd (ZMod N) (ZMod N))
        (Set.mapsTo_univ _ _)).comp hpair) hlarge
  refine ⟨V, W, B, hVs, hVW, hV, hW, hVl, hwidth, fun z hz => h137.2 (hCmem z (hBC hz)).1, hbox,
    Eq.trans_le ?_ hmassB, hbil⟩
  simp only [delta, zpow_neg, zpow_ofNat]
  ring

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
  have hα := S.alpha_pos
  have hRlen : 0 < F.R.length := (stage136_progression_nonempty S D E F h136).card_pos.trans_eq
    h136.2.2.1
  have hQlen : (0 : Real) < E.Q.length := by exact_mod_cast hRlen.trans_le hRupper
  have hI : (criticalHeights S D E).Nonempty := Finset.card_pos.mp (by
    exact_mod_cast (div_pos (mul_pos (pow_pos hα _) hQlen) (by norm_num)).trans_le
      h135.2.2.2.2.2)
  obtain ⟨G, hG, t, ht, hstep, hspan⟩ := lemma_13_7_with_step_span S D E F h136 hI hlarge
  have hGlen := hG.1.2.2.2.1
  obtain ⟨H, hH⟩ := lemma_13_8_holds N S D E F G hG (hwidth.trans hGlen)
  have he : 0 < cor711Exponent ((2 : Real) ^ (-(135 : Int)) * S.alpha ^ 704) 1 := by
    unfold cor711Exponent
    positivity
  have hfloor := (Nat.cast_le (α := Real)).mpr
    (Nat.div_le_div_right (c := 2) (Nat.floor_le_of_le hGlen))
  obtain ⟨V, W, B, hVs, hVW, hV, hW, hVl, hsize, hBA, hbox, hmass, hbil⟩ :=
    section13_square_of_indexed_coefficients S D E F G H hG hH h135.2.1
      (by exact_mod_cast (by linarith [hlarge.trans hGlen] : (2 : Real) ≤ G.S.length))
      t ht (h136.1 ▸ hstep) (hspan.trans_le hRupper)
      (hscale.trans (Real.rpow_le_rpow (Nat.cast_nonneg _) hfloor he.le))
  refine ⟨V, W, B, hVs, hVW, hV, hW, hVl, ?_, hBA, hbox, hmass, hbil⟩
  linarith [Real.rpow_le_rpow (Nat.cast_nonneg _) hfloor (div_nonneg he.le zero_le_two)]

end LeanProofs.GowersSzemeredi
