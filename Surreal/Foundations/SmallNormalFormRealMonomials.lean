import Surreal.Foundations.SmallNormalFormMonomials
import Surreal.Foundations.SignSequenceProductCuts

/-!
# Real multiples of Conway monomials in cut evaluation

The gaps in a product presentation of a real times an omega power have
valuation at most that of the omega power. An error of strictly higher
valuation preserves every product-cut inequality, giving the reverse prefix
needed to identify a singleton candidate with its actual real monomial.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

private theorem positive_add_of_valuation_lt {g e : SignSequence.{u}}
    (hg : 0 < g) (hv : valuation g < valuation e) : 0 < g + e := by
  apply (leadingCoeff_pos_iff _).mp
  rw [leadingCoeff_add_of_valuation_lt hv]
  exact (leadingCoeff_pos_iff _).mpr hg

private theorem lt_of_close_above {l m x : SignSequence.{u}} (hl : l < m)
    (hv : valuation (m - l) < valuation (x - m)) : l < x := by
  have h := positive_add_of_valuation_lt (sub_pos.mpr hl) hv
  have he : (m - l) + (x - m) = x - l := by abel
  rw [he] at h
  exact sub_pos.mp h

private theorem lt_of_close_below {m r x : SignSequence.{u}} (hr : m < r)
    (hv : valuation (m - r) < valuation (x - m)) : x < r := by
  have h := positive_add_of_valuation_lt (sub_pos.mpr hr)
    (show valuation (r - m) < valuation (m - x) by
      simpa only [valuation_sub_comm r m, valuation_sub_comm m x] using hv)
  have he : (r - m) + (m - x) = r - x := by abel
  rw [he] at h
  exact sub_pos.mp h

private theorem valuation_sub_le_of_ne {x y : SignSequence.{u}}
    (h : valuation x ≠ valuation y) : valuation (x - y) ≤ valuation x := by
  have hn : valuation x ≠ valuation (-y) := by simpa only [valuation_neg] using h
  rw [sub_eq_add_neg, valuation.map_add_of_distinct_val hn]
  exact min_le_left _ _

private theorem real_option_gap (r : ℝ) (y : SignSequence.{u})
    (hy : Simpler y (ofReal r)) : valuation (ofReal r - y) = 0 := by
  have hb := hy.2.trans_le (birthday_ofReal_le_omega0 r)
  obtain ⟨q, hq⟩ := (birthday_lt_omega0_iff_dyadic y).mp hb
  have he : y = ofReal (q.toRat : ℝ) := by
    simpa only [ofReal_ratCast] using hq.symm
  have hr : r ≠ (q.toRat : ℝ) := by
    intro hr
    have h : y = ofReal r := he.trans (congrArg ofReal hr.symm)
    exact hy.2.ne (congrArg birthday h)
  rw [he, ← map_sub]
  exact valuation_ofReal_of_ne_zero (sub_ne_zero.mpr hr)

private theorem omega_raw_option_gap (a : SignSequence.{u}) (p : Player)
    (y : IGame.{u}) (hy : y ∈ (ω^ (toIGame a)).moves p) :
    letI := IGame.Numeric.of_mem_moves hy
    valuation (omegaPower a - toSurrealOrderIso.symm (_root_.Surreal.mk y)) ≤
      valuation (omegaPower a) := by
  letI := IGame.Numeric.of_mem_moves hy
  apply valuation_sub_le_of_ne
  intro he
  have hn := (archimedeanClass_toSurreal_eq_iff _ _).mpr ((valuation_eq_iff _ _).mp he)
  simp only [toSurreal_omegaPower, toSurreal_orderIso_symm] at hn
  cases p with
  | left =>
    have hm := hy
    rw [IGame.leftMoves_wpow] at hm
    rcases Set.mem_insert_iff.mp hm with rfl | hm
    · simp at hn
    · obtain ⟨q, hq, b, hb, rfl⟩ := hm
      letI := IGame.Numeric.of_mem_moves hb
      have hq0 : q.toRat ≠ 0 := by exact_mod_cast ne_of_gt hq
      rw [_root_.Surreal.mk_mul, _root_.Surreal.mk_dyadic, _root_.Surreal.mk_wpow,
        ArchimedeanClass.mk_mul, ArchimedeanClass.mk_ratCast hq0, _root_.zero_add] at hn
      exact (_root_.Surreal.archimedeanClassMk_wpow_strictAnti
        ((_root_.Surreal.mk_lt_mk).mpr (IGame.Numeric.left_lt hb))).ne hn
  | right =>
    have hm := hy
    rw [IGame.rightMoves_wpow] at hm
    obtain ⟨q, hq, b, hb, rfl⟩ := hm
    letI := IGame.Numeric.of_mem_moves hb
    have hq0 : q.toRat ≠ 0 := by exact_mod_cast ne_of_gt hq
    rw [_root_.Surreal.mk_mul, _root_.Surreal.mk_dyadic, _root_.Surreal.mk_wpow,
      ArchimedeanClass.mk_mul, ArchimedeanClass.mk_ratCast hq0, _root_.zero_add] at hn
    exact (_root_.Surreal.archimedeanClassMk_wpow_strictAnti
      ((_root_.Surreal.mk_lt_mk).mpr (IGame.Numeric.lt_right hb))).ne' hn

private theorem product_isPrefix_of_close
    (c d : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·))
    (b : WithTop SignSequence.{u})
    (hcL : ∀ i, valuation (cut c - c.left i) = 0)
    (hcR : ∀ i, valuation (cut c - c.right i) = 0)
    (hdL : ∀ i, valuation (cut d - d.left i) ≤ b)
    (hdR : ∀ i, valuation (cut d - d.right i) ≤ b)
    (x : SignSequence.{u}) (hx : b < valuation (x - cut c * cut d)) :
    IsPrefix (cut c * cut d) x := by
  have hgap {q t : SignSequence.{u}} (hq : valuation (cut c - q) = 0)
      (ht : valuation (cut d - t) ≤ b) :
      valuation (cut c * cut d - mulOption (cut c) (cut d) q t) ≤ b := by
    rw [mul_sub_mulOption, valuation_mul, hq, _root_.zero_add]
    exact ht
  apply productCut_isPrefix_of_realizes
  apply (productCut_realizes_iff c d x).mpr
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro i j
    exact lt_of_close_above
      (mulOption_lt_mul_of_lt_of_lt ((cut_realizes c).1 i) ((cut_realizes d).1 j))
      ((hgap (hcL i) (hdL j)).trans_lt hx)
  · intro i j
    exact lt_of_close_above
      (mulOption_lt_mul_of_gt_of_gt ((cut_realizes c).2 i) ((cut_realizes d).2 j))
      ((hgap (hcR i) (hdR j)).trans_lt hx)
  · intro i j
    exact lt_of_close_below
      (mul_lt_mulOption_of_lt_of_gt ((cut_realizes c).1 i) ((cut_realizes d).2 j))
      ((hgap (hcL i) (hdR j)).trans_lt hx)
  · intro i j
    exact lt_of_close_below
      (mul_lt_mulOption_of_gt_of_lt ((cut_realizes c).2 i) ((cut_realizes d).1 j))
      ((hgap (hcR i) (hdL j)).trans_lt hx)

/-- A real monomial is a sign prefix of every surreal which differs from it
by a term of strictly higher valuation. The real coefficient may have any sign. -/
theorem real_mul_omegaPower_isPrefix_of_valuation_sub_gt
    (a : SignSequence.{u}) (r : ℝ) (x : SignSequence.{u})
    (hx : ((-a : SignSequence.{u}) : WithTop SignSequence.{u}) <
      valuation (x - ofReal r * omegaPower a)) :
    IsPrefix (ofReal r * omegaPower a) x := by
  let c := canonicalCut (ofReal r : SignSequence.{u})
  let d := numericGameSignCut (ω^ (toIGame a))
  have hc : cut c = ofReal r := cut_canonicalCut _
  have hd : cut d = omegaPower a := by
    rw [cut_numericGameSignCut, _root_.Surreal.mk_wpow]
    rfl
  have hcL (i : c.Left) : valuation (cut c - c.left i) = 0 := by
    rw [hc]
    exact real_option_gap r _
      (leftOption_simpler _ ((equivShrink (LeftIndex (ofReal r))).symm i))
  have hcR (i : c.Right) : valuation (cut c - c.right i) = 0 := by
    rw [hc]
    exact real_option_gap r _
      (rightOption_simpler _ ((equivShrink (RightIndex (ofReal r))).symm i))
  have hdL (i : d.Left) : valuation (cut d - d.left i) ≤ valuation (omegaPower a) := by
    rw [hd]
    let y := (equivShrink ((ω^ (toIGame a)).moves .left)).symm i
    exact omega_raw_option_gap a .left y.val y.property
  have hdR (i : d.Right) : valuation (cut d - d.right i) ≤ valuation (omegaPower a) := by
    rw [hd]
    let y := (equivShrink ((ω^ (toIGame a)).moves .right)).symm i
    exact omega_raw_option_gap a .right y.val y.property
  have h := product_isPrefix_of_close c d (valuation (omegaPower a)) hcL hcR hdL hdR x
    (by simpa only [hc, hd, valuation_omegaPower] using hx)
  simpa only [hc, hd] using h

end

end Surreal.Foundations.SignSequence

namespace Surreal.Foundations.SmallNormalForm

open SignSequence

noncomputable section

/-- The canonical cut evaluation agrees with every actual real Conway monomial. -/
@[simp] theorem cutEvaluation_single (a : SignSequence.{u}) (r : ℝ) :
    cutEvaluation (single a r) = ofReal r * omegaPower a := by
  by_cases hr : r = 0
  · subst r
    have hf : single a 0 = 0 := by
      apply ext
      intro b
      simp
    simp [hf]
  apply (cutEvaluation_single_isPrefix a r).antisymm
  apply real_mul_omegaPower_isPrefix_of_valuation_sub_gt
  have ha : a ∈ support (single a r) := by simpa using hr
  have h := cutEvaluation_remainder (single a r) a ha
  simpa [trunc_single_self, WithTop.LinearOrderedAddCommGroup.coe_neg] using h

end

end Surreal.Foundations.SmallNormalForm
