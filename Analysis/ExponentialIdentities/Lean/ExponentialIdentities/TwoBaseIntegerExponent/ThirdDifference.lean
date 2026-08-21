import ExponentialIdentities.TwoBaseIntegerExponent.ZeroDensity

/-!
# Third forward differences at the two-base exponent
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-- Exact third-forward-difference mean-value identity at step `h`. -/
theorem exists_third_difference_point_ap (n h : ℕ) (hn : 1 ≤ n) (hh : 1 ≤ h) :
    ∃ d : ℝ, (n : ℝ) < d ∧ d < (n + 3 * h : ℕ) ∧
      ((n + 3 * h : ℕ) : ℝ) ^ logThreeDivLogTwo -
          3 * ((n + 2 * h : ℕ) : ℝ) ^ logThreeDivLogTwo +
          3 * ((n + h : ℕ) : ℝ) ^ logThreeDivLogTwo -
          (n : ℝ) ^ logThreeDivLogTwo =
        logThreeDivLogTwo * (logThreeDivLogTwo - 1) *
          (logThreeDivLogTwo - 2) * (h : ℝ) ^ 3 *
            d ^ (logThreeDivLogTwo - 3) := by
  let α : ℝ := logThreeDivLogTwo
  let f : ℝ → ℝ := fun y ↦ y ^ α
  let q : ℝ → ℝ := fun y ↦ y ^ (α - 1)
  let t : ℝ → ℝ := fun y ↦ y ^ (α - 2)
  let s : ℝ → ℝ := fun y ↦ q (y + h) - q y
  let g : ℝ → ℝ := fun y ↦ f (y + h) - f y
  let g' : ℝ → ℝ := fun y ↦ α * (q (y + h) - q y)
  let G : ℝ → ℝ := fun y ↦ g (y + h) - g y
  let G' : ℝ → ℝ := fun y ↦ α * (s (y + h) - s y)
  let s' : ℝ → ℝ := fun y ↦ (α - 1) * (t (y + h) - t y)
  let t' : ℝ → ℝ := fun y ↦ (α - 2) * y ^ (α - 3)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hhpos : (0 : ℝ) < h := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh)
  have hg_deriv (y : ℝ) (hy : 0 < y) : HasDerivAt g (g' y) y := by
    have houter := Real.hasDerivAt_rpow_const (x := y + h) (p := α)
      (Or.inl (by positivity : y + (h : ℝ) ≠ 0))
    have hshift : HasDerivAt (fun z : ℝ ↦ (z + h) ^ α)
        (α * (y + h) ^ (α - 1)) y := houter.comp_add_const y h
    have hbase := Real.hasDerivAt_rpow_const (x := y) (p := α) (Or.inl hy.ne')
    dsimp only [g, g', f, q]
    convert hshift.sub hbase using 1 <;>
      first
      | rfl
      | exact Subsingleton.elim _ _
      | ring
  have hG_deriv (y : ℝ) (hy : 0 < y) : HasDerivAt G (G' y) y := by
    have houter := hg_deriv (y + h) (by positivity)
    have hshift : HasDerivAt (fun z : ℝ ↦ g (z + h)) (g' (y + h)) y :=
      houter.comp_add_const y h
    have hbase := hg_deriv y hy
    dsimp only [g', q] at hshift hbase
    dsimp only [G, G', s, q]
    convert hshift.sub hbase using 1 <;>
      first
      | rfl
      | exact Subsingleton.elim _ _
      | ring
  have hG_cont : ContinuousOn G (Icc (n : ℝ) ((n : ℝ) + h)) := by
    intro y hy
    exact (hG_deriv y (hnpos.trans_le hy.1)).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hcEq⟩ := exists_hasDerivAt_eq_slope G G'
    (by linarith : (n : ℝ) < (n : ℝ) + h) hG_cont (by
      intro y hy
      exact hG_deriv y (hnpos.trans hy.1))
  have hcpos : 0 < c := hnpos.trans hc.1
  have hs_deriv (y : ℝ) (hy : 0 < y) : HasDerivAt s (s' y) y := by
    have houter := Real.hasDerivAt_rpow_const (x := y + h) (p := α - 1)
      (Or.inl (by positivity : y + (h : ℝ) ≠ 0))
    rw [show α - 1 - 1 = α - 2 by ring] at houter
    have hshift : HasDerivAt (fun z : ℝ ↦ (z + h) ^ (α - 1))
        ((α - 1) * (y + h) ^ (α - 2)) y := houter.comp_add_const y h
    have hbase := Real.hasDerivAt_rpow_const (x := y) (p := α - 1) (Or.inl hy.ne')
    rw [show α - 1 - 1 = α - 2 by ring] at hbase
    have hbase' : HasDerivAt (fun z : ℝ ↦ z ^ (α - 1))
        ((α - 1) * y ^ (α - 2)) y := hbase
    dsimp only [s, s', q, t]
    convert hshift.sub hbase' using 1 <;>
      first
      | rfl
      | exact Subsingleton.elim _ _
      | ring
  have hs_cont : ContinuousOn s (Icc c (c + h)) := by
    intro y hy
    exact (hs_deriv y (hcpos.trans_le hy.1)).continuousAt.continuousWithinAt
  obtain ⟨e, he, heEq⟩ := exists_hasDerivAt_eq_slope s s'
    (by linarith : c < c + h) hs_cont (by
      intro y hy
      exact hs_deriv y (hcpos.trans hy.1))
  have hepos : 0 < e := hcpos.trans he.1
  have ht_deriv (y : ℝ) (hy : 0 < y) : HasDerivAt t (t' y) y := by
    have hp := Real.hasDerivAt_rpow_const (x := y) (p := α - 2) (Or.inl hy.ne')
    rw [show α - 2 - 1 = α - 3 by ring] at hp
    exact hp
  have ht_cont : ContinuousOn t (Icc e (e + h)) := by
    intro y hy
    exact (ht_deriv y (hepos.trans_le hy.1)).continuousAt.continuousWithinAt
  obtain ⟨d, hd, hdEq⟩ := exists_hasDerivAt_eq_slope t t'
    (by linarith : e < e + h) ht_cont (by
      intro y hy
      exact ht_deriv y (hepos.trans hy.1))
  refine ⟨d, hc.1.trans (he.1.trans hd.1), ?_, ?_⟩
  · have hcup : c < (n : ℝ) + h := hc.2
    have heup : e < c + h := he.2
    have hdup : d < e + h := hd.2
    push_cast
    linarith
  · have hhne : (h : ℝ) ≠ 0 := ne_of_gt hhpos
    have hcEq' : G ((n : ℝ) + h) - G n = G' c * h :=
      ((eq_div_iff hhne).mp (by simpa using hcEq)).symm
    have heEq' : s (c + h) - s c = s' e * h :=
      ((eq_div_iff hhne).mp (by simpa using heEq)).symm
    have hdEq' : t (e + h) - t e = t' d * h :=
      ((eq_div_iff hhne).mp (by simpa using hdEq)).symm
    dsimp only [G'] at hcEq'
    rw [heEq'] at hcEq'
    dsimp only [s'] at hcEq'
    rw [hdEq'] at hcEq'
    dsimp only [t'] at hcEq'
    dsimp only [G, g, f, α] at hcEq' ⊢
    push_cast at hcEq' ⊢
    ring_nf at hcEq' ⊢
    exact hcEq'

/-- Under the exact third-curvature inequality, the absolute third forward difference is
strictly between zero and one. -/
theorem abs_third_difference_logThreeDivLogTwo_ap_lt_one_of_curvature
    (n h : ℕ) (hn : 1 ≤ n) (hh : 1 ≤ h)
    (hcurv :
      |logThreeDivLogTwo * (logThreeDivLogTwo - 1) *
          (logThreeDivLogTwo - 2)| * (h : ℝ) ^ 3 <
        (n : ℝ) ^ (3 - logThreeDivLogTwo)) :
    0 < |((n + 3 * h : ℕ) : ℝ) ^ logThreeDivLogTwo -
          3 * ((n + 2 * h : ℕ) : ℝ) ^ logThreeDivLogTwo +
          3 * ((n + h : ℕ) : ℝ) ^ logThreeDivLogTwo -
          (n : ℝ) ^ logThreeDivLogTwo| ∧
      |((n + 3 * h : ℕ) : ℝ) ^ logThreeDivLogTwo -
          3 * ((n + 2 * h : ℕ) : ℝ) ^ logThreeDivLogTwo +
          3 * ((n + h : ℕ) : ℝ) ^ logThreeDivLogTwo -
          (n : ℝ) ^ logThreeDivLogTwo| < 1 := by
  obtain ⟨d, hdlo, _hdhi, hdEq⟩ := exists_third_difference_point_ap n h hn hh
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hhpos : (0 : ℝ) < h := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh)
  have hdpos : 0 < d := hnpos.trans hdlo
  have hα0 : logThreeDivLogTwo ≠ 0 :=
    ne_of_gt (lt_trans zero_lt_one one_lt_logThreeDivLogTwo)
  have hα1 : logThreeDivLogTwo - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr one_lt_logThreeDivLogTwo)
  have hα2 : logThreeDivLogTwo - 2 ≠ 0 := by
    linarith [logThreeDivLogTwo_lt_eight_fifths]
  have hαthree : logThreeDivLogTwo - 3 < 0 := by
    linarith [logThreeDivLogTwo_lt_eight_fifths]
  have hcoefne :
      logThreeDivLogTwo * (logThreeDivLogTwo - 1) *
          (logThreeDivLogTwo - 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hα0 hα1) hα2
  have hdiffne :
      ((n + 3 * h : ℕ) : ℝ) ^ logThreeDivLogTwo -
          3 * ((n + 2 * h : ℕ) : ℝ) ^ logThreeDivLogTwo +
          3 * ((n + h : ℕ) : ℝ) ^ logThreeDivLogTwo -
          (n : ℝ) ^ logThreeDivLogTwo ≠ 0 := by
    rw [hdEq]
    exact mul_ne_zero
      (mul_ne_zero hcoefne (pow_ne_zero _ (ne_of_gt hhpos)))
      (ne_of_gt (Real.rpow_pos_of_pos hdpos _))
  have habsEq :
      |((n + 3 * h : ℕ) : ℝ) ^ logThreeDivLogTwo -
          3 * ((n + 2 * h : ℕ) : ℝ) ^ logThreeDivLogTwo +
          3 * ((n + h : ℕ) : ℝ) ^ logThreeDivLogTwo -
          (n : ℝ) ^ logThreeDivLogTwo| =
        |logThreeDivLogTwo * (logThreeDivLogTwo - 1) *
          (logThreeDivLogTwo - 2)| * (h : ℝ) ^ 3 *
            d ^ (logThreeDivLogTwo - 3) := by
    rw [hdEq, abs_mul, abs_mul, abs_of_pos (pow_pos hhpos 3),
      abs_of_pos (Real.rpow_pos_of_pos hdpos _)]
  have hcoefpos :
      0 < |logThreeDivLogTwo * (logThreeDivLogTwo - 1) *
        (logThreeDivLogTwo - 2)| * (h : ℝ) ^ 3 :=
    mul_pos (abs_pos.mpr hcoefne) (pow_pos hhpos 3)
  have hpowlt : d ^ (logThreeDivLogTwo - 3) <
      (n : ℝ) ^ (logThreeDivLogTwo - 3) :=
    Real.rpow_lt_rpow_of_neg hnpos hdlo hαthree
  have hpowpos : 0 < (n : ℝ) ^ (logThreeDivLogTwo - 3) :=
    Real.rpow_pos_of_pos hnpos _
  have hmul :
      |logThreeDivLogTwo * (logThreeDivLogTwo - 1) *
          (logThreeDivLogTwo - 2)| * (h : ℝ) ^ 3 *
          (n : ℝ) ^ (logThreeDivLogTwo - 3) <
        (n : ℝ) ^ (3 - logThreeDivLogTwo) *
          (n : ℝ) ^ (logThreeDivLogTwo - 3) :=
    mul_lt_mul_of_pos_right hcurv hpowpos
  have hcancel :
      (n : ℝ) ^ (3 - logThreeDivLogTwo) *
          (n : ℝ) ^ (logThreeDivLogTwo - 3) = 1 := by
    rw [← Real.rpow_add hnpos]
    norm_num
  constructor
  · exact abs_pos.mpr hdiffne
  · rw [habsEq]
    exact (mul_lt_mul_of_pos_left hpowlt hcoefpos).trans
      (hmul.trans_eq hcancel)

/-- Four integral values of `m ↦ m ^ (log 3 / log 2)` cannot occur in an arithmetic
progression under the exact absolute third-curvature bound. -/
theorem not_four_arithmetic_progression_logThreeDivLogTwo_rpow_integers_of_curvature
    (n h : ℕ) (hn : 1 ≤ n) (hh : 1 ≤ h)
    (hcurv :
      |logThreeDivLogTwo * (logThreeDivLogTwo - 1) *
          (logThreeDivLogTwo - 2)| * (h : ℝ) ^ 3 <
        (n : ℝ) ^ (3 - logThreeDivLogTwo))
    (h₀ : ∃ z : ℤ, (z : ℝ) = (n : ℝ) ^ logThreeDivLogTwo)
    (h₁ : ∃ z : ℤ, (z : ℝ) = ((n + h : ℕ) : ℝ) ^ logThreeDivLogTwo)
    (h₂ : ∃ z : ℤ, (z : ℝ) = ((n + 2 * h : ℕ) : ℝ) ^ logThreeDivLogTwo)
    (h₃ : ∃ z : ℤ, (z : ℝ) = ((n + 3 * h : ℕ) : ℝ) ^ logThreeDivLogTwo) :
    False := by
  obtain ⟨z₀, hz₀⟩ := h₀
  obtain ⟨z₁, hz₁⟩ := h₁
  obtain ⟨z₂, hz₂⟩ := h₂
  obtain ⟨z₃, hz₃⟩ := h₃
  obtain ⟨habspos, habslt⟩ :=
    abs_third_difference_logThreeDivLogTwo_ap_lt_one_of_curvature n h hn hh hcurv
  have hzpos : (0 : ℤ) < |z₃ - 3 * z₂ + 3 * z₁ - z₀| := by
    exact_mod_cast (show (0 : ℝ) <
      |(z₃ : ℝ) - 3 * (z₂ : ℝ) + 3 * (z₁ : ℝ) - (z₀ : ℝ)| by
        rw [hz₃, hz₂, hz₁, hz₀]
        exact habspos)
  have hzlt : |z₃ - 3 * z₂ + 3 * z₁ - z₀| < (1 : ℤ) := by
    exact_mod_cast (show
      |(z₃ : ℝ) - 3 * (z₂ : ℝ) + 3 * (z₁ : ℝ) - (z₀ : ℝ)| < 1 by
        rw [hz₃, hz₂, hz₁, hz₀]
        exact habslt)
  omega

/-- Four natural two-base candidates cannot form a progression under the exact absolute
third-curvature bound. -/
theorem not_four_arithmetic_progression_twoBaseNaturalCandidates_of_curvature
    (n h : ℕ) (hn : 1 ≤ n) (hh : 1 ≤ h)
    (hcurv :
      |logThreeDivLogTwo * (logThreeDivLogTwo - 1) *
          (logThreeDivLogTwo - 2)| * (h : ℝ) ^ 3 <
        (n : ℝ) ^ (3 - logThreeDivLogTwo)) :
    ¬(TwoBaseNaturalCandidate n ∧
      TwoBaseNaturalCandidate (n + h) ∧
      TwoBaseNaturalCandidate (n + 2 * h) ∧
      TwoBaseNaturalCandidate (n + 3 * h)) := by
  rintro ⟨h₀, h₁, h₂, h₃⟩
  exact
    not_four_arithmetic_progression_logThreeDivLogTwo_rpow_integers_of_curvature
      n h hn hh hcurv h₀.2 h₁.2 h₂.2 h₃.2

end LeanProofs.TwoBaseIntegerExponent
