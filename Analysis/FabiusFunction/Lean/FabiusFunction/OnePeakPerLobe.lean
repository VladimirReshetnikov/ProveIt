import FabiusFunction.SideLobeConcavity
import FabiusFunction.CentralLobePeakAtZero

/-!
# One peak per lobe

The audits' `thm:one-peak`, assembled for the actual Rvachev product:
`log ‖Φ‖` is strictly concave on **every** lobe of `Φ` —

* the central lobe `(−1,1)` (`CentralLobeOnePeak`),
* every positive side lobe `(m, m+1)` (`m ≥ 1`), and
* every negative side lobe `(−(m+1), −m)` by evenness —

so `|Φ|` has at most one interior peak per lobe.  The interval glue
is pointwise: a strict-concavity inequality for a pair `x ≠ y` in
`(m, m+1)` only ever sees the compact sub-interval
`((m + min x y)/2, (max x y + m + 1)/2)`, where
`SideLobeConcavity` applies.

* `strictConcaveOn_lobe_series_full` — the series on all of `(m,m+1)`.
* `strictConcaveOn_log_norm_on_lobe` — **`log ‖Φ‖` on `(m, m+1)`**.
* `strictConcaveOn_log_norm_on_neg_lobe` — the reflected lobes.
-/

set_option autoImplicit false

open Filter Topology Real Set

namespace Fabius

/-- Points of the open lobe are not lattice values. -/
theorem lobeZero_ne_abs_of_mem_lobe {m : ℕ} {y : ℝ}
    (hy : y ∈ Set.Ioo (m:ℝ) ((m:ℝ) + 1)) (p : ℕ × ℕ) :
    lobeZero p ≠ |y| := by
  obtain ⟨hyu, hyv⟩ := hy
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have hy0 : 0 < y := lt_of_le_of_lt hm0 hyu
  rw [abs_of_pos hy0]
  rcases lobeZero_le_or_add_one_le m p with h | h
  · exact ne_of_lt (lt_of_le_of_lt h hyu)
  · exact ne_of_gt (lt_of_lt_of_le hyv h)

/-- **The canonical log-series is strictly concave on the full open
lobe** `(m, m+1)`. -/
theorem strictConcaveOn_lobe_series_full (m : ℕ) :
    StrictConcaveOn ℝ (Set.Ioo (m:ℝ) ((m:ℝ) + 1))
      (fun z => ∑' p : ℕ × ℕ,
        Real.log (1 - z ^ 2 / (lobeZero p) ^ 2)) := by
  constructor
  · exact convex_Ioo _ _
  · intro x hx y hy hxy a b ha hb hab
    have hxm := Set.mem_Ioo.mp hx
    have hym := Set.mem_Ioo.mp hy
    have hminm : (m:ℝ) < min x y := lt_min hxm.1 hym.1
    have hmaxm : max x y < (m:ℝ) + 1 := max_lt hxm.2 hym.2
    have hminmax : min x y ≤ max x y := min_le_max
    have h := strictConcaveOn_lobe_log_series m
      (u := ((m:ℝ) + min x y) / 2)
      (v := (max x y + ((m:ℝ) + 1)) / 2)
      (by linarith) (by linarith) (by linarith)
    exact h.2
      (Set.mem_Ioo.mpr ⟨by linarith [min_le_left x y],
        by linarith [le_max_left x y]⟩)
      (Set.mem_Ioo.mpr ⟨by linarith [min_le_right x y],
        by linarith [le_max_right x y]⟩)
      hxy ha hb hab

/-- **One peak per positive lobe** (`thm:one-peak`, side lobes):
`log ‖Φ‖` is strictly concave on `(m, m+1)`.  For `m = 0` this is the
right half of the central lobe; the genuinely new content is `m ≥ 1`. -/
theorem strictConcaveOn_log_norm_on_lobe (m : ℕ) :
    StrictConcaveOn ℝ (Set.Ioo (m:ℝ) ((m:ℝ) + 1))
      (fun x => Real.log ‖rvachevFourierProduct (x : ℂ)‖) := by
  have h := strictConcaveOn_lobe_series_full m
  have hkey : ∀ z ∈ Set.Ioo (m:ℝ) ((m:ℝ) + 1),
      Real.log ‖rvachevFourierProduct ((z : ℝ) : ℂ)‖ =
      ∑' p : ℕ × ℕ, Real.log (1 - z ^ 2 / (lobeZero p) ^ 2) :=
    fun z hz => log_norm_rvachevFourierProduct_eq_tsum
      (lobeZero_ne_abs_of_mem_lobe hz)
  refine ⟨h.1, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have hmem := h.1 hx hy ha.le hb.le hab
  show a • Real.log ‖rvachevFourierProduct (x : ℂ)‖ +
    b • Real.log ‖rvachevFourierProduct (y : ℂ)‖ <
    Real.log ‖rvachevFourierProduct ((a • x + b • y : ℝ) : ℂ)‖
  rw [hkey x hx, hkey y hy, hkey _ hmem]
  exact h.2 hx hy hxy ha hb hab

/-- **One peak per negative lobe**: by evenness, `log ‖Φ‖` is strictly
concave on `(−(m+1), −m)` as well. -/
theorem strictConcaveOn_log_norm_on_neg_lobe (m : ℕ) :
    StrictConcaveOn ℝ (Set.Ioo (-((m:ℝ) + 1)) (-(m:ℝ)))
      (fun x => Real.log ‖rvachevFourierProduct (x : ℂ)‖) := by
  have h := strictConcaveOn_log_norm_on_lobe m
  have hEvenLog : ∀ z : ℝ,
      Real.log ‖rvachevFourierProduct (((-z : ℝ)) : ℂ)‖ =
      Real.log ‖rvachevFourierProduct ((z : ℝ) : ℂ)‖ := fun z => by
    rw [norm_rvachevFourierProduct_neg]
  constructor
  · exact convex_Ioo _ _
  · intro x hx y hy hxy a b ha hb hab
    obtain ⟨hx1, hx2⟩ := Set.mem_Ioo.mp hx
    obtain ⟨hy1, hy2⟩ := Set.mem_Ioo.mp hy
    have hx' : -x ∈ Set.Ioo (m:ℝ) ((m:ℝ) + 1) :=
      Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    have hy' : -y ∈ Set.Ioo (m:ℝ) ((m:ℝ) + 1) :=
      Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    have hxy' : -x ≠ -y := fun hc => hxy (by linarith [neg_inj.mp hc])
    have hcombo : a • x + b • y = -(a • (-x) + b • (-y)) := by
      simp only [smul_eq_mul]
      ring
    show a • Real.log ‖rvachevFourierProduct (x : ℂ)‖ +
      b • Real.log ‖rvachevFourierProduct (y : ℂ)‖ <
      Real.log ‖rvachevFourierProduct ((a • x + b • y : ℝ) : ℂ)‖
    rw [← hEvenLog x, ← hEvenLog y, hcombo,
      hEvenLog (a • (-x) + b • (-y))]
    exact h.2 hx' hy' hxy' ha hb hab

end Fabius
