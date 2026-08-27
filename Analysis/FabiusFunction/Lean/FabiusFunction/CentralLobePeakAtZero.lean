import FabiusFunction.CentralLobeOnePeak

/-!
# The central peak of `|Φ|` sits at the origin

The quantitative endgame of `thm:one-peak` on the central lobe: the
even, strictly log-concave function `|Φ|` attains its unique maximum
on `(−1,1)` at `x = 0`, where `Φ(0) = 1`:

`‖Φ(x)‖ < 1` for all `x ∈ (−1,1)`, `x ≠ 0`.

No compactness is needed — evenness plus the strict midpoint
inequality at the pair `(x, −x)` pins the peak.

* `rvachevFourierProduct_zero` — `Φ(0) = 1`.
* `norm_rvachevFourierProduct_pos` — `0 < ‖Φ‖` on the lobe.
* `norm_rvachevFourierProduct_lt_one` — the strict peak.
* `isMaxOn_norm_rvachevFourierProduct` — `IsMaxOn` packaging.
-/

set_option autoImplicit false

open Filter Topology Real Set

namespace Fabius

/-- The sinc product is normalized to `1` at the origin. -/
@[simp] theorem rvachevFourierProduct_zero :
    rvachevFourierProduct 0 = 1 := by
  unfold rvachevFourierProduct
  have h : ∀ n : ℕ,
      complexSinc ((Real.pi : ℂ) * 0 / (2:ℂ) ^ n) = 1 := by
    intro n
    norm_num [complexSinc]
  rw [tprod_congr h, tprod_one]

/-- Evenness of the modulus on the real axis. -/
theorem norm_rvachevFourierProduct_neg (x : ℝ) :
    ‖rvachevFourierProduct (((-x : ℝ)) : ℂ)‖ =
      ‖rvachevFourierProduct ((x : ℝ) : ℂ)‖ := by
  rw [show (((-x : ℝ)) : ℂ) = -((x : ℝ) : ℂ) by push_cast; ring,
    rvachevFourierProduct_neg]

/-- The modulus is strictly positive throughout the central lobe. -/
theorem norm_rvachevFourierProduct_pos {x : ℝ} (hx : |x| < 1) :
    0 < ‖rvachevFourierProduct (x : ℂ)‖ := by
  rw [norm_rvachevFourierProduct_eq_exp hx]
  exact Real.exp_pos _

/-- **The strict central peak**: away from the origin the modulus is
strictly below its value `1` at the peak. -/
theorem norm_rvachevFourierProduct_lt_one {x : ℝ}
    (hx : x ∈ Set.Ioo (-1:ℝ) 1) (hne : x ≠ 0) :
    ‖rvachevFourierProduct (x : ℂ)‖ < 1 := by
  have h := strictConcaveOn_log_norm_rvachevFourierProduct
  have hx' : |x| < 1 := abs_lt.mpr (Set.mem_Ioo.mp hx)
  have hmx : (-x) ∈ Set.Ioo (-1:ℝ) 1 := by
    obtain ⟨h1, h2⟩ := Set.mem_Ioo.mp hx
    exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  have hxy : x ≠ -x := fun hcontra => hne (by linarith)
  have hmid := h.2 hx hmx hxy
    (show (0:ℝ) < 1/2 by norm_num) (show (0:ℝ) < 1/2 by norm_num)
    (show (1:ℝ)/2 + 1/2 = 1 by norm_num)
  rw [show ((1:ℝ)/2) • x + ((1:ℝ)/2) • (-x) = (0:ℝ) by
      rw [smul_eq_mul, smul_eq_mul]; ring] at hmid
  simp only [smul_eq_mul] at hmid
  rw [norm_rvachevFourierProduct_neg] at hmid
  have hzero : Real.log ‖rvachevFourierProduct ((0:ℝ) : ℂ)‖ = 0 := by
    rw [show ((0:ℝ) : ℂ) = 0 from Complex.ofReal_zero,
      rvachevFourierProduct_zero, norm_one, Real.log_one]
  rw [hzero] at hmid
  have hlog : Real.log ‖rvachevFourierProduct (x : ℂ)‖ < 0 := by
    linarith
  exact (Real.log_neg_iff (norm_rvachevFourierProduct_pos hx')).mp hlog

/-- `IsMaxOn` packaging: `x = 0` maximizes `‖Φ‖` over the central
lobe. -/
theorem isMaxOn_norm_rvachevFourierProduct :
    IsMaxOn (fun x : ℝ => ‖rvachevFourierProduct (x : ℂ)‖)
      (Set.Ioo (-1:ℝ) 1) 0 := by
  rw [isMaxOn_iff]
  intro x hx
  show ‖rvachevFourierProduct ((x : ℝ) : ℂ)‖ ≤
    ‖rvachevFourierProduct ((0:ℝ) : ℂ)‖
  have h0 : ‖rvachevFourierProduct ((0:ℝ) : ℂ)‖ = 1 := by
    rw [show ((0:ℝ) : ℂ) = 0 from Complex.ofReal_zero,
      rvachevFourierProduct_zero, norm_one]
  rw [h0]
  rcases eq_or_ne x 0 with rfl | hne
  · exact le_of_eq h0
  · exact (norm_rvachevFourierProduct_lt_one hx hne).le

end Fabius
