import FabiusFunction.CentralLobeConcavity
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# One peak per lobe: the central lobe of `|Φ|`

The audits' `thm:one-peak`, fully formal on the central lobe: the
pair-product form of the Rvachev Fourier transform
(`SincCanonicalProduct`) has positive real factors on `(−1,1)`, whose
summable logs give

`‖Φ(x)‖ = exp (∑'_{(h,r)} log (1 − x²/(2ʰ(r+1))²))`,

so `log ‖Φ‖` **is** the strictly concave series of
`CentralLobeConcavity`:

`log ‖Φ‖` is strictly concave on `(−1,1)` — in particular `|Φ|` has a
single peak on the central lobe.

* `summable_log_central` — summability of the factor logs.
* `norm_rvachevFourierProduct_eq_exp` — the product–series bridge.
* `strictConcaveOn_log_norm_rvachevFourierProduct` — **one peak**.
-/

set_option autoImplicit false

open Filter Topology Real Set

namespace Fabius

/-- The factor logs are summable at every point of the central
lobe. -/
theorem summable_log_central {x : ℝ} (hx : |x| < 1) :
    Summable (fun p : ℕ × ℕ =>
      Real.log (1 - x ^ 2 / (lobeZero p) ^ 2)) := by
  have h1 := abs_lt.mp hx
  have hx2 : x ^ 2 < 1 := by nlinarith
  have h1x : (0:ℝ) < 1 - x ^ 2 := by linarith
  apply Summable.of_abs
  apply Summable.of_nonneg_of_le (fun p => abs_nonneg _) (fun p => ?_)
    (summable_inv_sq_lobeZero.mul_left (x ^ 2 / (1 - x ^ 2)))
  have hfpos := factor_pos hx p
  have ha := one_le_sq_lobeZero p
  have ha0 : ((lobeZero p) ^ 2) ≠ 0 := by positivity
  have hf1 : 1 - x ^ 2 / (lobeZero p) ^ 2 ≤ 1 := by
    have : (0:ℝ) ≤ x ^ 2 / (lobeZero p) ^ 2 := by positivity
    linarith
  have hlog_np : Real.log (1 - x ^ 2 / (lobeZero p) ^ 2) ≤ 0 :=
    Real.log_nonpos hfpos.le hf1
  rw [abs_of_nonpos hlog_np]
  -- lower bound on the log: log t ≥ 1 − 1/t
  have hlb : 1 - 1 / (1 - x ^ 2 / (lobeZero p) ^ 2) ≤
      Real.log (1 - x ^ 2 / (lobeZero p) ^ 2) := by
    have h := Real.log_le_sub_one_of_pos
      (show (0:ℝ) < (1 - x ^ 2 / (lobeZero p) ^ 2)⁻¹ by positivity)
    rw [Real.log_inv] at h
    have hinv : (1 - x ^ 2 / (lobeZero p) ^ 2)⁻¹ =
        1 / (1 - x ^ 2 / (lobeZero p) ^ 2) := (one_div _).symm
    rw [hinv] at h
    linarith
  -- denominator comparison: f ≥ 1 − x²
  have hdivle : x ^ 2 / (lobeZero p) ^ 2 ≤ x ^ 2 :=
    div_le_self (by positivity) ha
  have hfge : 1 - x ^ 2 ≤ 1 - x ^ 2 / (lobeZero p) ^ 2 := by linarith
  -- 1/f − 1 = (x²/a²)/f
  have hquot : 1 / (1 - x ^ 2 / (lobeZero p) ^ 2) - 1 =
      (x ^ 2 / (lobeZero p) ^ 2) / (1 - x ^ 2 / (lobeZero p) ^ 2) := by
    rw [eq_div_iff hfpos.ne', sub_mul, one_div,
      inv_mul_cancel₀ hfpos.ne']
    ring
  have hmono : (x ^ 2 / (lobeZero p) ^ 2) /
      (1 - x ^ 2 / (lobeZero p) ^ 2) ≤
      (x ^ 2 / (lobeZero p) ^ 2) / (1 - x ^ 2) :=
    div_le_div_of_nonneg_left (by positivity) h1x hfge
  have heq : (x ^ 2 / (lobeZero p) ^ 2) / (1 - x ^ 2) =
      x ^ 2 / (1 - x ^ 2) * (1 / (lobeZero p) ^ 2) := by
    field_simp
  calc -Real.log (1 - x ^ 2 / (lobeZero p) ^ 2) ≤
      1 / (1 - x ^ 2 / (lobeZero p) ^ 2) - 1 := by linarith
    _ = (x ^ 2 / (lobeZero p) ^ 2) /
        (1 - x ^ 2 / (lobeZero p) ^ 2) := hquot
    _ ≤ (x ^ 2 / (lobeZero p) ^ 2) / (1 - x ^ 2) := hmono
    _ = x ^ 2 / (1 - x ^ 2) * (1 / (lobeZero p) ^ 2) := heq

/-- **The product–series bridge**: on the central lobe,
`‖Φ(x)‖ = exp (∑' log-factors)`. -/
theorem norm_rvachevFourierProduct_eq_exp {x : ℝ} (hx : |x| < 1) :
    ‖rvachevFourierProduct (x : ℂ)‖ =
      Real.exp (∑' p : ℕ × ℕ,
        Real.log (1 - x ^ 2 / (lobeZero p) ^ 2)) := by
  have hfpos : ∀ p : ℕ × ℕ, 0 < 1 - x ^ 2 / (lobeZero p) ^ 2 :=
    factor_pos hx
  have hsum := summable_log_central hx
  have hprod : HasProd (fun p : ℕ × ℕ => 1 - x ^ 2 / (lobeZero p) ^ 2)
      (Real.exp (∑' p : ℕ × ℕ,
        Real.log (1 - x ^ 2 / (lobeZero p) ^ 2))) :=
    Real.hasProd_of_hasSum_log hfpos hsum.hasSum
  have hfac : ∀ p : ℕ × ℕ,
      (1 + sineTerm ((x : ℂ) / 2 ^ p.1) p.2) =
      ((1 - x ^ 2 / (lobeZero p) ^ 2 : ℝ) : ℂ) := by
    rintro ⟨h, r⟩
    have h2 : ((2:ℂ) ^ h) ≠ 0 := pow_ne_zero h two_ne_zero
    have hr : ((r:ℂ) + 1) ≠ 0 := by
      rw [show ((r:ℂ) + 1) = ((r + 1 : ℕ) : ℂ) by push_cast; ring]
      exact Nat.cast_ne_zero.mpr r.succ_ne_zero
    simp only [sineTerm, lobeZero]
    push_cast
    field_simp
    ring
  have hprodC : HasProd (fun p : ℕ × ℕ =>
      ((1 - x ^ 2 / (lobeZero p) ^ 2 : ℝ) : ℂ))
      ((Real.exp (∑' p : ℕ × ℕ,
        Real.log (1 - x ^ 2 / (lobeZero p) ^ 2)) : ℝ) : ℂ) :=
    hprod.map Complex.ofRealHom.toMonoidHom Complex.continuous_ofReal
  have hΦ : rvachevFourierProduct (x : ℂ) =
      ((Real.exp (∑' p : ℕ × ℕ,
        Real.log (1 - x ^ 2 / (lobeZero p) ^ 2)) : ℝ) : ℂ) := by
    rw [rvachevFourierProduct_eq_tprod_pair, tprod_congr hfac]
    exact hprodC.tprod_eq
  rw [hΦ, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

/-- **One peak per lobe, central case** (`thm:one-peak`):
`log ‖Φ‖` is strictly concave on `(−1,1)`. -/
theorem strictConcaveOn_log_norm_rvachevFourierProduct :
    StrictConcaveOn ℝ (Set.Ioo (-1:ℝ) 1)
      (fun x => Real.log ‖rvachevFourierProduct (x : ℂ)‖) := by
  have h := strictConcaveOn_central_log_series
  have hkey : ∀ z ∈ Set.Ioo (-1:ℝ) 1,
      Real.log ‖rvachevFourierProduct ((z : ℝ) : ℂ)‖ =
      ∑' p : ℕ × ℕ, Real.log (1 - z ^ 2 / (lobeZero p) ^ 2) := by
    intro z hz
    rw [norm_rvachevFourierProduct_eq_exp
      (abs_lt.mpr (Set.mem_Ioo.mp hz)), Real.log_exp]
  refine ⟨h.1, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have hmem := h.1 hx hy ha.le hb.le hab
  show a • Real.log ‖rvachevFourierProduct (x : ℂ)‖ +
    b • Real.log ‖rvachevFourierProduct (y : ℂ)‖ <
    Real.log ‖rvachevFourierProduct ((a • x + b • y : ℝ) : ℂ)‖
  rw [hkey x hx, hkey y hy, hkey _ hmem]
  exact h.2 hx hy hxy ha hb hab

end Fabius
