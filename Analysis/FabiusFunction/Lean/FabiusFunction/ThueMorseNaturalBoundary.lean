import FabiusFunction.ThueMorseDiscSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The unit circle is a natural boundary

The atlas's `thm:natural-boundary`, in its self-contained radial-zero
form: **no holomorphic function on any disc centered at a point of the
unit circle can agree with the Thue–Morse series `F(z) = ∑ ε(n)zⁿ` on
the overlap with the unit disc.**  Every boundary point is singular;
no analytic continuation across any arc exists.

The proof is the atlas's:

1. At a `2^k`-th root of unity `ζ`, the iterated Mahler equation
   splits `F(ρζ)` into `k` head factors of modulus at most `2` and the
   real value `F(ρ^(2^k))`, which is at most `1 - ρ^(2^k)`.  Hence
   `F(ρζ) → 0` radially (`tendsto_thueMorseDiscSeries_radial_zero`).
2. Two-power roots of unity approximate every point of the circle
   from within any arc.  A hypothetical holomorphic extension `g` is
   continuous, so it vanishes at every dyadic root in its disc; those
   accumulate at the center, so `g ≡ 0` by the identity theorem.
3. Then `F ≡ 0` on a nonempty open subset of the unit disc, so
   `F ≡ 0` on the disc by the identity theorem again — contradicting
   `F(0) = 1`.

* `tendsto_thueMorseDiscSeries_radial_zero` — radial vanishing.
* `thueMorse_natural_boundary` — **the natural-boundary theorem**.
-/

set_option autoImplicit false

open Finset Filter Metric Set Topology

namespace Fabius

/-- A root of unity has norm one. -/
theorem norm_eq_one_of_pow_eq_one {ζ : ℂ} {n : ℕ} (hζ : ζ ^ n = 1)
    (hn : n ≠ 0) : ‖ζ‖ = 1 := by
  have h := congrArg norm hζ
  rw [norm_pow, norm_one] at h
  have ha0 : 0 < ‖ζ‖ := by
    rcases eq_or_lt_of_le (norm_nonneg ζ) with h0 | h0
    · exfalso
      rw [← h0, zero_pow hn] at h
      norm_num at h
    · exact h0
  have hlog := congrArg Real.log h
  rw [Real.log_pow, Real.log_one] at hlog
  have hz : Real.log ‖ζ‖ = 0 := by
    rcases mul_eq_zero.mp hlog with hcase | hcase
    · exact absurd hcase (Nat.cast_ne_zero.mpr hn)
    · exact hcase
  rw [← Real.exp_log ha0, hz, Real.exp_zero]

/-- **Radial vanishing at dyadic roots of unity**: along the radius
toward a `2^k`-th root of unity, the Thue–Morse series tends to zero
— the head of the iterated Mahler equation stays bounded by `2^k`
while the real tail is crushed by `1 - ρ^(2^k)`. -/
theorem tendsto_thueMorseDiscSeries_radial_zero {ζ : ℂ} {k : ℕ}
    (hζ : ζ ^ 2 ^ k = 1) :
    Tendsto (fun ρ : ℝ => thueMorseDiscSeries ((ρ : ℂ) * ζ))
      (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have hζ1 : ‖ζ‖ = 1 := norm_eq_one_of_pow_eq_one hζ (by positivity)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero'
    (g := fun ρ : ℝ => (2 : ℝ) ^ k * (1 - ρ ^ 2 ^ k))
    (Filter.Eventually.of_forall fun ρ => norm_nonneg _)
    ?_ ?_
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)]
      with ρ hρ
    obtain ⟨hρ0, hρ1⟩ := hρ
    have hnorm : ‖(ρ : ℂ) * ζ‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hρ0, hζ1, mul_one]
      exact hρ1
    have hpowz : ((ρ : ℂ) * ζ) ^ 2 ^ k = ((ρ ^ 2 ^ k : ℝ) : ℂ) := by
      rw [mul_pow, hζ, mul_one, Complex.ofReal_pow]
    have hρk0 : (0 : ℝ) ≤ ρ ^ 2 ^ k := by positivity
    have hρk1 : ρ ^ 2 ^ k < 1 :=
      pow_lt_one₀ hρ0.le hρ1 (by positivity)
    rw [thueMorseDiscSeries_iterate hnorm k, hpowz, norm_mul]
    have htail : ‖thueMorseDiscSeries ((ρ ^ 2 ^ k : ℝ) : ℂ)‖ ≤
        1 - ρ ^ 2 ^ k := thueMorseDiscSeries_real_le hρk0 hρk1
    have hfac : ∀ j ∈ range k, ‖1 - ((ρ : ℂ) * ζ) ^ 2 ^ j‖ ≤ 2 := by
      intro j _
      have h1 : ‖(ρ : ℂ) * ζ‖ ^ 2 ^ j ≤ 1 :=
        pow_le_one₀ (norm_nonneg _) hnorm.le
      calc ‖1 - ((ρ : ℂ) * ζ) ^ 2 ^ j‖
          ≤ ‖(1 : ℂ)‖ + ‖((ρ : ℂ) * ζ) ^ 2 ^ j‖ := norm_sub_le _ _
        _ ≤ 2 := by
            rw [norm_one, norm_pow]
            linarith
    have hhead : ‖∏ j ∈ range k, (1 - ((ρ : ℂ) * ζ) ^ 2 ^ j)‖ ≤
        2 ^ k := by
      rw [Complex.norm_prod]
      calc ∏ j ∈ range k, ‖1 - ((ρ : ℂ) * ζ) ^ 2 ^ j‖
          ≤ ∏ _j ∈ range k, (2 : ℝ) :=
            Finset.prod_le_prod (fun j _ => norm_nonneg _) hfac
        _ = 2 ^ k := by rw [Finset.prod_const, card_range]
    exact mul_le_mul hhead htail (norm_nonneg _) (by positivity)
  · have hcont : Tendsto
        (fun ρ : ℝ => (2 : ℝ) ^ k * (1 - ρ ^ 2 ^ k)) (𝓝 1)
        (𝓝 ((2 : ℝ) ^ k * (1 - 1 ^ 2 ^ k))) :=
      (continuous_const.mul
        (continuous_const.sub (continuous_pow _))).tendsto 1
    have h := hcont.mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
    simpa using h

/-- Two-power roots of unity approach every point of the unit circle,
from angles strictly above the argument: the constructed sequence
consists of `2^(k+1)`-th roots of unity distinct from the target. -/
private theorem exists_dyadic_root_seq (z₀ : ℂ) (hz₀ : ‖z₀‖ = 1) :
    ∃ u : ℕ → ℂ, (∀ k, (u k) ^ 2 ^ (k + 1) = 1) ∧
      (∀ k, u k ≠ z₀) ∧ Tendsto u atTop (𝓝 z₀) := by
  have hπ := Real.pi_pos
  set θ := Complex.arg z₀ with hθ
  have hz₀exp : Complex.exp ((θ : ℂ) * Complex.I) = z₀ := by
    have h := Complex.norm_mul_exp_arg_mul_I z₀
    rwa [hz₀, Complex.ofReal_one, one_mul] at h
  have key : ∀ k : ℕ, ∃ a : ℝ,
      (Complex.exp ((a : ℂ) * Complex.I)) ^ 2 ^ (k + 1) = 1 ∧
      Complex.exp ((a : ℂ) * Complex.I) ≠ z₀ ∧
      0 < a - θ ∧ a - θ ≤ 2 * Real.pi / 2 ^ (k + 1) := by
    intro k
    have hP0 : (0 : ℝ) < 2 ^ (k + 1) := by positivity
    set x : ℝ := 2 ^ (k + 1) * θ / (2 * Real.pi) with hx
    set m : ℤ := ⌊x⌋ + 1 with hm
    set a : ℝ := 2 * Real.pi * m / 2 ^ (k + 1) with ha
    have hfl : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
    have hfu : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
    have hmR : (m : ℝ) = (⌊x⌋ : ℝ) + 1 := by
      rw [hm]
      push_cast
      ring
    have hθx : θ = 2 * Real.pi * x / 2 ^ (k + 1) := by
      rw [hx]
      field_simp
      try ring
    have hdiff : a - θ = 2 * Real.pi * ((m : ℝ) - x) / 2 ^ (k + 1) := by
      rw [ha, hθx]
      ring
    have hmx0 : 0 < (m : ℝ) - x := by
      rw [hmR]
      linarith
    have hmx1 : (m : ℝ) - x ≤ 1 := by
      rw [hmR]
      linarith
    have hna : (2 : ℝ) ^ (k + 1) * a = (m : ℝ) * (2 * Real.pi) := by
      rw [ha]
      field_simp
      try ring
    refine ⟨a, ?_, ?_, ?_, ?_⟩
    · rw [← Complex.exp_nat_mul,
        show ((2 ^ (k + 1) : ℕ) : ℂ) * (((a : ℝ) : ℂ) * Complex.I) =
          ((m : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) from by
          calc ((2 ^ (k + 1) : ℕ) : ℂ) * (((a : ℝ) : ℂ) * Complex.I)
              = (((2 : ℝ) ^ (k + 1) * a : ℝ) : ℂ) * Complex.I := by
                push_cast
                ring
            _ = ((((m : ℝ) * (2 * Real.pi) : ℝ)) : ℂ) * Complex.I := by
                rw [hna]
            _ = ((m : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) := by
                push_cast
                ring]
      exact Complex.exp_int_mul_two_pi_mul_I m
    · intro hcon
      rw [← hz₀exp] at hcon
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hcon
      have h2 : (((a : ℝ) : ℂ) - ((θ : ℝ) : ℂ)) * Complex.I =
          ((n : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by
        linear_combination hn
      have h3 : (((a : ℝ) : ℂ) - ((θ : ℝ) : ℂ)) =
          (n : ℂ) * (2 * (Real.pi : ℂ)) :=
        mul_right_cancel₀ Complex.I_ne_zero h2
      have h4 : a - θ = (n : ℝ) * (2 * Real.pi) := by
        exact_mod_cast h3
      have hpos : 0 < a - θ := by
        rw [hdiff]
        positivity
      have hup : a - θ ≤ 2 * Real.pi / 2 ^ (k + 1) := by
        rw [hdiff, show 2 * Real.pi / 2 ^ (k + 1) =
          2 * Real.pi * 1 / 2 ^ (k + 1) by ring]
        gcongr
      have h2pow : (2 : ℝ) ≤ 2 ^ (k + 1) := by
        calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ (k + 1) :=
            pow_le_pow_right₀ one_le_two (by omega)
      have hhalf : 2 * Real.pi / 2 ^ (k + 1) ≤ Real.pi := by
        rw [div_le_iff₀ hP0]
        nlinarith
      rcases (by omega : n ≤ 0 ∨ 1 ≤ n) with hn0 | hn1
      · have : (n : ℝ) ≤ 0 := by exact_mod_cast hn0
        nlinarith
      · have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
        nlinarith
    · rw [hdiff]
      positivity
    · rw [hdiff, show 2 * Real.pi / 2 ^ (k + 1) =
        2 * Real.pi * 1 / 2 ^ (k + 1) by ring]
      gcongr
  choose a hapow hane hapos haup using key
  refine ⟨fun k => Complex.exp ((a k : ℂ) * Complex.I),
    hapow, hane, ?_⟩
  have hgeo : Tendsto (fun k : ℕ => 2 * Real.pi / 2 ^ (k + 1))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => ((1 : ℝ) / 2) ^ (k + 1)) atTop
        (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
        (by norm_num)).comp (tendsto_add_atTop_nat 1)
    have h2 := h1.const_mul (2 * Real.pi)
    rw [mul_zero] at h2
    refine h2.congr fun k => ?_
    rw [div_pow, one_pow]
    ring
  have htheta : Tendsto a atTop (𝓝 θ) := by
    have hdiff : Tendsto (fun k => a k - θ) atTop (𝓝 0) :=
      squeeze_zero (fun k => (hapos k).le) haup hgeo
    have h := hdiff.add_const θ
    rw [zero_add] at h
    exact h.congr fun k => by ring
  have hC : Tendsto (fun k => ((a k : ℝ) : ℂ) * Complex.I) atTop
      (𝓝 (((θ : ℝ) : ℂ) * Complex.I)) :=
    ((Complex.continuous_ofReal.tendsto θ).comp htheta).mul_const _
  have h := (Complex.continuous_exp.tendsto _).comp hC
  exact hz₀exp ▸ h

/-- **The natural-boundary theorem** (`thm:natural-boundary`): no
function holomorphic on a disc centered at a point of the unit circle
agrees with the Thue–Morse series on the overlap with the unit disc.
Every boundary point is singular: the circle is a natural boundary. -/
theorem thueMorse_natural_boundary (z₀ : ℂ) (hz₀ : ‖z₀‖ = 1)
    (R : ℝ) (hR : 0 < R) (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (ball z₀ R))
    (hagree : EqOn g thueMorseDiscSeries (ball z₀ R ∩ ball (0 : ℂ) 1)) :
    False := by
  have hgc : ContinuousOn g (ball z₀ R) := hg.continuousOn
  -- a hypothetical extension vanishes at every dyadic root in the disc
  have hroot0 : ∀ ζ ∈ ball z₀ R, ∀ k : ℕ,
      ζ ^ 2 ^ (k + 1) = 1 → g ζ = 0 := by
    intro ζ hζball k hζk
    have hζ1 : ‖ζ‖ = 1 := norm_eq_one_of_pow_eq_one hζk (by positivity)
    have hpath : Tendsto (fun ρ : ℝ => (ρ : ℂ) * ζ) (𝓝[<] (1 : ℝ))
        (𝓝 ζ) := by
      have h : Tendsto (fun ρ : ℝ => (ρ : ℂ) * ζ) (𝓝 (1 : ℝ))
          (𝓝 (((1 : ℝ) : ℂ) * ζ)) :=
        (Complex.continuous_ofReal.mul continuous_const).tendsto (1 : ℝ)
      have h2 := h.mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
      simpa using h2
    have hmem : ∀ᶠ ρ : ℝ in 𝓝[<] (1 : ℝ),
        ((ρ : ℂ) * ζ) ∈ ball z₀ R ∩ ball (0 : ℂ) 1 := by
      have h1 : ∀ᶠ ρ : ℝ in 𝓝[<] (1 : ℝ), ((ρ : ℂ) * ζ) ∈ ball z₀ R :=
        hpath.eventually_mem (isOpen_ball.mem_nhds hζball)
      have h2 : ∀ᶠ ρ : ℝ in 𝓝[<] (1 : ℝ),
          ((ρ : ℂ) * ζ) ∈ ball (0 : ℂ) 1 := by
        filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)]
          with ρ hρ
        rw [mem_ball_zero_iff, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hρ.1, hζ1, mul_one]
        exact hρ.2
      exact (h1.and h2).mono fun ρ h => ⟨h.1, h.2⟩
    have hgpath : Tendsto (fun ρ : ℝ => g ((ρ : ℂ) * ζ))
        (𝓝[<] (1 : ℝ)) (𝓝 (g ζ)) :=
      ((hgc.continuousAt (isOpen_ball.mem_nhds hζball)).tendsto).comp
        hpath
    have heq : (fun ρ : ℝ => g ((ρ : ℂ) * ζ)) =ᶠ[𝓝[<] (1 : ℝ)]
        fun ρ : ℝ => thueMorseDiscSeries ((ρ : ℂ) * ζ) := by
      filter_upwards [hmem] with ρ hρ using hagree hρ
    exact tendsto_nhds_unique (hgpath.congr' heq)
      (tendsto_thueMorseDiscSeries_radial_zero hζk)
  -- the roots accumulate at the center, so the extension vanishes
  obtain ⟨u, hupow, hune, hutend⟩ := exists_dyadic_root_seq z₀ hz₀
  have hballs : ∀ᶠ k in atTop, u k ∈ ball z₀ R :=
    hutend.eventually_mem (isOpen_ball.mem_nhds (mem_ball_self hR))
  have hg0seq : ∀ᶠ k in atTop, g (u k) = 0 :=
    hballs.mono fun k hk => hroot0 (u k) hk k (hupow k)
  have hT : Tendsto u atTop (𝓝[≠] z₀) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hutend
      (Filter.Eventually.of_forall fun k =>
        Set.mem_compl_singleton_iff.mpr (hune k))
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, g z = 0 :=
    hT.frequently hg0seq.frequently
  have hEq0 : EqOn g 0 (ball z₀ R) :=
    (hg.analyticOnNhd
      isOpen_ball).eqOn_zero_of_preconnected_of_frequently_eq_zero
      ((convex_ball z₀ R).isPreconnected) (mem_ball_self hR) hfreq
  -- transfer to the series on the overlap and finish at the origin
  have hδ0 : 0 < min R 1 / 2 := by
    have := lt_min hR one_pos
    linarith
  have hδR : min R 1 / 2 < R := by
    have := min_le_left R 1
    linarith
  have hδ1 : min R 1 / 2 < 1 := by
    have := min_le_right R 1
    linarith
  have hw₀R : ((1 - min R 1 / 2 : ℝ) : ℂ) * z₀ ∈ ball z₀ R := by
    rw [mem_ball, dist_eq_norm,
      show ((1 - min R 1 / 2 : ℝ) : ℂ) * z₀ - z₀ =
        ((-(min R 1 / 2) : ℝ) : ℂ) * z₀ by push_cast; ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, hz₀, mul_one,
      abs_neg, abs_of_pos hδ0]
    exact hδR
  have hw₀1 : ((1 - min R 1 / 2 : ℝ) : ℂ) * z₀ ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, hz₀, mul_one,
      abs_of_pos (by linarith : (0 : ℝ) < 1 - min R 1 / 2)]
    linarith
  have hnb : ∀ᶠ z in 𝓝 (((1 - min R 1 / 2 : ℝ) : ℂ) * z₀),
      thueMorseDiscSeries z = 0 := by
    filter_upwards [(isOpen_ball.inter isOpen_ball).mem_nhds
      ⟨hw₀R, hw₀1⟩] with z hz
    rw [← hagree hz]
    simpa using hEq0 hz.1
  have hfreqF : ∃ᶠ z in 𝓝[≠] (((1 - min R 1 / 2 : ℝ) : ℂ) * z₀),
      thueMorseDiscSeries z = 0 :=
    (hnb.filter_mono nhdsWithin_le_nhds).frequently
  have hF0 : EqOn thueMorseDiscSeries 0 (ball (0 : ℂ) 1) :=
    (thueMorseDiscSeries_differentiableOn.analyticOnNhd
      isOpen_ball).eqOn_zero_of_preconnected_of_frequently_eq_zero
      ((convex_ball (0 : ℂ) 1).isPreconnected) hw₀1 hfreqF
  have h1 : thueMorseDiscSeries 0 = 0 := by
    simpa using hF0 (mem_ball_self one_pos)
  rw [thueMorseDiscSeries_zero] at h1
  exact one_ne_zero h1

end Fabius
