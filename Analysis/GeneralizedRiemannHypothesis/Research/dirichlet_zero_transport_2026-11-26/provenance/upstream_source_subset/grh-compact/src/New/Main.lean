import Statements
import New.Data.DataExist
import New.Endgame.LongForms

/-! The inequality (⋆), an upper bound for weighted non-split primes. For admissible data with
scales x and x₁, the product formula and height bounds for twisted volumes show that the normalised
error of the weighted count of non-split primes ≡ 1 mod N₀ at x, minus that at x₁, plus a weight
times the error over all classes at x₁, is at most x^(−1/2+O(ε)), and a good choice of x₁ gives the
one-sided bound x^(8ε−1/2) for the error at x alone. Prime sums bounded by size against divisibility
are known (Chebyshev-order bounds, conditional CM heights, curves over F_q). Related work: Pritsker,
The Gelfond–Schnirelman method in prime number theory, 2005; Granville–Stark, ABC implies no Siegel
zeros, 2000; Bombieri, Counting points on curves over finite fields, Sém. Bourbaki 430, 1973; van
Frankenhuijsen, The Riemann hypothesis for function fields over a finite field, 2008.

No Dirichlet L-function vanishes in Re s > 1/2. For every Dirichlet character χ of any modulus,
L(s,χ) ≠ 0 when Re s > 1/2 (with s ≠ 1 if χ is principal), so by the functional equation the
non-trivial zeros of ζ and of all Dirichlet L-functions lie on Re s = 1/2, which is the Riemann
hypothesis and its generalisation and the final result of the argument. Related work: Bombieri,
Counting points on curves over finite fields, Sém. Bourbaki 430, 1973; Weil, Sur les courbes
algébriques, 1948.

This file: The inequality (⋆) from Theorems A to C; the one-sided bound; GRH. Zeros lie on the
critical line, given non-vanishing right of one half. -/

open DirichletCharacter Real Finset Filter Data Parameters ZMod Module

/- **The spine of the proof.**

Columns are algebraic forms on a definite U(k), rows are cusp forms on an indefinite U(r) (the
target), lifts are theta lifts; tops and thick places are sets of infinite places of `E`
(`Data.tops`, `Data.thick`). One covolume is bounded from both sides. `rowDim = finrank ℂ D.rows` is
the dimension of the target
(written `D` in the docstrings of `New.Endgame.LongForms`), `h_main = m k 𝖴` (`mainHeight`,
`dirCost`) is the main amount, `remainder` is a prime sum less its expected value,
`budget = f a log³ b`. For a family of target forms let `exp V` bound the squared covolume of the
lifts at all conjugates (`covolumeSq`) and let `δ` bound the logarithm of the index (`IndexLe`). Up
to errors, for the family of `exists_family_covolumeSq_le`,

    h_main  ≤  (V + 2 δ) / rowDim  ≤  h_main - m remainder.

Inputs (name, module, content).

Upper bound:
* `short_forms`, `enough_forms` (`New.Endgame.ShortAndEnough`): short forms (Theorem A); enough
  forms (Theorem B)
* `heightPerRow_le` (`New.Endgame.ShortAndEnough`): the level `N` pays the excess of the `m` lifts
* `exists_family_covolumeSq_le` (`New.Endgame.LongForms`): A and B together

Lower bound:
* `exists_isFitFamily` (`New.Selmer.FitTwistsExist`): twists `θ ι`, one for each `ι : ℂ ≃ ℚ̄_l`,
  with the congruence bounds `IsFitFamily`
* `volume_iota_eq_prod_liftVolume` (`New.Rows.RowVolume`): volume of the chain = constant × lift
  volumes
* `heightLe_liftVolume_ratio` (`New.Rows.LiftVolumeHeight`): each lift gains `rowDim k 𝖴` on the
  trivial twist
* `heightLe_volume_ratio_sq`, `heightLe_volume_rows` (`New.Endgame.LongForms`): heights of
  `𝔷 1² / 𝔷 θ²` and of `𝔷 θ / 𝔷 1`
* `HeightLe.nonneg` (`New.Heights.Heights`): product formula: the height of `1` is `≥ 0`
* `integral_forms_long` (`New.Endgame.LongForms`): the entries above together (Theorem C); the
  height of `𝔷 θ / 𝔷 1` uses `crude_rows` (`New.Exchange.CrudeRows`: cruder forms, which complete
  the family to a basis) and `one_determinant` (`New.Heights.OneDeterminant`)

Prime sums:
* `remainder_eq` (`New.Endgame.ShortAndEnough`): `remainder` in terms of the remainders
  `primeError`
* `abs_mainHeight_add_remainder_le` (`New.Endgame.ShortAndEnough`): crude bounds for `h_main` and
  `remainder`

Analysis:
* `exists_data` (`New.Data.DataExist`): data at every large `x`
* `IsPolar.exists_window_sub_mul_le` (`New.Endgame.OneSidedCriterion`): `R_{N₀} - c R₁ ≤ e^(-t)`
  at some `log x₁ ∈ [t, t²]`
* `entireL_ne_zero_of_primeError_le` (`New.Endgame.OneSidedCriterion`): Landau's lemma

Deduction (this file): `star_inequality`, then `eventually_primeError_le_rpow`, then `grh`.

What cancels, and where:
* `𝖴` (`dirCost`), as `h_main`: upper bound against lower bound; `star_inequality`, last step
* `chowlaSelbergConst` in the period `bigOmega`, Stirling: row of length `a` against `mainAsk`;
  `heightPerRow_le`, `excess`
* `m (w̄ + G)`, the main term of `logLevelTarget`: level against the `m` excesses;
  `heightPerRow_le`, third step
* `log x`, `log x₁`, `-1 - chowlaSelbergConst`: prime sums against `mainAsk`; `remainder_eq`

Here `w̄` is the mean of `log nominalWeight` over all `f` places, `G = log (g rootDisc / 2π)`, and
`logLevelTarget = m (w̄ + G) - G - (15 / 2) log b`.

Scales (`New.Data.AdmissibleData`, `New.Data.Magnitudes`; `N₀`, `d` fixed, `x → ∞`;
`logX logX₁ logB` = `log x, log x₁, log b`):
* log b ≪ x ≪ x₁ ≪ b: (log b)¹⁰⁰ ≤ x, x^(10⁶) ≤ x₁, x₁^(10⁶) ≤ b, (log x₁)⁶ ≤ log b,
  exp (10¹² c) ≤ log b (`P.c` bounds what depends on `N₀`, `d` only); `exists_data` has
  log b = x^ε, log x₁ = x^(ε/6), and `eventually_primeError_le_rpow` lowers log x₁ into [t, t²],
  t = 10⁶ log x
* `m`, number of lifts: in [√x, 2√x]; the saving x^(-1/2) is 1/m
* `r`, `k`, ranks of target and source: r in [x⁵, 3x⁵], r + 1 = k + m
* `t`, the ranks grow in steps: t = 5 r, n_j = k + j (t + 1)
* `f`, infinite places of `E`: #tops φ(N₀); #tops = `towerDeg s`, in [x¹¹, x¹¹ (log b)^(1/5)];
  #thick ≥ #tops / log b in `exists_data`
* `a`, long order, at the tops: in [x b, x b + N₁]
* `nominalWeight`, nominal weight: a / x at the thick places, a / x₁ elsewhere
* `g`, that is `gProd`, product of two primes: in [b²⁰, b²²]
* `N`, level, a prime: log N in [`logLevelTarget`, `logLevelTarget` + √(log b)], so in
  [m log b, 30 m log b]

`D.le_of_hasLogBound : F ≤ G` compares two such monomials by their exponents on these scales
(class `HasLogBound`).

Errors per dimension, with `L = f a log⁴ b`:
* length, Theorem A (a): L
* missing dimensions, Theorem B, `abs_mainHeight_add_remainder_le`: 4 b⁻² · b² x⁹⁹
* index, Theorems A (b), B: 2 · 5 log (1 + b²) · `budget`
* covolume, Theorem C: 3 L

Their sum is at most `f a log⁵ b`. Exponents such as 99 and 999 are slack: every power of `x` that
occurs is below `b`. -/

/-- The main inequality for admissible data D: m·rem ≤ (log b)²·𝓑, where rem is the remainder
`Data.remainder` and 𝓑 = f·a·(log b)³ is `Data.budget`.

The inequality (⋆): upper bound for weighted non-split primes. -/
lemma star_inequality {P} {D : Data P} : D.m * D.remainder ≤ D.logB ^ 2 * D.budget :=
  D.exists_family_covolumeSq_le.elim fun n ⟨y, i, big, ⟨δ, index, I⟩, short⟩ ↦ by
  have d0 : (0 : ℝ) < D.rowDim := mod_cast D.finrank_rows_ne_zero.pos
  -- `d` is the dimension, `L = f a log⁴ b` the unit of error, `exp h` the bound per form
  set d := (D.rowDim : ℝ)
  set L := D.logB * D.budget
  set h := D.mainHeight - D.m * D.remainder + L with def_h
  have crude : -h ≤ D.b ^ 2 * D.x ^ 99 := by
    grw [def_h, ← abs_mainHeight_add_remainder_le, ← neg_le_abs, ← le_abs_self,
      ← (HasLogBound.pos D : 0 < L)]
    simp
  have both : d * (D.mainHeight - 3 * L) ≤ d * (D.mainHeight - D.m * D.remainder + L + 4 *
    D.x ^ 99 + 10 * log (1 + D.b ^ 2) * D.budget) := calc
    _ ≤ d * h + (d - n) * -h + 2 * δ := (integral_forms_long i big I short).trans_eq (by ring)
                    -- the missing dimensions are a share `4 / b²`, and the index is small
    _ ≤ d * h + 4 / D.b ^ 2 * d * (D.b ^ 2 * D.x ^ 99) + 2 *
      (5 * d * log (1 + D.b ^ 2) * D.budget) := by
      grw [crude, index, show d - n ≤ 4 / D.b ^ 2 * d by linarith]
      exact sub_nonneg.2 (mod_cast Fintype.card_fin n ▸ i.fintype_card_le_finrank : (n : ℝ) ≤
        D.rowDim)
    _ = _ := by rw [def_h]; field [exp_ne_zero]
  -- divide by `d`; `h_main` cancels
  calc D.m * D.remainder ≤ 4 * L + 4 * D.x ^ 99 + 10 * log (1 + D.b ^ 2) * D.budget := by
        linarith [le_of_mul_le_mul_left both d0]
    _ ≤ _ := D.le_of_hasLogBound

/-- One-sided bound: for parameters N₀, d as in `Parameters` and 0 < ε < 1/100, the remainder
R_{N₀}(x) (`primeError`) is at most x^{8ε − 1/2} for all large x. -/
lemma eventually_primeError_le_rpow (P : Parameters) {ε : ℝ} (h : 0 < ε / 6 ∧ ε < 1 / 100) :
    ∀ᶠ x in atTop, primeError P.d P.N₀ x ≤ x ^ (8 * ε + 2⁻¹ - 1) := by
  filter_upwards [h.elim (exists_data P), tendsto_log_atTop.const_mul_atTop (r := 1e6) (by bound)
    ((isPolar_primeError PrimeSevenModEight.mod_eight (P.coprime_N₁_d
    0).coprime_mul_right).exists_window_sub_mul_le (isPolar_primeError PrimeSevenModEight.mod_eight
    P.d.coprime_one_left))] with x ⟨D, _, _, l, e, H'⟩ W
  subst x; simp only [log_exp, Set.mem_preimage, ← exp_mul] at *
  obtain := D.hasLogLower_of_le H', D.scale
  -- move `log x₁` to a point `u` of the window where `R_{N₀} - (#tops / #thick) R₁ ≤ x ^ (-10⁶)`
  obtain ⟨u, ⟨a, b⟩, w⟩ := W (towerDeg D.s / #D.thick) ⟨by bound, D.le_of_hasLogBound⟩
  let D' := {D with logX₁ := u, scale := by grw [b, l] <;> grind}
  have := D'.hasLogLower_of_le H'
  calc primeError P.d P.N₀ D.x = D'.m * D'.remainder / D'.m / D'.a / #D.thick + (primeError P.d P.N₀
      D'.x₁ - towerDeg D.s / #D.thick * primeError P.d 1 D'.x₁) := by simp [remainder_eq, tops,
      card_placeClass_eq, field, HasLogBound.pos D', ne_of_gt]
    _ ≤ D'.logB ^ 2 * D'.budget / D'.m / D'.a / #D.thick + exp
      (-(1e6 * D.logX)) := by grw [star_inequality, w]
    -- the first term is `f log⁵ b / (m #thick) ≤ φ(N₀) log⁶ b / √x`, and `log b = x ^ ε`
    _ ≤ _ := D'.le_of_hasLogBound (by grind)

/-- The generalised Riemann hypothesis for Dirichlet L-functions, in half-plane form: for every
N ≥ 1 and every Dirichlet character χ mod N, L(s, χ) ≠ 0 when Re s > 1/2, the pole s = 1 of the
principal character excepted.

No Dirichlet L-function vanishes in Re s > 1/2. -/
lemma New.grh : DirichletLNonvanishingRightOfHalf := fun q _ χ ρ hρ pole zero ↦ by
  -- `51` gives `ε < 1 / 100` and `8 ε + 1 / 2 < re ρ`
  set ε := (ρ.re ⊓ 1 - 2⁻¹) / 51
  -- pass to the modulus `N₀ = 18480 q` and the class `N₀ / 2 - 1`, whose square is `1`
  have induced : entireL (χ.changeLevel (dvd_mul_left q 18480)) ρ = 0 := by
    rw [entireL]
    grind [LFunction_changeLevel, changeLevel_eq_one_iff]
  refine entireL_ne_zero_of_primeError_le (β := 8 * ε + 2⁻¹) (by grind)
    (.of_mul_eq_one (9240 * q - 1) (by grind [natCast_self (18480 * q)]) :
    IsUnit (9240 * q - 1 : ZMod (_ * q))) (fun d h ↦ ?_) ρ (by grind) _ induced
  -- each prime `d` of the class gives parameters, and `eventually_primeError_le_rpow` is the bound
  -- that is asked for
  let P := mk _ d ⟨q, rfl⟩ d.2 (by
    simp [← natCast_eq_zero_iff, h]; norm_cast; simp [↓natCast_eq_zero_iff, ← mul_assoc,
      mul_dvd_mul_iff_right])
  exact ⟨⟨P.instHeegD.2, (P.coprime_N₁_d 0).coprime_mul_right⟩,
    eventually_primeError_le_rpow P (by grind)⟩

/-- Assume h: no Dirichlet L-function vanishes in Re s > 1/2 (the pole at s = 1 excepted). Then GRH
holds: for χ of any modulus, every zero of L(s, χ) with 0 < Re s < 1 has Re s = 1/2. -/
lemma New.zeros_on_line (h : DirichletLNonvanishingRightOfHalf) : DirichletLZerosOnLine :=
  fun N _ ↦ by grind [h N, Complex.one_re, Complex.sub_re, → LFunction_one_sub_eq_zero,
  Complex.ext_iff, DirichletCharacter.gammaFactor, Complex.Gammaℝ_ne_zero_of_re_pos]

/-- Assume h: no Dirichlet L-function vanishes in Re s > 1/2 (the pole at s = 1 excepted). Then
the Riemann hypothesis holds: every zero s ≠ 1 of ζ other than −2, −4, … has Re s = 1/2. -/
lemma New.zeta_zeros_on_line (h : DirichletLNonvanishingRightOfHalf) :
    RiemannZetaZerosOnLine := fun s ↦ by
  obtain _ := h 1 1 s, h 1 1 (1 - s), @Nat.or_exists_add_one, riemannZeta_zero
  simp_all
  grind [riemannZeta_def_of_ne_zero, completedRiemannZeta_one_sub, Complex.Gammaℝ_eq_zero_iff]
