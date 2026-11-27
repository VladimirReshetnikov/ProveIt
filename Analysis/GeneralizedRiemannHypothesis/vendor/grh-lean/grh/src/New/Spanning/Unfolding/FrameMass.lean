import Lib.SiegelWeil.OneVector.SiegelClassSum
import New.Spanning.Bessel.FillingData

/-!
# Masses of spheres and of frames

For the data `D` and an infinite place `v`, the file defines the mass `sph_l` of the unit sphere of
`ℂ ^ l` and the product `fr_v = N ^ k sph_{k+1} ⋯ sph_r`. By the approximate formula for the ratio
of masses in consecutive ranks, the product of the `fr_v` over the infinite places is at most
`N ^ (k f) mass_k / mass_r` up to a factor close to one, where `f` is the number of infinite places
and `mass_l` is the mass `New.mass` in rank `l`.

## Main definitions and results

* `New.Data.unitSphereMass`, `New.Data.frameMass`: the numbers `sph_l` and `fr_v`.
* `New.Data.prod_frameMass_mul_le`: the upper bound for the product of the `fr_v`.
* `New.Data.prod_frameMass_mul_openCellConst_eq`: the product of the `fr_v` in terms of the
  constants `New.Filling.siegelConst` and `New.Shape.openCellConst`.

Notions from other files:
* `New.Data`: the data: a CM field `E` with `f` infinite places (the type `D.Φ`) and root
  discriminant `rd = D.rootDisc`, a generator `P.deltaE D.towerExp` of its different, a prime level
  `N`, a weight `b`, the length `x` of the prime sum, and ranks `r = k + 2 ϱ + 1`.
* `New.Data.shape`: the shape of the hermitian space `Y₀` of rank `r`, which is the sum of `ϱ`
  hyperbolic planes, a space `X₀` of rank `k` and a line.
* `New.mass E l`: the mass of the genus of the standard hermitian lattice `O_E ^ l`.
* `New.Filling.siegelConst`: `c_S = (π ^ k / ((k - 1)! N ^ k)) ^ f |disc E| ^ (1/4) vol(Ô) ^ k`.
* `New.Shape.openCellConst`: `c_G = vol U(k) (2 π ^ k / (k - 1)!) / vol U(r)`.
* `New.volÔ E`: the volume `vol(Ô) = (2 / rd) ^ f` of the integral finite adeles.
-/

noncomputable section

namespace New.Data

open Finset Real Filling Shape NumberField

variable {P : Parameters} (D : Data P)

/-- For the prime level `N` and the rank `k ≥ 1` of the data, the logarithm of `N ^ k / (N ^ k - 1)`
is at most `2 / N`. -/
lemma log_pow_div_pow_sub_one_le : log (D.N ^ D.k / (D.N ^ D.k - 1)) ≤ (2 / D.N : ℝ) := by
  have two_le_N : 2 ≤ D.N := D.N_prime.two_le
  have N_le_pow : D.N ≤ D.N ^ D.k := Nat.le_self_pow D.k_pos.ne' D.N
  have pow_sub_one_pos : (0 : ℝ) < D.N ^ D.k - 1 :=
    sub_pos.mpr (one_lt_pow₀ (mod_cast D.N_prime.one_lt) D.k_pos.ne')
  calc _ ≤ (D.N ^ D.k : ℝ) / (D.N ^ D.k - 1) - 1 := log_le_sub_one_of_pos (by positivity)
    _ = 1 / (D.N ^ D.k - 1) := by field
    _ ≤ 2 / D.N := by
      field_simp
      norm_cast
      lia

/-- The `r - k` errors `2 / 2 ^ ϱ` of the mass formula in the ranks between `k` and `r` add up to at
most `log (1 + b⁻⁹) - 2 f · 2/N`. -/
lemma sum_two_div_two_pow_le_log_sub :
    ∑ _i ∈ Ico D.k D.r, (2 / 2 ^ D.ϱ : ℝ) ≤ log (1 + D.b⁻¹ ^ 9) - 2 * (D.f * (2 / D.N)) := by
  have h_error_budget : (D.r - D.k) * (2 / 2 ^ D.ϱ) + 2 * (D.f * (2 / D.N)) ≤
      2 * D.b⁻¹ ^ 9 / (D.b⁻¹ ^ 9 + 2) := D.le_of_hasLogBound
  rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub D.k_le_r]
  linarith [le_log_one_add_of_nonneg (x := D.b⁻¹ ^ 9) (by positivity)]

/-- The main term of `log (mass_{i+1} / mass_i)`, with `mass_l` the mass of the genus of `O_E ^ l`,
is `f ((i + 1/2) log rd + log i! - (i + 1) log 2π)`, with `rd` the root discriminant and `f` the
number of infinite places of `E`. The sum over `k ≤ i < r` of the differences between logarithm and
main term has absolute value at most `log (1 + b⁻⁹) - 2 f · 2/N`. -/
lemma abs_sum_log_mass_ratio_sub_le :
    |∑ i ∈ Ico D.k D.r, (log (mass D.E (i + 1)) - log (mass D.E i) -
      D.f * ((i + 1 / 2) * log D.rootDisc + log i.factorial - (i + 1) * log (2 * π)))| ≤
      log (1 + D.b⁻¹ ^ 9) - 2 * (D.f * (2 / D.N)) := by
  have h_places : 8 * D.f ≤ 2 ^ D.ϱ := D.nat_le_of_hasLogBound
  have h_rank : 4 * D.ϱ + 12 ≤ D.k := D.nat_le_of_hasLogBound
  have h_bound (i : ℕ) (hi : i ∈ Ico D.k D.r) :
      |log (mass D.E (i + 1)) - log (mass D.E i) -
        D.f * ((i + 1 / 2) * log D.rootDisc + log i.factorial - (i + 1) * log (2 * π))| ≤
          2 / 2 ^ D.ϱ :=
    abs_log_mass_ratio_sub_le D.E i D.ϱ h_places (h_rank.trans (mem_Ico.mp hi).1)
  calc |∑ i ∈ Ico D.k D.r, (log (mass D.E (i + 1)) - log (mass D.E i) -
        D.f * ((i + 1 / 2) * log D.rootDisc + log i.factorial - (i + 1) * log (2 * π)))|
      ≤ ∑ i ∈ Ico D.k D.r, |log (mass D.E (i + 1)) - log (mass D.E i) -
        D.f * ((i + 1 / 2) * log D.rootDisc + log i.factorial - (i + 1) * log (2 * π))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Ico D.k D.r, (2 / 2 ^ D.ϱ : ℝ) := sum_le_sum h_bound
    _ ≤ log (1 + D.b⁻¹ ^ 9) - 2 * (D.f * (2 / D.N)) := D.sum_two_div_two_pow_le_log_sub

/-- At every infinite place `v`, the generator `ϖ` of the different of `E` has `2 ≤ |ϖ|_v ≤ b`,
where `b` is the weight of the data. -/
lemma apply_deltaE_mem_Icc (v : D.Φ) : v (P.deltaE D.towerExp).val ∈ Set.Icc 2 D.b :=
  ⟨D.le_of_hasLogBound, D.le_of_hasLogBound⟩

/-- At the infinite place `v`, let `ϖ = P.deltaE D.towerExp`. Write `|ϖ|_v = v ϖ` and let `b = D.b`
be the scale of the data. Then the numbers `2 / |ϖ|_v` and `|ϖ|_v ^ (-1 / 2)` lie between `b⁻¹` and
`1`. -/
theorem two_div_and_inv_sqrt_deltaE_mem_Icc (v : D.Φ) :
    2 / v (P.deltaE D.towerExp).val ∈ Set.Icc D.b⁻¹ 1 ∧
      (√(v (P.deltaE D.towerExp).val))⁻¹ ∈ Set.Icc D.b⁻¹ 1 := by
  obtain ⟨h_two, h_le⟩ : 2 ≤ v (P.deltaE D.towerExp).val ∧ v (P.deltaE D.towerExp).val ≤ D.b :=
    D.apply_deltaE_mem_Icc v
  set w : ℝ := v (P.deltaE D.towerExp).val
  have hw_pos : 0 < w := two_pos.trans_le h_two
  have h_one_le_sqrt : 1 ≤ √w := one_le_sqrt.2 (one_le_two.trans h_two)
  have h_sqrt_le : √w ≤ D.b := (sqrt_le_left (hw_pos.le.trans h_le)).2 (by nlinarith)
  refine ⟨⟨?_, (div_le_one hw_pos).2 h_two⟩, inv_anti₀ (sqrt_pos.2 hw_pos) h_sqrt_le,
    inv_le_one_of_one_le₀ h_one_le_sqrt⟩
  calc D.b⁻¹ ≤ w⁻¹ := inv_anti₀ hw_pos h_le
    _ = 1 / w := inv_eq_one_div w
    _ ≤ 2 / w := div_le_div_of_nonneg_right one_le_two hw_pos.le

/-- The number `sph_l = (2π) ^ l / (|ϖ|_v ^ (l - 1 / 2) (l - 1)!)` at the infinite place `v`, where
`ϖ` generates the different of `E`. For `l ≥ 1` it is the mass of the unit sphere of `ℂ ^ l` for
the fibre measure `dy / d⟨y, y⟩`, when `ℂ` carries `2 / |ϖ|_v` and `ℝ` carries `|ϖ|_v ^ (-1 / 2)`
times Lebesgue measure. -/
def unitSphereMass (l : ℕ) (v : D.Φ) : ℝ :=
  (2 * π) ^ l / (v (P.deltaE D.towerExp).val ^ (l - 1 / 2 : ℝ) * (l - 1).factorial)

/-- The number `fr_v = N ^ k sph_{k+1} ⋯ sph_r` at the infinite place `v`, where `N` is the level,
`k ≤ r` are the ranks of the data and `sph_l` is `New.Data.unitSphereMass`. -/
def frameMass (v : D.Φ) : ℝ :=
  D.N ^ D.k * ∏ i ∈ Ico D.k D.r, D.unitSphereMass (i + 1) v

lemma unitSphereMass_pos (l : ℕ) (v : D.Φ) : 0 < D.unitSphereMass l v := by
  have hϖ : 0 < v (P.deltaE D.towerExp).val := InfinitePlace.pos_iff.mpr D.filling.deltaE_ne_zero
  unfold unitSphereMass
  positivity

lemma frameMass_pos (v : D.Φ) : 0 < D.frameMass v :=
  mul_pos (pow_pos (mod_cast D.N_prime.pos) _) (prod_pos fun _ _ ↦ D.unitSphereMass_pos _ v)

/-- The mass `sph_l` of the unit sphere of `ℂ ^ l` is at most one for `l ≥ 1`, at every infinite
place `v`. This is a corollary of the size of the different. -/
lemma one_le_inv_unitSphereMass {l : ℕ} (hl_pos : 1 ≤ l) (v : D.Φ) :
    1 ≤ (D.unitSphereMass l v)⁻¹ := by
  have hw_one : 1 ≤ v (P.deltaE D.towerExp).val := D.le_of_hasLogBound
  have hw_lower : 2 * π ≤ √(v (P.deltaE D.towerExp).val) := D.le_of_hasLogBound
  rw [unitSphereMass, inv_div, one_le_div (by positivity)]
  set w : ℝ := v (P.deltaE D.towerExp).val
  calc (2 * π) ^ l ≤ √w ^ l := by gcongr
    _ = w ^ (1 / 2 * l : ℝ) := by rw [sqrt_eq_rpow, rpow_mul_natCast (by linarith)]
    _ ≤ w ^ (l - 1 / 2 : ℝ) :=
      rpow_le_rpow_of_exponent_le hw_one (by linarith [Nat.one_le_cast (α := ℝ).mpr hl_pos])
    _ ≤ w ^ (l - 1 / 2 : ℝ) * (l - 1).factorial :=
      le_mul_of_one_le_right (by positivity) (mod_cast (l - 1).factorial_pos)

/-- For `l ≤ r` and every infinite place `v`, the number `sph_l` satisfies `sph_l⁻¹ ≤ x ^ (18 l)`.
For `l ≥ 1` it is the mass of the unit sphere of `ℂ ^ l`; for `l = 0` the formula that defines it
gives `|ϖ|_v ^ (1 / 2)`, with `ϖ` the generator of the different. -/
lemma inv_unitSphereMass_le_pow {l : ℕ} (hl_le : l ≤ D.r) (v : D.Φ) :
    (D.unitSphereMass l v)⁻¹ ≤ D.x ^ (18 * l) := by
  -- With `w = |ϖ|_v` we have `w ^ (l - 1 / 2) ≤ w ^ l`, `(l - 1)! ≤ r ^ l` and `w r ≤ x ^ 18`.
  have hw_one : 1 ≤ v (P.deltaE D.towerExp).val := D.le_of_hasLogBound
  have hw_upper : v (P.deltaE D.towerExp).val * D.r ≤ D.x ^ 18 := D.le_of_hasLogBound
  rw [unitSphereMass, inv_div]
  set w : ℝ := v (P.deltaE D.towerExp).val
  have h_rpow : w ^ (l - 1 / 2 : ℝ) ≤ w ^ l :=
    (rpow_le_rpow_of_exponent_le hw_one (by linarith)).trans_eq (rpow_natCast w l)
  have h_factorial : ((l - 1).factorial : ℝ) ≤ D.r ^ l := mod_cast
    (Nat.factorial_le (l.sub_le 1)).trans (l.factorial_le_pow.trans (Nat.pow_le_pow_left hl_le l))
  calc w ^ (l - 1 / 2 : ℝ) * (l - 1).factorial / (2 * π) ^ l
      ≤ w ^ (l - 1 / 2 : ℝ) * (l - 1).factorial :=
        div_le_self (by positivity) (one_le_pow₀ (by linarith [two_le_pi]))
    _ ≤ w ^ l * D.r ^ l := by gcongr
    _ = (w * D.r) ^ l := (mul_pow w D.r l).symm
    _ ≤ (D.x ^ 18) ^ l := by gcongr
    _ = D.x ^ (18 * l) := (pow_mul D.x 18 l).symm

/-- The rank `r` of the data equals `k + (2 ϱ + 1)`, where `k` is the smaller rank of the data and
`ϱ` the number of hyperbolic planes. -/
lemma r_eq_k_add_two_mul_varrho_add_one : D.r = D.k + (2 * D.ϱ + 1) := by
  linarith [D.r_add_one, D.m_eq_two_mul_varrho_add_two]

/-- For the ranks `k ≤ r` of the data there are `2 ϱ + 1` integers `i` with `k ≤ i < r`, where `ϱ`
is the number of hyperbolic planes. -/
lemma cast_card_Ico_k_r : ((Ico D.k D.r).card : ℝ) = 2 * D.ϱ + 1 := by
  simp [D.r_eq_k_add_two_mul_varrho_add_one]

/-- The number `fr_v = N ^ k sph_{k+1} ⋯ sph_r` is at least `b ^ (-(ϱ + 1) r)` at every infinite
place `v`. -/
lemma inv_pow_le_frameMass (v : D.Φ) : (D.b ^ ((D.ϱ + 1) * D.r))⁻¹ ≤ D.frameMass v := by
  -- Each of the `r - k = 2 ϱ + 1` sphere masses is at least `x ^ (-18 r)`, and `x ^ 36 ≤ b`.
  have hx_one : 1 ≤ D.x := D.le_of_hasLogBound
  have h_scale : D.x ^ 36 ≤ D.b := D.le_of_hasLogBound
  have h_card : (Ico D.k D.r).card = 2 * D.ϱ + 1 := mod_cast D.cast_card_Ico_k_r
  have h_factor (i : ℕ) (hi : i ∈ Ico D.k D.r) :
      (D.x ^ (18 * D.r))⁻¹ ≤ D.unitSphereMass (i + 1) v := by
    have hi_lt : i < D.r := (mem_Ico.mp hi).2
    refine inv_le_of_inv_le₀ (D.unitSphereMass_pos (i + 1) v) ?_
    calc (D.unitSphereMass (i + 1) v)⁻¹ ≤ D.x ^ (18 * (i + 1)) :=
          D.inv_unitSphereMass_le_pow hi_lt v
      _ ≤ D.x ^ (18 * D.r) := pow_le_pow_right₀ hx_one (Nat.mul_le_mul_left 18 hi_lt)
  have h_exponent : 18 * D.r * (2 * D.ϱ + 1) ≤ 36 * ((D.ϱ + 1) * D.r) := by nlinarith
  calc (D.b ^ ((D.ϱ + 1) * D.r))⁻¹ ≤ ((D.x ^ 36) ^ ((D.ϱ + 1) * D.r))⁻¹ := by gcongr
    _ ≤ ((D.x ^ (18 * D.r)) ^ (2 * D.ϱ + 1))⁻¹ := by
      rw [← pow_mul, ← pow_mul]
      gcongr
    _ = ∏ _i ∈ Ico D.k D.r, (D.x ^ (18 * D.r))⁻¹ := by rw [prod_const, h_card, inv_pow]
    _ ≤ ∏ i ∈ Ico D.k D.r, D.unitSphereMass (i + 1) v :=
      prod_le_prod₀ (fun _ _ ↦ by positivity) h_factor
    _ ≤ D.frameMass v := le_mul_of_one_le_left
      (prod_nonneg fun _ _ ↦ (D.unitSphereMass_pos _ v).le) (mod_cast pow_pos D.N_prime.pos _)

/-- The logarithm of the product of the sphere masses `sph_{i+1}` over the `f` infinite places is
`-f ((i + 1/2) log rd + log i! - (i + 1) log 2π)`, with `rd` the root discriminant of `E`. -/
lemma log_prod_unitSphereMass (i : ℕ) :
    log (∏ v : D.Φ, D.unitSphereMass (i + 1) v) =
      -(D.f * ((i + 1 / 2) * log D.rootDisc + log i.factorial - (i + 1) * log (2 * π))) := by
  have h_different : ∏ v : D.Φ, v (P.deltaE D.towerExp).val ^ ((i + 1 : ℕ) - 1 / 2 : ℝ) =
      (D.rootDisc ^ D.f) ^ ((i + 1 : ℕ) - 1 / 2 : ℝ) := by
    rw [Real.finsetProd_rpow _ _ fun v _ ↦ apply_nonneg v _, P.prod_deltaE_eq_rootDiscr_pow]
  have rd_pos : 0 < D.rootDisc := rootDiscr_pos D.E
  have h_prod : ∏ v : D.Φ, D.unitSphereMass (i + 1) v = ((2 * π) ^ (i + 1)) ^ D.f /
      ((D.rootDisc ^ D.f) ^ ((i + 1 : ℕ) - 1 / 2 : ℝ) * i.factorial ^ D.f) := by
    simp only [unitSphereMass, prod_div_distrib, prod_mul_distrib, h_different, prod_const,
      card_univ, Nat.add_sub_cancel]
  simp (disch := positivity) only [h_prod, log_div, log_mul, log_rpow, log_pow]
  push_cast
  ring

/-- The product of the sphere masses `sph_{i+1}` over the infinite places is `mass_i / mass_{i+1}`
up to a factor close to one: the logarithms differ by at most `2 / 2 ^ ϱ` for `i ≥ k`. -/
lemma abs_log_prod_unitSphereMass_sub_le {i : ℕ} (hi : D.k ≤ i) :
    |log (∏ v : D.Φ, D.unitSphereMass (i + 1) v) - (log (mass D.E i) - log (mass D.E (i + 1)))| ≤
      2 / 2 ^ D.ϱ := by
  have h_places : 8 * D.f ≤ 2 ^ D.ϱ := D.nat_le_of_hasLogBound
  have h_rank : 4 * D.ϱ + 12 ≤ D.k := D.nat_le_of_hasLogBound
  rw [log_prod_unitSphereMass, ← neg_sub (log (mass D.E (i + 1))), neg_sub_neg]
  exact abs_log_mass_ratio_sub_le D.E i D.ϱ h_places (h_rank.trans hi)

lemma prod_unitSphereMass_pos (l : ℕ) : 0 < ∏ v : D.Φ, D.unitSphereMass l v :=
  prod_pos fun v _ ↦ D.unitSphereMass_pos l v

/-- The product of the sphere masses `sph_{k+1}, …, sph_r` over all infinite places is positive. -/
lemma prod_prod_unitSphereMass_pos :
    0 < ∏ i ∈ Ico D.k D.r, ∏ v : D.Φ, D.unitSphereMass (i + 1) v :=
  prod_pos fun i _ ↦ D.prod_unitSphereMass_pos (i + 1)

/-- The product of `fr_v = D.frameMass v = N ^ k sph_{k+1} ⋯ sph_r` over the `f = D.f` infinite
places `v` in `D.Φ` equals `(N ^ k) ^ f` times the product, over `k ≤ i < r`, of the products of
`sph_{i+1}` over the infinite places. -/
lemma prod_frameMass_eq_mul_prod :
    ∏ v : D.Φ, D.frameMass v =
      (D.N ^ D.k) ^ D.f * ∏ i ∈ Ico D.k D.r, ∏ v : D.Φ, D.unitSphereMass (i + 1) v := by
  simp only [frameMass, prod_mul_distrib, prod_const, card_univ]
  rw [prod_comm]

/-- The product of the `fr_v = N ^ k sph_{k+1} ⋯ sph_r` over the `f` infinite places is at most
`(1 + b⁻⁹) (1 - N ^ (-k)) ^ (2 f) N ^ (k f) mass_k / mass_r`. The statement has `mass_r` and the
factor `(1 - N ^ (-k)) ^ (2 f)` moved to the left side. -/
lemma prod_frameMass_mul_le :
    (∏ v : D.Φ, D.frameMass v) * mass D.E D.r * (D.N ^ D.k / (D.N ^ D.k - 1)) ^ (2 * D.f) ≤
      (1 + D.b⁻¹ ^ 9) * ((D.N ^ D.k) ^ D.f * mass D.E D.k) := by
  -- Take logarithms: the product of the `sph_{i+1}` is `mass_i / mass_{i+1}` up to a small error,
  -- and these ratios telescope.
  let sphereProd : ℝ := ∏ i ∈ Ico D.k D.r, ∏ v : D.Φ, D.unitSphereMass (i + 1) v
  have sphereProd_pos : 0 < sphereProd := D.prod_prod_unitSphereMass_pos
  have mass_k_pos : 0 < mass D.E D.k := mass_pos D.E D.k
  have mass_r_pos : 0 < mass D.E D.r := mass_pos D.E D.r
  have ratio_pos : (0 : ℝ) < D.N ^ D.k / (D.N ^ D.k - 1) := div_pos
    (mod_cast pow_pos D.N_prime.pos _)
    (sub_pos.mpr (one_lt_pow₀ (mod_cast D.N_prime.one_lt) D.k_pos.ne'))
  have log_sphereProd_add_le : log (mass D.E D.r) - log (mass D.E D.k) + log sphereProd ≤
      log (1 + D.b⁻¹ ^ 9) - 2 * (D.f * (2 / D.N)) := by
    rw [log_prod fun i _ ↦ (D.prod_unitSphereMass_pos (i + 1)).ne',
      ← sum_Ico_sub (fun i : ℕ ↦ log (mass D.E i)) D.k_le_r, ← sum_add_distrib]
    refine (sum_le_sum fun i hi ↦ ?_).trans D.sum_two_div_two_pow_le_log_sub
    linarith [le_of_abs_le (D.abs_log_prod_unitSphereMass_sub_le (mem_Ico.mp hi).1)]
  have h_ratio : D.f * log (D.N ^ D.k / (D.N ^ D.k - 1)) ≤ D.f * (2 / D.N) :=
    mul_le_mul_of_nonneg_left D.log_pow_div_pow_sub_one_le D.f.cast_nonneg
  have sphereProd_mul_mass_le :
      sphereProd * mass D.E D.r * (D.N ^ D.k / (D.N ^ D.k - 1)) ^ (2 * D.f) ≤
        (1 + D.b⁻¹ ^ 9) * mass D.E D.k := by
    rw [← log_le_log_iff (by positivity) (by positivity)]
    simp (disch := positivity) only [log_mul, log_pow, Nat.cast_mul, Nat.cast_ofNat]
    linarith
  rw [D.prod_frameMass_eq_mul_prod]
  linear_combination ((D.N : ℝ) ^ D.k) ^ D.f * sphereProd_mul_mass_le

/-- For the ranks `k` and `r = k + 2 ϱ + 1` of the data, the sum of the integers `i` with
`k ≤ i < r` is `(2 ϱ + 1) (k + ϱ)`, where `ϱ` is the number of hyperbolic planes. -/
lemma sum_Ico_k_r_cast : ∑ i ∈ Ico D.k D.r, (i : ℝ) = (2 * D.ϱ + 1) * (D.k + D.ϱ) := by
  have h_gauss : (∑ i ∈ range (2 * D.ϱ + 1), i) * 2 = (2 * D.ϱ + 1) * (2 * D.ϱ) :=
    sum_range_id_mul_two (2 * D.ϱ + 1)
  rw [← Nat.cast_sum _ fun i : ℕ ↦ i, sum_Ico_eq_sum_range, D.r_eq_k_add_two_mul_varrho_add_one,
    add_tsub_cancel_left, sum_add_distrib, sum_const, card_range, smul_eq_mul]
  norm_cast
  linarith

/-- The logarithm of the product of the `fr_v = N ^ k sph_{k+1} ⋯ sph_r` over the `f` infinite
places, as a linear form in the logarithms of `N`, `2`, `π`, the root discriminant and the `i!`. -/
lemma log_prod_frameMass :
    log (∏ v : D.Φ, D.frameMass v) =
      D.f * (D.k * log D.N - ∑ i ∈ Ico D.k D.r, log i.factorial + (2 * D.ϱ + 1) *
        ((D.k + D.ϱ + 1) * (log 2 + log π) - (D.k + D.ϱ + 1 / 2) * log D.rootDisc)) := by
  have N_pos : (0 : ℝ) < D.N := mod_cast D.N_prime.pos
  rw [prod_frameMass_eq_mul_prod, log_mul (by positivity) D.prod_prod_unitSphereMass_pos.ne',
    log_prod fun i _ ↦ (D.prod_unitSphereMass_pos (i + 1)).ne', log_pow, log_pow]
  simp only [log_prod_unitSphereMass, sum_neg_distrib, ← mul_sum]
  have h_sum : ∑ i ∈ Ico D.k D.r,
      ((i + 1 / 2) * log D.rootDisc + log i.factorial - (i + 1) * log (2 * π)) =
        ∑ i ∈ Ico D.k D.r, log i.factorial + (2 * D.ϱ + 1) *
          ((D.k + D.ϱ + 1 / 2) * log D.rootDisc - (D.k + D.ϱ + 1) * log (2 * π)) := by
    simp only [sum_sub_distrib, sum_add_distrib, ← sum_mul, sum_const, nsmul_eq_mul,
      sum_Ico_k_r_cast, cast_card_Ico_k_r]
    ring
  rw [h_sum, log_mul two_ne_zero pi_ne_zero]
  ring

/-- The logarithm of `c_G = vol U(k) (2 π ^ k / (k - 1)!) / vol U(r)`, the constant of the open
cell, as a linear form in the logarithms of `2`, `π` and the factorials. Here `vol U(j)` is the
volume of the compact unitary group. The shape `D.shape` records the number `ϱ` of hyperbolic planes
and an index set with `k` elements. -/
lemma log_openCellConst :
    log D.shape.openCellConst =
      log 2 + D.k * log π - log (D.k - 1).factorial + ∑ i ∈ Ico D.k D.r, log i.factorial -
        (2 * D.ϱ + 1) * (log 2 + (D.k + D.ϱ + 1) * log π) := by
  have h_vol : volU D.r = volU D.k * ∏ i ∈ Ico D.k D.r, 2 * π ^ (i + 1) / i.factorial := by
    simp only [volU, sphereDensity, add_tsub_cancel_right, one_pow, mul_one,
      prod_range_mul_prod_Ico _ D.k_le_r]
  have h_cell : D.shape.openCellConst = (∏ i ∈ Ico D.k D.r, 2 * π ^ (i + 1) / i.factorial)⁻¹ *
      (2 * π ^ D.k / (D.k - 1).factorial) := by
    rw [openCellConst, Shape.k, Shape.r, card_X₀, card_rowIndex, h_vol,
      div_mul_cancel_left₀ (volU_pos _).ne', sphereDensity, one_pow, mul_one]
  rw [h_cell, log_mul (by positivity) (by positivity), log_inv, log_prod fun i _ ↦ by positivity]
  simp (disch := positivity) only [log_div, log_mul, log_pow, sum_sub_distrib, sum_add_distrib,
    ← sum_mul, sum_const, nsmul_eq_mul, Nat.cast_succ, sum_Ico_k_r_cast, cast_card_Ico_k_r]
  ring

/-- The product of the `fr_v = N ^ k sph_{k+1} ⋯ sph_r` over the `f` infinite places `v` of `E`
satisfies `(∏ fr_v) c_G ^ f |disc E| ^ (ϱ / 2) = c_S N ^ (2 k f) vol(Ô) ^ (ϱ + 1 + 2 ϱ (ϱ + k))`. -/
lemma prod_frameMass_mul_openCellConst_eq :
    (∏ v : D.Φ, D.frameMass v) *
        (D.shape.openCellConst ^ D.f * (√√|NumberField.discr D.E| ^ D.ϱ) ^ 2) =
      D.filling.siegelConst * ((D.N ^ D.k) ^ D.f) ^ 2 *
        volÔ D.E ^ (D.ϱ + 1 + 2 * (D.ϱ * (D.ϱ + D.k))) := by
  -- Both sides are positive, and their logarithms are linear in those of `2`, `π`, `N`, the root
  -- discriminant and the factorials.
  have rd_pos : 0 < D.rootDisc := rootDiscr_pos D.E
  have N_pos : (0 : ℝ) < D.N := mod_cast D.N_prime.pos
  have frame_pos : 0 < ∏ v : D.Φ, D.frameMass v := prod_pos fun v _ ↦ D.frameMass_pos v
  have cell_pos : 0 < D.shape.openCellConst := D.shape.openCellConst_pos
  have h_root : √√|(NumberField.discr D.E : ℝ)| = √(D.rootDisc ^ D.f) := by
    rw [abs_discr_eq_rootDiscr_pow, sqrt_sq (by positivity)]
  have h_siegel : D.filling.siegelConst = (π ^ D.k / (D.k - 1).factorial / D.N ^ D.k) ^ D.f *
      √(D.rootDisc ^ D.f) * ((D.rootDisc / 2) ^ D.f)⁻¹ ^ D.k := by
    rw [siegelConst, volÔ_eq, h_root, Shape.k, card_X₀, show D.filling.N = D.N from rfl]
  rw [h_siegel, volÔ_eq, h_root]
  refine log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) ?_
  simp (disch := positivity) only [log_mul, log_div, log_pow, log_inv, log_sqrt,
    log_prod_frameMass, log_openCellConst]
  push_cast
  ring

end New.Data

end
