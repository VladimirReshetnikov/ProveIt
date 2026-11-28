import Lib.Weil.DualPair.HolomorphicData

/-!
# The peaks of a bounded holomorphic form lie away from the cusps

`(V.move g).firstMinimum` is the length of a shortest vector of the lattice at g, cut off at 1. It
is small deep in a cusp.

* `New.Rows.IsPeak`: a peak of a bounded function F is a point where |F| exceeds half of its
  supremum. At a peak x, |F| is at most 2|F(x)| everywhere and F(x) ≠ 0. A point where |F| is at
  least |F(x)| is again a peak.
* `New.Rows.exists_isPeak`: a bounded nonzero function has a peak.
* `New.Rows.IsPeak.le_firstMinimum`: let the order put the signs +1 first, and let F be a bounded
  form, holomorphic of a weight with gap 1 and entries in [-A, A] where A ≥ 2, and of a level
  p = -p̄ with im (Φ w p) in (0, A'] where A' ≥ 1. At every peak g of F the first minimum is at
  least (A A')^(-1/2).

A short lattice vector v is isotropic, and the transvection 1 - p v v^* J fixes F(g ·). Completing
squares writes the points n(z) = 1 - p z v v^* J of its one-parameter group, for im z > -1, as h b
with h real and b triangular (`New.Rows.exists_unitary_mul_triangular_of_pos`). The factor b^u is
bounded and tends to 0 as im z → ∞ (`New.Rows.exists_unitary_mul_triangular`). So z ↦ F(g n(z))
extends to a bounded holomorphic function of period 1 on im z > -1 that vanishes at i∞, and the
Schwarz lemma makes F(g) too small for a peak (`New.Rows.norm_le_of_transvection_invariant`). The
parameter is shifted by i, so that the half plane im z > -1 becomes the upper half plane and z = 0
becomes i.

Notions from other files:
* `New.IsPosFirstOrder`: The order o has distinct values and puts every index of sign +1 before
  every index of sign −1.
* `New.Rows.IsAdelicHol`: For every adelic g, some φ is analytic at all products h b (h preserving
  diag(s), b invertible and triangular for o, at each infinite place) and φ(h b) = b^u F(g·(h,1))
  (`New.IsHolOfWeight`).
* `New.HasHolGap`: The condition on signs ε, integer vector w and natural number γ that
  w_i + γ ≤ w_j whenever ε_i = +1 and ε_j = −1.
* `New.Space`: A hermitian space with a point: a matrix J over E and x in GL_n(𝔸) with xᴴJx equal to
  diag(s) at the infinite places and 1 at the finite places. `V.vecAtPoint y` is the adelic vector
  x⁻¹y, and `V.move g` is the space (J, xg).
* `New.Rows.rapidOfLevel`: The functions F that are continuous, left invariant under the rational
  points of V and right invariant under the principal level K(a), and that decay rapidly (members of
  `V.rapidFunctions`).

## Relation to the literature

Known result: Siegel's argument that a cusp form is large only away from the cusps. Here it is
proved for unitary groups over a CM field, for scalar functions of vector-valued weight and for
bounded forms, with half the supremum in place of an attained maximum. The distance from the cusp is
measured by the first minimum of the lattice, bounded below explicitly in weight and level. Source:
C. Poor, D. Yuen, Linear dependence among Siegel modular forms, Math. Ann. 318 (2000) 205-234, Thm
1.3; M. Eichler, Math. Ann. 213 (1975) 281-291; for the factorisation, Gill, Golub, Murray,
Saunders, Math. Comp. 28 (1974) 505-535.
-/

open NumberField Matrix Real Finset UpperHalfPlane Function Prod ComplexConjugate New Space G
  Norms.L2Operator

/-- An integer vector `u` with gap `1` for the signs `s` (`u i + 1 ≤ u j` whenever `s i = 1` and
`s j = -1`) is separated by an integer `A`: its entries at the signs `+1` are less than `A`, those
at the signs `-1` are at least `A`. -/
lemma New.Rows.exists_int_separating {n : Type} [Fintype n] [Nonempty n] {s : n → ℤˣ} {u : n → ℤ}
    (hu : HasHolGap s u 1) :
    ∃ A : ℤ, (∀ k : n, s k = 1 → u k + 1 ≤ A) ∧ ∀ k : n, s k = -1 → A ≤ u k := by
  -- at a maximum `m` of `s * u`, take `u m + 1` if `s m = 1` and `u m` if `s m = -1`
  obtain ⟨m, hm⟩ := Finite.exists_max fun k : n ↦ s k * u k
  obtain h_sign | h_sign := Int.units_eq_one_or (s m)
  · refine ⟨u m + 1, fun k hk ↦ ?_, fun k hk ↦ hu m k h_sign hk⟩
    simpa [h_sign, hk] using hm k
  · refine ⟨u m, fun k hk ↦ hu k m hk h_sign, fun k hk ↦ ?_⟩
    simpa [h_sign, hk] using hm k

/-- For an injective `o`, the sum of `x l` over `o l < o k + 1` is the sum over `o l < o k` plus
`x k`. -/
lemma New.Rows.sum_filter_lt_add_one {n : Type} [Fintype n] [DecidableEq n] {o : n → ℤ}
    (o_inj : Injective o) (x : n → ℝ) (k : n) :
    ∑ l : n with o l < o k + 1, x l = (∑ l : n with o l < o k, x l) + x k := by
  simp [le_iff_eq_or_lt, o_inj.eq_iff, filter_or, filter_eq', add_comm]

/-- If `v` is isotropic for `J = diag s`, then `M = 1 - t v v^* J` has the Gram matrix
`Mᴴ J M = J - 2 re t J v v^* J`. -/
lemma New.Rows.transvection_gram {n : Type} [Fintype n] [DecidableEq n] {s : n → ℤˣ} {v : n → ℂ}
    (t : ℂ) (hv : star v ⬝ᵥ signMatrix s *ᵥ v = 0) :
    (1 - t • vecMulVec v (star v) * signMatrix s)ᴴ * signMatrix s *
        (1 - t • vecMulVec v (star v) * signMatrix s) =
      signMatrix s -
        ((2 * t.re : ℝ) : ℂ) • (signMatrix s * vecMulVec v (star v) * signMatrix s) := by
  -- expand the product; the term quadratic in `t` has the factor `v^* J v = 0`
  simp [hv, t.re_eq_add_conj, vecMulVec_mul, sub_mul, star_vecMul, mul_sub,
    mul_vecMulVec, vecMulVec_mulVec, ← dotProduct_mulVec, mul_div]
  module

/-- Completing squares. Let `o` be injective, `v` isotropic for `J = diag s`, put
`x k = s k |v k|²`, and suppose that the numbers `p a = 1 - 2 re t ∑ (x l, o l < a)` are positive.
Then `1 - t v v^* J = h b` with `h` in `USign s` (preserving `diag s`) and `b` invertible and
triangular for `o` (`IsBorelMatrix`), with diagonal entries `√(p (o k + 1) / p (o k))`. -/
lemma New.Rows.exists_unitary_mul_triangular_of_pos {n : Type} [Fintype n] [DecidableEq n]
    {s : n → ℤˣ} {o : n → ℤ} {v : n → ℂ} {t : ℂ} {x : n → ℝ} {p : ℤ → ℝ} (o_inj : Injective o)
    (hv : star v ⬝ᵥ signMatrix s *ᵥ v = 0)
    (hx : ∀ k : n, (x k : ℂ) = conj (v k) * (s k * v k))
    (hp : ∀ a : ℤ, p a = 1 - 2 * t.re * ∑ l : n with o l < a, x l) (p_pos : ∀ a : ℤ, 0 < p a) :
    ∃ (h : USign s) (b : Matrix n n ℂ), IsBorelMatrix o b ∧
      1 - t • vecMulVec v (star v) * signMatrix s = h * b ∧
      ∀ k : n, b k k = Real.exp (((p (o k + 1)).log - (p (o k)).log) / 2) := by
  -- The leading minors of `Mᴴ J M` are, up to sign, the numbers `p a`, and an explicit triangular
  -- `c` makes `M * c` unitary; take `b = c⁻¹`.
  let τ : ℝ := 2 * t.re
  replace hp (a : ℤ) : p a = 1 - τ * ∑ l with o l < a, x l := hp a
  have p_succ (k : n) : p (o k + 1) = p (o k) - τ * x k := by
    rw [hp, hp, sum_filter_lt_add_one o_inj]
    ring
  -- `L k` is the logarithm of the ratio of consecutive minors, and `c k k = exp (-L k / 2)`
  let L (k : n) : ℝ := (p (o k + 1)).log - (p (o k)).log
  let r (k : n) : ℝ := (-L k / 2).exp / p (o k)
  let β (l : n) : ℂ := s l * conj (v l) * r l
  let c : Matrix n n ℂ :=
    of fun k l ↦ if o k < o l then v k * τ * β l else if k = l then r l * p (o l) else 0
  have c_block : c.BlockTriangular o := by grind [BlockTriangular, of_apply]
  have c_tri : IsBorelMatrix o c := by
    refine ⟨c_block, ?_⟩
    rw [DiscreteSeries.det_eq_prod_diag_of_blockTriangular o_inj c_block]
    simp [prod_ne_zero_iff, c, r, p_pos, ne_of_gt]
  set M : Matrix n n ℂ := 1 - t • vecMulVec v (star v) * signMatrix s
  have unitary : (M * c)ᴴ * signMatrix s * (M * c) = signMatrix s := by
    have row : star v ᵥ* (signMatrix s * c) = β := by
      ext
      simp [vecMul, dotProduct, signMatrix, c, hp, ← mul_assoc, hx, mul_sub, sum_ite,
        ← sum_mul]
      ring
    have gram : (M * c)ᴴ * signMatrix s * (M * c) =
        cᴴ * (signMatrix s * (c - (τ : ℂ) • vecMulVec v β)) := by
      rw [show (M * c)ᴴ * signMatrix s * (M * c) = cᴴ * (Mᴴ * signMatrix s * M) * c by
        simp [mul_assoc], transvection_gram t hv]
      simp [τ, ← row, mul_sub, sub_mul, mul_assoc, vecMulVec_mul]
    ext i l
    wlog! hil : o i ≤ o l generalizing i l
    · simpa [← conjTranspose_apply, mul_assoc] using congr_arg star (this l i hil.le)
    -- `cᴴ` and `c - τ v β` are lower triangular, so for `o i ≤ o l` only the term `l` of the
    -- product can survive; it is `0` for `i ≠ l` and `s l` for `i = l`
    have right_apply (j : n) : (signMatrix s * (c - (τ : ℂ) • vecMulVec v β)) j l =
        s j * (c j l - τ * (v j * β l)) := by
      simp [signMatrix, vecMulVec_apply]
    rw [gram, mul_apply, sum_eq_single l]
    · rw [right_apply, conjTranspose_apply]
      obtain rfl | hne := eq_or_ne i l
      · have diag : r i * p (o i) * r i * (p (o i) - τ * x i) = 1 := by
          simp [r, L, exp_sub, p_pos, ← p_succ, ne_of_gt, mul_div, ← exp_add, exp_log,
            div_mul_eq_mul_div]
        calc star (c i i) * (s i * (c i i - τ * (v i * β i)))
            = (s i : ℂ) * (r i * p (o i) * r i * (p (o i) - τ * x i) : ℝ) := by
              simp [c, β, hx]
              ring
          _ = signMatrix s i i := by simp [diag, signMatrix]
      · simp [c_block (hil.lt_of_ne (o_inj.ne hne) : o i < o l), signMatrix, hne]
    · intro j _ hj
      obtain h_lt | h_gt := (o_inj.ne hj).lt_or_gt
      · rw [right_apply]
        simp [c, h_lt, mul_assoc, mul_left_comm]
      · simp [c_block (hil.trans_lt h_gt : o i < o j)]
    · simp
  refine ⟨U.of IsHermitianInvolution.isUnit (M * c) unitary, c⁻¹, c_tri.inv, by simp [c_tri.2],
    fun k ↦ ?_⟩
  have c_diag : c k k = Real.exp (-L k / 2) := by simp [c, r, (p_pos _).ne']
  rw [c_tri.inv_apply_diag o_inj, c_diag, ← Complex.ofReal_inv, ← Real.exp_neg, neg_div, neg_neg]

/-- If the real numbers `L k` sum to `0` and have the signs `s k`, and the integer vector `u` has
gap `1` for `s`, then `∑ L k * u k` is at most minus the sum of `L k` over the signs `+1`. -/
lemma New.Rows.sum_mul_le_of_sign_mul_nonneg {n : Type} [Fintype n] [Nonempty n] {s : n → ℤˣ}
    {u : n → ℤ} {L : n → ℝ} (hu : HasHolGap s u 1) (sum_L : ∑ k : n, L k = 0)
    (h_sign : ∀ k : n, 0 ≤ (s k : ℝ) * L k) :
    ∑ k : n, L k * u k ≤ -∑ k : n with s k = 1, L k := by
  obtain ⟨A, hA_pos, hA_neg⟩ := exists_int_separating hu
  have term_le (k : n) : L k * u k ≤ L k * A - if s k = 1 then L k else 0 := by
    obtain hk | hk := Int.units_eq_one_or (s k)
    · have h_le : (u k : ℝ) + 1 ≤ A := mod_cast hA_pos k hk
      simp only [hk, ite_true]
      nlinarith [show 0 ≤ L k by simpa [hk] using h_sign k]
    · have h_nonpos : L k ≤ 0 := by simpa [hk] using h_sign k
      simpa [hk] using mul_le_mul_of_nonpos_left (mod_cast hA_neg k hk : (A : ℝ) ≤ u k) h_nonpos
  refine (sum_le_sum fun k _ ↦ term_le k).trans_eq ?_
  rw [sum_sub_distrib, ← sum_mul, sum_L, ← sum_filter, zero_mul, zero_sub]

/-- If the real numbers `L k` sum to `0` and have the signs `-s k`, and the entries of the integer
vector `u` have absolute value at most `B`, then `∑ L k * u k` is at most `-2 B` times the sum of
`L k` over the signs `+1`. -/
lemma New.Rows.sum_mul_le_of_sign_mul_nonpos {n : Type} [Fintype n] {s : n → ℤˣ} {u : n → ℤ}
    {L : n → ℝ} {B : ℝ} (hB : ∀ k : n, |(u k : ℝ)| ≤ B) (sum_L : ∑ k : n, L k = 0)
    (h_sign : ∀ k : n, (s k : ℝ) * L k ≤ 0) :
    ∑ k : n, L k * u k ≤ -(2 * B * ∑ k : n with s k = 1, L k) := by
  have term_le (k : n) : L k * u k ≤ L k * B - 2 * B * if s k = 1 then L k else 0 := by
    obtain ⟨h_lower, h_upper⟩ := abs_le.1 (hB k)
    obtain hk | hk := Int.units_eq_one_or (s k)
    · simp only [hk, ite_true]
      nlinarith [show L k ≤ 0 by simpa [hk] using h_sign k]
    · have h_nonneg : 0 ≤ L k := by simpa [hk] using h_sign k
      simpa [hk] using mul_le_mul_of_nonneg_left h_upper h_nonneg
  refine (sum_le_sum fun k _ ↦ term_le k).trans_eq ?_
  rw [sum_sub_distrib, ← sum_mul, sum_L, ← mul_sum, ← sum_filter, zero_mul, zero_sub]

/-- Let `o` put the signs `1` first and let `x` have total `0` and the signs `s`. If
`τ ∑ |x l| < 1`, then `1 - τ ∑ (x l, o l < a)` is positive for every `a`. -/
lemma New.Rows.one_sub_mul_sum_filter_pos {n : Type} [Fintype n] [DecidableEq n] {s : n → ℤˣ}
    {o : n → ℤ} {x : n → ℝ} {τ : ℝ} (ho : IsPosFirstOrder s o)
    (hx : ∀ k : n, 0 ≤ (s k : ℝ) * x k) (sum_x : ∑ k : n, x k = 0)
    (hτ : τ * ∑ k : n, |x k| < 1) (a : ℤ) : 0 < 1 - τ * ∑ l : n with o l < a, x l := by
  obtain ⟨o_inj, o_lt⟩ := ho
  -- the positive `x l` come first and the total is `0`, so the partial sums are nonnegative
  have h_nonneg : 0 ≤ ∑ l with o l < a, x l := by
    by_cases! h : ∀ l : n, o l < a → 0 ≤ x l
    · exact sum_nonneg fun l hl ↦ h l (mem_filter.1 hl).2
    · obtain ⟨k, hk, hk_neg⟩ := h
      have h_outside (l : n) (hl : ¬o l < a) : x l ≤ 0 := by
        obtain h_sign | h_sign := Int.units_eq_one_or (s l)
        · have hk' : s k = -1 := (Int.units_eq_one_or _).resolve_left fun hk' ↦
            hk_neg.not_ge (by simpa [hk'] using hx k)
          exact absurd ((o_lt l k h_sign hk').trans hk) hl
        · simpa [h_sign] using hx l
      rw [← sum_x, sum_filter]
      exact sum_le_sum (by grind)
  have h_le : ∑ l with o l < a, x l ≤ ∑ l : n, |x l| :=
    (sum_le_sum fun l _ ↦ le_abs_self _).trans (sum_le_univ_sum_of_nonneg fun l ↦ abs_nonneg _)
  obtain hτ₀ | hτ₀ := le_total τ 0 <;> nlinarith

/-- For an injective `o` and numbers `p a = 1 - τ ∑ (x l, o l < a)`, the sum of
`log (p (o k + 1)) - log (p (o k))` over an initial segment `T` of the order `o` is
`log (1 - τ ∑ (x k, k ∈ T))`. -/
lemma New.Rows.sum_log_sub_log_eq {n : Type} [Fintype n] [DecidableEq n] {o : n → ℤ}
    {x : n → ℝ} {τ : ℝ} {p : ℤ → ℝ} (o_inj : Injective o)
    (hp : ∀ a : ℤ, p a = 1 - τ * ∑ l : n with o l < a, x l) (T : Finset n)
    (hT : ∀ l ∉ T, ∀ k ∈ T, o k < o l) :
    ∑ k ∈ T, ((p (o k + 1)).log - (p (o k)).log) = Real.log (1 - τ * ∑ k ∈ T, x k) := by
  induction T using Finset.induction_on_max_value o with
  | empty => simp
  | insert a S haS h_max ih =>
    have h_below : univ.filter (o · < o a) = S := by grind
    rw [sum_insert haS, sum_insert haS, ih (by grind), hp, hp, sum_filter_lt_add_one o_inj,
      h_below, sub_add_cancel, add_comm (x a)]

/-- If `c (b - a)` is nonnegative for positive `a` and `b`, then so is `c (log b - log a)`. -/
lemma New.Rows.mul_log_sub_log_nonneg {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h_mul_sub : 0 ≤ c * (b - a)) : 0 ≤ c * (b.log - a.log) := by
  obtain hc | rfl | hc := lt_trichotomy c 0
  · exact mul_nonneg_of_nonpos_of_nonpos hc.le (sub_nonpos.2 (log_le_log hb (by nlinarith)))
  · simp
  · exact mul_nonneg hc.le (sub_nonneg.2 (log_le_log ha (by nlinarith)))

/-- Let `o` be injective and put the signs `1` of `J = diag s` first, let the weight `u` have gap
`1` (`u i + 1 ≤ u j` whenever `s i = 1` and `s j = -1`) and size at most `B ≥ 2`, and let `v` be
isotropic. If `y - η = 1 - re t |v|²` with `1 < y` and `0 < η ≤ 1 / 2`, then `1 - t v v^* J = h b`
with `h` in `USign s` (preserving `diag s`), `b` invertible and triangular for `o`
(`IsBorelMatrix`), and `|b ^ u| ≤ exp (2 B η) / √y` (here `b ^ u` is `diagChar u b`, the product of
the `b k k ^ u k`). -/
lemma New.Rows.exists_unitary_mul_triangular {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    {s : n → ℤˣ} {o u : n → ℤ} {B η y : ℝ} {v : n → ℂ} {t : ℂ} (ho : IsPosFirstOrder s o)
    (hu : HasHolGap s u 1) (hB : ∀ i : n, |(u i : ℝ)| ≤ B) (hB₂ : 2 ≤ B)
    (hv : star v ⬝ᵥ signMatrix s *ᵥ v = 0) (ht : y - η = 1 - t.re * ∑ i : n, ‖v i‖ ^ 2) (hy : 1 < y)
    (hη : 0 < η) (hη' : η ≤ 2⁻¹) :
    ∃ (h : USign s) (b : Matrix n n ℂ), IsBorelMatrix o b ∧
      1 - t • vecMulVec v (star v) * signMatrix s = h * b ∧
      ‖diagChar u b‖ ≤ Real.exp (2 * B * η) / √y := by
  -- Complete squares; then bound the product of the diagonal entries, raised to the weights.
  -- The leading minors `p a` of the Gram matrix, divided by those of `J`, move from `1` to
  -- `y - η`, the value at the last sign `+1`, and back to `1`.
  have o_inj : Injective o := ho.1
  let x (k : n) : ℝ := if s k = 1 then ‖v k‖ ^ 2 else -‖v k‖ ^ 2
  have x_conj (k : n) : x k = conj (v k) * (s k * v k) := by
    obtain hk | hk := Int.units_eq_one_or (s k) <;> simp [hk, x, RCLike.conj_mul]
  have sign_mul (k : n) : (s k : ℝ) * x k = ‖v k‖ ^ 2 := by
    obtain hk | hk := Int.units_eq_one_or (s k) <;> simp [hk, x]
  have sum_x : ∑ k : n, x k = 0 := by
    simpa [← Complex.ofReal_sum, ← x_conj, signMatrix, mulVec_diagonal, dotProduct] using hv
  let τ : ℝ := 2 * t.re
  let p (a : ℤ) : ℝ := 1 - τ * ∑ l with o l < a, x l
  have p_pos (a : ℤ) : 0 < p a := by
    refine one_sub_mul_sum_filter_pos ho (fun k ↦ by simp [sign_mul]) sum_x ?_ a
    simp only [x, τ, apply_ite abs, abs_neg, abs_pow, abs_norm, ite_self]
    linarith
  obtain ⟨h, b, b_tri, h_eq, b_diag⟩ :=
    exists_unitary_mul_triangular_of_pos o_inj hv x_conj (fun _ ↦ rfl) p_pos
  refine ⟨h, b, b_tri, h_eq, ?_⟩
  -- `L k` is the logarithm of the ratio of consecutive minors, and `b k k = exp (L k / 2)`
  let L (k : n) : ℝ := (p (o k + 1)).log - (p (o k)).log
  replace b_diag (k : n) : b k k = Real.exp (L k / 2) := b_diag k
  -- `L` telescopes over every initial segment of the order
  have telescope (T : Finset n) (hT : ∀ l ∉ T, ∀ k ∈ T, o k < o l) :
      T.sum L = Real.log (1 - τ * T.sum x) := sum_log_sub_log_eq o_inj (fun _ ↦ rfl) T hT
  have sum_all : ∑ k : n, L k = 0 := by simp [telescope, sum_x]
  have sum_pos : ∑ k : n with s k = 1, L k = Real.log (y - η) := by
    -- the positive `x k` make up half of `|v|²`
    have sq_eq (k : n) : ‖v k‖ ^ 2 = 2 * (if s k = 1 then x k else 0) - x k := by grind
    have h_first (l : n) (hl : s l ≠ 1) (k : n) (hk : s k = 1) : o k < o l :=
      ho.2 k l hk ((Int.units_eq_one_or (s l)).resolve_left hl)
    rw [telescope _ (by simpa using h_first), ht]
    simp only [sq_eq, sum_sub_distrib, ← mul_sum, ← sum_filter, sum_x, τ]
    ring_nf
  have log_le : Real.log y ≤ Real.log (y - η) + 2 * η := by
    calc Real.log y ≤ Real.log ((y - η) * (2 * η + 1)) := log_le_log (by linarith) (by nlinarith)
      _ = Real.log (y - η) + Real.log (2 * η + 1) := log_mul (by linarith) (by linarith)
      _ ≤ _ := by linarith [log_le_sub_one_of_pos (show 0 < 2 * η + 1 by linarith)]
  -- `L k` has the sign of `-τ * s k`
  have h_diff (k : n) : (s k : ℝ) * (p (o k + 1) - p (o k)) = -τ * ‖v k‖ ^ 2 := by
    simp only [p, ← sign_mul k, sum_filter_lt_add_one o_inj]
    ring
  have h_log : (∑ k : n, L k * u k) / 2 ≤ 2 * (B * η) - Real.log y * 2⁻¹ := by
    obtain hτ | hτ := le_total τ 0
    · have h_sign (k : n) : 0 ≤ (s k : ℝ) * L k :=
        mul_log_sub_log_nonneg (p_pos _) (p_pos _) (by nlinarith [h_diff k])
      nlinarith [sum_mul_le_of_sign_mul_nonneg hu sum_all h_sign, sum_pos]
    · have h_sign (k : n) : (s k : ℝ) * L k ≤ 0 := by
        linarith [mul_log_sub_log_nonneg (c := -(s k : ℝ)) (p_pos (o k)) (p_pos (o k + 1))
          (by nlinarith [h_diff k])]
      nlinarith [sum_mul_le_of_sign_mul_nonpos hB sum_all h_sign, sum_pos, log_pos hy]
  calc ‖diagChar u b‖ = Real.exp ((∑ k : n, L k * u k) / 2) := by
        simp [diagChar, b_diag, Complex.norm_exp, ← rpow_intCast, ← exp_mul, div_mul_eq_mul_div,
          ← exp_sum, ← sum_div]
    _ ≤ Real.exp (2 * (B * η) - Real.log y * 2⁻¹) := exp_le_exp.2 h_log
    _ = _ := by
      rw [exp_sub, sqrt_eq_rpow, rpow_def_of_pos (one_pos.trans hy), one_div, mul_assoc]

/-- Two transvections `1 - a y y^* J`, `1 - c y y^* J` along one vector `y` isotropic for
`J = diag s` (`signMatrix s`) multiply by adding their parameters. -/
lemma New.Rows.transvection_mul {n : Type} [Fintype n] [DecidableEq n] {s : n → ℤˣ} {y : n → ℂ}
    (a c : ℂ) (iso : star y ⬝ᵥ signMatrix s *ᵥ y = 0) :
    (1 - a • vecMulVec y (star y) * signMatrix s) * (1 - c • vecMulVec y (star y) * signMatrix s) =
      1 - (a + c) • vecMulVec y (star y) * signMatrix s := by
  simp [iso, mul_sub, vecMulVec_mul, sub_mul, mul_vecMulVec, vecMulVec_mulVec, ← dotProduct_mulVec]
  module

/-- The factorisation `exists_unitary_mul_triangular` along the upper half plane. Let the signs `1`
of `J = diag s` come first in `o`, let the weight `u` have gap `1` and size at most `B ≥ 2` and let
`v` be isotropic. For purely imaginary `a` with `η = im a |v|²` in `(0, 1 / 2]`, the matrix
`1 - a (z - i) v v^* J` is `h b` (`h` preserves `J`, `b` is triangular for `o`) with
`|b ^ u| ≤ exp (2 B η) / √(1 + im z η)`. -/
lemma New.Rows.exists_unitary_mul_triangular_upperHalfPlane {n : Type} [Fintype n] [DecidableEq n]
    [Nonempty n] {s : n → ℤˣ} {o u : n → ℤ} {B η : ℝ} {v : n → ℂ} {a : ℂ}
    (ho : IsPosFirstOrder s o) (hu : HasHolGap s u 1) (hB : ∀ i : n, |(u i : ℝ)| ≤ B) (hB₂ : 2 ≤ B)
    (hv : star v ⬝ᵥ signMatrix s *ᵥ v = 0) (ha : a.re = 0)
    (hη_eq : η = a.im * ∑ i : n, ‖v i‖ ^ 2) (hη : 0 < η) (hη' : η ≤ 2⁻¹) (z : ℍ) :
    ∃ (h : USign s) (b : Matrix n n ℂ), IsBorelMatrix o b ∧
      1 - (a * (z - .I)) • vecMulVec v (star v) * signMatrix s = h * b ∧
      ‖diagChar u b‖ ≤ Real.exp (2 * B * η) / √(1 + z.im * η) := by
  have h_re : 1 + z.im * η - η = 1 - (a * (z - .I)).re * ∑ i : n, ‖v i‖ ^ 2 := by
    simp [ha, hη_eq, mul_sub]
    ring
  exact exists_unitary_mul_triangular ho hu hB hB₂ hv h_re
    (lt_add_of_pos_right 1 (mul_pos z.im_pos hη)) hη hη'

/-- The Schwarz lemma at the cusp: a holomorphic function on the upper half plane of period `1`
that vanishes at `i∞` and is bounded by `M` is at most `M exp (-2 π)` at `i`. -/
lemma New.Rows.norm_I_le_of_periodic {f : ℍ → ℂ} {M : ℝ} (f_per : Periodic (f ∘ ofComplex) 1)
    (f_hol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f)
    (f_zero : IsZeroAtImInfty f) (f_bdd : ∀ z : ℍ, ‖f z‖ ≤ M) :
    ‖f UpperHalfPlane.I‖ ≤ M * Real.exp (-(2 * π)) := by
  -- in the variable `q = exp (2 π i z)`, `f` maps the unit disc into the disc of radius `M`
  have maps : Set.MapsTo (cuspFunction 1 f) (Metric.ball 0 1)
      (Metric.closedBall (cuspFunction 1 f 0) M) := by
    intro q _
    obtain hq | rfl : q ≠ 0 ∨ q = 0 := ne_or_eq q 0
    · rw [f_zero.cuspFunction_apply_zero one_pos, mem_closedBall_zero_iff, cuspFunction,
        Periodic.cuspFunction_eq_of_nonzero _ _ hq]
      exact f_bdd _
    · exact Metric.mem_closedBall_self ((norm_nonneg _).trans (f_bdd .I))
  -- the point `z = i` corresponds to `q = exp (-2 π)`
  have h_dist : dist (cuspFunction 1 f (Periodic.qParam 1 UpperHalfPlane.I)) (cuspFunction 1 f 0) ≤
      M / 1 * dist (Periodic.qParam 1 UpperHalfPlane.I) 0 :=
    Complex.dist_le_div_mul_dist_of_mapsTo_ball
      (differentiableOn_cuspFunction_ball one_pos f_per f_hol f_zero.boundedAtFilter) maps
      (by simpa [-coe_I] using norm_qParam_lt_one 1 .I)
  rw [eq_cuspFunction _ one_ne_zero f_per, f_zero.cuspFunction_apply_zero one_pos] at h_dist
  simpa [Periodic.norm_qParam] using h_dist

/-- A peak of a bounded function is a point where its modulus exceeds half of its supremum. -/
structure New.Rows.IsPeak {X : Type} (F : X → ℂ) (x : X) : Prop where
  /-- The function is bounded. -/
  bddAbove : BddAbove (Set.range fun y : X ↦ ‖F y‖)
  /-- The modulus at `x` exceeds half of the supremum. -/
  half_lt : (⨆ y : X, ‖F y‖) / 2 < ‖F x‖

namespace New.Rows.IsPeak

lemma norm_le {X : Type} {F : X → ℂ} {x : X} (hx : IsPeak F x) (y : X) : ‖F y‖ ≤ 2 * ‖F x‖ := by
  linarith [le_ciSup hx.bddAbove y, hx.half_lt]

lemma ne_zero {X : Type} {F : X → ℂ} {x : X} (hx : IsPeak F x) : F x ≠ 0 :=
  norm_pos_iff.1 (by linarith [le_ciSup hx.bddAbove x, hx.half_lt])

lemma of_norm_le {X : Type} {F : X → ℂ} {x y : X} (hx : IsPeak F x) (hxy : ‖F x‖ ≤ ‖F y‖) :
    IsPeak F y :=
  ⟨hx.bddAbove, hx.half_lt.trans_le hxy⟩

end New.Rows.IsPeak

/-- A nonzero bounded function has a peak. -/
lemma New.Rows.exists_isPeak {X : Type} {F : X → ℂ} {C : ℝ} (hF : ∀ x : X, ‖F x‖ ≤ C)
    (hF₀ : F ≠ 0) : ∃ x : X, IsPeak F x := by
  have bdd : BddAbove (Set.range fun y : X ↦ ‖F y‖) := ⟨C, Set.forall_mem_range.2 hF⟩
  obtain ⟨y, hy⟩ := ne_iff.1 hF₀
  have sup_pos : 0 < ⨆ y : X, ‖F y‖ := (norm_pos_iff.2 hy).trans_le (le_ciSup bdd y)
  have : Nonempty X := ⟨y⟩
  obtain ⟨x, hx⟩ : ∃ x : X, (⨆ y : X, ‖F y‖) / 2 < ‖F x‖ :=
    exists_lt_of_lt_ciSup (half_lt_self sup_pos)
  exact ⟨x, bdd, hx⟩

/-- A nonzero member of `rapidOfLevel V a` (a rapidly decreasing form on the space `V` of level
`a`) has a peak. -/
lemma New.Rows.exists_isPeak_of_mem_rapidOfLevel {E n : Type} [Field E] [CMType E] [Fintype n]
    [DecidableEq n] {s : n → ℤˣ} {V : Space E n s} {a : 𝓞 E} {F : G E s → ℂ}
    (hF : F ∈ rapidOfLevel V a) (hF₀ : F ≠ 0) : ∃ g : G E s, IsPeak F g := by
  obtain ⟨h_rapid, _⟩ := Submodule.mem_inf.1 hF
  obtain ⟨C, hC⟩ := h_rapid.2.bounded
  exact exists_isPeak hC hF₀

/-- For positive `η i`, the product of `c i / √(1 + im z * η i)` over a nonempty finite type tends
to `0` as `im z → ∞`. -/
lemma New.Rows.tendsto_prod_div_sqrt_atImInfty {ι : Type} [Fintype ι] [Nonempty ι] {η : ι → ℝ}
    (c : ι → ℝ) (hη : ∀ i : ι, 0 < η i) :
    Filter.Tendsto (fun z : ℍ ↦ ∏ i : ι, c i / √(1 + z.im * η i)) atImInfty (nhds 0) := by
  have h_tendsto (i : ι) :
      Filter.Tendsto (fun z : ℍ ↦ c i / √(1 + z.im * η i)) atImInfty (nhds 0) :=
    (tendsto_sqrt_atTop.comp <| tendsto_const_nhds.add_atTop
      (Filter.tendsto_comap.atTop_mul_const (hη i))).const_div_atTop _
  simpa [-prod_div_distrib] using tendsto_finsetProd univ fun i _ ↦ h_tendsto i

/-- The analytic part of `IsPeak.le_firstMinimum`. Let the order `o` put the signs `+1` first. Let
`F` on the real group `GInf E s` be holomorphic of a weight `u` for `o` (`IsHolOfWeight`: `F` times
the weight-`u` character of invertible `o`-triangular `b` extends analytically to products `h b`).
Let `u` have gap `1` (`u w i + 1 ≤ u w j` whenever `s i = 1`, `s j = -1`) and entries in `[-A, A]`,
`A ≥ 2`. Let `F` be bounded by `C > 0` and left invariant under `t`, which at each place is the
transvection `1 - a y y^* J` along an isotropic vector `y`, with `a` purely imaginary and
`J = diag s`. If the sizes `η w = im (a w) |y w|²` are positive and `A ∑ η ≤ 1`, then
`|F 1| ≤ C exp (2 - 2 π)`.

The bound is that of Schwarz's lemma for the extension of `F` along the complexified transvections
`1 - a (z - i) y y^* J`, `im z > 0`. As a function of `q = exp (2 π i z)` on the unit disc it is
bounded by `C exp 2`, vanishes at `0` and takes the value `F 1` at `q = exp (-2 π)`. -/
lemma New.Rows.norm_le_of_transvection_invariant {E n : Type} [Field E] [CMType E] [Fintype n]
    [DecidableEq n] [Nonempty n] {s : n → ℤˣ} {o : n → ℤ} {u : InfinitePlace E → n → ℤ}
    {F : GInf E s → ℂ} {A C : ℝ} {a : InfinitePlace E → ℂ} {y : InfinitePlace E → n → ℂ}
    {t : GInf E s} (ho : IsPosFirstOrder s o)
    (h_gap : ∀ w : InfinitePlace E, HasHolGap s (u w) 1)
    (h_wt : ∀ (w : InfinitePlace E) (i : n), |(u w i : ℝ)| ≤ A) (hA : 2 ≤ A)
    (h_hol : IsHolOfWeight s o u F) (le_sup : ∀ h : GInf E s, ‖F h‖ ≤ C) (C_pos : 0 < C)
    (re_eq : ∀ w : InfinitePlace E, (a w).re = 0)
    (iso : ∀ w : InfinitePlace E, star (y w) ⬝ᵥ signMatrix s *ᵥ y w = 0)
    (η_pos : ∀ w : InfinitePlace E, 0 < (a w).im * ∑ i : n, ‖y w i‖ ^ 2)
    (η_sum : A * ∑ w : InfinitePlace E, (a w).im * ∑ i : n, ‖y w i‖ ^ 2 ≤ 1)
    (t_eq : ∀ w : InfinitePlace E,
      ((t w : USign s) : Matrix n n ℂ) =
        1 - a w • vecMulVec (y w) (star (y w)) * signMatrix s)
    (t_fix : ∀ h : GInf E s, F (t * h) = F h) :
    ‖F 1‖ ≤ C * exp (2 + -(2 * π)) := by
  -- Along the one-parameter group of `t`, `F` continues to a periodic holomorphic function `f` on
  -- the upper half plane that vanishes at `i∞`; apply the Schwarz lemma at `i`.
  -- `x ζ` is the point `ζ - i` of the one-parameter group, so `1 = x i` and `t = x (1 + i)`
  let x (ζ : ℂ) (w : InfinitePlace E) : Matrix n n ℂ := 1 -
    (a w * (ζ - .I)) • vecMulVec (y w) (star (y w)) * signMatrix s
  have x_add (ζ : ℂ) (w : InfinitePlace E) : t w * x ζ w = x (ζ + 1) w := by
    simp only [t_eq, x, transvection_mul _ _ (iso w)]
    ring_nf
  let η (w : InfinitePlace E) : ℝ := (a w).im * ∑ i, ‖y w i‖ ^ 2
  have η_le (w : InfinitePlace E) : η w ≤ 2⁻¹ := by
    nlinarith [single_le_sum (fun w _ ↦ (η_pos w).le) (mem_univ w), η_pos w]
  -- factor `x z` as an element of `USign s` times a triangular matrix
  have factor (z : ℍ) (w : InfinitePlace E) :
      ∃ (h : USign s) (b : Matrix n n ℂ), IsBorelMatrix o b ∧ x z w = h * b ∧
        ‖diagChar (u w) b‖ ≤ (2 * A * η w).exp / √(1 + z.im * η w) :=
    exists_unitary_mul_triangular_upperHalfPlane ho (h_gap w) (h_wt w) hA (iso w) (re_eq w) rfl
      (η_pos w) (η_le w) z
  choose h b b_tri x_eq b_le using factor
  -- `φ` is the holomorphic extension of `F`
  obtain ⟨φ, hφ⟩ := h_hol
  have φ_eq (h : InfinitePlace E → USign s) (b : InfinitePlace E → Matrix n n ℂ)
      (hb : ∀ w, IsBorelMatrix o (b w)) :
      φ (fun w ↦ h w * b w) = (∏ w, diagChar (u w) (b w)) * F h := (hφ h b hb (by simp)).2
  let f (z : ℍ) : ℂ := φ (x z)
  have f_I : f .I = F 1 := by
    simpa [f, x, diagChar, IsBorelMatrix, blockTriangular_one, mk_one_one] using φ_eq 1 1
  have f_eq (z : ℍ) : f z = (∏ w, diagChar (u w) (b z w)) * F (h z) :=
    (congr_arg φ (funext (x_eq z))).trans (φ_eq _ _ (b_tri z))
  have f_le (z : ℍ) : ‖f z‖ ≤ C * ∏ w, (2 * A * η w).exp / √(1 + z.im * η w) := by
    rw [f_eq, norm_mul, norm_prod, mul_comm]
    gcongr with w
    exacts [le_sup _, b_le z w]
  -- the product is at most `exp (2 A ∑ η) ≤ e ^ 2`, and tends to `0` as `im z → ∞`
  have f_bdd (z : ℍ) : ‖f z‖ ≤ C * exp 2 := by
    grw [f_le, ← mul_pos z.im_pos (η_pos _)]
    simpa [C_pos, mul_assoc, ← exp_sum, ← mul_sum] using η_sum
  have f_zero : IsZeroAtImInfty f := by
    refine squeeze_zero_norm f_le ?_
    simpa using (tendsto_prod_div_sqrt_atImInfty (fun w ↦ (2 * A * η w).exp) η_pos).const_mul C
  -- periodicity: `x (z + 1) = t * x z`, and `t` leaves `F` unchanged
  have f_per : Periodic (f ∘ ofComplex) 1 := by
    intro z
    by_cases hz : 0 < z.im
    · let z' : ℍ := ⟨z, hz⟩
      have x_shift : x (z + 1) = fun w ↦ ((t * h z') w : USign s) * b z' w := funext fun w ↦ by
        simp [← x_add, x_eq z' w, mul_assoc, z']
      calc (f ∘ ofComplex) (z + 1) = φ (x (z + 1)) := by simp [f, ofComplex_apply_eq_ite, hz]
        _ = f z' := by rw [x_shift, φ_eq _ _ (b_tri z'), t_fix, f_eq]
        _ = (f ∘ ofComplex) z := by simp [ofComplex_apply_eq_ite, hz, z']
    · simp [hz, ofComplex_apply_eq_ite]
  have f_hol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f := fun z ↦ by
    have φ_analytic : AnalyticAt ℂ φ (x z) := by
      simpa [funext (x_eq z)] using (hφ _ _ (b_tri z) (by simp)).1
    exact (φ_analytic.differentiableAt.comp _ (by fun_prop)).comp_mdifferentiableAt
      z.mdifferentiable_coe
  -- the Schwarz lemma with the bound `C * e ^ 2`
  rw [← f_I, exp_add, ← mul_assoc]
  exact norm_I_le_of_periodic f_per f_hol f_zero f_bdd

/-- Let `m = 1 - p Y Y^* S`, with `Y` the adelic coordinates of a rational vector `y` and
`S = stdForm E s` the diagonal form of signs, preserve `S`. Then the element `ofMatrix m hm` of the
adelic unitary group is a rational point of the space `V` (a member of `V.Γ`). -/
lemma New.Rows.ofMatrix_transvection_mem_Gamma {E n : Type} [Field E] [CMType E] [Fintype n]
    [DecidableEq n] {s : n → ℤˣ} (V : Space E n s) (y : n → E) (p : E)
    {m : Matrix n n (𝔸 E)} (hm : mᴴ * stdForm E s * m = stdForm E s)
    (m_eq : m = 1 - toAdele p • vecMulVec (V.vecAtPoint y) (star (V.vecAtPoint y)) * stdForm E s) :
    ofMatrix m hm ∈ V.Γ := by
  rw [mem_Gamma_iff_range]
  -- the conjugate by the point of `V` is the rational transvection `1 - p y y^* V.J`
  have h_conj : (V.x : Matrix n n (𝔸 E)) * (ofMatrix m hm).adeleMatrix * V.x⁻¹.val =
      (1 - p • vecMulVec y (star y) * V.J).map toAdele := by
    ext1 i j
    simp [m_eq, Space.vecAtPoint, star_mulVec, -coe_units_inv, vecMulVec_mul, mul_sub,
      mul_vecMulVec, sub_mul, ← Space.map_J, vecMul_apply_eq_sum, one_apply, vecMulVec_apply,
      apply_ite toAdele]
  exact fun i j ↦ ⟨_, (Matrix.ext_iff.2 h_conj i j).symm⟩

/-- Let `m = 1 - p Y Y^* S`, with `S = stdForm E s`, preserve `S`. If the finite components of `Y`
are integral (in `Ô E`), the finite part of `ofMatrix m hm` lies in the principal level `p`
(integral and congruent to `1` modulo `p`). -/
lemma New.Rows.ofMatrix_transvection_snd_mem_principalLevel {E n : Type} [Field E] [CMType E]
    [Fintype n] [DecidableEq n] {s : n → ℤˣ} {Y : n → 𝔸 E} {p : 𝓞 E} (hY : ∀ i : n, (Y i).2 ∈ Ô E)
    {m : Matrix n n (𝔸 E)} (hm : mᴴ * stdForm E s * m = stdForm E s)
    (m_eq : m = 1 - toAdele p.val • vecMulVec Y (star Y) * stdForm E s) :
    (ofMatrix m hm).2 ∈ principalLevel n p := by
  have h_int (i j : n) : (Y i).2 * star (Y j).2 ∈ Ô E := mul_mem (hY i) (star_mem_Ô (hY j))
  have h_entry (i j : n) : ((ofMatrix m hm).2.val : Matrix n n (𝔸f E)) i j =
      (1 : Matrix n n (𝔸f E)) i j - algebraMap (𝓞 E) (𝔸f E) p * ((Y i).2 * star (Y j).2) := by
    simp [m_eq, stdForm, one_apply, apply_ite snd, vecMulVec_mul, ← adeleMatrix_snd,
      vecMulVec_apply,
      vecMul_diagonal, ← coe_algebraMap_Ô]
    rfl
  refine ⟨mem_stdLevel.2 fun i j ↦ ?_, fun i j ↦
    ⟨-((Y i).2 * star (Y j).2), neg_mem (h_int i j), ?_⟩⟩
  · rw [h_entry]
    exact sub_mem (by simp [one_apply, ite_mem]) (mul_mem (algebraMap (𝓞 E) (Ô E) p).2 (h_int i j))
  · simp [h_entry]

/-- Peaks of a holomorphic form lie away from the cusp. The order `o` puts the signs `+1` first. Let
`F` on the adelic unitary group `G E s` be left invariant under the rational points `V.Γ` of the
space `V`. Let it be holomorphic at every translate (`IsAdelicHol`) of a weight `u` with gap `1`
(`u w i + 1 ≤ u w j` when `s i = 1`, `s j = -1`) and entries in `[-A, A]`, `A ≥ 2`. Let it be right
invariant under the principal level `p`, where `p = -p̄` and `im (Φ w p) ∈ (0, A']` for the
embedding `Φ w` at each infinite place `w`, `A' ≥ 1`. Then at a peak `g` of `F` (where `|F g|`
exceeds half the supremum of `|F|`), the first minimum of the moved space `V.move g` is at least
`(A A')^(-1/2)`. This first minimum is the length, in the norm of `archCoords`, of the shortest
nonzero vector of `baseLattice`, cut off at `1`. -/
theorem New.Rows.IsPeak.le_firstMinimum {E n : Type} [Field E] [CMType E] [Fintype n]
    [DecidableEq n] [Nonempty n] {s : n → ℤˣ} {V : Space E n s} {o : n → ℤ}
    {u : InfinitePlace E → n → ℤ} {F : G E s → ℂ} {g : G E s} (hg : IsPeak F g) (A A' : ℝ)
    {p : 𝓞 E} (ho : IsPosFirstOrder s o)
    (h_gap : ∀ w : InfinitePlace E, HasHolGap s (u w) 1)
    (h_wt : ∀ (w : InfinitePlace E) (i : n), |(u w i : ℝ)| ≤ A) (hA : 2 ≤ A) (hA' : 1 ≤ A')
    (hp : star p = -p) (hp_im : ∀ w : InfinitePlace E, (Φ w p.val).im ∈ Set.Ioc 0 A')
    (h_rat : ∀ γ ∈ V.Γ, ∀ x : G E s, F (γ * x) = F x)
    (h_level : ∀ k ∈ principalLevel n p, ∀ x : G E s, F (x * (1, k)) = F x)
    (h_hol : IsAdelicHol o u F) : (√(A * A'))⁻¹ ≤ (V.move g).firstMinimum := by
  -- If the first minimum at `g` is small, a short lattice vector is isotropic, and the transvection
  -- along it fixes `F (g ·)`. The Schwarz lemma then makes `F g` too small for a peak.
  let C : ℝ := ⨆ x, ‖F x‖
  have le_sup (x : G E s) : ‖F x‖ ≤ C := le_ciSup hg.bddAbove x
  have C_pos : 0 < C := (norm_pos_iff.2 hg.ne_zero).trans_le (le_sup g)
  have le_one : (√(A * A'))⁻¹ ≤ 1 := by
    grw [← hA, ← hA']
    bound
  refine le_firstMinimum_iff.2 ⟨le_one, fun y hy hy₀ ↦ ?_⟩
  by_contra! short
  -- a lattice vector `y` of length less than `1` is isotropic; `Y` are its coordinates at `g`
  set Y : n → 𝔸 E := (V.move g).vecAtPoint y
  have iso : star Y ⬝ᵥ stdForm E s *ᵥ Y = 0 := by
    rw [stdForm_vecAtPoint, form_eq_zero_of_norm_mul_lt_one hy hy
      (by grw [← sq, short, le_one, one_pow]), map_zero]
  replace short : ∑ w, ∑ i, ‖(Y i).1 w‖ ^ 2 < A'⁻¹ * A⁻¹ := by
    simpa [lt_sqrt, Space.archCoords, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
      ← sqrt_inv] using short
  replace hy (i : n) : (Y i).2 ∈ Ô E := hy i
  -- the transvection `t`: `g * t * g⁻¹` is rational and the finite part of `t` has level `p`
  let m : Matrix n n (𝔸 E) := 1 - toAdele p.val • vecMulVec Y (star Y) * stdForm E s
  have m_unitary : mᴴ * stdForm E s * m = stdForm E s := by
    simp [m, add_mul, *, vecMulVec_mul, ← coe_star_ringOfIntegers, star_vecMul, mul_sub,
      mul_vecMulVec, vecMulVec_mulVec, ← dotProduct_mulVec]
  let t : G E s := ofMatrix m m_unitary
  have t_rat : g * t * g⁻¹ ∈ V.Γ :=
    (V.mem_move_Gamma g).1 (ofMatrix_transvection_mem_Gamma _ y p.val m_unitary rfl)
  have t_cong : t.2 ∈ principalLevel n p :=
    ofMatrix_transvection_snd_mem_principalLevel hy m_unitary rfl
  have t_fix (h : GInf E s) : F (g * (t.1 * h, 1)) = F (g * (h, 1)) := by
    have t_split : t * ((h, 1) * (1, t.2⁻¹)) = (t.1 * h, 1) := by simp [t.mul_def]
    calc F (g * (t.1 * h, 1)) = F (g * t * g⁻¹ * (g * (h, 1) * (1, t.2⁻¹))) := by
          simp [← t_split, mul_assoc]
      _ = F (g * (h, 1) * (1, t.2⁻¹)) := h_rat _ t_rat _
      _ = F (g * (h, 1)) := h_level _ (inv_mem t_cong) _
  have re_eq (w : InfinitePlace E) : (Φ w p.val).re = 0 := self_eq_neg.1 <| by
    simpa [coe_star_ringOfIntegers] using congr_arg (fun q : 𝓞 E ↦ (Φ w q.val).re) hp
  have iso_inf (w : InfinitePlace E) :
      star (fun i ↦ (Y i).1 w) ⬝ᵥ signMatrix s *ᵥ (fun i ↦ (Y i).1 w) = 0 := by
    simp [← stdForm_dotProduct_fst, iso]
  have size_pos (w : InfinitePlace E) : 0 < (Φ w p.val).im * ∑ i, ‖(Y i).1 w‖ ^ 2 := by
    simpa [ne_iff, (hp_im w).1, sq_pos_iff, sum_pos_iff_of_nonneg]
      using eq_zero_of_vecAtPoint_fst_eq_zero.mt hy₀
  have size_sum : A * ∑ w, (Φ w p.val).im * ∑ i, ‖(Y i).1 w‖ ^ 2 ≤ 1 := by
    grw [(hp_im _).2, ← mul_sum, short]
    simp [field]
  have t_eq (w : InfinitePlace E) : ((t.1 w : USign s) : Matrix n n ℂ) =
      1 - Φ w p.val • vecMulVec (fun i ↦ (Y i).1 w) (star fun i ↦ (Y i).1 w) * signMatrix s := by
    simp [← ext_iff, t, m, stdForm, signMatrix, one_apply, apply_ite, ite_apply,
      ← adeleMatrix_fst, vecMulVec_apply]
  have schwarz : ‖F g‖ ≤ C * exp (2 + -(2 * π)) := by
    simpa [Prod.mk_one_one] using norm_le_of_transvection_invariant ho h_gap h_wt hA (h_hol g)
      (fun h ↦ le_sup _) C_pos re_eq iso_inf size_pos size_sum t_eq t_fix
  -- so `C / 2 < ‖F g‖ ≤ C * exp (2 - 2 π) ≤ C / e < C / 2`
  nlinarith [hg.half_lt,
    exp_neg_one_lt_half.trans_le' (show exp (2 + -(2 * π)) ≤ exp (-1) by bound [two_le_pi])]
