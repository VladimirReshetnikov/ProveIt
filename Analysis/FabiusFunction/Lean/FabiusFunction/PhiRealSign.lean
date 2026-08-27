import FabiusFunction.LobeLogFactorization

/-!
# `Φ` is real on the real axis, with an explicit sign

Sharpening the factorization of `LobeLogFactorization` from `‖Φ‖` to
`Φ` itself.  Splitting the lattice product at the exceptional block
(`HasProd.mul_compl`, which needs only a commutative monoid — the
division-based `Finset.hasProd_compl_iff` is unavailable over `ℝ`)
gives, off the zero lattice,

`Φ(x) = (∏_{a ≤ |x|} (1 − x²/a²)) · exp(∑'_{a > |x|} log(1 − x²/a²))`,

a **real** number whose sign is that of the finite block: every one of
its factors is negative, so

`Φ(x) = (−1)^{#{a ≤ |x|}} · ‖Φ(x)‖`.

The split itself needs no hypothesis on `x`: at a lattice point the
finite block simply contains a vanishing factor.  So `Φ` is
real-valued on *all* of `ℝ`, and only the sign statement asks `x` to
avoid the lattice.

* `hasProd_real_factors` — the split product, every real `x`.
* `rvachevFourierProduct_ofReal_eq` — `Φ(x)` as a real cast.
* `im_rvachevFourierProduct_ofReal` — realness, unconditionally.
* `rvachevFourierProduct_eq_sign_mul_norm` — **the sign**.
-/

set_option autoImplicit false

open Filter Topology Real Set

namespace Fabius

/-- The lattice values are exactly the positive integers. -/
theorem exists_lobeZero_eq {n : ℕ} (hn : 1 ≤ n) :
    ∃ p : ℕ × ℕ, lobeZero p = (n:ℝ) := by
  refine ⟨(0, n - 1), ?_⟩
  simp only [lobeZero]
  have h : 2 ^ (0:ℕ) * ((n - 1) + 1) = n := by
    rw [pow_zero, one_mul, Nat.sub_add_cancel hn]
  exact_mod_cast congrArg (fun k : ℕ => (k:ℝ)) h

/-- **The split product**, valid at *every* real point: the real
lattice factors converge to the finite exceptional block times the
positive tail exponential.  At a lattice point the finite block
contains a vanishing factor, so the statement degenerates correctly to
`Φ = 0` rather than needing an off-lattice hypothesis. -/
theorem hasProd_real_factors (x : ℝ) :
    HasProd (fun p : ℕ × ℕ => 1 - x ^ 2 / (lobeZero p) ^ 2)
      ((∏ p ∈ lobeExceptional |x|, (1 - x ^ 2 / (lobeZero p) ^ 2)) *
        Real.exp (∑' p : {p : ℕ × ℕ // p ∉ lobeExceptional |x|},
          Real.log (1 - x ^ 2 / (lobeZero p.val) ^ 2))) := by
  have hfin := (lobeExceptional |x|).hasProd
    (fun p : ℕ × ℕ => 1 - x ^ 2 / (lobeZero p) ^ 2)
  have hpos : ∀ p : {p : ℕ × ℕ // p ∉ lobeExceptional |x|},
      0 < 1 - x ^ 2 / (lobeZero p.val) ^ 2 := fun p =>
    factor_pos_of_abs_lt
      (lt_lobeZero_of_not_mem (abs_nonneg x) p.property)
  have htail := Real.hasProd_of_hasSum_log hpos
    (summable_log_compl x).hasSum
  exact hfin.mul_compl htail

/-- **`Φ(x)` is the real cast of the split product**, at every real
point. -/
theorem rvachevFourierProduct_ofReal_eq (x : ℝ) :
    rvachevFourierProduct (x : ℂ) =
      (((∏ p ∈ lobeExceptional |x|, (1 - x ^ 2 / (lobeZero p) ^ 2)) *
        Real.exp (∑' p : {p : ℕ × ℕ // p ∉ lobeExceptional |x|},
          Real.log (1 - x ^ 2 / (lobeZero p.val) ^ 2)) : ℝ) : ℂ) := by
  have hmult : Multipliable fun p : ℕ × ℕ =>
      1 + sineTerm ((x : ℂ) / 2 ^ p.1) p.2 :=
    multipliable_one_add_of_summable
      (summable_norm_sineTerm_pair (x : ℂ))
  have hprodC : HasProd (fun p : ℕ × ℕ =>
      1 + sineTerm ((x : ℂ) / 2 ^ p.1) p.2)
      (rvachevFourierProduct (x : ℂ)) := by
    rw [rvachevFourierProduct_eq_tprod_pair]
    exact hmult.hasProd
  have hcast := (hasProd_real_factors x).map
    (⟨⟨fun r : ℝ => (r : ℂ), Complex.ofReal_one⟩,
      Complex.ofReal_mul⟩ : ℝ →* ℂ) Complex.continuous_ofReal
  have hcast' : HasProd (fun p : ℕ × ℕ =>
      1 + sineTerm ((x : ℂ) / 2 ^ p.1) p.2)
      (((∏ p ∈ lobeExceptional |x|,
        (1 - x ^ 2 / (lobeZero p) ^ 2)) *
        Real.exp (∑' p : {p : ℕ × ℕ // p ∉ lobeExceptional |x|},
          Real.log (1 - x ^ 2 / (lobeZero p.val) ^ 2)) : ℝ) : ℂ) := by
    have hstep : HasProd (fun p : ℕ × ℕ =>
        ((1 - x ^ 2 / (lobeZero p) ^ 2 : ℝ) : ℂ))
        (((∏ p ∈ lobeExceptional |x|,
          (1 - x ^ 2 / (lobeZero p) ^ 2)) *
          Real.exp (∑' p : {p : ℕ × ℕ // p ∉ lobeExceptional |x|},
            Real.log (1 - x ^ 2 / (lobeZero p.val) ^ 2)) : ℝ) : ℂ) :=
      hcast
    have hfun : (fun p : ℕ × ℕ =>
        ((1 - x ^ 2 / (lobeZero p) ^ 2 : ℝ) : ℂ)) =
        fun p : ℕ × ℕ => 1 + sineTerm ((x : ℂ) / 2 ^ p.1) p.2 :=
      funext fun p => (one_add_sineTerm_eq x p).symm
    rw [hfun] at hstep
    exact hstep
  exact hprodC.unique hcast'

/-- Every exceptional factor is negative off the lattice. -/
theorem factor_neg_of_mem_exceptional {x : ℝ}
    (hx : ∀ p : ℕ × ℕ, lobeZero p ≠ |x|) {p : ℕ × ℕ}
    (hp : p ∈ lobeExceptional |x|) :
    1 - x ^ 2 / (lobeZero p) ^ 2 < 0 :=
  factor_neg_of_lt_abs (lt_of_le_of_ne
    ((mem_lobeExceptional_iff (abs_nonneg x) p).mp hp) (hx p))

/-- **The sign of `Φ`**: off the zero lattice,
`Φ(x) = (−1)^{#{lattice points ≤ |x|}} · ‖Φ(x)‖`. -/
theorem rvachevFourierProduct_eq_sign_mul_norm {x : ℝ}
    (hx : ∀ p : ℕ × ℕ, lobeZero p ≠ |x|) :
    rvachevFourierProduct (x : ℂ) =
      (((-1 : ℝ) ^ (lobeExceptional |x|).card *
        ‖rvachevFourierProduct (x : ℂ)‖ : ℝ) : ℂ) := by
  set A : ℝ := ∏ p ∈ lobeExceptional |x|,
    (1 - x ^ 2 / (lobeZero p) ^ 2) with hA
  set B : ℝ := Real.exp (∑' p : {p : ℕ × ℕ //
    p ∉ lobeExceptional |x|},
    Real.log (1 - x ^ 2 / (lobeZero p.val) ^ 2)) with hB
  have hB0 : 0 < B := Real.exp_pos _
  have hΦ := rvachevFourierProduct_ofReal_eq x
  -- the norm reads off the same product
  have hnorm : ‖rvachevFourierProduct (x : ℂ)‖ = |A| * B := by
    rw [hΦ, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos hB0]
  -- the finite block carries the sign
  have hsign : A = (-1 : ℝ) ^ (lobeExceptional |x|).card * |A| := by
    rw [hA, Finset.abs_prod, ← Finset.prod_const,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    rw [abs_of_neg (factor_neg_of_mem_exceptional hx hp)]
    ring
  rw [hnorm, hΦ]
  congr 1
  rw [show (-1 : ℝ) ^ (lobeExceptional |x|).card * (|A| * B) =
    ((-1 : ℝ) ^ (lobeExceptional |x|).card * |A|) * B by ring,
    ← hsign]

/-- **`Φ` is real-valued on the whole real axis** — no off-lattice
hypothesis needed, since the split product is a real cast everywhere
(at a lattice point both sides vanish). -/
theorem im_rvachevFourierProduct_ofReal (x : ℝ) :
    (rvachevFourierProduct (x : ℂ)).im = 0 := by
  rw [rvachevFourierProduct_ofReal_eq x, Complex.ofReal_im]

/-- The real value of `Φ` on the real axis. -/
theorem rvachevFourierProduct_ofReal_re (x : ℝ) :
    ((rvachevFourierProduct (x : ℂ)).re : ℂ) =
      rvachevFourierProduct (x : ℂ) := by
  rw [rvachevFourierProduct_ofReal_eq x, Complex.ofReal_re]

end Fabius
