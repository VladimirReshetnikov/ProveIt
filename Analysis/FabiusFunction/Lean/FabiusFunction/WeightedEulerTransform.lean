import FabiusFunction.EulerLogTransform

/-!
# The Euler log transform with natural multiplicities

`EulerLogTransform` proves the branch-free exponential Euler product
formula

`∏' i, (1 - f i) = exp (-∑' r, (∑' i, f i ^ (r+1)) / (r+1))`

for a summable family of small factors.  Every generalized Rvachev
product carries *multiplicities* instead — its factors appear with
exponents `c i : ℕ` — and the transform does not apply to
`∏' i, (1 - f i) ^ (c i)` as stated.

Adding the multiplicity to the transform directly would raise a branch
question, since `log ((1 - x) ^ c) = c · log (1 - x)` is false in
general: the right side can leave the principal branch even when
`1 - x` does not.  The device that avoids it is to put the
multiplicity **into the index** rather than into the exponent.  Over

`Σ i, Fin (c i)`

the family is exponent-free, the existing transform applies verbatim,
and both sides convert back: the product because each fibre is a
constant finite product, the power sums because each fibre is a
constant finite sum.  No logarithm of a power is ever taken.

The summability hypothesis converts the same way, and that is the one
place the multiplicities are visible: a family is summable over the
sigma index exactly when the `c`-weighted family is summable over the
base (`summable_sigma_fin_iff`).

* `Fabius.summable_sigma_fin_iff` — the summability transfer;
* `Fabius.tprod_sigma_fin_eq_tprod_pow` — the product transfer;
* `Fabius.tsum_sigma_fin_eq_tsum_nsmul` — the sum transfer;
* `Fabius.tprod_one_sub_pow_eq_cexp_powerSum` — **the transform with
  multiplicities**.
-/

set_option autoImplicit false

namespace Fabius

variable {ι : Type*} [Countable ι]

/-! ## Transfers along the sigma index -/

/-- A nonnegative family is summable over `Σ i, Fin (c i)` exactly when
its `c`-weighted version is summable over the base.  Each fibre is
finite, so its inner sum is `c i • g i`. -/
theorem summable_sigma_fin_iff (c : ι → ℕ) {g : ι → ℝ}
    (hg : ∀ i, 0 ≤ g i) :
    (Summable fun s : Σ i : ι, Fin (c i) => g s.1)
      ↔ Summable fun i => (c i : ℝ) * g i := by
  rw [summable_sigma_of_nonneg (fun s => hg s.1)]
  constructor
  · rintro ⟨-, h2⟩
    refine h2.congr fun i => ?_
    rw [tsum_fintype]
    simp [Finset.sum_const, mul_comm]
  · intro h
    refine ⟨fun i => (hasSum_fintype _).summable, h.congr fun i => ?_⟩
    rw [tsum_fintype]
    simp [Finset.sum_const, mul_comm]

set_option maxHeartbeats 1000000 in
/-- The product over the sigma index is the product of powers over the
base: each fibre contributes the same factor `c i` times. -/
theorem tprod_sigma_fin_eq_tprod_pow (c : ι → ℕ) (f : ι → ℂ)
    (hm : Multipliable fun s : Σ i : ι, Fin (c i) => f s.1) :
    (∏' s : Σ i : ι, Fin (c i), f s.1) = ∏' i, f i ^ c i := by
  have hfib : ∀ i : ι, Multipliable fun _ : Fin (c i) => f i := fun i =>
    (hasProd_fintype (fun _ : Fin (c i) => f i)).multipliable
  have h1 : (∏' s : Σ i : ι, Fin (c i), f s.1)
      = ∏' (i : ι) (_ : Fin (c i)), f i :=
    Multipliable.tprod_sigma' hfib hm
  rw [h1]
  refine tprod_congr fun i => ?_
  rw [tprod_fintype]
  simp

set_option maxHeartbeats 1000000 in
/-- The sum over the sigma index is the `c`-weighted sum over the
base. -/
theorem tsum_sigma_fin_eq_tsum_nsmul (c : ι → ℕ) (f : ι → ℂ)
    (hs : Summable fun s : Σ i : ι, Fin (c i) => f s.1) :
    (∑' s : Σ i : ι, Fin (c i), f s.1)
      = ∑' i, (c i : ℂ) * f i := by
  have hfib : ∀ i : ι, Summable fun _ : Fin (c i) => f i := fun i =>
    (hasSum_fintype (fun _ : Fin (c i) => f i)).summable
  have h1 : (∑' s : Σ i : ι, Fin (c i), f s.1)
      = ∑' (i : ι) (_ : Fin (c i)), f i :=
    Summable.tsum_sigma' hfib hs
  rw [h1]
  refine tsum_congr fun i => ?_
  rw [tsum_fintype]
  simp [Finset.sum_const, mul_comm]

/-! ## The transform -/

/-- **The Euler product formula with natural multiplicities**:

`∏' i, (1 - f i) ^ (c i)
  = exp (-∑' r, (∑' i, c i · f i ^ (r+1)) / (r+1))`.

Branch-free, like its unweighted source: no logarithm of a power is
taken anywhere.  The multiplicity is carried by the index
`Σ i, Fin (c i)`, over which the family is exponent-free, and both
sides are transferred back along the fibres. -/
theorem tprod_one_sub_pow_eq_cexp_powerSum (c : ι → ℕ) (f : ι → ℂ)
    (hlt : ∀ i, ‖f i‖ < 1)
    (hsum : Summable fun i => (c i : ℝ) * ‖f i‖) :
    (∏' i, (1 - f i) ^ c i) =
      Complex.exp (-∑' r : ℕ,
        (∑' i, (c i : ℂ) * f i ^ (r + 1)) / ((r : ℂ) + 1)) := by
  set A : (Σ i : ι, Fin (c i)) → ℂ := fun s => f s.1 with hA
  have hAlt : ∀ s, ‖A s‖ < 1 := fun s => hlt s.1
  have hAsum : Summable fun s => ‖A s‖ :=
    (summable_sigma_fin_iff c (fun i => norm_nonneg (f i))).mpr hsum
  have hbase := tprod_one_sub_eq_cexp_powerSum (a := A) hAlt hAsum
  have hmul : Multipliable fun s : Σ i : ι, Fin (c i) => (1 - f s.1) := by
    have h := Complex.multipliable_one_add_of_summable hAsum.of_norm.neg
    exact h.congr fun s => (sub_eq_add_neg _ _).symm
  have hprod : (∏' s : Σ i : ι, Fin (c i), (1 - f s.1))
      = ∏' i, (1 - f i) ^ c i :=
    tprod_sigma_fin_eq_tprod_pow c (fun i => 1 - f i) hmul
  have hpow : ∀ r : ℕ,
      (∑' s : Σ i : ι, Fin (c i), A s ^ (r + 1))
        = ∑' i, (c i : ℂ) * f i ^ (r + 1) := by
    intro r
    have hsr : Summable fun s : Σ i : ι, Fin (c i) => f s.1 ^ (r + 1) := by
      refine Summable.of_norm ?_
      refine (summable_sigma_fin_iff c
        (fun i => norm_nonneg (f i ^ (r + 1)))).mpr ?_
      refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) hsum
      rw [norm_pow]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      exact pow_le_of_le_one (norm_nonneg _) (hlt i).le r.succ_ne_zero
    exact tsum_sigma_fin_eq_tsum_nsmul c (fun i => f i ^ (r + 1)) hsr
  rw [← hprod, hbase]
  congr 2
  exact tsum_congr fun r => by rw [hpow r]

end Fabius
