import ExponentialIdentities.TwoBaseIntegerExponent.MinPlusCeiling
import Mathlib.Data.ZMod.Basic

/-!
# Tropical initial forms of integer determinants

This module records the exact algebra behind cancellation among tied minimum-valuation
Leibniz terms.  If every unsigned Leibniz product has a common factor `p ^ τ`, the
determinant is that factor times the signed sum of the chosen quotients.  Consequently every
further `p`-power in the determinant is exactly a `p`-power in this signed quotient sum.

Unlike the unique-minimizer criterion in `MinPlusCeiling`, these results allow an arbitrary
tied fiber.  They are the algebraic bridge needed to analyze cancellation depth in the
semigroup determinants used for the Alaoglu--Erdős problem.
-/

namespace LeanProofs.TwoBaseIntegerExponent

/-- The signed sum of chosen quotients of the unsigned Leibniz products. -/
def signedLeibnizQuotientSum {n : Type*} [Fintype n] [DecidableEq n]
    (q : Equiv.Perm n → ℤ) : ℤ :=
  ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ : ℤ) * q σ

/-- Factoring a common power out of every Leibniz product factors the same power out of the
determinant. -/
theorem det_eq_pow_mul_signedLeibnizQuotientSum
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : Matrix n n ℤ) {p : ℤ} (tau : ℕ) (q : Equiv.Perm n → ℤ)
    (hq : ∀ σ : Equiv.Perm n, ∏ i, E (σ i) i = p ^ tau * q σ) :
    E.det = p ^ tau * signedLeibnizQuotientSum q := by
  classical
  rw [Matrix.det_apply']
  unfold signedLeibnizQuotientSum
  calc
    ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ : ℤ) * ∏ i, E (σ i) i =
        ∑ σ : Equiv.Perm n, p ^ tau * ((Equiv.Perm.sign σ : ℤ) * q σ) := by
          apply Finset.sum_congr rfl
          intro σ _
          rw [hq σ]
          ring
    _ = p ^ tau * ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ : ℤ) * q σ := by
      rw [Finset.mul_sum]

/-- **All-depth tropical cancellation criterion.**  Once `p ^ tau` has been factored from
every Leibniz product, divisibility of the determinant by the additional power `p ^ k` is
equivalent to divisibility of the signed quotient sum by `p ^ k`.

No uniqueness assumption is made: `q` may contain an arbitrary tied fiber of
minimum-valuation permutations, and terms from every higher layer. -/
theorem det_pow_add_dvd_iff_signedLeibnizQuotientSum_dvd
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : Matrix n n ℤ) {p : ℤ} (hp : p ≠ 0) (tau k : ℕ)
    (q : Equiv.Perm n → ℤ)
    (hq : ∀ σ : Equiv.Perm n, ∏ i, E (σ i) i = p ^ tau * q σ) :
    p ^ (tau + k) ∣ E.det ↔ p ^ k ∣ signedLeibnizQuotientSum q := by
  rw [det_eq_pow_mul_signedLeibnizQuotientSum E tau q hq, pow_add,
    mul_dvd_mul_iff_left (pow_ne_zero tau hp)]

/-- At a prime `p`, one further factor of `p` divides the determinant exactly when the signed
tropical initial form vanishes in `ZMod p`. -/
theorem det_pow_succ_dvd_iff_signedLeibnizQuotientSum_eq_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : Matrix n n ℤ) {p : ℕ} (hp : p.Prime) (tau : ℕ)
    (q : Equiv.Perm n → ℤ)
    (hq : ∀ σ : Equiv.Perm n, ∏ i, E (σ i) i = (p : ℤ) ^ tau * q σ) :
    (p : ℤ) ^ (tau + 1) ∣ E.det ↔
      (signedLeibnizQuotientSum q : ZMod p) = 0 := by
  rw [det_pow_add_dvd_iff_signedLeibnizQuotientSum_dvd E
      (by exact_mod_cast hp.ne_zero) tau 1 q hq,
    pow_one, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- Non-cancellation modulo a prime is equivalently exact attainment of the termwise lower
bound at the first layer. -/
theorem det_not_pow_succ_dvd_iff_signedLeibnizQuotientSum_ne_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : Matrix n n ℤ) {p : ℕ} (hp : p.Prime) (tau : ℕ)
    (q : Equiv.Perm n → ℤ)
    (hq : ∀ σ : Equiv.Perm n, ∏ i, E (σ i) i = (p : ℤ) ^ tau * q σ) :
    ¬ ((p : ℤ) ^ (tau + 1) ∣ E.det) ↔
      (signedLeibnizQuotientSum q : ZMod p) ≠ 0 := by
  exact not_congr (det_pow_succ_dvd_iff_signedLeibnizQuotientSum_eq_zero E hp tau q hq)

/-- Modulo `p`, every higher-layer Leibniz quotient disappears, so the signed quotient sum is
supported on any finite set containing all terms not divisible by `p`.  This set may be an
arbitrary tied minimum-cost fiber. -/
theorem signedLeibnizQuotientSum_mod_eq_tiedFiberSum
    {n : Type*} [Fintype n] [DecidableEq n]
    {p : ℕ} (q : Equiv.Perm n → ℤ) (S : Finset (Equiv.Perm n))
    (hhigher : ∀ σ : Equiv.Perm n, σ ∉ S → (p : ℤ) ∣ q σ) :
    (signedLeibnizQuotientSum q : ZMod p) =
      ∑ σ ∈ S, (((Equiv.Perm.sign σ : ℤ) * q σ : ℤ) : ZMod p) := by
  classical
  simp only [signedLeibnizQuotientSum, Int.cast_sum, Int.cast_mul]
  symm
  apply Finset.sum_subset (Finset.subset_univ S)
  intro σ _ hσ
  have hqzero : (q σ : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (hhigher σ hσ)
  simp [hqzero]

/-- **Tied-fiber first-layer criterion.**  If `S` contains all Leibniz quotients that survive
modulo the prime `p`, then one extra factor of `p` in the determinant is equivalent to
cancellation of their signed sum in `ZMod p`. -/
theorem det_pow_succ_dvd_iff_tiedFiberSum_eq_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : Matrix n n ℤ) {p : ℕ} (hp : p.Prime) (tau : ℕ)
    (q : Equiv.Perm n → ℤ) (S : Finset (Equiv.Perm n))
    (hq : ∀ σ : Equiv.Perm n, ∏ i, E (σ i) i = (p : ℤ) ^ tau * q σ)
    (hhigher : ∀ σ : Equiv.Perm n, σ ∉ S → (p : ℤ) ∣ q σ) :
    (p : ℤ) ^ (tau + 1) ∣ E.det ↔
      (∑ σ ∈ S, (((Equiv.Perm.sign σ : ℤ) * q σ : ℤ) : ZMod p)) = 0 := by
  rw [det_pow_succ_dvd_iff_signedLeibnizQuotientSum_eq_zero E hp tau q hq,
    signedLeibnizQuotientSum_mod_eq_tiedFiberSum q S hhigher]

/-- The canonical first tropical fiber: precisely the quotient terms that remain nonzero
modulo `p` after removal of the common factor. -/
def leibnizInitialFiber {n : Type*} [Fintype n] [DecidableEq n]
    (p : ℕ) (q : Equiv.Perm n → ℤ) : Finset (Equiv.Perm n) :=
  Finset.univ.filter fun σ ↦ ¬ ((p : ℤ) ∣ q σ)

/-- Membership in the canonical first tropical fiber means exactly nondivisibility of the
chosen quotient by `p`. -/
theorem mem_leibnizInitialFiber_iff {n : Type*} [Fintype n] [DecidableEq n]
    {p : ℕ} {q : Equiv.Perm n → ℤ} {sigma : Equiv.Perm n} :
    sigma ∈ leibnizInitialFiber p q ↔ ¬ ((p : ℤ) ∣ q sigma) := by
  classical
  simp [leibnizInitialFiber]

/-- Canonical first-layer form: the determinant gains one further factor of `p` exactly when
the signed sum over all and only the quotient terms surviving modulo `p` vanishes. -/
theorem det_pow_succ_dvd_iff_initialFiberSum_eq_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : Matrix n n ℤ) {p : ℕ} (hp : p.Prime) (tau : ℕ)
    (q : Equiv.Perm n → ℤ)
    (hq : ∀ σ : Equiv.Perm n, ∏ i, E (σ i) i = (p : ℤ) ^ tau * q σ) :
    (p : ℤ) ^ (tau + 1) ∣ E.det ↔
      (∑ σ ∈ leibnizInitialFiber p q,
        (((Equiv.Perm.sign σ : ℤ) * q σ : ℤ) : ZMod p)) = 0 := by
  apply det_pow_succ_dvd_iff_tiedFiberSum_eq_zero E hp tau q
    (leibnizInitialFiber p q) hq
  intro σ hσ
  simpa only [mem_leibnizInitialFiber_iff, Classical.not_not] using hσ

end LeanProofs.TwoBaseIntegerExponent
