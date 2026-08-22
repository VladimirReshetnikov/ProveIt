import ExponentialIdentities.TwoBaseIntegerExponent.TropicalInitialForm
import ExponentialIdentities.TwoBaseIntegerExponent.BlockFiberFactorization

/-!
# Applying the tropical initial form to a block-preserving tied fiber

This module composes the all-depth determinant quotient from
`TropicalInitialForm` with the abstract block factorization from
`BlockFiberFactorization`.
-/

namespace LeanProofs.TwoBaseIntegerExponent

/-- If every quotient outside the permutations preserving `b` is divisible by
`p`, and every block-preserving quotient is the corresponding Leibniz product
of `A`, then one extra factor of `p` divides `E.det` exactly when the product
of the block determinants of `A` vanishes modulo `p`.

Block-preserving quotients themselves may also vanish modulo `p`; the theorem
does not assert that this set is exactly the nonvanishing tropical fiber. -/
theorem det_pow_succ_dvd_iff_prod_blockDet_eq_zero
    {n o : Type*} [Fintype n] [DecidableEq n]
    [Fintype o] [DecidableEq o] [LinearOrder o]
    (E A : Matrix n n ℤ) (b : n → o) {p : ℕ} (hp : p.Prime) (tau : ℕ)
    (q : Equiv.Perm n → ℤ)
    (hq : ∀ sigma : Equiv.Perm n,
      ∏ i, E (sigma i) i = (p : ℤ) ^ tau * q sigma)
    (hhigher : ∀ sigma : Equiv.Perm n,
      sigma ∉ blockPreservingPermutations b → (p : ℤ) ∣ q sigma)
    (hfiber : ∀ sigma ∈ blockPreservingPermutations b,
      q sigma = ∏ i, A (sigma i) i) :
    (p : ℤ) ^ (tau + 1) ∣ E.det ↔
      (((∏ k : o, (A.toSquareBlock b k).det : ℤ) : ℤ) : ZMod p) = 0 := by
  classical
  have hsum :
      (∑ sigma ∈ blockPreservingPermutations b,
          (Equiv.Perm.sign sigma : ℤ) * q sigma) =
        ∏ k : o, (A.toSquareBlock b k).det := by
    calc
      (∑ sigma ∈ blockPreservingPermutations b,
          (Equiv.Perm.sign sigma : ℤ) * q sigma) =
          ∑ sigma ∈ blockPreservingPermutations b,
            (Equiv.Perm.sign sigma : ℤ) * ∏ i, A (sigma i) i := by
        apply Finset.sum_congr rfl
        intro sigma hsigma
        rw [hfiber sigma hsigma]
      _ = ∏ k : o, (A.toSquareBlock b k).det :=
        sum_blockPreserving_eq_prod_blockDet b A
  have hcast :
      (∑ sigma ∈ blockPreservingPermutations b,
          ((((Equiv.Perm.sign sigma : ℤ) * q sigma : ℤ)) : ZMod p)) =
        (((∏ k : o, (A.toSquareBlock b k).det : ℤ) : ℤ) : ZMod p) := by
    have hmap := congrArg (fun z : ℤ ↦ (z : ZMod p)) hsum
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_prod] using hmap
  rw [det_pow_succ_dvd_iff_tiedFiberSum_eq_zero E hp tau q
    (blockPreservingPermutations b) hq hhigher, hcast]

/-- The report-shaped consecutive-power application.  If all quotients outside
the block-preserving set are divisible by `p`, and the block-preserving
quotient products have the consecutive-power form `x_k(row)^column`, then one
additional factor of `p` divides the original determinant exactly when the
product of the within-block Vandermonde products vanishes modulo `p`. -/
theorem det_pow_succ_dvd_iff_prod_vandermonde_eq_zero
    {r : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    (E : Matrix (Fin r × o) (Fin r × o) ℤ)
    (x : o → Fin r → ℤ) {p : ℕ} (hp : p.Prime) (tau : ℕ)
    (q : Equiv.Perm (Fin r × o) → ℤ)
    (hq : ∀ sigma : Equiv.Perm (Fin r × o),
      ∏ i, E (sigma i) i = (p : ℤ) ^ tau * q sigma)
    (hhigher : ∀ sigma : Equiv.Perm (Fin r × o),
      sigma ∉ blockPreservingPermutations (Prod.snd : Fin r × o → o) →
        (p : ℤ) ∣ q sigma)
    (hfiber : ∀ sigma ∈ blockPreservingPermutations (Prod.snd : Fin r × o → o),
      q sigma = ∏ i : Fin r × o, (x i.2 (sigma i).1) ^ (i.1 : ℕ)) :
    (p : ℤ) ^ (tau + 1) ∣ E.det ↔
      (((∏ k : o, ∏ i : Fin r, ∏ j ∈ Finset.Ioi i, (x k j - x k i) : ℤ) : ℤ) :
        ZMod p) = 0 := by
  classical
  have hsum :
      (∑ sigma ∈ blockPreservingPermutations (Prod.snd : Fin r × o → o),
          (Equiv.Perm.sign sigma : ℤ) * q sigma) =
        ∏ k : o, ∏ i : Fin r, ∏ j ∈ Finset.Ioi i, (x k j - x k i) := by
    calc
      (∑ sigma ∈ blockPreservingPermutations (Prod.snd : Fin r × o → o),
          (Equiv.Perm.sign sigma : ℤ) * q sigma) =
          ∑ sigma ∈ blockPreservingPermutations (Prod.snd : Fin r × o → o),
            (Equiv.Perm.sign sigma : ℤ) *
              ∏ i : Fin r × o, (x i.2 (sigma i).1) ^ (i.1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro sigma hsigma
        rw [hfiber sigma hsigma]
      _ = ∏ k : o, ∏ i : Fin r, ∏ j ∈ Finset.Ioi i, (x k j - x k i) :=
        sum_blockPreserving_consecutivePowers_eq_prod_vandermonde x
  have hcast :
      (∑ sigma ∈ blockPreservingPermutations (Prod.snd : Fin r × o → o),
          ((((Equiv.Perm.sign sigma : ℤ) * q sigma : ℤ)) : ZMod p)) =
        (((∏ k : o, ∏ i : Fin r, ∏ j ∈ Finset.Ioi i,
          (x k j - x k i) : ℤ) : ℤ) : ZMod p) := by
    have hmap := congrArg (fun z : ℤ ↦ (z : ZMod p)) hsum
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_prod] using hmap
  rw [det_pow_succ_dvd_iff_tiedFiberSum_eq_zero E hp tau q
    (blockPreservingPermutations (Prod.snd : Fin r × o → o)) hq hhigher, hcast]

end LeanProofs.TwoBaseIntegerExponent
