import FabiusFunction.QPochhammerDissection
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# The central Gaussian coefficient in base `q²` and the reduction to `(q;q²)_k/(q²;q²)_k`

The elementary identities `(x;q)_n (-x;q)_n = (x²;q²)_n` (pairing each factor
with its sign-flipped twin) and the dissection `(q;q)_{2k} = (q;q²)_k (q²;q²)_k`
give the reduction

`[2k,k]_{q²} (q²;q²)_k = (q;q²)_k (-q;q)_{2k}`,

first as an identity in `ℤ[X]` by cancelling the nonzero polynomial `(X²;X²)_k`,
and then in every commutative ring by naturality.  Over a field where the
denominators do not vanish this is `[2k,k]_{q²}/(-q;q)_{2k} = (q;q²)_k/(q²;q²)_k`.

## Main declarations

* `finiteQPochhammerIn_mul_neg`: `(x;q)_n (-x;q)_n = (x²;q²)_n`.
* `finiteQPochhammerIn_two_mul`: `(q;q)_{2k} = (q;q²)_k (q²;q²)_k`.
* `finiteQPochhammerIn_map_ringHom`: naturality of the finite symbol.
* `central_gaussianBinomial_sq_mul`: the reduction, division-free.
* `central_gaussianBinomial_sq_div`: the reduction as a quotient.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Polynomial Finset

section Ring

variable {R : Type*} [CommRing R]

/-- `(x;q)_n (-x;q)_n = (x²;q²)_n`. -/
theorem finiteQPochhammerIn_mul_neg (x q : R) (n : ℕ) :
    finiteQPochhammerIn x q n * finiteQPochhammerIn (-x) q n =
      finiteQPochhammerIn (x ^ 2) (q ^ 2) n := by
  unfold finiteQPochhammerIn
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  rw [← pow_mul, mul_comm 2 j, pow_mul]
  ring

/-- The even/odd dissection `(q;q)_{2k} = (q;q²)_k (q²;q²)_k`. -/
theorem finiteQPochhammerIn_two_mul (q : R) (k : ℕ) :
    finiteQPochhammerIn q q (2 * k) =
      finiteQPochhammerIn q (q ^ 2) k * finiteQPochhammerIn (q ^ 2) (q ^ 2) k := by
  rw [finiteQPochhammerIn_dissection q q 2 k, prod_range_succ, prod_range_succ, prod_range_zero,
    one_mul, pow_zero, mul_one, pow_one, ← sq]

/-- Ring homomorphisms commute with the finite symbol. -/
theorem finiteQPochhammerIn_map_ringHom {S : Type*} [CommRing S] (φ : R →+* S) (a q : R)
    (n : ℕ) : φ (finiteQPochhammerIn a q n) = finiteQPochhammerIn (φ a) (φ q) n := by
  unfold finiteQPochhammerIn
  rw [map_prod]
  refine prod_congr rfl fun j _ => ?_
  rw [map_sub, map_one, map_mul, map_pow]

/-- The reduction in `ℤ[X]`: `[2k,k]_{X²} (X²;X²)_k = (X;X²)_k (-X;X)_{2k}`. -/
theorem central_gaussianBinomial_sq_mul_int (k : ℕ) :
    gaussianBinomial ((X : ℤ[X]) ^ 2) (2 * k) k * finiteQPochhammerIn ((X : ℤ[X]) ^ 2) (X ^ 2) k =
      finiteQPochhammerIn (X : ℤ[X]) (X ^ 2) k * finiteQPochhammerIn (-(X : ℤ[X])) X (2 * k) := by
  have hne : finiteQPochhammerIn ((X : ℤ[X]) ^ 2) (X ^ 2) k ≠ 0 := by
    unfold finiteQPochhammerIn
    refine prod_ne_zero_iff.mpr fun j _ => ?_
    intro h
    have := congrArg (eval (0 : ℤ)) h
    simp at this
  -- (X²;X²)_k · [2k,k]_{X²} = ((X²)^{k+1};X²)_k, and (X²;X²)_k · that = (X²;X²)_{2k}
  have h1 := finiteQPochhammerIn_self_mul_gaussianBinomial ((X : ℤ[X]) ^ 2)
    (Nat.le_mul_of_pos_left k two_pos)
  rw [show 2 * k - k + 1 = k + 1 by omega] at h1
  have h2 := finiteQPochhammerIn_add ((X : ℤ[X]) ^ 2) (X ^ 2) k k
  rw [← two_mul, ← pow_succ'] at h2
  -- (X²;X²)_{2k} = (X;X)_{2k} (-X;X)_{2k} = (X;X²)_k (X²;X²)_k (-X;X)_{2k}
  have h3 := finiteQPochhammerIn_mul_neg (X : ℤ[X]) X (2 * k)
  rw [finiteQPochhammerIn_two_mul] at h3
  refine mul_left_cancel₀ hne ?_
  calc finiteQPochhammerIn ((X : ℤ[X]) ^ 2) (X ^ 2) k *
        (gaussianBinomial ((X : ℤ[X]) ^ 2) (2 * k) k *
          finiteQPochhammerIn ((X : ℤ[X]) ^ 2) (X ^ 2) k)
      = finiteQPochhammerIn ((X : ℤ[X]) ^ 2) (X ^ 2) k *
          (finiteQPochhammerIn ((X : ℤ[X]) ^ 2) (X ^ 2) k *
            gaussianBinomial ((X : ℤ[X]) ^ 2) (2 * k) k) := by ring
    _ = finiteQPochhammerIn ((X : ℤ[X]) ^ 2) (X ^ 2) (2 * k) := by rw [h1, ← h2]
    _ = finiteQPochhammerIn ((X : ℤ[X]) ^ 2) (X ^ 2) k *
          (finiteQPochhammerIn (X : ℤ[X]) (X ^ 2) k *
            finiteQPochhammerIn (-(X : ℤ[X])) X (2 * k)) := by rw [← h3]; ring

/-- **The central reduction**, division-free, in every commutative ring:
`[2k,k]_{q²} (q²;q²)_k = (q;q²)_k (-q;q)_{2k}`. -/
theorem central_gaussianBinomial_sq_mul (q : R) (k : ℕ) :
    gaussianBinomial (q ^ 2) (2 * k) k * finiteQPochhammerIn (q ^ 2) (q ^ 2) k =
      finiteQPochhammerIn q (q ^ 2) k * finiteQPochhammerIn (-q) q (2 * k) := by
  have h := congrArg (eval₂RingHom (Int.castRingHom R) q) (central_gaussianBinomial_sq_mul_int k)
  simpa only [map_mul, map_gaussianBinomial, finiteQPochhammerIn_map_ringHom, map_pow, map_neg,
    coe_eval₂RingHom, eval₂_X] using h

end Ring

/-- **The central reduction as a quotient**, over a field with nonvanishing denominators:
`[2k,k]_{q²} / (-q;q)_{2k} = (q;q²)_k / (q²;q²)_k`. -/
theorem central_gaussianBinomial_sq_div {K : Type*} [Field K] (q : K) (k : ℕ)
    (h1 : finiteQPochhammerIn (-q) q (2 * k) ≠ 0)
    (h2 : finiteQPochhammerIn (q ^ 2) (q ^ 2) k ≠ 0) :
    gaussianBinomial (q ^ 2) (2 * k) k / finiteQPochhammerIn (-q) q (2 * k) =
      finiteQPochhammerIn q (q ^ 2) k / finiteQPochhammerIn (q ^ 2) (q ^ 2) k := by
  rw [div_eq_div_iff h1 h2, central_gaussianBinomial_sq_mul]

end Fabius
