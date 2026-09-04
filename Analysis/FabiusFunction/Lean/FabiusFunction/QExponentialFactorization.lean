import FabiusFunction.QuantumBinomial
import FabiusFunction.QExponential

/-!
# The noncommutative factorization of the `q`-exponential

`cor:qexp-factor` ends with the assertion that, when `Y X = q X Y`,

`e_q(X + Y) = e_q(X) e_q(Y)`   as an identity of formal series in total degree,

and the monograph proves it by applying the noncommutative `q`-binomial theorem "degree by
degree".  This module carries that out.  Since the identity is asserted *in total degree*, the
faithful formalization is the degree-`n` component, which is `qExp_factor_degree`: it says
precisely that the degree-`n` part of `e_q(X+Y)` equals the degree-`n` part of the Cauchy product
of `e_q(X)` with `e_q(Y)`, with no analytic hypothesis and no formal-power-series construction
over a noncommutative ring.

The algebraic content is the scalar identity that the phrase "and use" in the source's proof
leaves implicit:

`[n,k]_q [k]_q! [n-k]_q! = [n]_q!`   for `k ≤ n`,

which is `gaussianBinomial_mul_qFactorial_mul_qFactorial`.  It is deduced here from the
division-free ring identity

`[n,k]_q (q;q)_k (q;q)_{n-k} = (q;q)_n`   (`gaussianBinomial_mul_finiteQPochhammer_mul`),

valid over *every* commutative ring with no hypothesis on `q` whatsoever — including `q = 0`, `q =
1` and roots of unity — which is the core identity
`finiteQPochhammerIn_self_eq_mul_mul_gaussianBinomial` with its factors reordered.  Only the
passage from Pochhammer symbols to `q`-factorials costs a hypothesis, namely `q ≠ 1`, since it
cancels `(1-q)^n`.

## Main declarations

* `gaussianBinomial_mul_finiteQPochhammer_mul` — over any commutative ring, unconditionally.
* `gaussianBinomial_mul_qFactorial_mul_qFactorial` — over a field, for `q ≠ 1`.
* `qExp_factor_degree` — the degree-`n` factorization, in any algebra over a field.

## Scope

Formalized: the degree-`n` identity, for arbitrary `X, Y` in an arbitrary `𝕜`-algebra subject only
to `Y * X = q • (X * Y)`, under the hypotheses that `q ≠ 1` and that the `q`-factorials up to `n`
are nonzero (both necessary: the statement divides by them).  Not formalized: any assembly of the
degree-wise identities into a single equation between formal series objects, which would require a
formal-power-series type over a noncommutative coefficient ring; and nothing here concerns the
analytic identities `e_q(x) = 1/((1-q)x;q)_∞` or `e_q(x)E_q(-x) = 1`, which are already in
`QExponential`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

section CommRing

variable {R : Type*} [CommRing R]

/-- **The division-free form.**  For `k ≤ n`, over every commutative ring and with no hypothesis
on `q`, `[n,k]_q (q;q)_k (q;q)_{n-k} = (q;q)_n`.  This is the statement the source's proof needs;
the `q`-factorial form below is a corollary that costs the hypothesis `q ≠ 1`. -/
theorem gaussianBinomial_mul_finiteQPochhammer_mul (q : R) {n k : ℕ} (hk : k ≤ n) :
    gaussianBinomial q n k *
        (finiteQPochhammerIn q q k * finiteQPochhammerIn q q (n - k)) =
      finiteQPochhammerIn q q n := by
  rw [finiteQPochhammerIn_self_eq_mul_mul_gaussianBinomial q hk]
  ring

end CommRing

section Field

variable {𝕜 : Type*} [Field 𝕜]

/-- **The scalar identity behind the factorization**: `[n,k]_q [k]_q! [n-k]_q! = [n]_q!` for
`k ≤ n` and `q ≠ 1`.  The source's proof of `cor:qexp-factor` uses it without stating it. -/
theorem gaussianBinomial_mul_qFactorial_mul_qFactorial {q : 𝕜} (hq : q ≠ 1) {n k : ℕ}
    (hk : k ≤ n) :
    gaussianBinomial q n k * (qFactorial q k * qFactorial q (n - k)) = qFactorial q n := by
  have h1 : (1 : 𝕜) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  have hpow : ((1 : 𝕜) - q) ^ k * ((1 : 𝕜) - q) ^ (n - k) = ((1 : 𝕜) - q) ^ n := by
    rw [← pow_add]
    congr 1
    omega
  have key := gaussianBinomial_mul_finiteQPochhammer_mul q hk
  rw [← qFactorial_mul_one_sub_pow q k, ← qFactorial_mul_one_sub_pow q (n - k),
    ← qFactorial_mul_one_sub_pow q n] at key
  have key' : gaussianBinomial q n k * (qFactorial q k * qFactorial q (n - k)) *
      ((1 : 𝕜) - q) ^ n = qFactorial q n * ((1 : 𝕜) - q) ^ n := by
    calc gaussianBinomial q n k * (qFactorial q k * qFactorial q (n - k)) * ((1 : 𝕜) - q) ^ n
        = gaussianBinomial q n k *
            (qFactorial q k * ((1 : 𝕜) - q) ^ k *
              (qFactorial q (n - k) * ((1 : 𝕜) - q) ^ (n - k))) := by
          rw [← hpow]; ring
      _ = qFactorial q n * ((1 : 𝕜) - q) ^ n := key
  exact mul_right_cancel₀ (pow_ne_zero n h1) key'

end Field

section Algebra

variable {𝕜 : Type*} [Field 𝕜] {A : Type*} [Ring A] [Algebra 𝕜 A]

/-- **The degree-`n` component of `e_q(X+Y) = e_q(X) e_q(Y)`** when `Y X = q X Y`.

This is exactly the assertion of `cor:qexp-factor` "as an identity of formal series in total
degree", read degree by degree: the left side is the degree-`n` term of `e_q(X+Y)` and the right
side is the degree-`n` term of the product of `e_q(X)` and `e_q(Y)`. -/
theorem qExp_factor_degree {q : 𝕜} (hq : q ≠ 1) {X Y : A} (h : Y * X = q • (X * Y)) (n : ℕ)
    (hfac : ∀ j, j ≤ n → qFactorial q j ≠ 0) :
    (qFactorial q n)⁻¹ • (X + Y) ^ n =
      ∑ k ∈ range (n + 1),
        ((qFactorial q (n - k))⁻¹ • X ^ (n - k)) * ((qFactorial q k)⁻¹ • Y ^ k) := by
  -- move to the image of `q` in `A`, where the noncommutative `q`-binomial theorem lives
  have hQX : Commute (algebraMap 𝕜 A q) X := Algebra.commutes q X
  have hQY : Commute (algebraMap 𝕜 A q) Y := Algebra.commutes q Y
  have h' : Y * X = algebraMap 𝕜 A q * (X * Y) := by rw [h, Algebra.smul_def]
  have hbin := quantum_binomial hQX hQY h' n
  rw [hbin, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hkn : n - k ≤ n := Nat.sub_le _ _
  have hfn : qFactorial q n ≠ 0 := hfac n le_rfl
  have hfk : qFactorial q k ≠ 0 := hfac k hk'
  have hfnk : qFactorial q (n - k) ≠ 0 := hfac (n - k) hkn
  -- the scalar coefficients agree
  have hcoeff : (qFactorial q n)⁻¹ * gaussianBinomial q n k =
      (qFactorial q (n - k))⁻¹ * (qFactorial q k)⁻¹ := by
    have hid := gaussianBinomial_mul_qFactorial_mul_qFactorial hq hk'
    field_simp
    linear_combination hid
  -- and the two sides are the same scalar acting on the same monomial
  have hQb : gaussianBinomial (algebraMap 𝕜 A q) n k =
      algebraMap 𝕜 A (gaussianBinomial q n k) :=
    (map_gaussianBinomial (algebraMap 𝕜 A) q n k).symm
  -- `A` is only a `Ring`, so `ring` is unavailable; the two steps are exactly `smul_smul`
  -- (collapsing an iterated scalar action) and `smul_mul_smul_comm` (pulling both scalars out
  -- of a product, which is where `Algebra.commutes` is really used).
  rw [hQb, ← Algebra.smul_def, smul_smul, hcoeff, smul_mul_smul_comm]

end Algebra

end Fabius
