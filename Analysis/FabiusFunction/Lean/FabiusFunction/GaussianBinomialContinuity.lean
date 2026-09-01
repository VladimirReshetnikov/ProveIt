import FabiusFunction.GaussianBinomialAtOne
import FabiusFunction.QPochhammerInfinite
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Continuity of Gaussian coefficients in the base, and the classical limit

`gaussianBinomial q n k` is built from `q` by additions, multiplications and
powers only, so it is a continuous function of `q` in every topological
semiring.  Combined with the evaluation `[n,k]_1 = C(n,k)` this gives the
classical limit

`[n,k]_q → C(n,k)` as `q → 1`,

in any topological semiring, and in particular over `ℝ` and `ℂ`.  The
product form `[n,k]_q = (q^{n-k+1};q)_k / (q;q)_k` over a field with
`(q;q)_k ≠ 0` is recorded alongside.

## Main declarations

* `continuous_gaussianBinomial`: continuity in the base.
* `tendsto_gaussianBinomial_nhds_one`: the classical limit.
* `gaussianBinomial_eq_finiteQPochhammerIn_div`: the product form.
-/

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace Fabius

/-- Gaussian coefficients are continuous functions of the base. -/
theorem continuous_gaussianBinomial {R : Type*} [Semiring R] [TopologicalSpace R]
    [IsTopologicalSemiring R] (n k : ℕ) :
    Continuous fun q : R => gaussianBinomial q n k := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => simpa using continuous_const
      | succ k => simpa using continuous_const
  | succ n ih =>
      cases k with
      | zero => simpa using continuous_const
      | succ k =>
          simp only [gaussianBinomial_succ_succ]
          exact (ih (k + 1)).add ((continuous_id.pow _).mul (ih k))

/-- **The classical limit** `[n,k]_q → C(n,k)` as `q → 1`. -/
theorem tendsto_gaussianBinomial_nhds_one {R : Type*} [Semiring R] [TopologicalSpace R]
    [IsTopologicalSemiring R] (n k : ℕ) :
    Tendsto (fun q : R => gaussianBinomial q n k) (𝓝 1) (𝓝 (n.choose k : R)) := by
  have h := (continuous_gaussianBinomial (R := R) n k).tendsto 1
  rwa [gaussianBinomial_one_eq_natCast_choose] at h

/-- The product form `[n,k]_q = (q^{n-k+1};q)_k / (q;q)_k` for `k ≤ n` and
`(q;q)_k ≠ 0`. -/
theorem gaussianBinomial_eq_finiteQPochhammerIn_div {K : Type*} [Field K] {q : K} {n k : ℕ}
    (hk : k ≤ n) (hq : finiteQPochhammerIn q q k ≠ 0) :
    gaussianBinomial q n k = finiteQPochhammerIn (q ^ (n - k + 1)) q k / finiteQPochhammerIn q q k := by
  rw [eq_div_iff hq, mul_comm, finiteQPochhammerIn_self_mul_gaussianBinomial q hk]

end Fabius
