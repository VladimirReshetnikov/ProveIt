import FabiusFunction.GeneralizedRvachevEntire
import FabiusFunction.BaselineDecay
import FabiusFunction.LobeSignLaw

/-!
# `Φ_a` is bounded by one on the real axis

The volume reads `Φ_a` as the characteristic function of a random
variable `X_a`, and the corpus has two of the three properties that
reading requires: `Φ_a(0) = 1`
(`Fabius.generalizedRvachevProduct_at_zero`) and continuity, from
entirety (`FabiusFunction.GeneralizedRvachevEntire`).  The third,

`‖Φ_a(x)‖ ≤ 1`  for every real `x`,

was missing, at every weight including the constant one.  It is
proved here.

The estimate is termwise and needs nothing analytic beyond a limit:
each real-argument sinc has modulus at most one
(`Fabius.norm_complexSinc_ofReal_le_one`), raising to `a h` keeps that,
so every finite subproduct is bounded by one, and the bound passes to
the limit of the subproducts.  What makes the last step available is
that the factors are `Multipliable`
(`Fabius.generalizedSincFactors_multipliable`), which is where
admissibility enters — it is the only hypothesis.

Two consequences worth stating separately.  The real canonical
product inherits the bound, since it *is* `Φ_a` on the reals
(`Fabius.generalizedRvachevProduct_ofReal_eq_canonicalRealProduct`);
and the bound is attained, at `x = 0`, so it is sharp with no room to
spare.

* `Fabius.prod_norm_generalizedSincFactor_ofReal_le_one` — the finite
  products of factor norms are bounded by one;
* `Fabius.norm_generalizedRvachevProduct_ofReal_le_one` — **the
  bound**;
* `Fabius.abs_canonicalRealProduct_le_one` — the same for the real
  canonical product;
* `Fabius.norm_generalizedRvachevProduct_ofReal_zero` — the bound is
  attained at `x = 0`, so it is sharp.  Where else it is attained is
  not addressed: that is a statement about the modulus on the open
  lobes, and nothing here bounds `Φ_a` away from `1` there.
-/

set_option autoImplicit false

open Filter Topology

namespace Fabius

/-- Every finite subproduct of real-argument sinc factors has modulus
at most one, since every factor does. -/
theorem prod_norm_generalizedSincFactor_ofReal_le_one (a : ℕ → ℕ)
    (x : ℝ) (s : Finset ℕ) :
    ∏ h ∈ s, ‖complexSinc ((Real.pi : ℂ) * ((x : ℝ) : ℂ) /
        (2 : ℂ) ^ h) ^ a h‖ ≤ 1 := by
  refine Finset.prod_le_one (fun h _ => norm_nonneg _) fun h _ => ?_
  rw [norm_pow]
  refine pow_le_one₀ (norm_nonneg _) ?_
  have harg : (Real.pi : ℂ) * ((x : ℝ) : ℂ) / (2 : ℂ) ^ h
      = ((Real.pi * x / 2 ^ h : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg]
  exact norm_complexSinc_ofReal_le_one _

/-- **`Φ_a` is bounded by one on the real axis.**

The finite subproducts are bounded by one and converge to `Φ_a(x)`,
so the bound passes to the limit.  Admissibility is used only to know
that they converge. -/
theorem norm_generalizedRvachevProduct_ofReal_le_one (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) (x : ℝ) :
    ‖generalizedRvachevProduct a ((x : ℝ) : ℂ)‖ ≤ 1 := by
  have hmul := generalizedSincFactors_multipliable a ha ((x : ℝ) : ℂ)
  have hprod : HasProd
      (fun h : ℕ => complexSinc ((Real.pi : ℂ) * ((x : ℝ) : ℂ) /
        (2 : ℂ) ^ h) ^ a h)
      (generalizedRvachevProduct a ((x : ℝ) : ℂ)) := by
    rw [generalizedRvachevProduct]
    exact hmul.hasProd
  have hnorm := hprod.norm
  refine le_of_tendsto hnorm ?_
  exact Eventually.of_forall
    (prod_norm_generalizedSincFactor_ofReal_le_one a x)

/-- The real canonical product is bounded by one, being `Φ_a` on the
reals. -/
theorem abs_canonicalRealProduct_le_one (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) (x : ℝ) :
    |canonicalRealProduct a x| ≤ 1 := by
  have hb := norm_generalizedRvachevProduct_ofReal_le_one a ha x
  rw [generalizedRvachevProduct_ofReal_eq_canonicalRealProduct a ha x,
    Complex.norm_real, Real.norm_eq_abs] at hb
  exact hb

/-- The bound is attained: `‖Φ_a(0)‖ = 1`.  So `Φ_a` on the reals has
exactly the shape a characteristic function must: value `1` at the
origin, modulus at most `1` everywhere, and continuous. -/
theorem norm_generalizedRvachevProduct_ofReal_zero (a : ℕ → ℕ) :
    ‖generalizedRvachevProduct a (((0 : ℝ) : ℝ) : ℂ)‖ = 1 := by
  rw [Complex.ofReal_zero, generalizedRvachevProduct_at_zero]
  exact norm_one

end Fabius
