import FabiusFunction.SmoothingOperatorInversion
import FabiusFunction.ImplicitPowerSeries

/-!
# The algebraic inverse germ

The inverse volume's roadmap asks to *define the concrete polynomial
`𝒜_r(z,Q)` in Lean, verify the hypotheses of the delivered formal-root
engine, and instantiate the generic theorem*
(`PowerSeries.Implicit.existsUnique_zeroConstant_root` from
`ImplicitPowerSeries.lean`).  This module does that one level more
generally, for an arbitrary jet and arbitrary correction weights, so
that every inverse-dyadic instance is a specialization.

The data is a *jet* `J ∈ R[X]` (in the Fabius instance, the
terminating Taylor jet `J_r(z) = ∑_{k=1}^r α_{r,k} z^k` of `F` at
`x_r = 2^{-r}`) and a sequence of *correction weights* `b : ℕ → R`
(in the Fabius instance, the signed reciprocal-sinc coefficients
`(-1)^j b_j` with `b 0 = 1`).  Out of them we build

`germPolynomial b J = ∑_j b_j Q^j D^{2j}J(z)  ∈ (R⟦Q⟧)[z]` —

the volume's `𝒜_r(z,Q)` — not term by term but as one application of
the smoothing-operator calculus: the weights form the even series
`evenWeightSeries b = ∑_j b_j Q^j t^{2j}` over `R⟦Q⟧`, and the germ
polynomial is `seriesDerivOp` of that series acting on the jet.

* `constantCoeff_coeff_germPolynomial` — **the germ reduces to the
  jet at `Q = 0`**: `𝒜(z,0) = J(z)` coefficientwise, because every
  positive weight carries a positive power of `Q`.
* `existsUnique_germRoot` — for `b 0 = 1`, `J(0) = 0`, and `J'(0)` a
  unit, the germ polynomial has a **unique zero-constant formal root**
  `Δ(Q)`: `Δ(0) = 0` and `𝒜(Δ(Q),Q) = 0`.  This is the formal half of
  the volume's exact algebraic quantile germ theorem, with
  `Δ_r(4^{-n})` recovering `G_n(y_r) - x_r` analytically.
* `germRoot` — the distinguished root, with its defining equations.
* `germPolynomial_eq_sum` — the display form
  `𝒜 = ∑_{j=0}^{⌊r/2⌋} b_j Q^j (D^{2j}J)` for `deg J ≤ r`, matching
  the volume's `𝒜_r` definition verbatim.
* `dyadicGermTwo` — the first concrete Fabius instance `r = 2`:
  `J_2 = z + 4z²` (from `F(½) = ½`, `F(1) = 1`), signed weights
  `(1, -1/18)`, and its unique formal quantile germ.
-/

set_option autoImplicit false

open Polynomial PowerSeries Finset

namespace Fabius

variable {R : Type*} [CommRing R]

/-- The correction weights `b` as an even power series over `R⟦Q⟧`:
the coefficient of `t^{2j}` is `b j · Q^j`, and odd coefficients
vanish.  Substituting `t ↦ D` turns it into the volume's smoothing
correction operator `∑_j b_j Q^j D^{2j}`. -/
noncomputable def evenWeightSeries (b : ℕ → R) :
    PowerSeries (PowerSeries R) :=
  PowerSeries.mk fun m =>
    if Even m then PowerSeries.C (b (m / 2)) * PowerSeries.X ^ (m / 2)
    else 0

/-- The coefficient of `evenWeightSeries b` at index `m` is
`b (m / 2) · Q^(m / 2)` when `m` is even, and zero otherwise. -/
@[simp] theorem coeff_evenWeightSeries (b : ℕ → R) (m : ℕ) :
    PowerSeries.coeff m (evenWeightSeries b) =
      if Even m then PowerSeries.C (b (m / 2)) * PowerSeries.X ^ (m / 2)
      else 0 :=
  PowerSeries.coeff_mk _ _

/-- Every odd-indexed coefficient of `evenWeightSeries b` vanishes. -/
theorem coeff_evenWeightSeries_odd (b : ℕ → R) {m : ℕ} (hm : Odd m) :
    PowerSeries.coeff m (evenWeightSeries b) = 0 := by
  rw [coeff_evenWeightSeries, if_neg (Nat.not_even_iff_odd.mpr hm)]

/-- **The germ polynomial** `𝒜(z,Q) = ∑_j b_j Q^j D^{2j}J(z)`, as one
application of the smoothing-operator calculus to the jet. -/
noncomputable def germPolynomial (b : ℕ → R) (J : R[X]) :
    Polynomial (PowerSeries R) :=
  seriesDerivOp (evenWeightSeries b) 1 (J.map (PowerSeries.C))

/-- **The germ reduces to the jet at `Q = 0`**: every coefficient of
`germPolynomial b J` has parameter-constant part the corresponding
coefficient of `J`, because all positive weights carry positive powers
of `Q`. -/
theorem constantCoeff_coeff_germPolynomial (b : ℕ → R) (hb0 : b 0 = 1)
    (J : R[X]) (k : ℕ) :
    PowerSeries.constantCoeff ((germPolynomial b J).coeff k) =
      J.coeff k := by
  simp only [germPolynomial, seriesDerivOp]
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_smul, smul_eq_mul, one_pow, mul_one]
  rw [map_sum, Finset.sum_eq_single 0]
  · simp [Polynomial.coeff_map, hb0]
  · intro m _ hm
    rw [map_mul]
    rcases Nat.even_or_odd m with hme | hmo
    · obtain ⟨t, ht⟩ := hme
      rw [coeff_evenWeightSeries, if_pos ⟨t, ht⟩, map_mul, map_pow,
        PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X,
        zero_pow (by omega : m / 2 ≠ 0), mul_zero, zero_mul]
    · rw [coeff_evenWeightSeries_odd b hmo, map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h

/-- **The unique zero-constant formal root of the germ polynomial**:
for unit-normalized weights (`b 0 = 1`) and a jet vanishing at the
origin with unit linear coefficient, there is exactly one power series
`Δ(Q)` with `Δ(0) = 0` and `𝒜(Δ(Q),Q) = 0`. -/
theorem existsUnique_germRoot (b : ℕ → R) (hb0 : b 0 = 1) (J : R[X])
    (hJ0 : J.coeff 0 = 0) (hJ1 : IsUnit (J.coeff 1)) :
    ∃! S : PowerSeries R,
      PowerSeries.constantCoeff S = 0 ∧
        (germPolynomial b J).eval S = 0 :=
  PowerSeries.Implicit.existsUnique_zeroConstant_root _
    (by rw [constantCoeff_coeff_germPolynomial b hb0]; exact hJ0)
    (by rw [constantCoeff_coeff_germPolynomial b hb0]; exact hJ1)

/-- The distinguished formal quantile germ `Δ(Q)`. -/
noncomputable def germRoot (b : ℕ → R) (J : R[X]) (hb0 : b 0 = 1)
    (hJ0 : J.coeff 0 = 0) (hJ1 : IsUnit (J.coeff 1)) : PowerSeries R :=
  PowerSeries.Implicit.root (germPolynomial b J)
    (by rw [constantCoeff_coeff_germPolynomial b hb0]; exact hJ0)
    (by rw [constantCoeff_coeff_germPolynomial b hb0]; exact hJ1)

/-- The distinguished germ root has zero constant coefficient. -/
@[simp] theorem constantCoeff_germRoot (b : ℕ → R) (J : R[X])
    (hb0 : b 0 = 1) (hJ0 : J.coeff 0 = 0) (hJ1 : IsUnit (J.coeff 1)) :
    PowerSeries.constantCoeff (germRoot b J hb0 hJ0 hJ1) = 0 :=
  PowerSeries.Implicit.constantCoeff_root _ _ _

/-- Substituting the distinguished germ root into `germPolynomial b J`
gives zero. -/
@[simp] theorem eval_germRoot (b : ℕ → R) (J : R[X]) (hb0 : b 0 = 1)
    (hJ0 : J.coeff 0 = 0) (hJ1 : IsUnit (J.coeff 1)) :
    (germPolynomial b J).eval (germRoot b J hb0 hJ0 hJ1) = 0 :=
  PowerSeries.Implicit.eval_root _ _ _

/-- Every zero-constant root of the germ polynomial is the
distinguished germ. -/
theorem eq_germRoot (b : ℕ → R) (J : R[X]) (hb0 : b 0 = 1)
    (hJ0 : J.coeff 0 = 0) (hJ1 : IsUnit (J.coeff 1))
    {S : PowerSeries R} (hS0 : PowerSeries.constantCoeff S = 0)
    (hS : (germPolynomial b J).eval S = 0) :
    S = germRoot b J hb0 hJ0 hJ1 :=
  PowerSeries.Implicit.eq_root _ _ _ hS0 hS

/-- **The display form of the germ polynomial**: for a jet of degree
at most `r`, the operator sum truncates at `⌊r/2⌋` and
`𝒜 = ∑_{j=0}^{⌊r/2⌋} b_j Q^j (D^{2j}J)` — the volume's definition of
`𝒜_r(z,Q)` verbatim (with the signs carried inside `b`). -/
theorem germPolynomial_eq_sum (b : ℕ → R) (J : R[X]) {r : ℕ}
    (hJ : J.natDegree ≤ r) :
    germPolynomial b J =
      ∑ j ∈ Finset.range (r / 2 + 1),
        (PowerSeries.C (b j) * PowerSeries.X ^ j) •
          (derivative^[2 * j] J).map (PowerSeries.C) := by
  simp only [germPolynomial]
  rw [seriesDerivOp_eq_sum_even
    (fun k hk => coeff_evenWeightSeries_odd b hk) 1
    ((Polynomial.natDegree_map_le).trans hJ)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_evenWeightSeries, if_pos ⟨j, by ring⟩,
    Nat.mul_div_cancel_left j (by norm_num), one_pow, mul_one,
    Polynomial.iterate_derivative_map]

section DyadicInstance

/-- The `r = 2` terminating Fabius jet `J_2(z) = z + 4z²`: from the
dilation identity, `α_{2,1} = 2F(½) = 1` and
`α_{2,2} = 2³F(1)/2! = 4`. -/
noncomputable def dyadicJetTwo : Polynomial ℚ :=
  Polynomial.X + 4 • Polynomial.X ^ 2

/-- The signed reciprocal-sinc weights truncated for `r = 2`:
`b'_0 = 1`, `b'_1 = -b_1 = -1/18`. -/
def dyadicWeightsTwo : ℕ → ℚ := fun j =>
  if j = 0 then 1 else if j = 1 then -(1 / 18) else 0

/-- The quadratic `r = 2` dyadic jet has zero constant coefficient. -/
theorem dyadicJetTwo_coeff_zero : dyadicJetTwo.coeff 0 = 0 := by
  simp [dyadicJetTwo]

/-- The linear coefficient of the quadratic `r = 2` dyadic jet is one. -/
theorem dyadicJetTwo_coeff_one : dyadicJetTwo.coeff 1 = 1 := by
  simp [dyadicJetTwo]

/-- **The first concrete algebraic quantile germ** (`r = 2`): the
polynomial `𝒜_2(z,Q) = z + 4z² - (4/9)Q` has a unique zero-constant
formal root — the germ `Δ_2(Q)` whose value at `Q = 4^{-n}` is the
exact local inverse displacement `G_n(y_2) - x_2`. -/
theorem existsUnique_dyadicGermTwo :
    ∃! S : PowerSeries ℚ,
      PowerSeries.constantCoeff S = 0 ∧
        (germPolynomial dyadicWeightsTwo dyadicJetTwo).eval S = 0 :=
  existsUnique_germRoot dyadicWeightsTwo rfl dyadicJetTwo
    dyadicJetTwo_coeff_zero
    (by rw [dyadicJetTwo_coeff_one]; exact isUnit_one)

/-- The distinguished `r = 2` quantile germ `Δ_2(Q)`. -/
noncomputable def dyadicGermTwo : PowerSeries ℚ :=
  germRoot dyadicWeightsTwo dyadicJetTwo rfl dyadicJetTwo_coeff_zero
    (by rw [dyadicJetTwo_coeff_one]; exact isUnit_one)

end DyadicInstance

end Fabius
