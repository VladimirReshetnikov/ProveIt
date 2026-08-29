import FabiusFunction.GeneralizedRvachevEntire
import FabiusFunction.NewtonBasisGeneratingFunction
import FabiusFunction.ThueMorseMoments

/-!
# The alternating Newton family `Ψ_d` and its zero orders

The exponents volume builds, for even `d ≥ 0`, the weight

`P_d(h) = C(h-1, d)`,  with the convention `C(-1, d) = (-1)^d = 1`,

and sets `Ψ_d = Φ_{P_d}`.  The parity restriction on `d` is exactly
what makes the `h = 0` exponent nonnegative, so that `P_d` is a
genuine `ℕ`-valued weight and `Ψ_d` a genuine transform; in `ℕ` the
convention is not a convention at all but the definition
`P_d(0) = 1`, `P_d(h+1) = C(h, d)`, which is what
`Fabius.alternatingNewtonWeight` records.  Nothing below needs `d`
even: the `ℕ`-valued weight exists for every `d`, and the parity
enters only when one asks whether it agrees with the volume's
signed formula.

The volume's boxed display

`ord_{z=n} Ψ_d(z) = 1 + C(v₂(n), d+1)`,  `n ≥ 1`

was recorded as unformalized apart from its hockey-stick step.  It is
proved here, in both halves `z = ±n`.  Two ingredients that did not
exist when the volume was written make it a short argument: the order
of vanishing at a general admissible weight
(`FabiusFunction.GeneralizedRvachevEntire`) and the multiplicity
calculus of `FabiusFunction.WeightedScaleMultiplicity`.  What is left
is the exclusive-form hockey-stick identity

`∑_{k < v} C(k, d) = C(v, d+1)`,

which the corpus already carries as
`Fabius.sum_range_choose_eq_choose_succ`
(`FabiusFunction.ThueMorseMoments`), proved there for the binomial
moments of the Thue--Morse signs.  It is the right form here because
the `h = 0` term is split off first: the inclusive form
`Fabius.inclusivePrefixSum_choose` would need a `v ≥ 1` side
condition, while the exclusive one is correct at `v = 0` as well, both
sides vanishing.

* `Fabius.alternatingNewtonWeight` — the weight `P_d`, and
  `alternatingNewtonWeight_zero`, `_succ` for its two clauses;
* `Fabius.summable_alternatingNewtonWeight` — it is admissible, so
  `Ψ_d` is defined, entire, and has the zero structure below;
* `Fabius.weightedScaleMultiplicity_alternatingNewton` —
  **`m_{P_d}(n) = 1 + C(v₂(n), d+1)`**, the arithmetic half of the
  display, at every `n` including `n = 0`;
* `Fabius.analyticOrderAt_alternatingNewton`,
  `Fabius.analyticOrderAt_alternatingNewton_neg` — **the display**,
  at `z = n` and at `z = -n`.

The spectral zeta and the cumulants of the same theorem are not
addressed here.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ## The weight `P_d` -/

/-- The volume's `P_d(h) = C(h-1, d)`, as a `ℕ`-valued weight.  The
exceptional value `P_d(0) = C(-1,d) = (-1)^d = 1` is available in `ℕ`
only because `d` is even in the volume; here it is simply the
definition of the `h = 0` clause. -/
def alternatingNewtonWeight (d h : ℕ) : ℕ :=
  if h = 0 then 1 else (h - 1).choose d

/-- The alternating Newton weight has exceptional value one at height zero. -/
@[simp]
theorem alternatingNewtonWeight_zero (d : ℕ) :
    alternatingNewtonWeight d 0 = 1 := rfl

/-- At positive height, the alternating Newton weight is the corresponding
binomial coefficient. -/
@[simp]
theorem alternatingNewtonWeight_succ (d h : ℕ) :
    alternatingNewtonWeight d (h + 1) = h.choose d := by
  rw [alternatingNewtonWeight, if_neg (Nat.succ_ne_zero h),
    Nat.succ_sub_one]

/-- `P_d` is admissible, so `Ψ_d = Φ_{P_d}` is defined and, by
`FabiusFunction.GeneralizedRvachevEntire`, entire.  Binomial
coefficients grow polynomially in `h`, which the corpus's
`Fabius.summable_choose_mul_pow` already dominates against `q ^ h` for
`|q| < 1`; the exceptional `h = 0` term is absorbed by shifting the
index. -/
theorem summable_alternatingNewtonWeight (d : ℕ) :
    Summable fun h : ℕ => (alternatingNewtonWeight d h : ℝ) / 2 ^ h := by
  have hq : |(1 / 2 : ℝ)| < 1 := by
    rw [abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    norm_num
  have hbase := (summable_choose_mul_pow hq d).mul_left (1 / 2 : ℝ)
  have hshift : Summable fun k : ℕ =>
      (alternatingNewtonWeight d (k + 1) : ℝ) / 2 ^ (k + 1) := by
    refine hbase.congr fun k => ?_
    rw [alternatingNewtonWeight_succ]
    rw [div_pow, one_pow, pow_succ]
    field_simp
  exact (summable_nat_add_iff
    (f := fun h : ℕ => (alternatingNewtonWeight d h : ℝ) / 2 ^ h)
    1).mp hshift

/-! ## The multiplicity and the order of vanishing -/

/-- **The arithmetic half of the volume's display.**

`m_{P_d}(n) = 1 + C(v₂(n), d+1)`.

The prefix sum splits off its `h = 0` term, which is `1`, and the
remaining `∑_{k < v₂(n)} C(k,d)` is the exclusive hockey stick.  No
hypothesis on `n`: at `n = 0` the convention `v₂(0) = 0` makes both
sides `1`. -/
theorem weightedScaleMultiplicity_alternatingNewton (d n : ℕ) :
    weightedScaleMultiplicity 2 (alternatingNewtonWeight d) n
      = 1 + (padicValNat 2 n).choose (d + 1) := by
  rw [weightedScaleMultiplicity, inclusivePrefixSum,
    Finset.sum_range_succ']
  simp only [alternatingNewtonWeight_zero, alternatingNewtonWeight_succ]
  rw [sum_range_choose_eq_choose_succ (padicValNat 2 n) d]
  exact Nat.add_comm _ _

/-- **The volume's boxed display**, `ord_{z=n} Ψ_d = 1 + C(v₂(n), d+1)`
for `n ≥ 1`.

`FabiusFunction.GeneralizedRvachevEntire` supplies the order at a
general admissible weight, and the multiplicity above evaluates it. -/
theorem analyticOrderAt_alternatingNewton (d : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    analyticOrderAt
        (generalizedRvachevProduct (alternatingNewtonWeight d))
        ((n : ℕ) : ℂ)
      = ((1 + (padicValNat 2 n).choose (d + 1) : ℕ) : ℕ∞) := by
  rw [analyticOrderAt_generalizedRvachevProduct_pos
    (alternatingNewtonWeight d) (summable_alternatingNewtonWeight d) hn,
    weightedScaleMultiplicity_alternatingNewton]

/-- The same at the reflected point `z = -n`. -/
theorem analyticOrderAt_alternatingNewton_neg (d : ℕ) {n : ℕ}
    (hn : 1 ≤ n) :
    analyticOrderAt
        (generalizedRvachevProduct (alternatingNewtonWeight d))
        (-((n : ℕ) : ℂ))
      = ((1 + (padicValNat 2 n).choose (d + 1) : ℕ) : ℕ∞) := by
  rw [analyticOrderAt_generalizedRvachevProduct_neg_pos
    (alternatingNewtonWeight d) (summable_alternatingNewtonWeight d) hn,
    weightedScaleMultiplicity_alternatingNewton]

/-- At an odd `n` the order is `1`: `v₂(n) = 0` and `C(0, d+1) = 0`.
This is the volume's remark that every `Ψ_d` has a simple zero at
every odd integer, uniformly in `d`. -/
theorem analyticOrderAt_alternatingNewton_odd (d : ℕ) {n : ℕ}
    (hn : 1 ≤ n) (hodd : ¬ 2 ∣ n) :
    analyticOrderAt
        (generalizedRvachevProduct (alternatingNewtonWeight d))
        ((n : ℕ) : ℂ) = 1 := by
  have hv : padicValNat 2 n = 0 := by
    by_contra hne
    exact hodd (dvd_of_one_le_padicValNat (Nat.one_le_iff_ne_zero.mpr hne))
  rw [analyticOrderAt_alternatingNewton d hn, hv,
    Nat.choose_zero_succ]
  rfl

end Fabius
