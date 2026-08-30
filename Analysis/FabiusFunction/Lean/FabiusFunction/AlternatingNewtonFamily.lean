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

The spectral zeta and analytic cumulant kernel are not addressed in this
module; their downstream specializations are
`FabiusFunction.AlternatingNewtonZeta` and
`FabiusFunction.AlternatingNewtonCumulantKernel`, respectively.  The latter
is an analytic exponential identity, not a probabilistic cumulant theorem.
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

/-- The alternating Newton weight has the exceptional value one at height (scale) zero. -/
@[simp]
theorem alternatingNewtonWeight_zero (d : ℕ) :
    alternatingNewtonWeight d 0 = 1 := rfl

/-- At positive height (scale) `h + 1`, the alternating Newton weight is
`h.choose d`. -/
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

So every `Ψ_d` has a simple zero at every odd integer, uniformly in
`d`.  The volume does not state this in that generality; what it
states is the `d = 2` instance of it, inside the example recorded as
guards below. -/
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

/-! ## Guards against the volume's `d = 2` example

The volume works `d = 2` out by hand: it records the weight
`P_2 = (1, 0, 0, 1, 3, 6, 10, 15, …)`, states that every positive
integer with `v₂(n) ≤ 2` stays a simple zero, and prints the first
three larger zero orders — hence the corresponding multiplicities —
as `2` at `n = 8`, `5` at `n = 16`, `11` at `n = 32`.  Those numbers
were obtained independently of anything here, so checking the general
formula against them is a real test of it and not a restatement: they
are `1 + C(v₂ n, 3)` at `v₂ = 3, 4, 5`. -/

/-- The volume's `P_2 = (1, 0, 0, 1, 3, 6, 10, 15, …)`. -/
theorem alternatingNewtonWeight_two_values :
    alternatingNewtonWeight 2 0 = 1 ∧ alternatingNewtonWeight 2 1 = 0 ∧
      alternatingNewtonWeight 2 2 = 0 ∧ alternatingNewtonWeight 2 3 = 1 ∧
      alternatingNewtonWeight 2 4 = 3 ∧ alternatingNewtonWeight 2 5 = 6 ∧
      alternatingNewtonWeight 2 6 = 10 ∧
      alternatingNewtonWeight 2 7 = 15 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [alternatingNewtonWeight] <;> decide

/-- `v₂(2 ^ k) = k`, in the shape the three guards below need. -/
theorem padicValNat_two_pow (k : ℕ) : padicValNat 2 (2 ^ k) = k :=
  padicValNat_base_pow (by decide : 1 < 2) k

/-- **`m_{P_2}(8) = 2`**, the arithmetic multiplicity behind the
volume's first extra zero order. -/
theorem weightedScaleMultiplicity_alternatingNewton_two_eight :
    weightedScaleMultiplicity 2 (alternatingNewtonWeight 2) 8 = 2 := by
  rw [show (8 : ℕ) = 2 ^ 3 by norm_num,
    weightedScaleMultiplicity_alternatingNewton, padicValNat_two_pow]
  decide

/-- **`m_{P_2}(16) = 5`**, the corresponding arithmetic
multiplicity. -/
theorem weightedScaleMultiplicity_alternatingNewton_two_sixteen :
    weightedScaleMultiplicity 2 (alternatingNewtonWeight 2) 16 = 5 := by
  rw [show (16 : ℕ) = 2 ^ 4 by norm_num,
    weightedScaleMultiplicity_alternatingNewton, padicValNat_two_pow]
  decide

/-- **`m_{P_2}(32) = 11`**, the corresponding arithmetic
multiplicity. -/
theorem weightedScaleMultiplicity_alternatingNewton_two_thirtyTwo :
    weightedScaleMultiplicity 2 (alternatingNewtonWeight 2) 32 = 11 := by
  rw [show (32 : ℕ) = 2 ^ 5 by norm_num,
    weightedScaleMultiplicity_alternatingNewton, padicValNat_two_pow]
  decide

/-- The arithmetic guard behind the volume's simple-zero range at
`d = 2`: `v₂(n) ≤ 2` makes the weighted multiplicity `1`.  The
theorem also holds at `n = 0` under the corpus's valuation convention;
only for positive `n` may it be read as a simple-zero statement, via
`analyticOrderAt_alternatingNewton`. -/
theorem weightedScaleMultiplicity_alternatingNewton_two_of_le
    {n : ℕ} (hn : padicValNat 2 n ≤ 2) :
    weightedScaleMultiplicity 2 (alternatingNewtonWeight 2) n = 1 := by
  rw [weightedScaleMultiplicity_alternatingNewton,
    Nat.choose_eq_zero_of_lt (by omega)]

/-- The analytic-order form of
`weightedScaleMultiplicity_alternatingNewton_two_eight`. -/
theorem analyticOrderAt_alternatingNewton_two_eight :
    analyticOrderAt
        (generalizedRvachevProduct (alternatingNewtonWeight 2))
        ((8 : ℕ) : ℂ) = 2 := by
  rw [analyticOrderAt_alternatingNewton 2 (by norm_num : 1 ≤ 8),
    show padicValNat 2 8 = 3 by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat_two_pow]]
  rfl

end Fabius
