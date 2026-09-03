import FabiusFunction.FiniteQBinomialCore
import FabiusFunction.GaussianBinomialAtOne
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# The formal q-binomial theorem in `A⟦X⟧`

This module proves the *formal* q-binomial theorem — Euler's product expansion, its
reciprocal, and the ratio expansion `(az;q)_∞/(z;q)_∞ = ∑ (a;q)_n z^n/(q;q)_n` — as an
identity of formal power series over an **arbitrary commutative ring** `A`.

## The printed statement and what replaces it

The source proposition assumes that `A` is complete and separated for the `I`-adic topology
with `q ∈ I`, and asserts that the coefficientwise `I`-adic infinite products are defined in
`A⟦z⟧`, that `(z;q)_∞` is a unit, that every `(q;q)_n` is a unit, and that
`(az;q)_∞/(z;q)_∞ = ∑_{n≥0} (a;q)_n z^n /(q;q)_n`.

That hypothesis enters the printed proof in exactly two places: it gives the infinite
products a meaning, as `I`-adic limits of the finite ones, and it makes each `1 - q^n`
invertible.  Here the products are instead *defined* by their Euler coefficient expansions,

* `qPochhammerSeries q = ∑_n (-1)^n q^{n choose 2} (q;q)_n⁻¹ z^n`, which is `(z;q)_∞`;
* `rescale a (qPochhammerSeries q)`, which is `(az;q)_∞`;

so only the invertibility is still needed, and it is isolated as the purely algebraic

`QRegular q : ∀ n, IsUnit (1 - q ^ (n + 1))`.

This is *derived* from the printed hypothesis (`qRegular_of_isAdicComplete`), so every result
below applies verbatim in the printed setting; the implication is strict, since `A = ℚ`,
`q = 2` is `QRegular` while no ideal `I` of `ℚ` has `2 ∈ I` with `ℚ` `I`-adically complete
(the only ideals are `⊥`, which omits `2`, and `⊤`, for which completeness forces `ℚ` to be
subsingleton).  Two further sources of `QRegular` come for free: `q` nilpotent
(`qRegular_of_isNilpotent`) and `q = X` in a power series ring (`qRegular_X`), the latter
giving verbatim the printed remark that the identity holds in `ℤ[a]⟦q⟧⟦z⟧`.

The defined series are tied to the honest finite products
`partialQPochhammer b q N = ∏_{j<N} (1 - b q^j z) = (bz;q)_N` by an **effective congruence**
(`dvd_coeff_partialQPochhammer_sub`): for `n ≤ N`,

`q ^ (N - n + 1) ∣ coeff n (bz;q)_N - coeff n (bz;q)_∞`.

This is the algebraic content of the printed (unproved) sentence that the partial products are
coefficientwise `I`-adically Cauchy with limits in `A⟦z⟧`: it gives an explicit modulus, it
implies the Cauchy property and identifies the limit with the Euler expansion, it yields the
`I`-adic form in one line (`coeff_partialQPochhammer_sub_mem_pow`), and it needs no hypothesis
on `A` beyond commutativity, no completeness, and no topology.

## Main declarations

* `IsQDifference b c q F` — the q-difference equation `(1 - cz) F(z) = (1 - bz) F(qz)`, the
  single predicate underlying both series; `isQDifference_iff` converts it to the coefficient
  recurrence `(1 - q^{n+1}) c_{n+1} = (c - b q^n) c_n`, `eq_of_isQDifference` is the
  uniqueness statement, `IsQDifference.rescale` is stability under `z ↦ tz`, and
  `IsQDifference.mul_shift` is the whole multiplicative step (no Cauchy product is ever
  unfolded).
* `qBinomialSeries a q` — the series `∑_n (a;q)_n z^n / (q;q)_n`; `qPochhammerSeries q` — the
  series `(z;q)_∞`; `isUnit_qPochhammerSeries` (**unconditional**) — `(z;q)_∞` is a unit;
  `isUnit_finiteQPochhammerIn_self` — every `(q;q)_n` is a unit.
* `qPochhammerSeries_mul_qBinomialSeries` — **the proposition**:
  `(z;q)_∞ · ∑_n (a;q)_n z^n/(q;q)_n = (az;q)_∞`, and `qBinomialSeries_eq_inverse_mul` its
  literal quotient form.
* `qPochhammerSeries_mul_qBinomialSeries_zero` — Euler's reciprocal identity, the case `a = 0`.
* `finiteQPochhammerIn_self_mul_coeff_of_isQDifference` — **stronger than print**: the
  division-free coefficient formula `(q;q)_n · c_n = (a;q)_n` follows from the functional
  equation and `c_0 = 1` alone, with *no* hypothesis on `q`; it is valid at roots of unity, in
  positive characteristic, and in the presence of zero divisors.
* `coeff_partialQPochhammer` (**no hypothesis relating `n` and `N`**),
  `dvd_coeff_partialQPochhammer_sub`, `coeff_partialQPochhammer_sub_mem_pow` — the finite
  products and the effective convergence.
* `qRegular_of_isAdicComplete`, `qRegular_of_le_jacobson_bot`, `qRegular_of_isNilpotent`,
  `qRegular_X` — sources of the hypothesis.

## What is NOT covered

* The infinite products are **not** obtained as topological limits: there is no `HasProd`,
  `Multipliable` or `∏'` in a topologised `A⟦z⟧` here, and no `PowerSeries.WithPiTopology`
  instance stack.  `(z;q)_∞` is defined by its Euler expansion and connected to the finite
  products only through the effective congruence above.  The printed phrase "the
  coefficientwise `I`-adic products are defined" is therefore formalised in its effective
  shape, not as convergence in a topological ring.
* Nothing here is stated for an `A` carrying an actual `I`-adic topology; `QRegular` and the
  divisibility statements are the algebraic shadow of that setting.  In particular
  `isUnit_qPochhammerSeries` says that the *defined* series is a unit; that it is the infinite
  product needs `QRegular q`, through `dvd_coeff_partialQPochhammer_sub`.
* No analytic content: the analytic q-binomial theorem over a complete normed field is
  `QBinomialTheoremInfinite`, not this module.

Everything below is proved for an arbitrary `CommRing A`; the base ring is never assumed to be
`ℂ`, a field, a domain, of characteristic zero, Noetherian, or nontrivial.
-/

set_option autoImplicit false

open PowerSeries

namespace Fabius

variable {A : Type*} [CommRing A]

/-! ## Coefficient helpers

Three one-line lemmas that make every recurrence below first-order: they compute the
coefficients of `(1 - b z) · F(z)` and of `F(qz)` without ever unfolding a Cauchy product. -/

/-- The constant coefficient of `(1 - b z) F(z)` is that of `F`. -/
theorem coeff_zero_one_sub_C_mul_X_mul (b : A) (F : A⟦X⟧) :
    coeff 0 ((1 - C b * X) * F) = constantCoeff F := by
  have h : (1 - C b * X) * F = F - C b * (X * F) := by ring
  rw [h, map_sub, coeff_C_mul, coeff_zero_X_mul, mul_zero, sub_zero,
    coeff_zero_eq_constantCoeff_apply]

/-- The `(n+1)`-st coefficient of `(1 - b z) F(z)`. -/
theorem coeff_succ_one_sub_C_mul_X_mul (b : A) (F : A⟦X⟧) (n : ℕ) :
    coeff (n + 1) ((1 - C b * X) * F) = coeff (n + 1) F - b * coeff n F := by
  have h : (1 - C b * X) * F = F - C b * (X * F) := by ring
  rw [h, map_sub, coeff_C_mul, coeff_succ_X_mul]

/-- Rescaling does not move the constant coefficient. -/
theorem constantCoeff_rescale (t : A) (F : A⟦X⟧) :
    constantCoeff (rescale t F) = constantCoeff F := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
    coeff_zero_eq_constantCoeff_apply]

/-! ## The q-difference equation

Both series of the theorem satisfy an equation of the shape `(1 - cz)F(z) = (1 - bz)F(qz)`:
the product series `(z;q)_∞` with `(b, c) = (1, 0)`, the q-binomial series with `(b, c) =
(a, 1)`.  Isolating this single predicate lets the recurrence, the uniqueness argument and
the substitution `z ↦ tz` be proved once. -/

/-- The formal q-difference equation `(1 - cz) F(z) = (1 - bz) F(qz)` in `A⟦z⟧`. -/
def IsQDifference (b c q : A) (F : A⟦X⟧) : Prop :=
  (1 - C c * X) * F = (1 - C b * X) * rescale q F

/-- `IsQDifference` unfolded. -/
theorem isQDifference_def (b c q : A) (F : A⟦X⟧) :
    IsQDifference b c q F ↔ (1 - C c * X) * F = (1 - C b * X) * rescale q F :=
  Iff.rfl

/-- The algebraic hypothesis replacing `I`-adic completeness: every `1 - q^{n+1}` is a unit.
It is implied by (and strictly weaker than) the printed hypothesis; see
`qRegular_of_isAdicComplete`. -/
def QRegular (q : A) : Prop := ∀ n : ℕ, IsUnit (1 - q ^ (n + 1))

/-- **The q-difference equation as a coefficient recurrence.**  The equation at the constant
term is automatic — both sides have constant coefficient `constantCoeff F` — so the whole
content is the two-term recurrence `(1 - q^{n+1}) c_{n+1} = (c - b q^n) c_n`.  No hypothesis
on `q` is used. -/
theorem isQDifference_iff (b c q : A) (F : A⟦X⟧) :
    IsQDifference b c q F ↔
      ∀ n : ℕ, (1 - q ^ (n + 1)) * coeff (n + 1) F = (c - b * q ^ n) * coeff n F := by
  constructor
  · intro h n
    have hEq := (isQDifference_def b c q F).mp h
    have h' : coeff (n + 1) ((1 - C c * X) * F)
        = coeff (n + 1) ((1 - C b * X) * rescale q F) := by rw [hEq]
    rw [coeff_succ_one_sub_C_mul_X_mul, coeff_succ_one_sub_C_mul_X_mul] at h'
    simp only [coeff_rescale] at h'
    linear_combination h'
  · intro h
    refine (isQDifference_def b c q F).mpr (PowerSeries.ext fun n => ?_)
    cases n with
    | zero =>
        rw [coeff_zero_one_sub_C_mul_X_mul, coeff_zero_one_sub_C_mul_X_mul,
          constantCoeff_rescale]
    | succ n =>
        rw [coeff_succ_one_sub_C_mul_X_mul, coeff_succ_one_sub_C_mul_X_mul,
          coeff_rescale, coeff_rescale]
        linear_combination h n

/-- **Uniqueness.**  A solution of the q-difference equation is determined by its constant
coefficient as soon as every `1 - q^{n+1}` is a unit. -/
theorem eq_of_isQDifference {b c q : A} {F G : A⟦X⟧} (hq : QRegular q)
    (hF : IsQDifference b c q F) (hG : IsQDifference b c q G)
    (h0 : constantCoeff F = constantCoeff G) : F = G := by
  have hF' := (isQDifference_iff b c q F).mp hF
  have hG' := (isQDifference_iff b c q G).mp hG
  refine PowerSeries.ext fun n => ?_
  induction n with
  | zero =>
      rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply]
      exact h0
  | succ n ih =>
      refine (hq n).mul_left_cancel ?_
      rw [hF' n, hG' n, ih]

/-- **Substitution `z ↦ tz`.**  The q-difference equation is stable under rescaling, with both
parameters scaled by `t`. -/
theorem IsQDifference.rescale {b c q : A} {F : A⟦X⟧} (h : IsQDifference b c q F) (t : A) :
    IsQDifference (b * t) (c * t) q (PowerSeries.rescale t F) := by
  rw [isQDifference_iff] at h ⊢
  intro n
  rw [coeff_rescale, coeff_rescale]
  calc (1 - q ^ (n + 1)) * (t ^ (n + 1) * coeff (n + 1) F)
      = t ^ (n + 1) * ((1 - q ^ (n + 1)) * coeff (n + 1) F) := by ring
    _ = t ^ (n + 1) * ((c - b * q ^ n) * coeff n F) := by rw [h n]
    _ = (c * t - b * t * q ^ n) * (t ^ n * coeff n F) := by ring

/-- **The product step.**  Multiplying a solution of `F(z) = (1 - z) F(qz)` by a solution of
`(1 - z) G(z) = (1 - bz) G(qz)` produces a solution of `H(z) = (1 - bz) H(qz)`.  This is the
entire multiplicative content of the theorem, and it never touches a Cauchy product. -/
theorem IsQDifference.mul_shift {b q : A} {F G : A⟦X⟧}
    (hF : IsQDifference 1 0 q F) (hG : IsQDifference b 1 q G) :
    IsQDifference b 0 q (F * G) := by
  have hF' := (isQDifference_def 1 0 q F).mp hF
  simp only [map_zero, map_one, zero_mul, one_mul, sub_zero] at hF'
  have hG' := (isQDifference_def b 1 q G).mp hG
  simp only [map_one, one_mul] at hG'
  rw [isQDifference_def]
  simp only [map_zero, zero_mul, sub_zero, one_mul]
  rw [map_mul]
  linear_combination G * hF' + PowerSeries.rescale q F * hG'

/-! ## Units among the finite q-Pochhammer symbols -/

/-- **Every `(q;q)_n` is a unit** under `QRegular q`.  This is the printed sentence "here
every `(q;q)_n` is a unit", with the completeness hypothesis replaced by its consequence. -/
theorem isUnit_finiteQPochhammerIn_self {q : A} (hq : QRegular q) (n : ℕ) :
    IsUnit (finiteQPochhammerIn q q n) := by
  simp only [finiteQPochhammerIn]
  refine IsUnit.prod_iff.mpr fun j _ => ?_
  rw [← pow_succ']
  exact hq j

/-! ## The q-binomial series `∑ (a;q)_n z^n / (q;q)_n` -/

/-- The formal q-binomial series `∑_{n≥0} (a;q)_n z^n / (q;q)_n`, with the reciprocals taken
by `Ring.inverse` so that the definition makes sense over every commutative ring.  Under
`QRegular q` the reciprocals are genuine inverses. -/
noncomputable def qBinomialSeries (a q : A) : A⟦X⟧ :=
  PowerSeries.mk fun n => Ring.inverse (finiteQPochhammerIn q q n) * finiteQPochhammerIn a q n

/-- The coefficients of the q-binomial series. -/
theorem coeff_qBinomialSeries (a q : A) (n : ℕ) :
    coeff n (qBinomialSeries a q)
      = Ring.inverse (finiteQPochhammerIn q q n) * finiteQPochhammerIn a q n :=
  coeff_mk _ _

@[simp] theorem constantCoeff_qBinomialSeries (a q : A) :
    constantCoeff (qBinomialSeries a q) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_qBinomialSeries]
  simp

/-- At `a = 0` the q-binomial series is Euler's reciprocal series `∑_n z^n/(q;q)_n`. -/
theorem coeff_qBinomialSeries_zero (q : A) (n : ℕ) :
    coeff n (qBinomialSeries 0 q) = Ring.inverse (finiteQPochhammerIn q q n) := by
  rw [coeff_qBinomialSeries, finiteQPochhammerIn_zero_left, mul_one]

/-- Clearing the denominator of the q-binomial series. -/
theorem finiteQPochhammerIn_self_mul_coeff_qBinomialSeries {q : A} (hq : QRegular q) (a : A)
    (n : ℕ) :
    finiteQPochhammerIn q q n * coeff n (qBinomialSeries a q) = finiteQPochhammerIn a q n := by
  rw [coeff_qBinomialSeries,
    Ring.mul_inverse_cancel_left _ _ (isUnit_finiteQPochhammerIn_self hq n)]

/-- The q-binomial series solves `(1 - z) F(z) = (1 - az) F(qz)`. -/
theorem isQDifference_qBinomialSeries {q : A} (hq : QRegular q) (a : A) :
    IsQDifference a 1 q (qBinomialSeries a q) := by
  rw [isQDifference_iff]
  intro n
  refine (isUnit_finiteQPochhammerIn_self hq n).mul_left_cancel ?_
  have hpoch : finiteQPochhammerIn q q n * (1 - q ^ (n + 1))
      = finiteQPochhammerIn q q (n + 1) := by
    rw [finiteQPochhammerIn_succ, pow_succ']
  have hL : finiteQPochhammerIn q q n *
      ((1 - q ^ (n + 1)) * coeff (n + 1) (qBinomialSeries a q))
      = finiteQPochhammerIn a q (n + 1) := by
    rw [← mul_assoc, hpoch]
    exact finiteQPochhammerIn_self_mul_coeff_qBinomialSeries hq a (n + 1)
  have hR : finiteQPochhammerIn q q n *
      ((1 - a * q ^ n) * coeff n (qBinomialSeries a q))
      = finiteQPochhammerIn a q (n + 1) := by
    rw [finiteQPochhammerIn_succ]
    calc finiteQPochhammerIn q q n * ((1 - a * q ^ n) * coeff n (qBinomialSeries a q))
        = (finiteQPochhammerIn q q n * coeff n (qBinomialSeries a q)) * (1 - a * q ^ n) := by
          ring
      _ = finiteQPochhammerIn a q n * (1 - a * q ^ n) := by
          rw [finiteQPochhammerIn_self_mul_coeff_qBinomialSeries hq a n]
  rw [hL, hR]

/-- **Stronger than the printed statement.**  The division-free coefficient formula
`(q;q)_n · c_n = (a;q)_n` is a consequence of the functional equation and `c_0 = 1` alone:
there is **no** hypothesis on `q`, no unit, and no completeness.  It therefore holds at roots
of unity, in positive characteristic, and in the presence of zero divisors, where the printed
quotient form is meaningless. -/
theorem finiteQPochhammerIn_self_mul_coeff_of_isQDifference {a q : A} {F : A⟦X⟧}
    (hF : IsQDifference a 1 q F) (h0 : constantCoeff F = 1) (n : ℕ) :
    finiteQPochhammerIn q q n * coeff n F = finiteQPochhammerIn a q n := by
  have hrec := (isQDifference_iff a 1 q F).mp hF
  induction n with
  | zero =>
      simp only [finiteQPochhammerIn_zero, one_mul, coeff_zero_eq_constantCoeff_apply]
      exact h0
  | succ n ih =>
      calc finiteQPochhammerIn q q (n + 1) * coeff (n + 1) F
          = finiteQPochhammerIn q q n * ((1 - q ^ (n + 1)) * coeff (n + 1) F) := by
            rw [finiteQPochhammerIn_succ, pow_succ']
            ring
        _ = finiteQPochhammerIn q q n * ((1 - a * q ^ n) * coeff n F) := by rw [hrec n]
        _ = (finiteQPochhammerIn q q n * coeff n F) * (1 - a * q ^ n) := by ring
        _ = finiteQPochhammerIn a q n * (1 - a * q ^ n) := by rw [ih]
        _ = finiteQPochhammerIn a q (n + 1) := (finiteQPochhammerIn_succ a q n).symm

/-! ## The product series `(z;q)_∞` -/

private theorem choose_two_succ_eq (k : ℕ) : (k + 1).choose 2 = k.choose 2 + k := by
  simpa [Nat.add_comm] using Nat.choose_succ_succ k 1

/-- Euler's expansion `(z;q)_∞ = ∑_n (-1)^n q^{n choose 2} z^n / (q;q)_n`, taken as the
*definition* of the infinite product in `A⟦z⟧`.  See `dvd_coeff_partialQPochhammer_sub` for
the effective link with the honest finite products. -/
noncomputable def qPochhammerSeries (q : A) : A⟦X⟧ :=
  PowerSeries.mk fun n => (-1 : A) ^ n * q ^ n.choose 2 * Ring.inverse (finiteQPochhammerIn q q n)

/-- The coefficients of `(z;q)_∞`. -/
theorem coeff_qPochhammerSeries (q : A) (n : ℕ) :
    coeff n (qPochhammerSeries q)
      = (-1 : A) ^ n * q ^ n.choose 2 * Ring.inverse (finiteQPochhammerIn q q n) :=
  coeff_mk _ _

@[simp] theorem constantCoeff_qPochhammerSeries (q : A) :
    constantCoeff (qPochhammerSeries q) = 1 := by
  have hc : Nat.choose 0 2 = 0 := by decide
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_qPochhammerSeries, hc]
  simp

/-- **`(z;q)_∞` is a unit in `A⟦z⟧` — with no hypothesis at all.**  Its constant coefficient
is `1`, and that alone makes a power series invertible.  This is the printed clause
"`(z;q)_∞` is a unit there", proved in greater generality. -/
theorem isUnit_qPochhammerSeries (q : A) : IsUnit (qPochhammerSeries q) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_qPochhammerSeries]
  exact isUnit_one

/-- `(z;q)_∞` solves `F(z) = (1 - z) F(qz)`, the functional equation obtained by splitting off
the first factor of the product. -/
theorem isQDifference_qPochhammerSeries {q : A} (hq : QRegular q) :
    IsQDifference 1 0 q (qPochhammerSeries q) := by
  rw [isQDifference_iff]
  intro n
  have hinv : (1 - q ^ (n + 1)) * Ring.inverse (finiteQPochhammerIn q q (n + 1))
      = Ring.inverse (finiteQPochhammerIn q q n) := by
    rw [finiteQPochhammerIn_succ, ← pow_succ',
      Ring.inverse_mul (a := finiteQPochhammerIn q q n) (b := 1 - q ^ (n + 1))
        (Or.inr (hq n))]
    exact Ring.mul_inverse_cancel_left _ _ (hq n)
  have hsign : (-1 : A) ^ (n + 1) = -((-1 : A) ^ n) := by
    rw [pow_succ, mul_neg_one]
  have hqpow : q ^ ((n + 1).choose 2) = q ^ n.choose 2 * q ^ n := by
    rw [choose_two_succ_eq, pow_add]
  rw [coeff_qPochhammerSeries, coeff_qPochhammerSeries, hsign, hqpow]
  linear_combination (-((-1 : A) ^ n * q ^ n.choose 2 * q ^ n)) * hinv

/-! ## The main identity -/

/-- **The formal q-binomial theorem.**  Over any commutative ring in which every `1 - q^{n+1}`
is a unit,

`(z;q)_∞ · ∑_{n≥0} (a;q)_n z^n / (q;q)_n = (az;q)_∞`,

the substitution `z ↦ az` being `PowerSeries.rescale a`.  This is the printed proposition; see
`qBinomialSeries_eq_inverse_mul` for the literal quotient form. -/
theorem qPochhammerSeries_mul_qBinomialSeries {q : A} (hq : QRegular q) (a : A) :
    qPochhammerSeries q * qBinomialSeries a q = rescale a (qPochhammerSeries q) := by
  have hL : IsQDifference a 0 q (qPochhammerSeries q * qBinomialSeries a q) :=
    (isQDifference_qPochhammerSeries hq).mul_shift (isQDifference_qBinomialSeries hq a)
  have hR : IsQDifference a 0 q (rescale a (qPochhammerSeries q)) := by
    have h := (isQDifference_qPochhammerSeries hq).rescale a
    rwa [one_mul, zero_mul] at h
  refine eq_of_isQDifference hq hL hR ?_
  rw [map_mul, constantCoeff_qPochhammerSeries, constantCoeff_qBinomialSeries,
    constantCoeff_rescale, constantCoeff_qPochhammerSeries, one_mul]

/-- The printed quotient form `(az;q)_∞ / (z;q)_∞ = ∑_{n≥0} (a;q)_n z^n/(q;q)_n`, dividing
by the unit `(z;q)_∞` of `isUnit_qPochhammerSeries`. -/
theorem qBinomialSeries_eq_inverse_mul {q : A} (hq : QRegular q) (a : A) :
    qBinomialSeries a q
      = Ring.inverse (qPochhammerSeries q) * rescale a (qPochhammerSeries q) := by
  rw [← qPochhammerSeries_mul_qBinomialSeries hq a,
    Ring.inverse_mul_cancel_left _ _ (isUnit_qPochhammerSeries q)]

/-- **Euler's reciprocal identity**, the case `a = 0`: the series `∑_n z^n/(q;q)_n` is the
inverse of `(z;q)_∞` in `A⟦z⟧`.  Its coefficients are `coeff_qBinomialSeries_zero`. -/
theorem qPochhammerSeries_mul_qBinomialSeries_zero {q : A} (hq : QRegular q) :
    qPochhammerSeries q * qBinomialSeries 0 q = 1 := by
  rw [qPochhammerSeries_mul_qBinomialSeries hq 0, rescale_zero_apply,
    constantCoeff_qPochhammerSeries, map_one]

/-- **Uniqueness clause of the proposition**: the q-binomial series is the only normalised
solution of `(1 - z) F(z) = (1 - az) F(qz)`. -/
theorem eq_qBinomialSeries_of_isQDifference {a q : A} {F : A⟦X⟧} (hq : QRegular q)
    (hF : IsQDifference a 1 q F) (h0 : constantCoeff F = 1) :
    F = qBinomialSeries a q :=
  eq_of_isQDifference hq hF (isQDifference_qBinomialSeries hq a)
    (by rw [h0, constantCoeff_qBinomialSeries])

/-! ## The finite products and effective convergence

The printed proof asserts, without proof, that the partial products are coefficientwise
`I`-adically Cauchy and therefore converge in `A⟦z⟧`.  The following results replace that
assertion by a theorem with an explicit modulus, valid over every commutative ring. -/

/-- The honest finite product `(bz;q)_N = ∏_{j<N} (1 - b q^j z)` in `A⟦z⟧`. -/
noncomputable def partialQPochhammer (b q : A) (N : ℕ) : A⟦X⟧ :=
  ∏ j ∈ Finset.range N, (1 - C (b * q ^ j) * X)

/-- The partial product is the finite q-Pochhammer symbol of `bz` at base `q`, computed
inside `A⟦z⟧`. -/
theorem partialQPochhammer_eq (b q : A) (N : ℕ) :
    partialQPochhammer b q N = finiteQPochhammerIn ((C b : A⟦X⟧) * X) (C q) N := by
  simp only [partialQPochhammer, finiteQPochhammerIn]
  refine Finset.prod_congr rfl fun j _ => ?_
  have h : (C b : A⟦X⟧) * X * C q ^ j = C (b * q ^ j) * X := by
    rw [map_mul, map_pow]
    ring
  rw [h]

/-- **The coefficients of the finite product**, by the finite q-binomial theorem of
`FiniteQBinomialCore`: they are `(-1)^n q^{n choose 2} [N,n]_q b^n` for *every* `n`, with no
hypothesis relating `n` and `N` — above the degree both sides vanish, since the Gaussian
coefficient is extended by zero. -/
theorem coeff_partialQPochhammer (b q : A) (n N : ℕ) :
    coeff n (partialQPochhammer b q N)
      = (-1 : A) ^ n * q ^ n.choose 2 * gaussianBinomial q N n * b ^ n := by
  have hexp : partialQPochhammer b q N
      = ∑ k ∈ Finset.range (N + 1),
          C ((-1 : A) ^ k * q ^ k.choose 2 * gaussianBinomial q N k * b ^ k) * X ^ k := by
    rw [partialQPochhammer_eq, ← finite_qBinomial_theorem (C q : A⟦X⟧) (C b * X) N]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul, map_pow, map_neg, map_one, map_gaussianBinomial, mul_pow]
    ring
  rw [hexp]
  simp only [map_sum]
  by_cases hn : n ≤ N
  · have hmem : n ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    have hzero : ∀ k ∈ Finset.range (N + 1), k ≠ n →
        coeff n (C ((-1 : A) ^ k * q ^ k.choose 2 * gaussianBinomial q N k * b ^ k) * X ^ k)
          = 0 := by
      intro k _ hk
      rw [coeff_C_mul_X_pow, if_neg (Ne.symm hk)]
    rw [Finset.sum_eq_single_of_mem n hmem hzero, coeff_C_mul_X_pow, if_pos rfl]
  · rw [gaussianBinomial_eq_zero_of_lt q (by omega : N < n), mul_zero, zero_mul]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' : k < N + 1 := Finset.mem_range.mp hk
    have hne : n ≠ k := by omega
    rw [coeff_C_mul_X_pow, if_neg hne]

/-- Every finite q-Pochhammer symbol differs from `1` by a multiple of its first parameter. -/
theorem dvd_finiteQPochhammerIn_sub_one (x q : A) (n : ℕ) :
    x ∣ finiteQPochhammerIn x q n - 1 := by
  induction n with
  | zero =>
      rw [finiteQPochhammerIn_zero, sub_self]
      exact dvd_zero x
  | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨c - finiteQPochhammerIn x q n * q ^ n, ?_⟩
      rw [finiteQPochhammerIn_succ]
      linear_combination hc

/-- **Effective coefficientwise convergence of the partial products.**  For `n ≤ N` the `n`-th
coefficient of the finite product `(bz;q)_N` agrees with that of `(bz;q)_∞` modulo
`q^{N-n+1}`:

`q ^ (N - n + 1) ∣ coeff n (bz;q)_N - coeff n (bz;q)_∞`.

Applied to two exponents `N ≤ M` it gives the Cauchy property asserted without proof in the
printed argument, and letting `N → ∞` with `n` fixed it identifies the limit with the Euler
expansion — with an explicit modulus and no topology.  The error term is exhibited as
`(q^{N-n+1};q)_n - 1` through the denominator-free Gaussian identity
`finiteQPochhammerIn_self_mul_gaussianBinomial`. -/
theorem dvd_coeff_partialQPochhammer_sub {q : A} (hq : QRegular q) (b : A) {n N : ℕ}
    (hn : n ≤ N) :
    q ^ (N - n + 1) ∣
      coeff n (partialQPochhammer b q N) - coeff n (rescale b (qPochhammerSeries q)) := by
  have hPu : finiteQPochhammerIn q q n * Ring.inverse (finiteQPochhammerIn q q n) = 1 :=
    Ring.mul_inverse_cancel _ (isUnit_finiteQPochhammerIn_self hq n)
  have hG : finiteQPochhammerIn q q n * gaussianBinomial q N n
      = finiteQPochhammerIn (q ^ (N - n + 1)) q n :=
    finiteQPochhammerIn_self_mul_gaussianBinomial q hn
  obtain ⟨c, hc⟩ := dvd_finiteQPochhammerIn_sub_one (q ^ (N - n + 1)) q n
  refine ⟨(-1 : A) ^ n * q ^ n.choose 2 * b ^ n
      * Ring.inverse (finiteQPochhammerIn q q n) * c, ?_⟩
  rw [coeff_partialQPochhammer b q n N, coeff_rescale, coeff_qPochhammerSeries]
  linear_combination
    (-((-1 : A) ^ n * q ^ n.choose 2 * b ^ n * gaussianBinomial q N n)) * hPu
      + ((-1 : A) ^ n * q ^ n.choose 2 * b ^ n
          * Ring.inverse (finiteQPochhammerIn q q n)) * hG
      + ((-1 : A) ^ n * q ^ n.choose 2 * b ^ n
          * Ring.inverse (finiteQPochhammerIn q q n)) * hc

/-- The printed `I`-adic form of the previous theorem: for any ideal `I` containing `q`, the
`n`-th coefficients of `(bz;q)_N` and `(bz;q)_∞` agree modulo `I^{N-n+1}`.  With `A` separated
for the `I`-adic topology this pins down `(bz;q)_∞` uniquely as the limit. -/
theorem coeff_partialQPochhammer_sub_mem_pow {q : A} (hq : QRegular q) (b : A) (I : Ideal A)
    (hqI : q ∈ I) {n N : ℕ} (hn : n ≤ N) :
    coeff n (partialQPochhammer b q N) - coeff n (rescale b (qPochhammerSeries q))
      ∈ I ^ (N - n + 1) := by
  obtain ⟨c, hc⟩ := dvd_coeff_partialQPochhammer_sub hq b hn
  rw [hc]
  exact Ideal.mul_mem_right c (I ^ (N - n + 1)) (Ideal.pow_mem_pow hqI (N - n + 1))

/-! ## Sources of the hypothesis `QRegular` -/

/-- Anything in the Jacobson radical is `QRegular`. -/
theorem qRegular_of_le_jacobson_bot {q : A} (h : q ∈ Ideal.jacobson (⊥ : Ideal A)) :
    QRegular q := by
  intro n
  have hu := Ideal.mem_jacobson_bot.mp h (-(q ^ n))
  have hre : q * (-(q ^ n)) + 1 = 1 - q ^ (n + 1) := by ring
  rwa [hre] at hu

/-- **The printed hypothesis, discharged.**  If `A` is `I`-adically complete (hence separated)
and `q ∈ I`, then every `1 - q^{n+1}` is a unit.  So every result of this module applies
verbatim in the setting of the printed proposition — and in strictly more settings, since the
converse fails. -/
theorem qRegular_of_isAdicComplete {q : A} (I : Ideal A) [IsAdicComplete I A] (hq : q ∈ I) :
    QRegular q :=
  qRegular_of_le_jacobson_bot (IsAdicComplete.le_jacobson_bot I hq)

/-- A nilpotent base is `QRegular`; no completeness is involved. -/
theorem qRegular_of_isNilpotent {q : A} (h : IsNilpotent q) : QRegular q := by
  intro n
  obtain ⟨m, hm⟩ := h
  have hne : n + 1 ≠ 0 := by omega
  refine IsNilpotent.isUnit_one_sub ⟨m, ?_⟩
  rw [← pow_mul, Nat.mul_comm, pow_mul, hm, zero_pow hne]

/-- The indeterminate of a power series ring is `QRegular`. -/
theorem qRegular_X (R : Type*) [CommRing R] : QRegular (X : R⟦X⟧) := by
  intro n
  have hne : n + 1 ≠ 0 := by omega
  rw [PowerSeries.isUnit_iff_constantCoeff, map_sub, map_one, map_pow, constantCoeff_X,
    zero_pow hne, sub_zero]
  exact isUnit_one

/-- **The printed special case.**  Taking the base ring to be a power series ring and `q` its
indeterminate, the identity holds in `R⟦q⟧⟦z⟧` for every commutative ring `R`; with
`R = ℤ[a]` this is the printed statement that the q-binomial theorem holds formally in
`ℤ[a]⟦q⟧⟦z⟧` with `a` and `q` indeterminates. -/
theorem qPochhammerSeries_mul_qBinomialSeries_X {R : Type*} [CommRing R] (a : R⟦X⟧) :
    qPochhammerSeries (X : R⟦X⟧) * qBinomialSeries a (X : R⟦X⟧)
      = rescale a (qPochhammerSeries (X : R⟦X⟧)) :=
  qPochhammerSeries_mul_qBinomialSeries (qRegular_X R) a

end Fabius
