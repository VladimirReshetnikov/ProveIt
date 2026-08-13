import KlarnerConstant.Recurrence
import KlarnerConstant.Convolution

/-!
# Bui's seventeen weighted coefficient recurrences

This module exposes the coefficient-algebra boundary of Bui's polyomino
argument coordinate by coordinate.  A `WeightedBuiRecurrences ζ S` contains
the seventeen finite weighted-prefix inequalities, rather than one opaque
profile inequality.  The nonlinear right-hand sides are exactly the Cauchy
products represented in `KlarnerConstant.Convolution`; those lemmas can be
used independently to establish the fields from pointwise coefficient
recurrences.

The five linear equations (`F`, `G`, `H`, `R`, and `T`) are stated at the
current prefix.  In `satisfiesPrefixRecurrence` they are combined in
topological order with the twelve inequalities whose right-hand sides use the
previous prefix.  The result is precisely the `advance` step required by the
order-theoretic certificate argument.
-/

namespace LeanProofs.KlarnerConstant

namespace CoefficientProfile

/-- All seventeen coefficient sequences use the positive-index convention. -/
def ZeroAtZero (S : CoefficientProfile) : Prop :=
  S.c 0 = 0 ∧ S.d 0 = 0 ∧ S.e 0 = 0 ∧ S.f 0 = 0 ∧ S.g 0 = 0 ∧
  S.h 0 = 0 ∧ S.p 0 = 0 ∧ S.q 0 = 0 ∧ S.r 0 = 0 ∧ S.s 0 = 0 ∧
  S.t 0 = 0 ∧ S.u 0 = 0 ∧ S.v 0 = 0 ∧ S.w 0 = 0 ∧ S.x 0 = 0 ∧
  S.y 0 = 0 ∧ S.z 0 = 0

/-- Bui's degree-one initial bounds.  The six linear types can contribute one
object; all eleven nonlinear/shifted auxiliary types vanish.  Together with
nonnegativity, the latter inequalities force exact zero. -/
def BuiInitialBounds (S : CoefficientProfile) : Prop :=
  S.c 1 ≤ 1 ∧ S.d 1 ≤ 1 ∧ S.e 1 ≤ 1 ∧ S.f 1 ≤ 1 ∧ S.g 1 ≤ 1 ∧
  S.h 1 ≤ 1 ∧ S.p 1 ≤ 0 ∧ S.q 1 ≤ 0 ∧ S.r 1 ≤ 0 ∧ S.s 1 ≤ 0 ∧
  S.t 1 ≤ 0 ∧ S.u 1 ≤ 0 ∧ S.v 1 ≤ 0 ∧ S.w 1 ≤ 0 ∧ S.x 1 ≤ 0 ∧
  S.y 1 ≤ 0 ∧ S.z 1 ≤ 0

end CoefficientProfile

/--
The seventeen separately visible, finite weighted versions of Bui's
coefficient recurrences.

For example, the `p` field is what follows after summing

`Pₙ ≤ (E*H)ₙ + (Q*D)ₙ + (X*R)ₙ + (V*Y)ₙ + (U*Y*Z)ₙ`

through the current endpoint and applying the two- and three-fold convolution
bounds.  The shift lemmas similarly account for every displayed factor of
`ζ` or `ζ²`.
-/
structure WeightedBuiRecurrences (ζ : ℚ) (S : CoefficientProfile) where
  nonnegative : S.Nonnegative
  zeroAtZero : S.ZeroAtZero
  initial : S.BuiInitialBounds

  c : ∀ N,
    weightedPrefix ζ S.c (N + 1) ≤
      ζ + ζ * weightedPrefix ζ S.e N
  d : ∀ N,
    weightedPrefix ζ S.d (N + 1) ≤
      ζ + ζ * weightedPrefix ζ S.g N
  e : ∀ N,
    weightedPrefix ζ S.e (N + 1) ≤
      ζ + ζ * weightedPrefix ζ S.f N

  f : ∀ N,
    weightedPrefix ζ S.f (N + 1) ≤
      weightedPrefix ζ S.g (N + 1) + weightedPrefix ζ S.p (N + 1)
  g : ∀ N,
    weightedPrefix ζ S.g (N + 1) ≤
      weightedPrefix ζ S.e (N + 1) + weightedPrefix ζ S.q (N + 1)
  h : ∀ N,
    weightedPrefix ζ S.h (N + 1) ≤
      weightedPrefix ζ S.d (N + 1) + weightedPrefix ζ S.s (N + 1)

  p : ∀ N,
    weightedPrefix ζ S.p (N + 1) ≤
      weightedPrefix ζ S.e N * weightedPrefix ζ S.h N +
      weightedPrefix ζ S.q N * weightedPrefix ζ S.d N +
      weightedPrefix ζ S.x N * weightedPrefix ζ S.r N +
      weightedPrefix ζ S.v N * weightedPrefix ζ S.y N +
      weightedPrefix ζ S.u N * weightedPrefix ζ S.y N * weightedPrefix ζ S.z N
  q : ∀ N,
    weightedPrefix ζ S.q (N + 1) ≤
      ζ * weightedPrefix ζ S.g N +
      ζ * weightedPrefix ζ S.g N * weightedPrefix ζ S.e N +
      ζ ^ 2 * (weightedPrefix ζ S.u N +
        weightedPrefix ζ S.t N * weightedPrefix ζ S.g N +
        weightedPrefix ζ S.r N * weightedPrefix ζ S.u N)

  r : ∀ N,
    weightedPrefix ζ S.r (N + 1) ≤
      weightedPrefix ζ S.y (N + 1) + weightedPrefix ζ S.w (N + 1)
  s : ∀ N,
    weightedPrefix ζ S.s (N + 1) ≤
      ζ * weightedPrefix ζ S.g N +
      ζ * weightedPrefix ζ S.e N ^ 2 +
      ζ ^ 2 * weightedPrefix ζ S.t N +
      ζ ^ 2 * weightedPrefix ζ S.x N * weightedPrefix ζ S.g N +
      ζ ^ 2 * weightedPrefix ζ S.y N * weightedPrefix ζ S.u N
  t : ∀ N,
    weightedPrefix ζ S.t (N + 1) ≤
      weightedPrefix ζ S.x (N + 1) + weightedPrefix ζ S.v (N + 1)

  u : ∀ N,
    weightedPrefix ζ S.u (N + 1) ≤
      weightedPrefix ζ S.d N * weightedPrefix ζ S.h N +
      weightedPrefix ζ S.s N * weightedPrefix ζ S.d N +
      weightedPrefix ζ S.y N * weightedPrefix ζ S.r N +
      weightedPrefix ζ S.w N * weightedPrefix ζ S.y N +
      weightedPrefix ζ S.u N * weightedPrefix ζ S.z N ^ 2
  v : ∀ N,
    weightedPrefix ζ S.v (N + 1) ≤
      ζ * weightedPrefix ζ S.s N +
      ζ ^ 2 * (weightedPrefix ζ S.g N ^ 2 +
        weightedPrefix ζ S.t N * weightedPrefix ζ S.e N +
        weightedPrefix ζ S.r N * weightedPrefix ζ S.t N)
  w : ∀ N,
    weightedPrefix ζ S.w (N + 1) ≤
      ζ * weightedPrefix ζ S.s N +
      ζ ^ 2 * (weightedPrefix ζ S.e N * weightedPrefix ζ S.g N +
        weightedPrefix ζ S.x N * weightedPrefix ζ S.e N +
        weightedPrefix ζ S.y N * weightedPrefix ζ S.t N)
  x : ∀ N,
    weightedPrefix ζ S.x (N + 1) ≤
      ζ * weightedPrefix ζ S.d N +
      ζ ^ 2 * (weightedPrefix ζ S.g N + weightedPrefix ζ S.u N)
  y : ∀ N,
    weightedPrefix ζ S.y (N + 1) ≤
      ζ * weightedPrefix ζ S.c N +
      ζ ^ 2 * (weightedPrefix ζ S.g N + weightedPrefix ζ S.t N)
  z : ∀ N,
    weightedPrefix ζ S.z (N + 1) ≤
      ζ * weightedPrefix ζ S.c N +
      ζ ^ 2 * (weightedPrefix ζ S.e N + weightedPrefix ζ S.x N)

namespace WeightedBuiRecurrences

/-- The seventeen explicit weighted inequalities assemble into the single
profile recurrence consumed by `Recurrence.lean`. -/
theorem satisfiesPrefixRecurrence {ζ : ℚ} {S : CoefficientProfile}
    (R : WeightedBuiRecurrences ζ S) : S.SatisfiesPrefixRecurrence ζ := by
  intro N
  have hc := R.c N
  have hd := R.d N
  have he := R.e N
  have hp := R.p N
  have hq := R.q N
  have hs := R.s N
  have hu := R.u N
  have hv := R.v N
  have hw := R.w N
  have hx := R.x N
  have hy := R.y N
  have hz := R.z N
  have hg := (R.g N).trans (add_le_add he hq)
  have hf := (R.f N).trans (add_le_add hg hp)
  have hh := (R.h N).trans (add_le_add hd hs)
  have hr := (R.r N).trans (add_le_add hy hw)
  have ht := (R.t N).trans (add_le_add hx hv)
  simp only [CoefficientProfile.SatisfiesPrefixRecurrence,
    Profile.ComponentwiseLE, CoefficientProfile.prefixProfile, advance]
  exact
    And.intro hc <| And.intro hd <| And.intro he <| And.intro hf <|
    And.intro hg <| And.intro hh <| And.intro hp <| And.intro hq <|
    And.intro hr <| And.intro hs <| And.intro ht <| And.intro hu <|
    And.intro hv <| And.intro hw <| And.intro hx <| And.intro hy hz

/-- The weighted Bui system gives a genuine finite-prefix recurrence object. -/
def toPrefixRecurrence {ζ : ℚ} (hζ : 0 ≤ ζ) {S : CoefficientProfile}
    (R : WeightedBuiRecurrences ζ S) : PrefixRecurrence ζ :=
  S.toPrefixRecurrence hζ R.nonnegative R.satisfiesPrefixRecurrence

/-- The exact rational exponential bound obtained from the seventeen Bui
recurrences and the checked supersolution certificate. -/
theorem dominatedCoefficient_le_9047_div_2000_pow
    {A : ℕ → ℚ} {S : CoefficientProfile}
    (R : WeightedBuiRecurrences certificateZeta S)
    (hA : ∀ n, A n ≤ S.g n) (n : ℕ) :
    A n ≤ (9047 / 2000 : ℚ) ^ n := by
  exact LeanProofs.KlarnerConstant.dominatedCoefficient_le_9047_div_2000_pow
    S hA R.nonnegative R.satisfiesPrefixRecurrence n

end WeightedBuiRecurrences

end LeanProofs.KlarnerConstant
