import Sharma2012.Definitions

/-!
# Sharma (2009): statement catalogue

This file records every theorem, lemma, proposition, and corollary in Arun
Sharma's "Enumerating permutations that avoid three term arithmetic
progressions", together with the two numbered recurrence inequalities and the
three open problems at the end of the paper.

The entries are definitions with values in `Prop`.  Thus they formalize the
statements without asserting unproved results in Lean's environment.
-/

set_option autoImplicit false

noncomputable section

open Finset Filter Topology

namespace LeanProofs.Sharma2012

/-! ## Section 1: Introduction -/

/-- **Theorem 1.1.** The elementary exponential lower bound. -/
def theorem_1_1 : Prop :=
  forall n : Nat, 0 < n -> 2 ^ (n - 1) <= theta n

/-- Inequality (1), the even recurrence used again in Section 3. -/
def inequality_1 : Prop :=
  forall k : Nat, 0 < k -> 2 * (theta k) ^ 2 <= theta (2 * k)

/-- Inequality (2), the odd recurrence used again in Section 3. -/
def inequality_2 : Prop :=
  forall k : Nat, 0 < k ->
    2 * theta k * theta (k + 1) <= theta (2 * k + 1)

/-- The first open asymptotic question mentioned in the Introduction. -/
def introduction_ratio_question : Prop :=
  Tendsto (fun n : Nat => (theta (n + 1) : Real) / theta n)
    atTop (nhds 2)

/-! ## Section 2: Structural properties of Theta permutations -/

/-- **Proposition 2.1.** The first and final entries have different parity. -/
def proposition_2_1 : Prop :=
  forall (n : Nat) (gamma : List Nat), 2 <= n -> IsTheta n gamma ->
    exists first last : Nat,
      StartsWith gamma first /\ EndsWith gamma last /\
        ¬ Nat.ModEq 2 first last

/-- **Proposition 2.2.** If `1` precedes `2`, the permutation starts odd. -/
def proposition_2_2 : Prop :=
  forall (n : Nat) (gamma : List Nat), IsTheta n gamma ->
    OccursLeftOf gamma 1 2 -> IsTheta12 n gamma

/-- **Proposition 2.3.** Of two consecutive values, the odd one precedes the
even one in every `Theta_12` permutation. -/
def proposition_2_3 : Prop :=
  forall (n : Nat) (gamma : List Nat) (x : Nat),
    IsTheta12 n gamma -> x ∈ segment n -> x + 1 ∈ segment n ->
      (Odd x -> OccursLeftOf gamma x (x + 1)) /\
      (Even x -> OccursLeftOf gamma (x + 1) x)

/-- **Proposition 2.4.** Every element of `[n]` can be the initial entry of a
`Theta` permutation. -/
def proposition_2_4 : Prop :=
  forall (n j : Nat), j ∈ segment n ->
    exists gamma : List Nat, IsTheta n gamma /\ StartsWith gamma j

/-- **Proposition 2.5.** Complementation preserves prologue length outside
the single exceptional middle-entry case for odd `n`. -/
def proposition_2_5 : Prop :=
  forall (n : Nat) (gamma : List Nat), IsTheta n gamma ->
    ¬ (Odd n /\ (n + 1) / 2 ∈ prologue n gamma) ->
      (prologue n gamma).length = (prologue n (complement n gamma)).length

/-- **Proposition 2.6.** Doubling into the even block followed by the odd
block preserves prologue length, as does complementation. -/
def proposition_2_6 : Prop :=
  forall (n : Nat) (gamma : List Nat), IsTheta n gamma ->
    let delta := doubledEvenOdd gamma
    IsTheta (2 * n) delta /\
      (prologue n gamma).length = (prologue (2 * n) delta).length /\
      (prologue (2 * n) delta).length =
        (prologue (2 * n) (complement (2 * n) delta)).length

/-- **Theorem 2.1.** Odd endpoints with even mean precede their mean; the
parity-reversed version has the mean preceding both endpoints. -/
def theorem_2_1 : Prop :=
  forall (n : Nat) (gamma : List Nat), IsTheta12 n gamma ->
    forall x y m : Nat,
      x ∈ segment n -> y ∈ segment n -> m ∈ segment n -> x != y ->
      x + y = 2 * m ->
        (Odd x /\ Odd y /\ Even m ->
          OccursLeftOf gamma x m /\ OccursLeftOf gamma y m) /\
        (Even x /\ Even y /\ Odd m ->
          OccursLeftOf gamma m x /\ OccursLeftOf gamma m y)

/-- **Theorem 2.2.** Characterization of commuting odd/even pairs.

The side conditions before each natural-number subtraction state literally
that the corresponding integer reflection belongs to `[n]`; they avoid any
truncated-subtraction ambiguity.  We also require `3 <= n`, correcting a
boundary omission in the printed statement: for `n = 2`, `x = 1`, and
`y = 2`, the left-hand side holds but neither reflection lies in `[2]`.
-/
def theorem_2_2 : Prop :=
  forall (n x y : Nat), 3 <= n -> x ∈ segment n -> y ∈ segment n -> Odd x -> Even y ->
    (DoNotCommute n x y <->
      (y <= 2 * x /\ 2 * x - y ∈ segment n) \/
      (x <= 2 * y /\ 2 * y - x ∈ segment n))

/-- **Proposition 2.7.** Adjacent commuting entries may be swapped. -/
def proposition_2_7 : Prop :=
  forall (n x y : Nat) (alpha : List Nat),
    x ∈ segment n -> y ∈ segment n -> Odd x -> Even y ->
    IsTheta12 n alpha -> Commute n x y -> ImmediatelyLeftOf alpha x y ->
      IsTheta12 n (swapValues x y alpha)

/-- **Corollary 2.2.1.** Opposite-parity entries in the same half do not
commute. -/
def corollary_2_2_1 : Prop :=
  forall (n x y : Nat), x ∈ segment n -> y ∈ segment n -> SameHalf n x y ->
    (Odd x -> Even y -> DoNotCommute n x y) /\
    (Even x -> Odd y -> DoNotCommute n y x)

/-- **Corollary 2.2.2.** The first `floor((n+1)/4)` entries have the same
parity. -/
def corollary_2_2_2 : Prop :=
  forall (n : Nat) (gamma : List Nat), IsTheta n gamma ->
    PrefixCongruent gamma ((n + 1) / 4) 2

/-- **Lemma 2.1.** The parity-block induction step. -/
def lemma_2_1 : Prop :=
  forall (n k j : Nat), 0 < n -> 0 < k -> 0 < j -> 4 * k <= n + 1 ->
    (forall gamma : List Nat, IsTheta n gamma ->
      PrefixCongruent gamma k (2 ^ j)) ->
    (forall gamma : List Nat, IsTheta (n + 1) gamma ->
      PrefixCongruent gamma k (2 ^ j)) ->
    (forall gamma : List Nat, IsTheta (2 * n) gamma ->
      PrefixCongruent gamma k (2 ^ (j + 1))) /\
    (forall gamma : List Nat, IsTheta (2 * n + 1) gamma ->
      PrefixCongruent gamma k (2 ^ (j + 1)))

/-- **Theorem 2.3.** The initial block forced to be congruent modulo a power
of two. -/
def theorem_2_3 : Prop :=
  forall (n j : Nat), 0 < n -> forall gamma : List Nat, IsTheta n gamma ->
    PrefixCongruent gamma (((n / (2 ^ j)) + 1) / 4) (2 ^ (j + 1))

/-- **Theorem 2.4.** A higher degree of binary congruence with the first
entry forces the mean to precede both endpoints. -/
def theorem_2_4 : Prop :=
  forall (n : Nat) (gamma : List Nat) (a1 x y z : Nat),
    IsTheta n gamma -> StartsWith gamma a1 ->
    x ∈ segment n -> y ∈ segment n -> z ∈ segment n ->
    x + y = 2 * z -> a1 != z -> a1 != x ->
    binaryCongruenceDegree a1 x < binaryCongruenceDegree a1 z ->
      OccursLeftOf gamma z x /\ OccursLeftOf gamma z y

/-- **Lemma 2.2.** The first entry is extremal in its prologue. -/
def lemma_2_2 : Prop :=
  forall (n : Nat) (gamma : List Nat) (a1 : Nat),
    IsTheta n gamma -> StartsWith gamma a1 ->
      (a1 ∈ lowerHalf n -> forall x : Nat, x ∈ prologue n gamma -> x <= a1) /\
      ((forall x : Nat, x ∈ prologue n gamma -> x ∈ upperHalf n) ->
        forall x : Nat, x ∈ prologue n gamma -> a1 <= x)

/-- **Lemma 2.3.** The three forced relative-order assertions around the
first entry.  The two inequalities characterize the paper's largest `t`
with `2^t < a1`. -/
def lemma_2_3 : Prop :=
  forall (n : Nat) (gamma : List Nat) (a1 t : Nat),
    IsTheta n gamma -> StartsWith gamma a1 -> 4 < a1 ->
    2 ^ t < a1 -> a1 <= 2 ^ (t + 1) ->
    let u := 2 ^ (t - 2);
      OccursLeftOf gamma a1 (a1 - 4 * u) /\
      OccursLeftOf gamma (a1 - 4 * u) (a1 - 2 * u) /\
      OccursLeftOf gamma (a1 - 2 * u) (a1 - u) /\
      (n >= a1 + 2 * u -> OccursLeftOf gamma (a1 + 2 * u) (a1 - u)) /\
      (n >= a1 + 7 * u ->
        OccursLeftOf gamma (a1 + 2 * u) (a1 - 3 * u) /\
        OccursLeftOf gamma (a1 + 2 * u) (a1 + 7 * u))

/-- **Lemma 2.4.** A lower-half first entry gives a prologue of length at
most six. -/
def lemma_2_4 : Prop :=
  forall (n : Nat) (gamma : List Nat) (a1 : Nat),
    IsTheta n gamma -> StartsWith gamma a1 -> a1 ∈ lowerHalf n ->
      (prologue n gamma).length <= 6

/-- **Theorem 2.5.** Every prologue has length at most six. -/
def theorem_2_5 : Prop :=
  forall (n : Nat) (gamma : List Nat), IsTheta n gamma ->
    (prologue n gamma).length <= 6

/-- **Lemma 2.5.** Under Notation 2.2's standing hypotheses, the
interleaving-class size is a binomial coefficient. -/
def lemma_2_5 : Prop :=
  forall (n : Nat) (gamma : List Nat), StandingInterleavingHypotheses n gamma ->
    let gammaOdd := oddTrace gamma
    let gammaEven := evenTrace gamma
    let u := (epilogue n gammaOdd).length
    let v := (prologue n gammaEven).length
    (interleavingClass n gammaOdd gammaEven).card = Nat.choose (u + v) v

/-- **Proposition 2.8.** Congruence blocks at the first dyadic threshold. -/
def proposition_2_8 : Prop :=
  forall (n : Nat) (gamma : List Nat), 32 <= n -> IsTheta n gamma ->
    let q := dyadicQ n
    16 * q <= n ->
      let pattern := fun word : List Nat =>
        PrefixCongruent word 2 (4 * q) /\
        PrefixCongruent word 4 (2 * q) /\
        PrefixCongruent word 8 q
      pattern gamma /\ pattern (oddTrace gamma) /\ pattern (evenTrace gamma)

/-- **Proposition 2.9.** Congruence blocks at the second dyadic threshold. -/
def proposition_2_9 : Prop :=
  forall (n : Nat) (gamma : List Nat), 32 <= n -> IsTheta n gamma ->
    let q := dyadicQ n
    22 * q <= n ->
      let pattern := fun word : List Nat =>
        PrefixCongruent word 3 (4 * q) /\
        PrefixCongruent word 5 (2 * q) /\
        PrefixCongruent word 11 q
      pattern gamma /\ pattern (oddTrace gamma) /\ pattern (evenTrace gamma)

/-- **Proposition 2.10.** Congruence blocks at the third dyadic threshold. -/
def proposition_2_10 : Prop :=
  forall (n : Nat) (gamma : List Nat), 32 <= n -> IsTheta n gamma ->
    let q := dyadicQ n
    28 * q <= n ->
      let pattern := fun word : List Nat =>
        PrefixCongruent word 2 (8 * q) /\
        PrefixCongruent word 3 (4 * q) /\
        PrefixCongruent word 7 (2 * q) /\
        PrefixCongruent word 14 q
      pattern gamma /\ pattern (oddTrace gamma) /\ pattern (evenTrace gamma)

/-- **Theorem 2.6.** If either relevant end block has length at least four,
the other has length at most two. -/
def theorem_2_6 : Prop :=
  forall (n : Nat) (gamma : List Nat), StandingInterleavingHypotheses n gamma ->
    let u := (epilogue n (oddTrace gamma)).length
    let v := (prologue n (evenTrace gamma)).length
    (4 <= u -> v <= 2) /\ (4 <= v -> u <= 2)

/-- **Theorem 2.7.** If either relevant end block has length at least five,
the other has length one. -/
def theorem_2_7 : Prop :=
  forall (n : Nat) (gamma : List Nat), StandingInterleavingHypotheses n gamma ->
    let u := (epilogue n (oddTrace gamma)).length
    let v := (prologue n (evenTrace gamma)).length
    (5 <= u -> v = 1) /\ (5 <= v -> u = 1)

/-- **Corollary 2.7.1.** Every odd/even interleaving class has at most twenty
members. -/
def corollary_2_7_1 : Prop :=
  forall (n : Nat) (gammaOdd gammaEven : List Nat),
    (interleavingClass n gammaOdd gammaEven).card <= 20

/-- **Corollary 2.7.2.** At least the first `floor(n/2) - 6` entries have
one parity.  Natural subtraction makes the assertion harmless for small `n`.
-/
def corollary_2_7_2 : Prop :=
  forall (n : Nat) (gamma : List Nat), IsTheta n gamma ->
    PrefixCongruent gamma (n / 2 - 6) 2

/-- **Theorem 2.8.** The recursive upper bound for `theta`. -/
def theorem_2_8 : Prop :=
  forall n : Nat, 3 <= n ->
    theta n <= 21 * theta ((n + 1) / 2) * theta (n / 2)

/-- **Theorem 2.9.** The exponential upper bound. -/
def theorem_2_9 : Prop :=
  forall n : Nat, 11 <= n ->
    (theta n : Real) <= ((27 : Real) / 10) ^ n / 21

/-- **Theorem 2.10.** The limit superior of the `n`th-root growth rate is at
most `2.7`. -/
def theorem_2_10 : Prop :=
  Filter.limsup exponentialRate atTop <= (27 : Real) / 10

/-! ## Section 3: Extending the domain of the lower bound -/

/-- **Theorem 3.1.** The iterated interval lower bounds. -/
def theorem_3_1 : Prop :=
  forall p n : Nat,
    5 * 2 ^ (p + 1) <= n -> n < 5 * 2 ^ (p + 2) ->
      2 ^ (n + 2 ^ p - 1) <= theta n

/-- **Theorem 3.2.** For every fixed integer `p`, `theta(n)` eventually
dominates `n^p * 2^n` by an unbounded factor. -/
def theorem_3_2 : Prop :=
  forall p : Int,
    Tendsto
      (fun n : Nat =>
        (theta n : Real) / ((n : Real) ^ p * (2 : Real) ^ n))
      atTop atTop

/-- **Corollary 3.2.1.** A concrete lower bound valid for every positive
integer. -/
def corollary_3_2_1 : Prop :=
  forall n : Nat, 0 < n ->
    ((n : Real) * (2 : Real) ^ n) / 10 <= theta n

/-! ## Open problems -/

/-- Open problem (1): is `theta` monotone on the positive integers? -/
def open_problem_1 : Prop :=
  forall m n : Nat, 0 < m -> m <= n -> theta m <= theta n

/-- Open problem (2): does the `n`th-root growth rate converge? -/
def open_problem_2 : Prop :=
  exists L : Real, Tendsto exponentialRate atTop (nhds L)

/-- Open problem (3): does `theta(n+1) < 3 theta(n)` always hold? -/
def open_problem_3 : Prop :=
  forall n : Nat, 0 < n -> theta (n + 1) < 3 * theta n

end LeanProofs.Sharma2012
