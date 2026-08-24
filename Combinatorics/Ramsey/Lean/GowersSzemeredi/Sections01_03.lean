import GowersSzemeredi.Definitions

/-!
# Gowers (2001), Sections 1--3: formal statements

Every numbered result in Sections 1--3 of "A new proof of Szemeredi's
theorem" is represented below by a `Prop`-valued definition.  Consequently
this file records the statements, but asserts none of them.  The six displayed
Fourier identities preceding Lemma 2.2 are recorded as well because later
statements refer to them by number.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ## Section 1: Introduction -/

/-- **Theorem 1.1 (van der Waerden).** -/
def theorem_1_1 : Prop :=
  forall k r : Nat, 0 < k -> 0 < r ->
    exists M : Nat, 0 < M /\ forall color : Nat -> Fin r,
      HasMonochromaticAP M r color k

/-- **Theorem 1.2 (Szemeredi).** -/
def theorem_1_2 : Prop :=
  forall (k : Nat) (delta : Real), 0 < k -> 0 < delta ->
    exists N : Nat, 0 < N /\ forall A : Finset Nat,
      A ⊆ Finset.Icc 1 N -> delta * N <= A.card -> HasNatAP A k

/-- The explicit constant in Theorem 1.3. -/
def theorem_1_3_constant (k : Nat) : Real :=
  (2 : Real) ^ (-((2 : Real) ^ (k + 9 : Nat)))

/-- **Theorem 1.3.** The quantitative headline theorem, with the paper's
implicit "for all sufficiently large `N`" made explicit. -/
def theorem_1_3 : Prop :=
  forall k : Nat, 0 < k -> exists N0 : Nat, forall N : Nat, N0 <= N ->
    forall A : Finset Nat, A ⊆ Finset.Icc 1 N ->
      (N : Real) * (Real.log (Real.log N)) ^ (-theorem_1_3_constant k) <= A.card ->
      HasNatAP A k

/-! ## Section 2: Uniform sets and Roth's theorem -/

/-- Fourier identity (1): correlation transforms to a pointwise product. -/
def identity_2_1 : Prop :=
  forall (N : Nat) [NeZero N] (f g : ZMod N -> Complex) (r : ZMod N),
    fourier (correlation f g) r = fourier f r * star (fourier g r)

/-- Fourier identity (2): Parseval's identity. -/
def identity_2_2 : Prop :=
  forall (N : Nat) [NeZero N] (f g : ZMod N -> Complex),
    (∑ r : ZMod N, fourier f r * star (fourier g r)) =
      (N : Complex) * ∑ s : ZMod N, f s * star (g s)

/-- Fourier identity (3): the square-norm form of Parseval. -/
def identity_2_3 : Prop :=
  forall (N : Nat) [NeZero N] (f : ZMod N -> Complex),
    (∑ r : ZMod N, ‖fourier f r‖ ^ 2) =
      (N : Real) * ∑ s : ZMod N, ‖f s‖ ^ 2

/-- Fourier identity (4): inversion. -/
def identity_2_4 : Prop :=
  forall (N : Nat) [NeZero N] (f : ZMod N -> Complex) (s : ZMod N),
    f s = (N : Complex)⁻¹ *
      ∑ r : ZMod N, fourier f r * exponential (r * s)

/-- **Lemma 2.1 / identity (5).** -/
def lemma_2_1 : Prop :=
  forall (N : Nat) [NeZero N] (f g : ZMod N -> Complex),
    (∑ r : ZMod N, ‖fourier f r‖ ^ 2 * ‖fourier g r‖ ^ 2) =
      (N : Real) * ∑ t : ZMod N,
        ‖∑ s : ZMod N, f s * star (g (s - t))‖ ^ 2

/-- Fourier identity (6), the additive-quadruple form of the fourth moment. -/
def identity_2_6 : Prop :=
  forall (N : Nat) [NeZero N] (f : ZMod N -> Complex),
    ((∑ r : ZMod N, ‖fourier f r‖ ^ 4 : Real) : Complex) =
      (N : Complex) * ∑ q : Fin 4 -> ZMod N,
        if q 0 - q 1 = q 2 - q 3
          then f (q 0) * star (f (q 1) * f (q 2)) * f (q 3)
          else 0

/-! The five conditions in Lemma 2.2. -/

def uniformCondition2i {N : Nat} [NeZero N]
    (f : ZMod N -> Complex) (c : Real) : Prop :=
  ∑ k : ZMod N, ‖∑ s : ZMod N, f s * star (f (s - k))‖ ^ 2 <=
    c * (N : Real) ^ 3

def uniformCondition2ii {N : Nat} [NeZero N]
    (f : ZMod N -> Complex) (c : Real) : Prop :=
  (∑ q : Fin 4 -> ZMod N,
      if q 0 - q 1 = q 2 - q 3
        then f (q 0) * star (f (q 1) * f (q 2)) * f (q 3)
        else 0).re <= c * (N : Real) ^ 3

def uniformCondition2iii {N : Nat} [NeZero N]
    (f : ZMod N -> Complex) (c : Real) : Prop :=
  ∑ r : ZMod N, ‖fourier f r‖ ^ 4 <= c * (N : Real) ^ 4

def uniformCondition2iv {N : Nat} [NeZero N]
    (f : ZMod N -> Complex) (c : Real) : Prop :=
  forall r : ZMod N, ‖fourier f r‖ <= c * N

def uniformCondition2v {N : Nat} [NeZero N]
    (f : ZMod N -> Complex) (c : Real) : Prop :=
  forall g : ZMod N -> Complex,
    ∑ k : ZMod N, ‖∑ s : ZMod N, f s * star (g (s - k))‖ ^ 2 <=
      c * (N : Real) ^ 2 * ∑ s : ZMod N, ‖g s‖ ^ 2

/-- **Lemma 2.2.** The paper calls these conditions equivalent while allowing
the constants to change.  This definition records the exact implications and
power losses stated in its proof. -/
def lemma_2_2 : Prop :=
  forall (N : Nat) [NeZero N] (f : ZMod N -> Complex), DiscValued f ->
    forall c1 c2 c3 : Real,
      (uniformCondition2i f c1 <-> uniformCondition2ii f c1) /\
      (uniformCondition2i f c1 <-> uniformCondition2iii f c1) /\
      (c1 ^ ((1 : Real) / 4) <= c2 ->
        uniformCondition2iii f c1 -> uniformCondition2iv f c2) /\
      (c2 ^ 2 <= c1 -> uniformCondition2iv f c2 -> uniformCondition2iii f c1) /\
      (c3 <= c1 -> uniformCondition2v f c3 -> uniformCondition2i f c1) /\
      (c1 ^ ((1 : Real) / 2) <= c3 ->
        uniformCondition2iii f c1 -> uniformCondition2v f c3)

/-- A map from the first `r` natural numbers is affine-linear modulo `N`. -/
def NatToZModLinear {N : Nat} (r : Nat) (phi : Nat -> ZMod N) : Prop :=
  exists a b : ZMod N, ∀ x, x < r → phi x = a * (x : Nat) + b

/-- **Lemma 2.3.** The printed lower bound `sqrt (r*s/(4*N))` is not
compatible with integer rounding: for `N=r=s=5` and a constant map it would
force a partition of five points into cells all of size two.  The denominator
`16` is the uniform bound supported by the proof after accounting for the
ceiling in its choice of the auxiliary step. -/
def lemma_2_3 : Prop :=
  forall (N r s : Nat), 0 < N -> 0 < r -> 0 < s -> r <= N -> s <= N -> N <= r * s ->
    forall phi : Nat -> ZMod N, NatToZModLinear r phi ->
      exists m : Nat, exists P : Fin m -> NatAP,
        IsNatAPPartition P (Finset.range r) /\
        (forall j, (P j).IsProper /\ diameterAtMost ((P j).carrier.image phi) s /\
          Real.sqrt ((r : Real) * s / (16 * N)) <= (P j).length /\
          ((P j).length : Real) <= Real.sqrt ((r : Real) * s / N))

/-- **Corollary 2.4.** The OCR's `phi(s)` in the hypothesis is corrected to
`phi(x)`, as required by the bound and by the proof.  For an exact finite
statement, `r ≤ N` and the scale condition `4π ≤ αr` ensure that positive
integer progression lengths can meet the asserted upper bound.  Above the
next rounding threshold an integer diameter parameter exists; below it the
singleton partition applies.  Lemma 2.3's rounding-corrected lower length
bound propagates the constant `128` below.  Properness is recorded explicitly,
as it is needed when the cell lengths are used in Corollary 2.5. -/
def corollary_2_4 : Prop :=
  forall (N r : Nat) [NeZero N] (f : Nat -> Complex) (phi : ZMod N -> ZMod N)
      (alpha : Real),
    r <= N -> 4 * Real.pi <= alpha * r ->
    (∀ x, x < r → ‖f x‖ <= 1) -> LinearOn Finset.univ phi -> 0 < alpha ->
    alpha * r <= ‖∑ x ∈ Finset.range r, f x * exponential (-(phi x))‖ ->
    exists m : Nat, exists P : Fin m -> NatAP,
      IsNatAPPartition P (Finset.range r) /\
      (m : Real) <= Real.sqrt (128 * Real.pi * r / alpha) /\
      (alpha / 2) * r <= ∑ j, ‖∑ x ∈ (P j).carrier, f x‖ /\
      (forall j, (P j).IsProper /\
        Real.sqrt (alpha * r / (128 * Real.pi)) <= (P j).length /\
        ((P j).length : Real) <= Real.sqrt (alpha * r / (4 * Real.pi)))

/-- The pullback of a modular set to the standard representatives `0,...,N-1`. -/
noncomputable def standardRepresentatives {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) : Finset Nat := by
  classical
  exact (Finset.range N).filter fun x => (x : ZMod N) ∈ A

/-- **Corollary 2.5.** The source's unbound `delta` is read as the density of
`A`, which is also how `delta` is used in the proof. -/
def corollary_2_5 : Prop :=
  forall (N : Nat) [NeZero N] (A : Finset (ZMod N)) (alpha : Real), 0 < alpha ->
    (exists r : ZMod N, r != 0 /\ alpha * N <= ‖fourier (indicator A) r‖) ->
    exists P : NatAP, P.IsProper /\ P.carrier ⊆ Finset.range N /\
      Real.sqrt (alpha ^ 3 * N / (128 * Real.pi)) <= P.length /\
      (density A + alpha / 8) * P.length <=
        ((P.carrier ∩ standardRepresentatives A).card : Real)

/-- **Theorem 2.6 (Roth).** -/
def theorem_2_6 : Prop :=
  exists C : Real, 0 < C /\ forall (delta : Real) (N : Nat), 0 < delta ->
    Real.exp (Real.exp (C * delta⁻¹)) <= N -> forall A : Finset Nat,
      A ⊆ Finset.Icc 1 N -> delta * N <= A.card -> HasNatAP A 3

/-! ## Section 3: Higher-degree uniformity -/

def higherUniformConditionii {N : Nat} [NeZero N]
    (f : ZMod N -> Complex) (c : Real) (d : Nat) : Prop :=
  (∑ a : Point N (d + 1), ∑ s : ZMod N, cubeDifference f a s).re <=
    c * (N : Real) ^ (d + 2)

def higherUniformConditioniii {N : Nat} [NeZero N]
    (f : ZMod N -> Complex) (c : Real) (d : Nat) : Prop :=
  exists alpha : Point N (d - 1) -> Real,
    (forall a, 0 <= alpha a /\ alpha a <= 1) /\
    (∑ a, alpha a) <= c * (N : Real) ^ (d - 1) /\
    (forall a, UniformOfDegree (cubeDifference f a) (alpha a) 1)

def higherUniformConditioniv {N : Nat} [NeZero N]
    (f : ZMod N -> Complex) (c : Real) (d : Nat) : Prop :=
  exists alpha : ZMod N -> Real,
    (forall r, 0 <= alpha r /\ alpha r <= 1) /\
    (∑ r, alpha r) = c * N /\
    (forall r, UniformOfDegree (difference f r) (alpha r) (d - 1))

def higherUniformConditionv {N : Nat} [NeZero N]
    (f : ZMod N -> Complex) (c : Real) (d : Nat) : Prop :=
  ∑ a : Point N (d - 1), ∑ r : ZMod N,
      ‖fourier (cubeDifference f a) r‖ ^ 4 <= c * (N : Real) ^ (d + 3)

def higherUniformConditionvi {N : Nat} [NeZero N]
    (f : ZMod N -> Complex) (c : Real) (d : Nat) : Prop :=
  (countWhere fun a : Point N (d - 1) =>
      ¬ UniformOfDegree (cubeDifference f a) c 1 : Real) <=
    c * (N : Real) ^ (d - 1)

def higherUniformConditionvii {N : Nat} [NeZero N]
    (f : ZMod N -> Complex) (c : Real) (d : Nat) : Prop :=
  (countWhere fun a : Point N (d - 1) =>
      exists r : ZMod N, c * N <= ‖fourier (cubeDifference f a) r‖ : Real) <=
    c * (N : Real) ^ (d - 1)

/-- **Lemma 3.1.** Exact equivalences and quantitative implications stated in
the proof of the paper's approximate-equivalence formulation. -/
def lemma_3_1 : Prop :=
  forall (N d : Nat) [NeZero N] (f : ZMod N -> Complex), 1 <= d -> DiscValued f ->
    forall c1 c2 c3 : Real,
      0 <= c1 -> c1 <= 1 -> 0 <= c2 -> c2 <= 1 -> 0 <= c3 -> c3 <= 1 ->
      (UniformOfDegree f c1 d <-> higherUniformConditionii f c1 d) /\
      (higherUniformConditionii f c1 d <-> higherUniformConditioniii f c1 d) /\
      (higherUniformConditionii f c1 d <-> higherUniformConditioniv f c1 d) /\
      (UniformOfDegree f c1 d <-> higherUniformConditionv f c1 d) /\
      (c1 <= c2 ^ 2 -> higherUniformConditioniii f c1 d ->
        higherUniformConditionvi f c2 d) /\
      (2 * c2 <= c1 -> higherUniformConditionvi f c2 d ->
        higherUniformConditioniii f c1 d) /\
      (c2 ^ ((1 : Real) / 4) < c3 -> higherUniformConditionvi f c2 d ->
        higherUniformConditionvii f c3 d) /\
      (c3 <= c2 -> higherUniformConditionvii f c3 d ->
        higherUniformConditionvi f c2 d)

/-- The multilinear progression average in Theorem 3.2. -/
def progressionAverage {N k : Nat} [NeZero N]
    (f : Fin k -> ZMod N -> Complex) : Complex :=
  ∑ r : ZMod N, ∑ s : ZMod N, ∏ i, f i (s - (i : Nat) * r)

/-- **Theorem 3.2.** The prime-modulus hypothesis and `k ≤ N` make every
nonzero progression coefficient occurring in the induction invertible. -/
def theorem_3_2 : Prop :=
  forall (N k : Nat) [NeZero N] [Fact N.Prime], 2 <= k -> k <= N ->
    forall f : Fin k -> ZMod N -> Complex, (forall i, DiscValued (f i)) ->
      forall alpha : Real, 0 <= alpha ->
        (forall i : Fin k, (i : Nat) + 1 = k ->
          UniformOfDegree (f i) alpha (k - 2)) ->
        ‖progressionAverage f‖ <=
          alpha ^ ((1 : Real) / (2 : Real) ^ (k - 1)) * (N : Real) ^ 2

/-- The total number of translated intersections in Corollary 3.3. -/
noncomputable def translatedIntersectionCount {N k : Nat} [NeZero N]
    (A : Fin k -> Finset (ZMod N)) : Nat :=
  countWhere fun p : ZMod N × ZMod N =>
    forall i, p.2 - ((i : Nat) + 1) * p.1 ∈ A i

/-- **Corollary 3.3.** -/
def corollary_3_3 : Prop :=
  forall (N k : Nat) [NeZero N] (A : Fin k -> Finset (ZMod N))
      (delta : Fin k -> Real) (alpha : Real),
    (forall i, (A i).card = delta i * N) ->
    (forall i : Fin k, 3 <= (i : Nat) + 1 ->
      UniformSetOfDegree (A i) (alpha ^ ((2 : Nat) ^ (i : Nat))) ((i : Nat) - 1)) ->
    |(translatedIntersectionCount A : Real) -
        (∏ i, delta i) * (N : Real) ^ 2| <= 2 ^ k * alpha * (N : Real) ^ 2

/-- **Lemma 3.4.** -/
def lemma_3_4 : Prop :=
  forall (N d : Nat) [NeZero N] (f : ZMod N -> Complex) (alpha : Real),
    1 <= d -> DiscValued f -> UniformOfDegree f alpha d ->
      UniformOfDegree f (alpha ^ ((1 : Real) / 2)) (d - 1)

/-- **Lemma 3.5 (corrected).**

The interval length must be at most `N`; otherwise its modular carrier repeats while the
right-hand main term still grows with `M`.  The printed proof also incorrectly claims that the
`L^(4/3)` mass of the interval's nonzero Fourier coefficients is at most `N^(4/3)`.  The elementary
decay estimate used there gives the safe constant `3` below. -/
def lemma_3_5 : Prop :=
  forall (N : Nat) [NeZero N] (A : Finset (ZMod N)) (alpha delta beta : Real)
      (a : ZMod N) (M : Nat),
    (A.card : Real) = delta * N -> UniformSetOfDegree A alpha 1 ->
    M <= N -> (M : Real) = beta * N ->
    |((A ∩ (modInterval N (a + 1) M).carrier).card : Real) - beta * delta * N| <=
      3 * alpha ^ ((1 : Real) / 4) * N

/-- **Corollary 3.6.** -/
def corollary_3_6 : Prop :=
  forall (N k : Nat) [NeZero N] (A : Finset (ZMod N)) (alpha delta : Real),
    2 <= k -> (A.card : Real) = delta * N ->
    UniformSetOfDegree A alpha (k - 2) ->
    alpha <= (delta / 2) ^ ((k : Real) * 2 ^ k) ->
    32 * (k : Real) ^ 2 * delta ^ (-(k : Real)) <= N ->
    HasModAP A k

/-- **Lemma 3.7.** -/
def lemma_3_7 : Prop :=
  forall (N d : Nat) [NeZero N] (A : Finset (ZMod N)) (delta : Real),
    (A.card : Real) = delta * N ->
    delta ^ ((2 : Nat) ^ d) * (N : Real) ^ (d + 1) <= cubeCount (d := d) A

/-- **Lemma 3.8 (Gowers--Cauchy--Schwarz).** -/
def lemma_3_8 : Prop :=
  forall (N d : Nat) [NeZero N]
      (f : (Fin d -> Bool) -> ZMod N -> Complex),
    (forall e, DiscValued (f e)) ->
    ‖cubeForm f‖ <= ∏ e : Fin d -> Bool,
      ‖cubeForm (d := d) (fun (_ : Fin d -> Bool) => f e)‖ ^
        ((1 : Real) / (2 : Real) ^ d)

/-- **Lemma 3.9 (Minkowski for the Gowers norm).** -/
def lemma_3_9 : Prop :=
  forall (N d : Nat) [NeZero N], 2 <= d -> forall f g : ZMod N -> Complex,
    gowersNorm d (f + g) <= gowersNorm d f + gowersNorm d g

/-- **Lemma 3.10.** -/
def lemma_3_10 : Prop :=
  forall (N d : Nat) [NeZero N] (A : Finset (ZMod N)) (alpha delta : Real),
    (A.card : Real) = delta * N -> UniformSetOfDegree A alpha (d - 1) ->
    (cubeCount (d := d) A : Real) <=
      (delta + alpha ^ ((1 : Real) / (2 : Real) ^ d)) ^ ((2 : Nat) ^ d) *
        (N : Real) ^ (d + 1)

end LeanProofs.GowersSzemeredi
