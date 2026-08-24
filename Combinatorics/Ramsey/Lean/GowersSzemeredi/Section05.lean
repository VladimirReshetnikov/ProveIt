import GowersSzemeredi.Definitions

/-!
# Gowers (2001), Section 5: consequences of Weyl's inequality

This file records, as `Prop`-valued definitions, the statements of all fifteen
numbered results in Section 5 of "A new proof of Szemeredi's theorem".  No
result is asserted here.

The transcription is corrected where the printed statement conflicts with
its proof.  In particular, Lemma 5.2 has the factor `1 / 4`; the polynomial
partition results use the target-length form actually produced by their
proofs; Corollary 5.8 has density increment `alpha / 16`; the iterated
exponents in Lemma 5.10 and Corollary 5.11 are parenthesized according to
their proofs; and Lemma 5.14 uses the same polynomial constant as Corollary
5.7.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ## Section-specific notation -/

/-- The image in `ZMod N` of the integer interval `[-M, M)`. -/
noncomputable def centeredInterval (N M : Nat) : Finset (ZMod N) := by
  classical
  exact (Finset.Ico (-(M : Int)) (M : Int)).image fun x : Int => (x : ZMod N)

/-- A real-valued version of the paper's integral modular-diameter bound. -/
def diameterAtMostReal {N : Nat} (A : Finset (ZMod N)) (s : Real) : Prop :=
  exists d : Nat, diameterAtMost A d /\ (d : Real) <= s

/-- The lengths in a family of natural-number progressions differ by at most one. -/
def NatAPLengthsDifferAtMostOne {m : Nat} (P : Fin m -> NatAP) : Prop :=
  forall i j, (P i).length <= (P j).length + 1

/-- The constant `(k!)^2 2^((k+1)^2)` used in polynomial partitioning. -/
def polynomialPartitionConstant (k : Nat) : Nat :=
  (Nat.factorial k) ^ 2 * 2 ^ ((k + 1) ^ 2)

/-- The threshold `2^(2^(32 k^2))` in the explicit form of Weyl's inequality. -/
def weylThreshold (k : Nat) : Nat :=
  2 ^ (2 ^ (32 * k ^ 2))

/-- The threshold `2^(2^(40 k^2))` for one-polynomial partitioning. -/
def polynomialPartitionThreshold (k : Nat) : Nat :=
  2 ^ (2 ^ (40 * k ^ 2))

/-- The threshold in the simultaneous polynomial partition lemma. -/
def simultaneousPolynomialThreshold (k q : Nat) : Nat :=
  2 ^ ((2 ^ (40 * k ^ 2)) * polynomialPartitionConstant k ^ (q - 1))

/-- The constant `k^2 2^(k+3)` used for multilinear partitioning. -/
def multilinearPartitionConstant (k : Nat) : Nat :=
  k ^ 2 * 2 ^ (k + 3)

/-- The exponent `K^(-(2^k q))` resulting from `q` multilinear refinements. -/
def multilinearPartitionExponent (k q : Nat) : Real :=
  ((multilinearPartitionConstant k : Real) ^ (2 ^ k * q))⁻¹

/-- The corrected lower threshold in the `q`-map multilinear partition result. -/
def multilinearPartitionThreshold (k q : Nat) : Nat :=
  2 ^ (multilinearPartitionConstant k ^ (2 ^ k * q) * 2 ^ (32 * k ^ 2 + 1))

/-- The real exponential `e(x) = exp(2 pi i x)`. -/
def realExponential (x : Real) : Complex :=
  Complex.exp (((2 * Real.pi * x : Real) : Complex) * Complex.I)

/-- The monomial exponential sum occurring in Weyl's inequality. -/
def weylSum (alpha : Real) (k t : Nat) : Complex :=
  ∑ s ∈ Finset.Icc 1 t, realExponential (alpha * (s : Real) ^ k)

/-! ## Fourier estimates and Weyl approximation -/

/-- **Lemma 5.1.** Fourier decay of the centered interval.  The second
estimate is stated only away from frequency zero, where its denominator is
defined; this is the mathematically meaningful reading of the printed
minimum bound. -/
def lemma_5_1 : Prop :=
  forall (N M : Nat) [NeZero N], 2 * M <= N -> forall r : ZMod N,
    ‖fourier (indicator (centeredInterval N M)) r‖ <= 2 * M /\
      (r != 0 ->
        ‖fourier (indicator (centeredInterval N M)) r‖ <=
          (N : Real) / (2 * centeredAbs r))

/-- **Lemma 5.2.** A set avoiding a centered interval has a large low
Fourier coefficient.  The conclusion uses `t M / (4 N)`, as obtained in the
proof (rather than the erroneous `t M / (2 N)` in the printed statement). -/
def lemma_5_2 : Prop :=
  forall (N M t : Nat) [NeZero N] (A : Finset (ZMod N)),
    1 < N -> 0 < M -> Even M -> 2 * M <= N -> A.card = t ->
    Disjoint A (centeredInterval N M) ->
      exists r : ZMod N, r != 0 /\
        (centeredAbs r : Real) <= (N : Real) ^ 2 / (M : Real) ^ 2 /\
        (t : Real) * M / (4 * N) <= ‖fourier (indicator A) r‖

/-- **Lemma 5.3 (Weyl's inequality).** The first conjunct records the usual
constant depending on `k` and `epsilon`; the second records the paper's
explicit constant `1000` above its stated threshold. -/
def lemma_5_3 : Prop :=
  forall k : Nat, 1 <= k ->
    (forall epsilon : Real, 0 < epsilon -> exists C : Real, 0 <= C /\
      forall (t : Nat) (a q : Int) (alpha : Real),
        0 < q -> Int.gcd a q = 1 ->
        |alpha - (a : Real) / (q : Real)| <= ((q : Real) ^ 2)⁻¹ ->
        ‖weylSum alpha k t‖ <=
          C * (t : Real) ^ (1 + epsilon) *
            (((q : Real)⁻¹ + (t : Real)⁻¹ +
              (q : Real) * (t : Real) ^ (-(k : Real))) ^
                ((2 : Real) ^ (k - 1))⁻¹)) /\
    (forall (t : Nat) (a q : Int) (alpha : Real),
      weylThreshold k <= t -> 0 < q -> Int.gcd a q = 1 ->
      |alpha - (a : Real) / (q : Real)| <= ((q : Real) ^ 2)⁻¹ ->
      ‖weylSum alpha k t‖ <=
        1000 * (t : Real) ^
            (1 + ((k : Real) * (2 : Real) ^ (k + 1))⁻¹) *
          (((q : Real)⁻¹ + (t : Real)⁻¹ +
            (q : Real) * (t : Real) ^ (-(k : Real))) ^
              ((2 : Real) ^ (k - 1))⁻¹))

/-- **Lemma 5.4 (Dirichlet approximation).** -/
def lemma_5_4 : Prop :=
  forall (alpha : Real) (u : Nat), 1 <= u ->
    exists (a : Int) (q : Nat), 1 <= q /\ q <= u /\ Nat.Coprime a.natAbs q /\
      |alpha - (a : Real) / (q : Real)| <= ((q : Real) * u)⁻¹

/-- **Lemma 5.5.** Quantitative polynomial recurrence.  The positive lower
bound on `p` makes explicit the nonzero recurrence intended in the proof. -/
def lemma_5_5 : Prop :=
  forall (k t N : Nat) [NeZero N], 2 <= k -> weylThreshold k <= t -> t <= N ->
    forall a : ZMod N, exists p : Nat, 1 <= p /\ p <= t /\
      (centeredAbs (((p : ZMod N) ^ k) * a) : Real) <=
        (t : Real) ^ (-((k : Real) * (2 : Real) ^ (k + 1))⁻¹) * N

/-- The square-root-size strengthening obtained inside the proof of Lemma
5.5 and needed by the induction in Corollary 5.6.  The integral inequality
`p ^ 2 <= t` is the rounding-safe meaning of the proof's `p <= t^(1/2)`. -/
def lemma_5_5_square_root_auxiliary : Prop :=
  forall (k t N : Nat) [NeZero N], 2 <= k -> weylThreshold k <= t -> t <= N ->
    forall a : ZMod N, exists p : Nat, 1 <= p /\ p ^ 2 <= t /\
      (centeredAbs (((p : ZMod N) ^ k) * a) : Real) <=
        (t : Real) ^ (-((k : Real) * (2 : Real) ^ (k + 1))⁻¹) * N

/-! ## Polynomial partitioning -/

/-- **Corollary 5.6.** Partition into progressions of a prescribed target
length on which a polynomial has small diameter.  The printed exact-cell-count
form is false; its induction instead produces an emergent number of nonempty
cells, each of length `v - 1` or `v`.  The proof-supported bound `r <= N`
makes the invocation of Lemma 5.5 with scale `t = r` explicit. -/
def corollary_5_6 : Prop :=
  forall (N k r v : Nat) [NeZero N] (phi : ZMod N -> ZMod N),
    1 <= k -> PolynomialOn k Finset.univ phi ->
    polynomialPartitionThreshold k < r -> r <= N ->
    1 <= v -> (v : Real) <=
      (r : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ ->
      exists M : Nat, exists P : Fin M -> NatAP,
        0 < M /\ IsNatAPPartition P (Finset.range r) /\
        (forall j, (P j).IsProper /\ 0 < (P j).length /\
          ((P j).length = v - 1 \/ (P j).length = v)) /\
        forall j, diameterAtMostReal
          ((P j).carrier.image fun x : Nat => phi (x : ZMod N))
          ((r : Real) ^ (-(polynomialPartitionConstant k : Real)⁻¹) * N)

/-- **Corollary 5.7.** Polynomial bias becomes ordinary bias on the nonempty
cells of the target-length partition supplied by Corollary 5.6. -/
def corollary_5_7 : Prop :=
  forall (N k r v : Nat) [NeZero N] (phi : ZMod N -> ZMod N) (alpha : Real),
    1 <= k -> PolynomialOn k Finset.univ phi -> 0 < alpha ->
    max (polynomialPartitionThreshold k : Real)
        ((4 * Real.pi / alpha) ^ polynomialPartitionConstant k) < r ->
    r <= N -> 1 <= v -> (v : Real) <=
      (r : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ ->
      exists M : Nat, exists P : Fin M -> NatAP,
        0 < M /\ IsNatAPPartition P (Finset.range r) /\
        (forall j, (P j).IsProper /\ 0 < (P j).length /\
          ((P j).length = v - 1 \/ (P j).length = v)) /\
        forall f : ZMod N -> Complex, DiscValued f ->
          alpha * r <=
            ‖∑ s ∈ Finset.range r,
              f (s : ZMod N) * exponential (-(phi (s : ZMod N)))‖ ->
          (alpha / 2) * r <=
            ∑ j, ‖∑ s ∈ (P j).carrier, f (s : ZMod N)‖

/-- **Corollary 5.8.** A family of local polynomial correlations yields a
density increment.  The conclusion is corrected from `delta + alpha / 8`
to the `delta + alpha / 16` actually established by the proof. -/
def corollary_5_8 : Prop :=
  forall (N k M : Nat) [NeZero N] (A : Finset (ZMod N))
      (P : Fin M -> ModAP N) (phi : Fin M -> ZMod N -> ZMod N)
      (delta alpha : Real),
    1 <= k -> 0 < M -> 0 < alpha -> (A.card : Real) = delta * N ->
    (forall i, (P i).IsProper /\ PolynomialOn k Finset.univ (phi i)) ->
    (forall x, x ∈ A -> exists i, x ∈ (P i).carrier) ->
    (forall i j, i != j -> Disjoint (P i).carrier (P j).carrier) ->
    (forall i j, (P i).carrier.card <= 2 * (P j).carrier.card) ->
    alpha * N <= ∑ i, ‖∑ s ∈ (P i).carrier,
      balanced A s * exponential (-(phi i s))‖ ->
      exists Q : ModAP N, Q.IsProper /\
        ((N : Real) / M) ^ (polynomialPartitionConstant k : Real)⁻¹ / 8 <=
          Q.carrier.card /\
        (delta + alpha / 16) * Q.carrier.card <= (A ∩ Q.carrier).card

/-- **Lemma 5.9.** Simultaneous small-diameter partitioning for finitely many
modular polynomials, in the target-length form supported by its refinement
proof. -/
def lemma_5_9 : Prop :=
  forall (N k q r v : Nat) [NeZero N]
      (phi : Fin q -> ZMod N -> ZMod N),
    1 <= k -> 1 <= q -> (forall i, PolynomialOn k Finset.univ (phi i)) ->
    simultaneousPolynomialThreshold k q < r -> r <= N ->
    1 <= v -> (v : Real) <= (r : Real) ^
      (2 * (polynomialPartitionConstant k : Real) ^ q)⁻¹ ->
      exists M : Nat, exists P : Fin M -> NatAP,
        0 < M /\ IsNatAPPartition P (Finset.range r) /\
        (forall j, (P j).IsProper /\ 0 < (P j).length /\
          ((P j).length = v - 1 \/ (P j).length = v)) /\
        forall i j, diameterAtMostReal
          ((P j).carrier.image fun x : Nat => phi i (x : ZMod N))
          ((r : Real) ^
            (-((polynomialPartitionConstant k : Real) ^ q)⁻¹) * N)

/-! ## Multilinear partitioning -/

/-- **Lemma 5.10.** Small-diameter partitioning for one multilinear map.
The threshold is `2^(K^(2^k) * 2^(32 k^2+1))`, and the scale exponent is
`K^(-2^k)`, as dictated by the height induction. -/
def lemma_5_10 : Prop :=
  forall (N k m : Nat) [NeZero N] (P : Box N k) (mu : Point N k -> ZMod N),
    2 <= k -> multilinearPartitionThreshold k 1 <= m -> m <= P.width ->
    MultilinearOn P.carrier mu ->
      exists M : Nat, exists Q : Fin M -> Box N k,
        IsBoxPartition Q P /\
        forall j,
          (m : Real) ^ multilinearPartitionExponent k 1 <= (Q j).width /\
          diameterAtMostReal ((Q j).carrier.image mu)
            (2 * (m : Real) ^ (-multilinearPartitionExponent k 1) * N)

/-- **Corollary 5.11.** Simultaneous small-diameter partitioning for `q`
multilinear maps.  Repeating Lemma 5.10 gives exponent
`K^(-(2^k q))`, not the OCR's ambiguous product. -/
def corollary_5_11 : Prop :=
  forall (N k q m : Nat) [NeZero N] (P : Box N k)
      (mu : Fin q -> Point N k -> ZMod N),
    2 <= k -> 1 <= q -> multilinearPartitionThreshold k q <= m -> m <= P.width ->
    (forall i, MultilinearOn P.carrier (mu i)) ->
      exists M : Nat, exists Q : Fin M -> Box N k,
        IsBoxPartition Q P /\
        forall i j,
          (m : Real) ^ multilinearPartitionExponent k q <= (Q j).width /\
          diameterAtMostReal ((Q j).carrier.image (mu i))
            (2 * (m : Real) ^ (-multilinearPartitionExponent k q) * N)

/-! ## Final partition and density lemmas -/

/-- **Lemma 5.12.** A modular progression of size `m` has a partition into
at most `4 sqrt(m)` proper progressions. -/
def lemma_5_12 : Prop :=
  forall (N m : Nat) [NeZero N] (Q : ModAP N), Q.carrier.card = m ->
    exists L : Nat, exists P : Fin L -> ModAP N,
      IsPartition (fun j => (P j).carrier) Q.carrier /\
      (forall j, (P j).IsProper) /\ (L : Real) <= 4 * Real.sqrt m

/-- **Lemma 5.13.** A modular-progression partition of `ZMod N` has a
proper refinement with at most `4 sqrt(N M)` cells. -/
def lemma_5_13 : Prop :=
  forall (N M : Nat) [NeZero N] (Q : Fin M -> ModAP N),
    IsPartition (fun i => (Q i).carrier) Finset.univ ->
      exists L : Nat, exists R : Fin L -> ModAP N,
        IsRefinement (fun j => (R j).carrier) (fun i => (Q i).carrier) /\
        (forall j, (R j).IsProper) /\
        (L : Real) <= 4 * Real.sqrt ((N : Real) * M)

/-- **Lemma 5.14.** Removing a fixed polynomial phase after refining a
progression partition.  The polynomial constant is corrected to
`(k!)^2 2^((k+1)^2)`, consistently with Corollary 5.7.  The proof's implicit
partition hypothesis and its constant `C = C(k, alpha)` are explicit. -/
def lemma_5_14 : Prop :=
  forall (k : Nat) (alpha : Real), 1 <= k -> 0 < alpha ->
    exists C : Real, 0 < C /\ forall (N M : Nat) [NeZero N]
        (phi : ZMod N -> ZMod N) (f : ZMod N -> Real)
        (Q : Fin M -> ModAP N),
      PolynomialOn k Finset.univ phi -> (forall s, |f s| <= 1) ->
      IsPartition (fun i => (Q i).carrier) Finset.univ ->
      alpha * N <= ∑ i, ‖∑ s ∈ (Q i).carrier,
        (f s : Complex) * exponential (-(phi s))‖ ->
        exists L : Nat, exists R : Fin L -> ModAP N,
          IsRefinement (fun j => (R j).carrier) (fun i => (Q i).carrier) /\
          (forall j, (R j).IsProper) /\
          (L : Real) <= C * (M : Real) ^
              (polynomialPartitionConstant k : Real)⁻¹ *
            (N : Real) ^ (1 - (polynomialPartitionConstant k : Real)⁻¹) /\
          (alpha / 2) * N <= ∑ j, |∑ s ∈ (R j).carrier, f s|

/-- **Lemma 5.15.** A large total cell discrepancy and mean zero force a
large positive discrepancy on a sufficiently large cell. -/
def lemma_5_15 : Prop :=
  forall (N M : Nat) [NeZero N] (f : ZMod N -> Real)
      (P : Fin M -> Finset (ZMod N)) (alpha : Real),
    0 < M -> 0 <= alpha -> (forall s, |f s| <= 1) ->
    (∑ s : ZMod N, f s) = 0 -> IsPartition P Finset.univ ->
    alpha * N <= ∑ j, |∑ s ∈ P j, f s| ->
      exists j, alpha * (P j).card / 4 <= ∑ s ∈ P j, f s /\
        alpha * N / (4 * M) <= (P j).card

end LeanProofs.GowersSzemeredi
