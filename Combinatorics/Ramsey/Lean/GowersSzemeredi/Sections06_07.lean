import GowersSzemeredi.Definitions

/-!
# Gowers (2001), Sections 6--7: formal statements

Every numbered result in Sections 6 and 7 of W. T. Gowers,
"A new proof of Szemeredi's theorem", is represented below by a
`Prop`-valued definition.  Thus this file records the statements without
asserting them.

As elsewhere in this formalization, a partial map in the paper is represented
by a total map together with the `Finset` on which it is being considered.
The corrections recorded in the source audit are incorporated in the
statements and documented at the relevant results.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod Combinatorics.Additive
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ## Section 6: Somewhat additive functions -/

/-- The graph of a function restricted to a finite domain. -/
noncomputable def functionGraph {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (A : Finset X) (phi : X -> Y) : Finset (X × Y) := by
  classical
  exact A.image fun x => (x, phi x)

/-- **Proposition 6.1.** Large Fourier coefficients of many first differences
force many quadruples that are additive both before and after applying
`phi`. -/
def proposition_6_1 : Prop :=
  forall (N : Nat) [NeZero N] (alpha : Real) (f : ZMod N -> Complex)
      (B : Finset (ZMod N)) (phi : ZMod N -> ZMod N),
    0 < alpha -> DiscValued f ->
    alpha * (N : Real) ^ 3 <=
      ∑ k ∈ B, ‖fourier (difference f k) (phi k)‖ ^ 2 ->
    alpha ^ 4 * (N : Real) ^ 3 <= phiAdditiveCount B phi

/-- **Lemma 6.2.** The graph of a `gamma`-additive function contains the
same number of additive quadruples, now viewed in the product group. -/
def lemma_6_2 : Prop :=
  forall (N : Nat) [NeZero N] (gamma : Real) (B : Finset (ZMod N))
      (phi : ZMod N -> ZMod N),
    0 < gamma -> GammaAdditive B phi gamma ->
    gamma * (N : Real) ^ 3 <=
      Finset.addEnergy (functionGraph B phi) (functionGraph B phi)

/-! ## Section 7: Variations on a theorem of Freiman -/

/-! ### Integer and generalized progressions -/

/-- A finite arithmetic progression in the integers.  This local variant of
`NatAP` is needed in Corollary 7.11, where the ambient progression may begin
at a negative integer. -/
structure IntAP where
  start : Int
  step : Nat
  length : Nat

/-- The finite set underlying an integer arithmetic progression. -/
noncomputable def IntAP.carrier (P : IntAP) : Finset Int := by
  classical
  exact Finset.univ.image fun i : Fin P.length =>
    P.start + ((i : Nat) * P.step : Nat)

/-- An integer progression is genuine when it has positive common difference
and no repeated terms. -/
def IntAP.IsProper (P : IntAP) : Prop :=
  0 < P.step /\ P.carrier.card = P.length

/-- A finite family of integer progressions partitions `R`. -/
def IsIntAPPartition {m : Nat} (P : Fin m -> IntAP) (R : IntAP) : Prop :=
  IsPartition (fun i => (P i).carrier) R.carrier

/-- A modular-valued map is affine-linear, in progression coordinates, on
the points of `A` lying in `P`.  Progression coordinates are essential here:
the common difference of an integer progression need not be invertible in
`ZMod N`. -/
def IntAPLinearOn {N : Nat} (P : IntAP) (A : Finset Int)
    (phi : Int -> ZMod N) : Prop :=
  exists a b : ZMod N, forall i : Fin P.length,
    let x := P.start + ((i : Nat) * P.step : Nat)
    x ∈ A -> phi x = a * (i : Nat) + b

/-- The structured covering conclusion in Freiman's theorem for subsets of
the integers. -/
def HasFreimanCover (A : Finset Int) (d0 : Nat) (K : Real) : Prop :=
  exists P : GeneralizedAP Int,
    P.dimension <= d0 /\
    (forall i, 0 < P.step i /\ 0 < P.length i) /\
    (P.size : Real) <= K * A.card /\
    A ⊆ P.carrier

/-- **Theorem 7.1 (Freiman).** Both the small-sumset and small-difference-set
forms stated in the paper are included. -/
def theorem_7_1 : Prop :=
  forall C : Real, 0 < C ->
    exists d0 : Nat, exists K : Real, 0 < K /\ forall A : Finset Int,
      ((((A + A).card : Real) <= C * A.card) -> HasFreimanCover A d0 K) /\
      ((((A - A).card : Real) <= C * A.card) -> HasFreimanCover A d0 K)

/-- The conclusion of the Balog--Szemeredi theorem, expressed using the
generalized progressions from `Definitions.lean`. -/
def HasBalogSzemerediProgression {D : Nat} (A : Finset (Fin D -> Int))
    (c K : Real) (d0 : Nat) : Prop :=
  exists P : GeneralizedAP (Fin D -> Int),
    P.dimension <= d0 /\
    (forall i, 0 < P.length i) /\
    (P.size : Real) <= K * A.card /\
    c * A.card <= ((A ∩ P.carrier).card : Real)

/-- **Theorem 7.2 (Balog--Szemeredi).** Large additive energy forces a
positive proportion of the set into a bounded-dimensional generalized
progression of comparable formal size. -/
def theorem_7_2 : Prop :=
  forall c0 : Real, 0 < c0 ->
    exists c K : Real, exists d0 : Nat, 0 < c /\ 0 < K /\
      forall (D : Nat) (A : Finset (Fin D -> Int)),
        c0 * (A.card : Real) ^ 3 <= Finset.addEnergy A A ->
        HasBalogSzemerediProgression A c K d0

/-- **Proposition 7.3.** The quantitative Balog--Szemeredi reduction, with
the explicit constants given in the paper. -/
def proposition_7_3 : Prop :=
  forall (n : Nat) (A : Finset (Fin n -> Int)) (c0 : Real),
    0 < c0 -> c0 * (A.card : Real) ^ 3 <= Finset.addEnergy A A ->
    exists A'' : Finset (Fin n -> Int),
      A'' ⊆ A /\
      (2 : Real) ^ (-(20 : Real)) * c0 ^ 12 * A.card <= A''.card /\
      (((A'' - A'').card : Real) <=
        (2 : Real) ^ (38 : Nat) * c0 ^ (-(24 : Real)) * A.card)

/-! ### The dense-intersection lemma -/

/-- The number of ordered pairs in `K^2` whose corresponding sets have
intersection at least `threshold`. -/
noncomputable def largeIntersectionPairCount {X : Type*} [DecidableEq X]
    {n : Nat} (A : Fin n -> Finset X) (K : Finset (Fin n))
    (threshold : Real) : Nat := by
  classical
  exact (K ×ˢ K).filter
    (fun xy => threshold <= (((A xy.1 ∩ A xy.2).card : Nat) : Real)) |>.card

/-- The dense core supplied by Lemma 7.4. -/
def HasDenseIntersectionCore {X : Type*} [DecidableEq X] {n : Nat}
    (m : Nat) (A : Fin n -> Finset X) (delta : Real) : Prop :=
  exists K : Finset (Fin n),
    (2 : Real) ^ (-(1 : Real) / 2) * delta ^ 5 * n <= K.card /\
    (9 : Real) / 10 * (K.card : Real) ^ 2 <=
      largeIntersectionPairCount A K (delta ^ 2 * m / 2)

/-- **Lemma 7.4.** The final conjunct records the paper's "in particular"
clause as well as its main implication.  We make explicit the standard density
bound `delta <= 1`; without it the conclusion is false (for example, take one
empty set and `delta > 1`). -/
def lemma_7_4 : Prop :=
  forall (X : Type*) [DecidableEq X] (m n : Nat) (V : Finset X)
      (A : Fin n -> Finset X) (delta : Real),
    V.card = m -> (forall i, A i ⊆ V) -> 0 < delta -> delta <= 1 ->
    ((delta ^ 2 * m * (n : Real) ^ 2 <=
        ∑ x, ∑ y, (((A x ∩ A y).card : Nat) : Real)) ->
      HasDenseIntersectionCore m A delta) /\
    ((forall x, delta * m <= (A x).card) ->
      HasDenseIntersectionCore m A delta)

/-! ### Freiman restrictions and Bohr neighborhoods -/

/-- **Lemma 7.5.** The OCR's `C` in the conclusion is corrected to `B'`:
it is the restriction of `phi` to the newly found subset that is a Freiman
homomorphism.  Primality makes explicit the paper's standing convention for
`ZMod N`, which is used in this lemma's proof. -/
def lemma_7_5 : Prop :=
  forall (N k : Nat) [NeZero N] (B : Finset (ZMod N))
      (phi : ZMod N -> ZMod N) (C : Real),
    Nat.Prime N -> 0 < k -> 0 < C ->
    (((functionGraph B phi - functionGraph B phi).card : Real) <=
      C * (functionGraph B phi).card) ->
    exists B' : Finset (ZMod N),
      B' ⊆ B /\
      (B.card : Real) /
          (8 * (k : Real) * C ^ (4 * k)) <= B'.card /\
      FreimanHom k B' phi

/-- **Corollary 7.6.** A function with many additive quadruples has a large
restriction that is a Freiman homomorphism of order eight. -/
def corollary_7_6 : Prop :=
  forall (N : Nat) [NeZero N] (B0 : Finset (ZMod N))
      (phi : ZMod N -> ZMod N) (alpha gamma : Real),
    Nat.Prime N -> 0 < alpha -> 0 < gamma ->
    (B0.card : Real) = alpha * N ->
    gamma * (alpha * N) ^ 3 <= phiAdditiveCount B0 phi ->
    exists B : Finset (ZMod N),
      B ⊆ B0 /\
      (2 : Real) ^ (-(1882 : Real)) * gamma ^ 1164 * alpha * N <= B.card /\
      FreimanHom 8 B phi

/-- The large Fourier spectrum of `A` at a specified threshold. -/
noncomputable def largeFourierSpectrum {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (threshold : Real) : Finset (ZMod N) := by
  classical
  exact Finset.univ.filter fun r =>
    threshold <= ‖fourier (indicator A) r‖

/-- The spectrum `K` occurring in Lemma 7.8 and its corollaries. -/
noncomputable def section7Spectrum {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (alpha : Real) : Finset (ZMod N) :=
  largeFourierSpectrum A (alpha ^ ((3 : Real) / 2) * N / 4)

/-- The symmetric modular progression `{j*d : -m <= j <= m}`. -/
noncomputable def symmetricMultiples {N : Nat} (d : ZMod N) (m : Nat) :
    Finset (ZMod N) := by
  classical
  exact (Finset.Icc (-(m : Int)) (m : Int)).image
    (fun j : Int => (j : ZMod N) * d)

/-- **Lemma 7.7 (Bohr-neighborhood size).** The paper's intended parameter
range `0 < delta <= 1` is made explicit: without an upper bound the displayed
cardinality estimate is false.  The nonzero conclusion also needs `2 <= N`,
and `K.Nonempty` makes the exponent `-1 / |K|` meaningful.  Finally, the
printed threshold `(N / 2)^(-1 / |K|)` is corrected to
`2 * N^(-1 / |K|)`, which is exactly what makes the preceding lower bound
strictly greater than one. -/
def lemma_7_7 : Prop :=
  forall (N : Nat) [NeZero N] (K : Finset (ZMod N)) (delta : Real),
    2 <= N -> 0 < delta -> delta <= 1 ->
    (delta / 2) ^ K.card * N <= (bohr K delta).card /\
    (K.Nonempty ->
      2 * (N : Real) ^ (-(1 / (K.card : Real))) < delta ->
      exists d : ZMod N, d ∈ bohr K delta /\ d != 0)

/-- **Lemma 7.8.** A Freiman homomorphism of order eight induces a
homomorphism on the Bohr neighborhood determined by the large spectrum of
its domain. -/
def lemma_7_8 : Prop :=
  forall (N : Nat) [NeZero N] (A : Finset (ZMod N))
      (phi : ZMod N -> ZMod N) (alpha : Real),
    0 < alpha -> (A.card : Real) = alpha * N ->
    FreimanHom 8 A phi ->
    let K := section7Spectrum A alpha
    (K.card : Real) <= 16 * alpha ^ (-(2 : Real)) /\
      IsBHomomorphism A (bohr K (alpha / (32 * Real.pi))) phi

/-- **Corollary 7.9.** On every sufficiently short progression generated by
an element of the smaller Bohr neighborhood, the induced homomorphism is
scalar multiplication.  The paper's standing prime-modulus hypothesis is
made explicit: division by the nonzero common difference is used to obtain
the ambient scalar. -/
def corollary_7_9 : Prop :=
  forall (N : Nat) [NeZero N] (A : Finset (ZMod N))
      (phi : ZMod N -> ZMod N) (alpha : Real),
    Nat.Prime N -> 0 < alpha -> (A.card : Real) = alpha * N ->
    FreimanHom 8 A phi ->
    let K := section7Spectrum A alpha
    forall m : Nat, 0 < m -> forall d : ZMod N,
      d ∈ bohr K (alpha / (32 * Real.pi * m)) ->
      exists c : ZMod N, forall x, x ∈ A -> forall y, y ∈ A ->
        x - y ∈ symmetricMultiples d m ->
        phi x - phi y = c * (x - y)

/-- **Corollary 7.10.** A somewhat additive map agrees with an affine map
on a dense subset of a long modular progression.  The OCR is corrected in
two places: all of `2^-3770 * gamma^2328 * alpha^2` is the exponent of `N`,
and the density constant is `2^-1882`, as required by Corollary 7.6 and the
proof (rather than the inconsistent printed `2^-1849`). -/
def corollary_7_10 : Prop :=
  forall (alpha gamma : Real), 0 < alpha -> 0 < gamma ->
    exists N0 : Nat, forall (N : Nat) [NeZero N],
      Nat.Prime N -> N0 <= N ->
      forall (B0 : Finset (ZMod N)) (phi : ZMod N -> ZMod N),
        (B0.card : Real) = alpha * N ->
        gamma * (alpha * N) ^ 3 <= phiAdditiveCount B0 phi ->
        exists P : ModAP N, exists H : Finset (ZMod N),
          P.IsProper /\ P.step != 0 /\ H ⊆ P.carrier /\
          (N : Real) ^
              ((2 : Real) ^ (-(3770 : Real)) * gamma ^ 2328 * alpha ^ 2) <=
            P.length /\
          (2 : Real) ^ (-(1882 : Real)) * gamma ^ 1164 * alpha * P.length <=
            H.card /\
          LinearOn H phi

/-- **Corollary 7.11.** Simultaneously partition an integer progression so
that every one of a finite family of order-eight Freiman homomorphisms is
affine-linear on each cell of its domain.  The explicit lower-size inequality
repairs a hypothesis omitted from the printed statement: it is what makes the
nonzero-element conclusion of Lemma 7.7 applicable in the proof. -/
def corollary_7_11 : Prop :=
  forall (N q m : Nat) [NeZero N] (R : IntAP)
      (A : Fin q -> Finset Int) (phi : Fin q -> Int -> ZMod N)
      (alpha : Real),
    0 < q -> 0 < m -> 0 < alpha -> 0 < R.length -> R.IsProper ->
    (forall i, A i ⊆ R.carrier /\ alpha * R.length <= (A i).card /\
      FreimanHom 8 (A i) (phi i)) ->
    (m : Real) <=
      (R.length : Real) ^
        ((2 : Real) ^ (-(14 : Real)) * alpha ^ 2 * (q : Real)⁻¹) ->
    1024 * Real.pi / alpha <
      (R.length : Real) ^
        ((2 : Real) ^ (-(14 : Real)) * alpha ^ 2 * (q : Real)⁻¹) ->
    exists M : Nat, exists S : Fin M -> IntAP,
      IsIntAPPartition S R /\
      (forall j, (S j).IsProper /\
        ((S j).length = m \/ (S j).length = m + 1)) /\
      (exists d : Nat, 0 < d /\ forall j, (S j).step = d) /\
      (forall i j, IntAPLinearOn (S j) (A i) (phi i))

end LeanProofs.GowersSzemeredi
