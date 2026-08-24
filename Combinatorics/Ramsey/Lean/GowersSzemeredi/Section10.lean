import GowersSzemeredi.Definitions

/-!
# Gowers (2001), Section 10: properties of approximate homomorphisms

This file records all fourteen numbered results in Section 10 of "A new proof
of Szemeredi's theorem" as `Prop`-valued definitions.  It also formalizes the
paper's finite multifunction domains, their fibres, approximate homomorphisms,
invariance, and nested "almost every" notation.  No numbered result is asserted.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ## Multifunction domains and approximate homomorphisms -/

/-- A Section 10 domain is a finite type whose elements lie over residues
through the map called `r` in the paper. -/
structure MultifunctionDomain (N : Nat) (X : Type*) where
  index : X -> ZMod N

/-- The fibre `X_s` of a multifunction domain. -/
noncomputable def MultifunctionDomain.fibre {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X) (s : ZMod N) : Finset X := by
  classical
  exact Finset.univ.filter fun x => D.index x = s

/-- The size `R(x) = |X_{r(x)}|` of the fibre containing `x`. -/
def MultifunctionDomain.fibreSize {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X) (x : X) : Nat :=
  (D.fibre (D.index x)).card

/-- The elements in fibres whose indices occur in `W`, translated by `d`.
This is the paper's `W + d`. -/
noncomputable def MultifunctionDomain.shift {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (W : Finset X) (d : ZMod N) : Finset X := by
  classical
  exact Finset.univ.filter fun x => exists w, w ∈ W /\ D.index x = D.index w + d

/-- A subset of a domain is a union of whole fibres. -/
def MultifunctionDomain.FibreSaturated {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X) (W : Finset X) : Prop :=
  forall x, x ∈ W -> forall y, D.index y = D.index x -> y ∈ W

/-- At least the proportion `p` of a finite set satisfies `P`.  This directly
formalizes the paper's `(p a.e. x in U) P(x)` notation and supports nesting. -/
noncomputable def AlmostEvery {X : Type*} [DecidableEq X]
    (p : Real) (U : Finset X) (P : X -> Prop) : Prop := by
  classical
  exact p * U.card <= ((U.filter P).card : Real)

/-- The two halves of a `2k`-tuple have the same sum after applying `f`. -/
def HasEqualHalfSums {G : Type*} [AddCommMonoid G] {k : Nat}
    (f : Fin (2 * k) -> G) : Prop :=
  (Finset.univ.filter (fun i : Fin (2 * k) => (i : Nat) < k)).sum f =
    (Finset.univ.filter (fun i : Fin (2 * k) => k <= (i : Nat))).sum f

/-- Number of `2k`-tuples respecting the index relation of a domain. -/
noncomputable def domainAdditiveTupleCount {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X) (k : Nat) : Nat :=
  countWhere fun x : Fin (2 * k) -> X => HasEqualHalfSums (fun i => D.index (x i))

/-- Number of index-additive `2k`-tuples also respected by `phi`. -/
noncomputable def domainPhiAdditiveTupleCount {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X -> ZMod N) (k : Nat) : Nat :=
  countWhere fun x : Fin (2 * k) -> X =>
    HasEqualHalfSums (fun i => D.index (x i)) /\
      HasEqualHalfSums (fun i => phi (x i))

/-- A `(1-eta)`-homomorphism of order `k`, written without division so the
definition remains meaningful when there are no index-additive tuples. -/
def DomainApproxHomOfOrder {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X -> ZMod N) (eta : Real) (k : Nat) : Prop :=
  (1 - eta) * domainAdditiveTupleCount D k <= domainPhiAdditiveTupleCount D phi k

/-! ## The weights `q`, `b`, and `epsilon` -/

/-- The popularity `q(x,y)` of the indexed difference `r(y)-r(x)`. -/
noncomputable def domainDifferenceWeight {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X) (x y : X) : Nat :=
  countWhere fun zw : X × X =>
    D.index zw.2 - D.index zw.1 = D.index y - D.index x

/-- The number `b(x,y)` of `B`-restricted translates of `(x,y)`. -/
noncomputable def domainRestrictedDifferenceWeight {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (B : Finset (ZMod N)) (x y : X) : Nat :=
  countWhere fun uv : X × X =>
    D.index uv.1 - D.index x = D.index uv.2 - D.index y /\
      D.index uv.1 - D.index x ∈ B

/-- The error count `e(x,y)` among the `B`-restricted translates. -/
noncomputable def domainDifferenceErrorCount {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X -> ZMod N) (B : Finset (ZMod N)) (x y : X) : Nat :=
  countWhere fun uv : X × X =>
    D.index uv.1 - D.index x = D.index uv.2 - D.index y /\
      D.index uv.1 - D.index x ∈ B /\
      phi uv.1 - phi x != phi uv.2 - phi y

/-- The proportionate error `epsilon(x,y) = e(x,y) / b(x,y)`. -/
def domainProportionateError {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X -> ZMod N) (B : Finset (ZMod N)) (x y : X) : Real :=
  domainDifferenceErrorCount D phi B x y / domainRestrictedDifferenceWeight D B x y

/-- The quantity `Q(x) = sum_y q(x,y)`. -/
def domainTotalWeight {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X) (x : X) : Nat :=
  ∑ y : X, domainDifferenceWeight D x y

/-- The quantity `E(x) = sum_y epsilon(x,y) q(x,y)`. -/
def domainWeightedError {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X -> ZMod N) (B : Finset (ZMod N)) (x : X) : Real :=
  ∑ y : X, domainProportionateError D phi B x y * domainDifferenceWeight D x y

/-! ## Common hypotheses, invariance, and regular components -/

/-- A finite set of residues is symmetric. -/
def IsSymmetricModSet {N : Nat} (B : Finset (ZMod N)) : Prop :=
  forall d, d ∈ B <-> -d ∈ B

/-- The domain is `(B,L)`-invariant when translating by an element of `B`
changes every fibre size by at most `L`. -/
def DomainInvariant {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (B : Finset (ZMod N)) (L : Real) : Prop :=
  forall s, forall d, d ∈ B ->
    |((D.fibre (s + d)).card : Real) - (D.fibre s).card| <= L

/-- The size and fibre-cap hypotheses shared by Lemmas 10.1--10.5. -/
def Section10DomainBounds {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (alpha : Real) (M : Nat) : Prop :=
  0 < alpha /\ alpha <= 1 /\ 0 < M /\
    (Fintype.card X : Real) = alpha * M * N /\
    forall s, (D.fibre s).card <= M

/-- The running hypotheses fixed before Lemma 10.1. -/
def Section10Setup {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X -> ZMod N) (B : Finset (ZMod N))
    (alpha : Real) (M : Nat) (sigma eta : Real) : Prop :=
  Section10DomainBounds D alpha M /\ 0 < sigma /\ 0 <= eta /\ eta <= 1 /\
    IsSymmetricModSet B /\ DomainInvariant D B (sigma * M) /\
    DomainApproxHomOfOrder D phi eta 2

/-- A function with natural values varies by at most a factor of two on `W`. -/
def VariesByFactorAtMostTwo {X : Type*} [DecidableEq X]
    (W : Finset X) (f : X -> Nat) : Prop :=
  forall x, x ∈ W -> forall y, y ∈ W -> f x <= 2 * f y

/-- The three properties of the point selected in Lemma 10.3. -/
def IsSection10Anchor {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X -> ZMod N) (B : Finset (ZMod N))
    (alpha : Real) (M N0 : Nat) (eta : Real) (x : X) : Prop :=
  alpha ^ 2 * M / 2 <= D.fibreSize x /\
    alpha ^ 3 * M ^ 3 * N0 ^ 2 / 4 <= domainTotalWeight D x /\
    domainWeightedError D phi B x <= 60 * eta * domainTotalWeight D x

/-- The six conclusions imposed on the component `W` in Lemma 10.5.  Item
(iii) uses the exponents supported by the proof and needed by Lemma 10.6. -/
def IsSection10RegularComponent {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X -> ZMod N) (B : Finset (ZMod N)) (x : X)
    (alpha eta rho : Real) (M N0 : Nat) (W : Finset X) : Prop :=
  D.FibreSaturated W /\
    VariesByFactorAtMostTwo W (fun y => domainDifferenceWeight D x y) /\
    AlmostEvery (1 - 5 * eta ^ ((1 : Real) / 5)) W
      (fun y => domainProportionateError D phi B x y <=
        300 * eta ^ ((4 : Real) / 5)) /\
    rho ^ 2 * alpha ^ 2 * M * N0 / 16 <= W.card /\
    VariesByFactorAtMostTwo W D.fibreSize /\
    (forall y, y ∈ W -> alpha ^ 2 * M / 16 <= D.fibreSize y) /\
    forall d, d ∈ B -> (1 - eta) * W.card <= (W ∩ D.shift W d).card

/-- The part of the running Section 10 setup used by the shifting lemma:
`W` is a union of fibres, `B` is symmetric, fibre sizes are comparable on
`W`, and `W` has large overlap with all `B`-translates.  Fibre saturation
and symmetry are necessary in Lemma 10.8: without them, an almost-everywhere
property on `W` need not control the full shifted fibres. -/
def IsSection10ShiftRegular {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (W : Finset X) (B : Finset (ZMod N)) (eta : Real) : Prop :=
  D.FibreSaturated W /\ IsSymmetricModSet B /\
    VariesByFactorAtMostTwo W D.fibreSize /\
    forall d, d ∈ B -> (1 - eta) * W.card <= (W ∩ D.shift W d).card

/-- The four thin boundary bands in the averaging proof of Lemma 10.5.
They form a **union**: the printed/OCR intersection would require a point to
be simultaneously near every boundary and does not give the stated estimate. -/
noncomputable def section10WindowBoundary {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X) (x : X)
    (alpha lambda mu rho sigma : Real) (M N0 : Nat) : Finset X := by
  classical
  exact Finset.univ.filter fun y =>
    let q : Real := domainDifferenceWeight D x y
    let R : Real := D.fibreSize y
    ((lambda - rho) * alpha * M ^ 2 * N0 <= q /\
      q <= (lambda - rho + sigma) * alpha * M ^ 2 * N0) \/
    ((lambda + rho - sigma) * alpha * M ^ 2 * N0 <= q /\
      q <= (lambda + rho) * alpha * M ^ 2 * N0) \/
    ((mu - rho) * M <= R /\ R <= (mu - rho + sigma) * M) \/
    ((mu + rho - sigma) * M <= R /\ R <= (mu + rho) * M)

/-! ## Lemmas 10.1--10.5: finding a regular component -/

/-- **Lemma 10.1.** The three basic estimates for `q`. -/
def lemma_10_1 : Prop :=
  forall (N : Nat) [NeZero N] (X : Type*) [Fintype X] [DecidableEq X]
      (D : MultifunctionDomain N X) (alpha : Real) (M : Nat),
    Section10DomainBounds D alpha M ->
    (forall x y, (domainDifferenceWeight D x y : Real) <= alpha * M ^ 2 * N) /\
    (forall x, (domainTotalWeight D x : Real) <= alpha ^ 2 * M ^ 3 * N ^ 2) /\
    alpha ^ 4 * M ^ 4 * N ^ 3 <=
      ∑ x : X, ∑ y : X, (domainDifferenceWeight D x y : Real)

/-- **Lemma 10.2.** The weighted proportionate error is small. -/
def lemma_10_2 : Prop :=
  forall (N : Nat) [NeZero N] (X : Type*) [Fintype X] [DecidableEq X]
      (D : MultifunctionDomain N X) (phi : X -> ZMod N)
      (B : Finset (ZMod N)) (alpha : Real) (M : Nat) (sigma eta : Real),
    Section10Setup D phi B alpha M sigma eta -> sigma <= eta * alpha ^ 2 ->
    (∑ x : X, ∑ y : X,
      domainProportionateError D phi B x y * domainDifferenceWeight D x y) <=
        15 * eta * ∑ x : X, ∑ y : X, (domainDifferenceWeight D x y : Real)

/-- **Lemma 10.3.** There is a point with a large fibre and large total
weight but small weighted error.  The hypothesis needed to invoke Lemma
10.2 is explicit. -/
def lemma_10_3 : Prop :=
  forall (N : Nat) [NeZero N] (X : Type*) [Fintype X] [DecidableEq X]
      (D : MultifunctionDomain N X) (phi : X -> ZMod N)
      (B : Finset (ZMod N)) (alpha : Real) (M : Nat) (sigma eta : Real),
    Section10Setup D phi B alpha M sigma eta -> sigma <= eta * alpha ^ 2 ->
      exists x : X, IsSection10Anchor D phi B alpha M N eta x

/-- **Lemma 10.4.** Translation by an element of `B` changes `q(x,-)` by
at most `sigma alpha M^2 N`. -/
def lemma_10_4 : Prop :=
  forall (N : Nat) [NeZero N] (X : Type*) [Fintype X] [DecidableEq X]
      (D : MultifunctionDomain N X) (phi : X -> ZMod N)
      (B : Finset (ZMod N)) (alpha : Real) (M : Nat) (sigma eta : Real),
    Section10Setup D phi B alpha M sigma eta -> forall x y z,
      D.index z - D.index y ∈ B ->
      |(domainDifferenceWeight D x z : Real) - domainDifferenceWeight D x y| <=
        sigma * alpha * M ^ 2 * N

/-- **Lemma 10.5.** A regular component `W`.  The printed statement leaves
`rho` unbound; the proof requires `0 < rho`, `rho <= alpha/192`,
`rho <= alpha^2/32`, and `sigma <= eta rho^4 alpha/384`, all made explicit.
Also, item (iii) is corrected from its internally inconsistent square-root
form to the proof-supported `(1-5 eta^(1/5))`, `300 eta^(4/5)` form used in
Lemma 10.6. -/
def lemma_10_5 : Prop :=
  forall (N : Nat) [NeZero N] (X : Type*) [Fintype X] [DecidableEq X]
      (D : MultifunctionDomain N X) (phi : X -> ZMod N)
      (B : Finset (ZMod N)) (alpha rho : Real) (M : Nat) (sigma eta : Real)
      (x : X),
    Section10Setup D phi B alpha M sigma eta ->
    sigma <= eta * alpha ^ 2 -> IsSection10Anchor D phi B alpha M N eta x ->
    0 < rho -> rho <= alpha / 192 -> rho <= alpha ^ 2 / 32 ->
    sigma <= eta * rho ^ 4 * alpha / 384 ->
      exists W : Finset X,
        IsSection10RegularComponent D phi B x alpha eta rho M N W

/-! ## Lemmas 10.6--10.9: constructing the local homomorphism -/

/-- The complete conclusion of Lemma 10.6 for a candidate `B'` and `psi`. -/
def IsSection10LocalDifferenceModel {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X -> ZMod N) (W : Finset X) (B B' : Finset (ZMod N))
    (psi : ZMod N -> ZMod N) (theta : Real) : Prop :=
  B' ⊆ B /\ (1 - theta) * B.card <= B'.card /\
    forall d, d ∈ B' -> AlmostEvery (1 - theta) W fun w =>
      AlmostEvery (1 - theta) (D.fibre (D.index w + d)) fun z =>
        phi z - phi w = psi d

/-- **Lemma 10.6.** Construction of a difference map on almost all of `B`.
The smallness bound on `rho`, inherited from the application of Lemma 10.5,
is explicit: it is needed to compare translated fibres with the anchor fibre. -/
def lemma_10_6 : Prop :=
  forall (N : Nat) [NeZero N] (X : Type*) [Fintype X] [DecidableEq X]
      (D : MultifunctionDomain N X) (phi : X -> ZMod N)
      (B : Finset (ZMod N)) (alpha rho : Real) (M : Nat) (sigma eta : Real)
      (x : X) (W : Finset X),
    Section10Setup D phi B alpha M sigma eta ->
    IsSection10Anchor D phi B alpha M N eta x ->
    IsSection10RegularComponent D phi B x alpha eta rho M N W ->
    rho <= alpha ^ 2 / 32 ->
    sigma <= eta * rho * alpha ^ 2 / 16 ->
      exists B' : Finset (ZMod N), exists psi : ZMod N -> ZMod N,
        IsSection10LocalDifferenceModel D phi W B B' psi
          (10 * eta ^ ((1 : Real) / 5))

/-- **Lemma 10.7.** Reversing the order of the two outer "almost every"
quantifiers in the conclusion of Lemma 10.6. -/
def lemma_10_7 : Prop :=
  forall (N : Nat) [NeZero N] (X : Type*) [Fintype X] [DecidableEq X]
      (D : MultifunctionDomain N X) (phi : X -> ZMod N)
      (W : Finset X) (B B' : Finset (ZMod N)) (psi : ZMod N -> ZMod N)
      (eta : Real),
    let theta := 10 * eta ^ ((1 : Real) / 5)
    IsSection10LocalDifferenceModel D phi W B B' psi theta ->
      AlmostEvery (1 - Real.sqrt theta) W fun w =>
        AlmostEvery (1 - Real.sqrt theta) B' fun d =>
          AlmostEvery (1 - theta) (D.fibre (D.index w + d)) fun z =>
            phi z - phi w = psi d

/-- **Lemma 10.8.** An almost-everywhere property may be shifted along a
direction in `B`, with the displayed loss. -/
def lemma_10_8 : Prop :=
  forall (N : Nat) [NeZero N] (X : Type*) [Fintype X] [DecidableEq X]
      (D : MultifunctionDomain N X) (W : Finset X) (B : Finset (ZMod N))
      (eta theta : Real) (P : X -> Prop),
    IsSection10ShiftRegular D W B eta -> 0 < theta ->
    AlmostEvery (1 - theta) W P -> forall d, d ∈ B ->
      AlmostEvery (1 - Real.sqrt theta - eta) W fun w =>
        AlmostEvery (1 - 2 * Real.sqrt theta) (D.fibre (D.index w + d)) P

/-- **Lemma 10.9.** The locally constructed difference map is a Freiman
homomorphism.  Nonemptiness of `W`, inherited from Lemma 10.5 in the paper,
is explicit: otherwise both nested almost-everywhere assertions are vacuous. -/
def lemma_10_9 : Prop :=
  forall (N : Nat) [NeZero N] (X : Type*) [Fintype X] [DecidableEq X]
      (D : MultifunctionDomain N X) (phi : X -> ZMod N)
      (W : Finset X) (B B' : Finset (ZMod N)) (psi : ZMod N -> ZMod N)
      (eta : Real),
    let theta := 10 * eta ^ ((1 : Real) / 5)
    W.Nonempty -> IsSection10ShiftRegular D W B eta ->
    IsSection10LocalDifferenceModel D phi W B B' psi theta ->
    6 * Real.sqrt theta < 1 -> FreimanHom 2 B' psi

/-! ## Lemmas 10.10--10.12: extending across a Bohr neighborhood -/

/-- Translation of a modular set. -/
noncomputable def section10Translate {N : Nat}
    (A : Finset (ZMod N)) (d : ZMod N) : Finset (ZMod N) := by
  classical
  exact A.image fun x => x + d

/-- A difference map on `B'` induces `psi1` on the difference set `C`. -/
def InducesDifferenceMap {N : Nat} (B' C : Finset (ZMod N))
    (psi psi1 : ZMod N -> ZMod N) : Prop :=
  forall c, c ∈ C -> forall x, x ∈ B' -> forall y, y ∈ B' ->
    x - y = c -> psi x - psi y = psi1 c

/-- **Lemma 10.10.** A small Bohr translation has large overlap.  The
standard range `0 < delta <= 1` and `0 <= zeta <= delta`, implicit in the
boundary argument, is explicit. -/
def lemma_10_10 : Prop :=
  forall (N k : Nat) [NeZero N] (K : Finset (ZMod N)) (delta zeta : Real),
    K.card = k -> 0 < delta -> delta <= 1 -> 0 <= zeta -> zeta <= delta ->
    let B := bohr K delta
    forall d, d ∈ bohr K zeta ->
      (1 - (2 : Real) ^ (k + 1) * delta ^ (-(k : Real)) * k * zeta) * B.card <=
        (B ∩ section10Translate B d).card

/-- **Corollary 10.11.** A Freiman homomorphism on most of a Bohr
neighborhood induces one on a smaller Bohr neighborhood.  The radius is
corrected to `2^(-(k+4)) delta^k / k`; multiplication by `k` is incompatible
with Lemma 10.10. -/
def corollary_10_11 : Prop :=
  forall (N : Nat) [NeZero N] (K : Finset (ZMod N)) (delta : Real),
    K.Nonempty -> 0 < delta -> delta <= 1 ->
    let k := K.card
    let B := bohr K delta
    let zeta := (2 : Real) ^ (-((k : Real) + 4)) * delta ^ k / k
    let C := bohr K zeta
    forall (B' : Finset (ZMod N)) (psi : ZMod N -> ZMod N),
      B' ⊆ B -> (7 / 8 : Real) * B.card <= B'.card -> FreimanHom 2 B' psi ->
      C ⊆ B' - B' /\ exists psi1 : ZMod N -> ZMod N,
        FreimanHom 2 C psi1 /\ InducesDifferenceMap B' C psi psi1

/-- The set `W1` defined immediately before Lemma 10.12. -/
noncomputable def section10RegularSet {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X -> ZMod N) (W : Finset X) (B' : Finset (ZMod N))
    (psi : ZMod N -> ZMod N) (theta : Real) : Finset X := by
  classical
  exact W.filter fun w => AlmostEvery (1 - Real.sqrt theta) B' fun d =>
    AlmostEvery (1 - theta) (D.fibre (D.index w + d)) fun z =>
      phi z - phi w = psi d

/-- **Lemma 10.12.** On `W1`, the induced map on the smaller Bohr
neighborhood agrees with differences of `phi`. -/
def lemma_10_12 : Prop :=
  forall (N : Nat) [NeZero N] (X : Type*) [Fintype X] [DecidableEq X]
      (D : MultifunctionDomain N X) (phi : X -> ZMod N)
      (K : Finset (ZMod N)) (delta theta : Real) (W : Finset X)
      (B' : Finset (ZMod N)) (psi psi1 : ZMod N -> ZMod N),
    K.Nonempty -> 0 < delta -> delta <= 1 -> Real.sqrt theta <= 1 / 8 ->
    (forall w, w ∈ W -> forall d, d ∈ B' ->
      (D.fibre (D.index w + d)).Nonempty) ->
    let k := K.card
    let B := bohr K delta
    let zeta := (2 : Real) ^ (-((k : Real) + 4)) * delta ^ k / k
    let C := bohr K zeta
    IsSection10LocalDifferenceModel D phi W B B' psi theta ->
    FreimanHom 2 C psi1 -> InducesDifferenceMap B' C psi psi1 ->
    let W1 := section10RegularSet D phi W B' psi theta
    forall w1, w1 ∈ W1 -> forall w2, w2 ∈ W1 ->
      D.index w1 - D.index w2 ∈ C ->
      phi w1 - phi w2 = psi1 (D.index w1 - D.index w2)

/-! ## The main theorem and its scalar-multiplication corollary -/

/-- The fibre-size function `g(s)=|X_s|`, coerced to `Complex`. -/
def domainFibreCountFunction {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X) : ZMod N -> Complex :=
  fun s => (D.fibre s).card

/-- The large Fourier spectrum of a multifunction domain. -/
noncomputable def domainLargeSpectrum {N : Nat} [NeZero N] {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (threshold : Real) : Finset (ZMod N) := by
  classical
  exact Finset.univ.filter fun r => threshold <= ‖fourier (domainFibreCountFunction D) r‖

/-- The parameter `lambda = 2^-37 alpha^(11/2)` in Theorem 10.13. -/
def section10Lambda (alpha : Real) : Real :=
  (2 : Real) ^ (-(37 : Real)) * alpha ^ ((11 : Real) / 2)

/-- The real spectrum-cardinality bound in Theorem 10.13. -/
def section10SpectrumBound (alpha : Real) : Real :=
  (2 : Real) ^ (74 : Nat) * alpha ^ (-(10 : Real))

/-- The integer parameter used in exponents is the ceiling of the real
spectrum bound, correcting the paper's use of a generally nonintegral `k`. -/
def section10SpectrumParameter (alpha : Real) : Nat :=
  Nat.ceil (section10SpectrumBound alpha)

/-- The radius called `epsilon` in the proof of Theorem 10.13. -/
def section10BohrRadius (alpha : Real) : Real :=
  alpha ^ (-(4 : Real)) * section10Lambda alpha ^ (4 : Nat) / Real.pi

/-- The corrected radius `zeta`, including division by the integer `k`. -/
def section10Zeta (alpha : Real) : Real :=
  let k := section10SpectrumParameter alpha
  (2 : Real) ^ (-(155 : Real) * k) * alpha ^ (18 * k) / k

/-- A homomorphism on a Bohr neighborhood controls all indexed differences
inside `Y`. -/
def HasBohrDifferenceModel {N : Nat} [NeZero N] {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X -> ZMod N) (K : Finset (ZMod N)) (zeta : Real)
    (Y : Finset X) (psi : ZMod N -> ZMod N) : Prop :=
  FreimanHom 2 (bohr K zeta) psi /\
    forall y, y ∈ Y -> forall z, z ∈ Y ->
      D.index y - D.index z ∈ bohr K zeta ->
      phi y - phi z = psi (D.index y - D.index z)

/-- **Theorem 10.13.** The Fourier threshold is `lambda M N`, `alpha` is
restricted to the range used in the parameter calculation, and the exponent
parameter is the natural ceiling of `2^74 alpha^-10`.  The printed lower
bound `alpha^3 |X| / 1000` uses `rho` where Lemma 10.5 supplies `rho^2`.
Accordingly, this statement records the proof-supported editorial weakening
`alpha^6 |X| / 20000`. -/
def theorem_10_13 : Prop :=
  forall (N M : Nat) [NeZero N] (X : Type*) [Fintype X] [DecidableEq X]
      (D : MultifunctionDomain N X) (phi : X -> ZMod N) (alpha : Real),
    0 < alpha -> alpha <= 1 / 6 -> 0 < M ->
    (forall s, (D.fibre s).card <= M) ->
    (Fintype.card X : Real) = alpha * M * N ->
    DomainApproxHomOfOrder D phi ((2 : Real) ^ (-(43 : Real))) 8 ->
    let lambda := section10Lambda alpha
    let K := domainLargeSpectrum D (lambda * M * N)
    let k := section10SpectrumParameter alpha
    let epsilon := section10BohrRadius alpha
    let zeta := section10Zeta alpha
    (K.card : Real) <= section10SpectrumBound alpha /\
      zeta <= (2 : Real) ^ (-((k : Real) + 4)) * epsilon ^ k / k /\
      exists Y : Finset X, exists psi1 : ZMod N -> ZMod N,
        alpha ^ 6 * Fintype.card X / 20000 <= Y.card /\
        HasBohrDifferenceModel D phi K zeta Y psi1

/-- The symmetric set `{j d : -m <= j <= m}`. -/
noncomputable def section10SymmetricMultiples {N : Nat} (d : ZMod N) (m : Nat) :
    Finset (ZMod N) := by
  classical
  exact (Finset.Icc (-(m : Int)) (m : Int)).image fun j : Int => (j : ZMod N) * d

/-- **Corollary 10.14.** On every short progression generated by a smaller
Bohr element, the local homomorphism is scalar multiplication. -/
def corollary_10_14 : Prop :=
  forall (N : Nat) [NeZero N] (X : Type*) [Fintype X] [DecidableEq X]
      (D : MultifunctionDomain N X) (phi : X -> ZMod N)
      (K : Finset (ZMod N)) (zeta : Real) (Y : Finset X)
      (psi1 : ZMod N -> ZMod N),
    HasBohrDifferenceModel D phi K zeta Y psi1 ->
    forall m : Nat, 0 < m -> forall d, d ∈ bohr K (zeta / m) ->
      exists c : ZMod N, forall x, x ∈ Y -> forall y, y ∈ Y ->
        D.index x - D.index y ∈ section10SymmetricMultiples d m ->
        phi x - phi y = c * (D.index x - D.index y)

end LeanProofs.GowersSzemeredi
