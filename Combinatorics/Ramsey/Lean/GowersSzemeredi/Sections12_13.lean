import GowersSzemeredi.Sections06_07

/-!
# Gowers (2001), Sections 12--13: formal statements

This file records the paper's vertical-parallelogram and bilinear-extraction
results.  As elsewhere in this formalization, numbered results are
`Prop`-valued definitions: they state the claims without asserting proofs.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ## Vertical parallelograms and arrangements -/

/-- A point of the two-dimensional ambient group. -/
abbrev Pair (N : Nat) := ZMod N × ZMod N

/-- A vertical parallelogram is encoded by `(x,y,y',w,h)`. -/
abbrev VerticalParallelogram (N : Nat) := Fin 5 → ZMod N

def VerticalParallelogram.x {N : Nat} (P : VerticalParallelogram N) : ZMod N := P 0
def VerticalParallelogram.y {N : Nat} (P : VerticalParallelogram N) : ZMod N := P 1
def VerticalParallelogram.y' {N : Nat} (P : VerticalParallelogram N) : ZMod N := P 2
def VerticalParallelogram.width {N : Nat} (P : VerticalParallelogram N) : ZMod N := P 3
def VerticalParallelogram.height {N : Nat} (P : VerticalParallelogram N) : ZMod N := P 4

/-- The four vertices of a vertical parallelogram. -/
noncomputable def VerticalParallelogram.carrier {N : Nat}
    (P : VerticalParallelogram N) : Finset (Pair N) := by
  classical
  exact {(P.x, P.y), (P.x, P.y + P.height),
    (P.x + P.width, P.y'), (P.x + P.width, P.y' + P.height)}

/-- A vertical parallelogram lies in a partial-function domain. -/
def VerticalParallelogram.IsIn {N : Nat} (P : VerticalParallelogram N)
    (B : Finset (Pair N)) : Prop :=
  P.carrier ⊆ B

/-- The alternating value `phi(P)` of a vertical parallelogram. -/
def VerticalParallelogram.value {N : Nat} (phi : Pair N → ZMod N)
    (P : VerticalParallelogram N) : ZMod N :=
  phi (P.x, P.y) - phi (P.x, P.y + P.height) -
    phi (P.x + P.width, P.y') + phi (P.x + P.width, P.y' + P.height)

/-- The number of equal-width, equal-height parallelogram pairs on which
`phi` has equal alternating value. -/
def parallelogramPairCount {N : Nat} [NeZero N] (B : Finset (Pair N))
    (phi : Pair N → ZMod N) : Nat :=
  countWhere fun P : VerticalParallelogram N × VerticalParallelogram N =>
    P.1.IsIn B ∧ P.2.IsIn B ∧ P.1.width = P.2.width ∧
      P.1.height = P.2.height ∧ P.1.value phi = P.2.value phi

/-- A `d`-arrangement consists of `2d` vertical edges and a common height. -/
abbrev DArrangement (N d : Nat) :=
  (Fin (2 * d) → ZMod N) × (Fin (2 * d) → ZMod N) × ZMod N

def DArrangement.x {N d : Nat} (R : DArrangement N d) : Fin (2 * d) → ZMod N := R.1
def DArrangement.y {N d : Nat} (R : DArrangement N d) : Fin (2 * d) → ZMod N := R.2.1
def DArrangement.height {N d : Nat} (R : DArrangement N d) : ZMod N := R.2.2

/-- Membership of every endpoint of an arrangement in `B`. -/
def DArrangement.IsIn {N d : Nat} (R : DArrangement N d)
    (B : Finset (Pair N)) : Prop :=
  IsAdditiveTuple R.x ∧ ∀ i,
    (R.x i, R.y i) ∈ B ∧ (R.x i, R.y i + R.height) ∈ B

/-- The image relation saying that `phi` respects an arrangement. -/
def DArrangement.IsRespected {N d : Nat} (R : DArrangement N d)
    (phi : Pair N → ZMod N) : Prop :=
  IsAdditiveTuple fun i =>
    phi (R.x i, R.y i + R.height) - phi (R.x i, R.y i)

/-- Number of `d`-arrangements contained in a finite domain. -/
def arrangementCount {N : Nat} [NeZero N] (d : Nat)
    (B : Finset (Pair N)) : Nat :=
  countWhere fun R : DArrangement N d => R.IsIn B

/-- Number of contained `d`-arrangements respected by `phi`. -/
def respectedArrangementCount {N : Nat} [NeZero N] (d : Nat)
    (B : Finset (Pair N)) (phi : Pair N → ZMod N) : Nat :=
  countWhere fun R : DArrangement N d => R.IsIn B ∧ R.IsRespected phi

/-- Arrangement count with a prescribed height. -/
def arrangementCountAtHeight {N : Nat} [NeZero N] (d : Nat)
    (B : Finset (Pair N)) (h : ZMod N) : Nat :=
  countWhere fun R : DArrangement N d => R.IsIn B ∧ R.height = h

/-- Respected-arrangement count with a prescribed height. -/
def respectedArrangementCountAtHeight {N : Nat} [NeZero N] (d : Nat)
    (B : Finset (Pair N)) (phi : Pair N → ZMod N) (h : ZMod N) : Nat :=
  countWhere fun R : DArrangement N d =>
    R.IsIn B ∧ R.height = h ∧ R.IsRespected phi

/-- A quadruple is additive for every member of a family of functions. -/
def IsSimultaneouslyAdditive {N p : Nat} (phi : Fin p → ZMod N → ZMod N)
    (q : Fin 4 → ZMod N) : Prop :=
  q 0 - q 1 = q 2 - q 3 ∧
    ∀ i, phi i (q 0) - phi i (q 1) = phi i (q 2) - phi i (q 3)

/-- Total weight of the simultaneously additive quadruples. -/
noncomputable def simultaneouslyAdditiveWeight {N p : Nat} [NeZero N]
    (lambda : ZMod N → Real) (phi : Fin p → ZMod N → ZMod N) : Real := by
  classical
  exact ∑ q : Fin 4 → ZMod N,
    if IsSimultaneouslyAdditive phi q then
      lambda (q 0) * lambda (q 1) * lambda (q 2) * lambda (q 3)
    else 0

/-! ## Section 12: Strengthening a bihomomorphism -/

/-- **Proposition 12.1.** Weighted simultaneous additivity. -/
def proposition_12_1 : Prop :=
  ∀ (N p : Nat) [NeZero N] (lambda : ZMod N → Real)
      (f : Fin p → ZMod N → Complex) (phi : Fin p → ZMod N → ZMod N)
      (alpha : Real),
    (∀ k, 0 ≤ lambda k) → (∀ i, DiscValued (f i)) →
    alpha * (N : Real) ^ (2 * p + 1) ≤
      ∑ k : ZMod N, lambda k *
        ∏ i : Fin p, ‖fourier (difference (f i) k) (phi i k)‖ ^ 2 →
    alpha ^ 4 * (N : Real) ^ 3 ≤
      simultaneouslyAdditiveWeight lambda phi

/-- The second difference used from Lemma 12.2 onward. -/
def secondDifference {N : Nat} (f : ZMod N → Complex) (k l : ZMod N) :
    ZMod N → Complex :=
  difference (difference f k) l

/-- Its unnormalized Fourier coefficient. -/
def secondDifferenceFourier {N : Nat} [NeZero N] (f : ZMod N → Complex)
    (k l r : ZMod N) : Complex :=
  fourier (secondDifference f k l) r

/-- **Lemma 12.2.** The printed paper omitted both the two-dimensional type of
`B` and the function `phi`; both are made explicit here. -/
def lemma_12_2 : Prop :=
  ∀ (N : Nat) [NeZero N] (beta gamma : Real) (f : ZMod N → Complex)
      (B : Finset (Pair N)) (phi : Pair N → ZMod N),
    0 < beta → 0 < gamma → DiscValued f →
    (B.card : Real) = beta * (N : Real) ^ 2 →
    (∀ z, z ∈ B → gamma * N ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖) →
    beta ^ 16 * gamma ^ 48 * (N : Real) ^ 8 ≤ parallelogramPairCount B phi

/-- **Lemma 12.3.** -/
def lemma_12_3 : Prop :=
  ∀ (N : Nat) [NeZero N] (theta : Real) (B : Finset (Pair N))
      (phi : Pair N → ZMod N),
    theta * (N : Real) ^ 8 ≤ parallelogramPairCount B phi →
    theta ^ 7 * (N : Real) ^ 32 ≤ respectedArrangementCount 8 B phi

/-- **Lemma 12.4.** -/
def lemma_12_4 : Prop :=
  ∀ (N : Nat) [NeZero N] (beta gamma : Real) (f : ZMod N → Complex)
      (B : Finset (Pair N)) (phi : Pair N → ZMod N),
    0 < beta → 0 < gamma → DiscValued f →
    (B.card : Real) = beta * (N : Real) ^ 2 →
    (∀ z, z ∈ B → gamma * N ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖) →
    beta ^ 112 * gamma ^ 336 * (N : Real) ^ 32 ≤
      respectedArrangementCount 8 B phi

/-- **Lemma 12.5.** The paper's sufficiently-large hypothesis is represented
by the threshold `N0`. -/
def lemma_12_5 : Prop :=
  ∀ alpha beta eta : Real, 0 < alpha → 0 < beta → 0 < eta →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N], N0 ≤ N →
      ∀ (B : Finset (Pair N)) (phi : Pair N → ZMod N),
        (B.card : Real) = beta * (N : Real) ^ 2 →
        alpha * beta ^ 15 * (N : Real) ^ 32 ≤ respectedArrangementCount 8 B phi →
        ∃ B' : Finset (Pair N), B' ⊆ B ∧
          (alpha * eta / 4) ^ ((2 : Nat) ^ 36) * beta ^ 15 * (N : Real) ^ 32 ≤
            arrangementCount 8 B' ∧
          (1 - eta) * arrangementCount 8 B' ≤ respectedArrangementCount 8 B' phi

/-- **Lemma 12.6.** The source's implicit sufficiently-large condition is made
explicit. -/
def lemma_12_6 : Prop :=
  ∀ beta gamma eta : Real, 0 < beta → 0 < gamma → 0 < eta →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N], N0 ≤ N →
      ∀ (f : ZMod N → Complex) (B : Finset (Pair N))
          (phi : Pair N → ZMod N),
        DiscValued f → beta * (N : Real) ^ 2 ≤ B.card →
        (∀ z, z ∈ B → gamma * N ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖) →
        ∃ B' : Finset (Pair N), B' ⊆ B ∧
          (2 : Real) ^ (-((2 : Real) ^ 37)) * beta ^ ((2 : Nat) ^ 43) *
              gamma ^ ((2 : Nat) ^ 45) * eta ^ ((2 : Nat) ^ 36) *
              (N : Real) ^ 32 ≤ arrangementCount 8 B' ∧
          (1 - eta) * arrangementCount 8 B' ≤ respectedArrangementCount 8 B' phi

/-! ## Section 13: Finding a bilinear piece -/

/-- The domain of vertical edges of height `h` in `A`, represented by their
lower endpoints. -/
noncomputable def verticalEdgeDomain {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (h : ZMod N) : Finset (Pair N) := by
  classical
  exact Finset.univ.filter fun z => z ∈ A ∧ (z.1, z.2 + h) ∈ A

/-- The number of height-`h` edges above a fixed first coordinate. -/
noncomputable def verticalEdgeFiberCount {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (h x : ZMod N) : Nat :=
  ((verticalEdgeDomain A h).filter fun z => z.1 = x).card

/-- The fibre-count function `f_h` from Corollary 13.2. -/
def verticalEdgeFiberFunction {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (h : ZMod N) : ZMod N → Complex :=
  fun x => verticalEdgeFiberCount A h x

/-- Difference of a partial function along a vertical edge. -/
def verticalPhiDifference {N : Nat} (phi : Pair N → ZMod N)
    (h : ZMod N) (z : Pair N) : ZMod N :=
  phi (z.1, z.2 + h) - phi z

/-- The vertical correlation `f_h` from Lemma 13.1. -/
def verticalCorrelation {N : Nat} [NeZero N] (f : Pair N → Complex)
    (h : ZMod N) : ZMod N → Complex :=
  fun x => ∑ y : ZMod N, f (x, y + h) * star (f (x, y))

/-- Vertical cross-section of a two-dimensional finite set. -/
noncomputable def verticalSection {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (x : ZMod N) : Finset (ZMod N) := by
  classical
  exact Finset.univ.filter fun y => (x, y) ∈ A

/-- Horizontal cross-section of a two-dimensional finite set. -/
noncomputable def horizontalSection {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (y : ZMod N) : Finset (ZMod N) := by
  classical
  exact Finset.univ.filter fun x => (x, y) ∈ A

/-- A partial function is a Freiman homomorphism of order eight separately in
each coordinate. -/
def SeparatelyFreimanEight {N : Nat} [NeZero N] (A : Finset (Pair N))
    (phi : Pair N → ZMod N) : Prop :=
  (∀ x, FreimanHom 8 (verticalSection A x) (fun y => phi (x, y))) ∧
    ∀ y, FreimanHom 8 (horizontalSection A y) (fun x => phi (x, y))

/-- At least the stated proportion of 8-arrangements is respected. -/
def MostlyRespectsEight {N : Nat} [NeZero N] (A : Finset (Pair N))
    (phi : Pair N → ZMod N) (eta : Real) : Prop :=
  (1 - eta) * arrangementCount 8 A ≤ respectedArrangementCount 8 A phi

/-- The paper's bilinear functions include affine and one-variable terms. -/
def IsBilinear {N : Nat} (mu : Pair N → ZMod N) : Prop :=
  ∃ c00 c10 c01 c11 : ZMod N, ∀ z,
    mu z = c00 + c10 * z.1 + c01 * z.2 + c11 * z.1 * z.2

/-- Agreement with a bilinear function on a finite partial domain. -/
def BilinearOn {N : Nat} (B : Finset (Pair N)) (phi : Pair N → ZMod N) : Prop :=
  ∃ mu : Pair N → ZMod N, IsBilinear mu ∧ ∀ z, z ∈ B → phi z = mu z

/-- Linearity of a function on an abstract finite domain through a coordinate
map. -/
def LinearOnDomain {N : Nat} {X : Type*} (A : Finset X)
    (r : X → ZMod N) (phi : X → ZMod N) : Prop :=
  ∃ a b : ZMod N, ∀ x, x ∈ A → phi x = a * r x + b

/-- **Lemma 13.1.** -/
def lemma_13_1 : Prop :=
  ∀ (N : Nat) [NeZero N] (f : Pair N → Complex) (B : Finset (ZMod N))
      (sigma : ZMod N → ZMod N) (alpha : Real),
    DiscValued f →
    alpha * (N : Real) ^ 5 ≤
      ∑ h ∈ B, ‖fourier (verticalCorrelation f h) (sigma h)‖ ^ 2 →
    alpha ^ 4 * (N : Real) ^ 3 ≤ phiAdditiveCount B sigma

/-- **Corollary 13.2.** The 0--1-valued specialization of Lemma 13.1. -/
def corollary_13_2 : Prop :=
  ∀ (N : Nat) [NeZero N] (A : Finset (Pair N)) (B : Finset (ZMod N))
      (sigma : ZMod N → ZMod N) (alpha : Real),
    alpha * (N : Real) ^ 5 ≤
      ∑ h ∈ B, ‖fourier (verticalEdgeFiberFunction A h) (sigma h)‖ ^ 2 →
    alpha ^ 4 * (N : Real) ^ 3 ≤ phiAdditiveCount B sigma

/-- **Corollary 13.3.** Large Fourier coefficients are covered, away from a
small exceptional set of heights, by finitely many order-eight Freiman graphs.
The threshold is `theta*N^2`; one factor of `N` was lost later in the OCR. -/
def corollary_13_3 : Prop :=
  ∀ (N : Nat) [NeZero N] (A : Finset (Pair N)) (theta : Real), 0 < theta →
    ∃ q : Nat, ∃ B : Fin q → Finset (ZMod N),
      ∃ sigma : Fin q → ZMod N → ZMod N, ∃ G : Finset (ZMod N),
        (1 - theta) * N ≤ G.card ∧
        (∀ i, FreimanHom 8 (B i) (sigma i)) ∧
        (∀ i, (2 : Real) ^ (-(1882 : Int)) * theta ^ 10477 * N ≤
          (B i).card) ∧
        (q : Real) ≤ (2 : Real) ^ 1882 * theta ^ (-(10479 : Int)) ∧
        ∀ h, h ∈ G → ∀ r,
          theta * (N : Real) ^ 2 ≤
            ‖fourier (verticalEdgeFiberFunction A h) r‖ →
          ∃ i, h ∈ B i ∧ r = sigma i h

/-! ### The common hypotheses and the successive extraction data for 13.4--13.10 -/

/-- The standing hypotheses declared in the paragraph before Lemma 13.4. -/
structure Section13Context (N : Nat) [NeZero N] where
  A : Finset (Pair N)
  phi : Pair N → ZMod N
  alpha : Real
  eta : Real
  alpha_pos : 0 < alpha
  alpha_at_most_one : alpha ≤ 1
  card_A : (A.card : Real) = alpha * (N : Real) ^ 2
  separately_freiman : SeparatelyFreimanEight A phi
  eta_value : eta = (2 : Real) ^ (-(44 : Int))
  mostly_respected : MostlyRespectsEight A phi eta

def section13C {N : Nat} [NeZero N] (S : Section13Context N)
    (h : ZMod N) : Nat :=
  arrangementCountAtHeight 8 S.A h

def section13G {N : Nat} [NeZero N] (S : Section13Context N)
    (h : ZMod N) : Nat :=
  respectedArrangementCountAtHeight 8 S.A S.phi h

def IsGoodHeight {N : Nat} [NeZero N] (S : Section13Context N)
    (h : ZMod N) : Prop :=
  (1 - 2 * S.eta) * section13C S h ≤ section13G S h

noncomputable def goodHeightWeight {N : Nat} [NeZero N]
    (S : Section13Context N) (H : Finset (ZMod N)) : Nat := by
  classical
  exact (H.filter (IsGoodHeight S)).sum (section13C S)

def section13ThetaOne (theta : Real) : Real :=
  (2 : Real) ^ (-(1882 : Int)) * theta ^ 10477

def section13QBound (theta : Real) : Real :=
  (2 : Real) ^ 1882 * theta ^ (-(10479 : Int))

/-- `n` is the floor of the nonnegative real number `x`. -/
def IsNatFloor (x : Real) (n : Nat) : Prop :=
  (n : Real) ≤ x ∧ x < n + 1

/-- Data produced by Lemma 13.4. -/
structure Stage134Data (N : Nat) where
  q : Nat
  m : Nat
  P : ModAP N
  H : Finset (ZMod N)
  a : Fin q → ZMod N
  b : Fin q → ZMod N

/-- The complete conclusion of Lemma 13.4, including its two displayed
properties. -/
def IsStage134Data {N : Nat} [NeZero N] (S : Section13Context N)
    (theta : Real) (D : Stage134Data N) : Prop :=
  0 < D.q ∧ D.P.step != 0 ∧ D.P.IsProper ∧ D.H ⊆ D.P.carrier ∧
  (D.q : Real) ≤ section13QBound theta ∧
  IsNatFloor
    (section13ThetaOne theta / (64 * Real.pi) *
      (N : Real) ^
        (section13ThetaOne theta ^ 2 / (16 * (D.q : Real)))) D.m ∧
  (D.P.length = D.m ∨ D.P.length + 1 = D.m) ∧
  S.alpha ^ 32 * (N : Real) ^ 31 * D.P.length / 8 ≤
    goodHeightWeight S D.H ∧
  ∀ h, h ∈ D.H → ∀ r,
    theta * (N : Real) ^ 2 ≤
      ‖fourier (verticalEdgeFiberFunction S.A h) r‖ →
    ∃ i, r = D.a i * h + D.b i

/-- **Lemma 13.4.** The large-coefficient threshold is corrected to
`theta*N^2`, consistently with Corollary 13.3 and Parseval. -/
def lemma_13_4 : Prop :=
  ∀ (N : Nat) [NeZero N] (S : Section13Context N) (theta : Real),
    0 < theta → ∃ D : Stage134Data N, IsStage134Data S theta D

/-- Data produced by Lemma 13.5. -/
structure Stage135Data (N : Nat) where
  Q : ModAP N

def IsStrongHeight {N : Nat} [NeZero N] (S : Section13Context N)
    (h : ZMod N) : Prop :=
  S.alpha ^ 32 * (N : Real) ^ 31 / 16 ≤ section13C S h ∧
    IsGoodHeight S h

noncomputable def criticalHeights {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N) :
    Finset (ZMod N) := by
  classical
  exact (E.Q.carrier ∩ D.H).filter (IsStrongHeight S)

/-- The complete conclusion of Lemma 13.5. -/
def IsStage135Data {N : Nat} [NeZero N] (S : Section13Context N)
    (D : Stage134Data N) (E : Stage135Data N) : Prop :=
  E.Q.step != 0 ∧ E.Q.IsProper ∧ E.Q.carrier ⊆ D.P.carrier ∧
  (D.P.length : Real) ^
      ((1 : Real) / (2 : Real) ^ (12 * D.q)) / 2 ≤ E.Q.length ∧
  (∀ i, ∀ h, h ∈ E.Q.carrier →
    (centeredAbs ((D.a i * h + D.b i) * E.Q.step) : Real) ≤
      (D.P.length : Real) ^
        (-((1 : Real) / (2 : Real) ^ (11 * D.q))) * N) ∧
  S.alpha ^ 32 * E.Q.length / 20 ≤ (criticalHeights S D E).card

/-- **Lemma 13.5.** The lower bound for `C(h)` uses `N^31`; the `N^15`
appearing in the following prose is an OCR error. -/
def lemma_13_5 : Prop :=
  ∀ (N : Nat) [NeZero N] (S : Section13Context N) (theta : Real)
      (D : Stage134Data N),
    IsStage134Data S theta D →
    ∃ E : Stage135Data N, IsStage135Data S D E

/-- Data produced by Lemma 13.6. -/
structure Stage136Data (N : Nat) where
  R : ModAP N
  Y : ZMod N → Finset (Pair N)

def section13K (alpha : Real) : Real :=
  (2 : Real) ^ 114 * alpha ^ (-(320 : Int))

def section13Zeta (alpha : Real) : Real :=
  (2 : Real) ^ (-(228 * section13K alpha)) *
    alpha ^ (576 * section13K alpha)

def section13Q (alpha : Real) : Real :=
  (2 : Real) ^ ((2 : Nat) ^ 20) *
    alpha ^ (-((2 : Real) ^ (21 : Nat)))

noncomputable def stage136RestrictedEdges {N : Nat} [NeZero N]
    (F : Stage136Data N) (h : ZMod N) : Finset (Pair N) := by
  classical
  exact (F.Y h).filter fun z => z.1 ∈ F.R.carrier

/-- The complete conclusion of Lemma 13.6. -/
def IsStage136Data {N : Nat} [NeZero N] (S : Section13Context N)
    (D : Stage134Data N) (E : Stage135Data N) (F : Stage136Data N) : Prop :=
  F.R.step = E.Q.step ∧ F.R.step != 0 ∧ F.R.IsProper ∧
  section13Zeta S.alpha / 2 *
      (N : Real) ^
        ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha)) ≤ F.R.length ∧
  (∀ h, h ∈ criticalHeights S D E →
    F.Y h ⊆ verticalEdgeDomain S.A h ∧
    (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 * (N : Real) ^ 2 ≤
      (F.Y h).card ∧
    LinearOnDomain (stage136RestrictedEdges F h) (fun z : Pair N => z.1)
      (verticalPhiDifference S.phi h)) ∧
  (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 * F.R.length * N *
      (criticalHeights S D E).card ≤
    ∑ h ∈ criticalHeights S D E, (stage136RestrictedEdges F h).card ∧
  (2 : Real) ^ (-(48 : Int)) * S.alpha ^ 256 * E.Q.length * F.R.length * N ≤
    ∑ h ∈ criticalHeights S D E, (stage136RestrictedEdges F h).card

/-- **Lemma 13.6.** The `2^-43*alpha^224` bounds propagate the
proof-supported `alpha^6/20000` correction to Theorem 10.13; the stronger
printed `2^-26*alpha^128` bounds rely on that theorem's inconsistent claim. -/
def lemma_13_6 : Prop :=
  ∀ (N : Nat) [NeZero N] (S : Section13Context N) (D : Stage134Data N)
      (E : Stage135Data N),
    IsStage135Data S D E →
    ∃ F : Stage136Data N, IsStage136Data S D E F

/-- Translate a finite subset of `ZMod N`. -/
noncomputable def translateFinset {N : Nat} (A : Finset (ZMod N))
    (y : ZMod N) : Finset (ZMod N) := by
  classical
  exact A.image fun h => y + h

/-- Data produced by Lemma 13.7. -/
structure Stage137Data (N : Nat) where
  y : ZMod N
  S : ModAP N
  B : Finset (Pair N)

/-- The complete conclusion of Lemma 13.7. -/
def IsStage137Data {N : Nat} [NeZero N] (S0 : Section13Context N)
    (D : Stage134Data N) (E : Stage135Data N) (F : Stage136Data N)
    (G : Stage137Data N) : Prop :=
  G.S.step != 0 ∧ G.S.IsProper ∧ G.S.carrier ⊆ F.R.carrier ∧
  (F.R.length : Real) ^
      ((2 : Real) ^ (-(100 : Int)) * S0.alpha ^ 448) ≤ G.S.length ∧
  G.B ⊆ G.S.carrier.product (translateFinset (criticalHeights S0 D E) G.y) ∧
  (2 : Real) ^ (-(43 : Int)) * S0.alpha ^ 224 * G.S.length *
      (criticalHeights S0 D E).card ≤ G.B.card ∧
  (2 : Real) ^ (-(48 : Int)) * S0.alpha ^ 256 * E.Q.length * G.S.length ≤
      G.B.card ∧
  ∀ h, h ∈ criticalHeights S0 D E →
    LinearOn (G.S.carrier.filter fun x => (x, G.y + h) ∈ G.B)
      (fun x => S0.phi (x, G.y + h))

/-- **Lemma 13.7.** After propagating the corrected Lemma 13.6 density, the
progression-size exponent is `2^-100 * alpha^448`, all in the exponent of
`m2`. -/
def lemma_13_7 : Prop :=
  ∀ (N : Nat) [NeZero N] (S : Section13Context N) (D : Stage134Data N)
      (E : Stage135Data N) (F : Stage136Data N),
    IsStage136Data S D E F →
    ∃ G : Stage137Data N, IsStage137Data S D E F G

/-- Data produced by Lemma 13.8.  The row coefficients are stored as choices;
the paper's claim that they are unique is false for rows with fewer than two
points. -/
structure Stage138Data (N : Nat) where
  a : ZMod N → ZMod N
  c : ZMod N → ZMod N
  J : Finset (ZMod N)
  C : Finset (Pair N)

def IsStage138Data {N : Nat} [NeZero N] (S : Section13Context N)
    (D : Stage134Data N) (E : Stage135Data N) (G : Stage137Data N)
    (H : Stage138Data N) : Prop :=
  (∀ h, h ∈ criticalHeights S D E → ∀ x,
    (x, G.y + h) ∈ G.B →
      S.phi (x, G.y + h) = H.a h + H.c h * x) ∧
  H.J ⊆ criticalHeights S D E ∧
  FreimanHom 8 H.J (fun h => (H.a h, H.c h)) ∧
  H.C = G.B.filter (fun z => z.2 - G.y ∈ H.J) ∧
  (2 : Real) ^ (-(135 : Int)) * S.alpha ^ 704 * E.Q.length * G.S.length ≤
    H.C.card

/-- **Lemma 13.8.** -/
def lemma_13_8 : Prop :=
  ∀ (N : Nat) [NeZero N] (S : Section13Context N) (D : Stage134Data N)
      (E : Stage135Data N) (F : Stage136Data N) (G : Stage137Data N),
    IsStage137Data S D E F G →
    (2 : Real) ^ 135 * S.alpha ^ (-(704 : Int)) ≤ G.S.length →
    ∃ H : Stage138Data N, IsStage138Data S D E G H

/-- Data produced by Lemma 13.9. -/
structure Stage139Data (N : Nat) where
  U : ModAP N
  D : Finset (Pair N)

def IsStage139Data {N : Nat} [NeZero N] (S : Section13Context N)
    (E : Stage135Data N) (G : Stage137Data N) (H : Stage138Data N)
    (J : Stage139Data N) : Prop :=
  J.U.step != 0 ∧ J.U.IsProper ∧ J.U.carrier ⊆ E.Q.carrier ∧
  (∃ t : Nat, J.U.step = t • G.S.step) ∧
  (G.S.length : Real) ^
      ((2 : Real) ^ (-(284 : Int)) * S.alpha ^ 1408) ≤ J.U.length ∧
  J.D = H.C.filter (fun z => z.2 - G.y ∈ J.U.carrier ∩ H.J) ∧
  (2 : Real) ^ (-(135 : Int)) * S.alpha ^ 704 * G.S.length * J.U.length ≤
    J.D.card ∧
  BilinearOn J.D S.phi

/-- **Lemma 13.9.** Propagating the corrected preceding densities changes the
progression-size exponent to `2^-284 * alpha^1408`. -/
def lemma_13_9 : Prop :=
  ∀ (N : Nat) [NeZero N] (S : Section13Context N) (D : Stage134Data N)
      (E : Stage135Data N) (F : Stage136Data N) (G : Stage137Data N)
      (H : Stage138Data N),
    IsStage137Data S D E F G → IsStage138Data S D E G H →
    ∃ J : Stage139Data N, IsStage139Data S E G H J

/-- **Corollary 13.10.** -/
def corollary_13_10 : Prop :=
  ∀ (N : Nat) [NeZero N] (S : Section13Context N) (E : Stage135Data N)
      (G : Stage137Data N) (H : Stage138Data N) (J : Stage139Data N),
    IsStage139Data S E G H J →
    ∃ V W : ModAP N, ∃ E' : Finset (Pair N),
      V.step != 0 ∧ V.step = W.step ∧ V.IsProper ∧ W.IsProper ∧
      V.length = W.length ∧
      (J.U.length : Real) ^ ((1 : Real) / 2) - 1 ≤ V.length ∧
      E' ⊆ V.carrier.product W.carrier ∧
      (2 : Real) ^ (-(137 : Int)) * S.alpha ^ 704 * V.length * W.length ≤
        E'.card ∧
      BilinearOn E' S.phi

/-- **Lemma 13.11.** The respected proportion is corrected from the statement's
`1-2^-73` to `1-2^-44`, which is what the proof and Theorem 13.12 use.  The
large-`N` threshold inherited from Lemma 12.6 is made explicit. -/
def lemma_13_11 : Prop :=
  ∀ alpha : Real, 0 < alpha → alpha ≤ 1 → ∃ N0 : Nat,
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ f : ZMod N → Complex, DiscValued f →
        ¬ UniformOfDegree f alpha 3 →
        ∃ A : Finset (Pair N), ∃ phi : Pair N → ZMod N,
          (alpha / 2) ^ ((2 : Nat) ^ 66) * (N : Real) ^ 2 ≤ A.card ∧
          SeparatelyFreimanEight A phi ∧
          MostlyRespectsEight A phi ((2 : Real) ^ (-(44 : Int))) ∧
          ∀ z, z ∈ A →
            alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖

/-- **Theorem 13.12 (weak bilinear Freiman theorem).** The progression bound
in the PDF is the three-level exponent
`N^((1/2)^((1/alpha)^(2^70)))`; the OCR lost the top exponent.  Absolute-value
bars missing from the OCR'd Fourier conclusion are also restored. -/
def theorem_13_12 : Prop :=
  ∀ alpha : Real, 0 < alpha → alpha ≤ 1 → ∃ N0 : Nat,
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ f : ZMod N → Complex, DiscValued f →
        ¬ UniformOfDegree f alpha 3 →
        ∃ P Q : ModAP N, ∃ B : Finset (Pair N),
          ∃ phi : Pair N → ZMod N,
            P.step != 0 ∧ P.step = Q.step ∧ P.IsProper ∧ Q.IsProper ∧
            P.length = Q.length ∧
            (N : Real) ^
                ((1 / 2 : Real) ^
                  ((1 / alpha) ^ ((2 : Nat) ^ 70))) ≤ P.length ∧
            B ⊆ P.carrier.product Q.carrier ∧
            (alpha / 2) ^ ((2 : Nat) ^ 76) * P.length * Q.length ≤ B.card ∧
            BilinearOn (P.carrier.product Q.carrier) phi ∧
            ∀ z, z ∈ B →
              alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖

end LeanProofs.GowersSzemeredi
