import GowersSzemeredi.Section05
import GowersSzemeredi.Section10
import GowersSzemeredi.Sections14_15

/-!
# Gowers (2001), Section 16: formal statements

This file records the multiple-multilinearity induction.  The paper permits a
relation to have several values above a base point; accordingly relations are
represented as finite subsets of `ZMod N ^ k × ZMod N` rather than as functions.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-- The quantitative control function `c(theta,gamma,k)`. -/
def multipleC (theta gamma : Real) (k : Nat) : Real :=
  (gamma * theta) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 8)))

/-- The quantitative graph-count function `q(theta,gamma,k)`. -/
def multipleQ (theta gamma : Real) (k : Nat) : Real :=
  (multipleC theta gamma k)⁻¹

/-- The quantitative iteration-count function `s(theta,gamma,k)`. -/
def multipleS (theta gamma : Real) (k : Nat) : Real :=
  (2 / (theta * gamma)) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6)))

/-- The graph of a partial function. -/
noncomputable def partialGraph {N k : Nat} (B : Finset (Point N k))
    (phi : Point N k → ZMod N) : Finset (Point N k × ZMod N) := by
  classical
  exact B.image fun x => (x, phi x)

/-- A partial function has its graph inside a relation. -/
def GraphContained {N k : Nat} (B : Finset (Point N k))
    (phi : Point N k → ZMod N) (Gamma : Finset (Point N k × ZMod N)) : Prop :=
  ∀ x, x ∈ B → (x, phi x) ∈ Gamma

/-- The paper's `(gamma,r)`-multiple `k`-linearity.  Natural graph counts are
bounded by the real-valued control function, avoiding the article's informal
use of real numbers as cardinalities. -/
def MultiplyLinear {N k : Nat} [NeZero N] (gamma r : Real)
    (Gamma : Finset (Point N k × ZMod N)) : Prop :=
  ∀ theta : Real, 0 < theta → ∀ P : Box N k,
    ∃ M q : Nat, ∃ H : Finset (Point N k),
      ∃ Q : Fin M → Box N k,
        ∃ mu : Fin M → Fin q → Point N k → ZMod N,
          H ⊆ P.carrier ∧ (1 - theta) * P.carrier.card ≤ H.card ∧
          IsBoxPartition Q P ∧
          (q : Real) ≤ (multipleQ (r⁻¹ * theta) gamma k) ^ r ∧
          (∀ j, (P.width : Real) ^
              ((multipleC (r⁻¹ * theta) gamma k) ^ r) ≤ (Q j).width) ∧
          (∀ j i, IsMultilinear (mu j i)) ∧
          ∀ j x, x ∈ (Q j).carrier → x ∈ H → ∀ y,
            (x, y) ∈ Gamma → ∃ i, y = mu j i x

/-- Multiple multilinearity for a partial function means the property for its
graph. -/
def MultiplyLinearFunction {N k : Nat} [NeZero N] (gamma r : Real)
    (B : Finset (Point N k)) (phi : Point N k → ZMod N) : Prop :=
  MultiplyLinear gamma r (partialGraph B phi)

/-- The downward-closure observation immediately following the definition. -/
def multiplyLinear_downward_closed : Prop :=
  ∀ (N k : Nat) [NeZero N] (gamma r : Real)
      (Gamma Gamma' : Finset (Point N k × ZMod N)),
    Gamma' ⊆ Gamma → MultiplyLinear gamma r Gamma → MultiplyLinear gamma r Gamma'

/-- The integer `K=(k+1)^2*2^(k+4)` in Lemma 16.1. -/
def section16K (k : Nat) : Nat :=
  (k + 1) ^ 2 * 2 ^ (k + 4)

def section16RecurrenceExponent (k q : Nat) : Real :=
  (section16K k : Real) ^
    (-((((2 : Nat) ^ (k + 1) * q : Nat) : Int)))

/-- The explicit lower threshold for `m` in Lemma 16.1. -/
def section16WidthThreshold (k q : Nat) : Nat :=
  2 ^ ((section16K k) ^ ((2 : Nat) ^ (k + 1) * q) *
    2 ^ (32 * (k + 1) ^ 2 + 1))

/-- **Lemma 16.1.** The OCR-lost exponent is
`K^(-2^(k+1)*q)`.  The undefined proof constant `C_(k+1)` is omitted: the
cited Corollary 5.11 supplies the displayed constant `2`. -/
def lemma_16_1 : Prop :=
  ∀ (N k q m : Nat) [NeZero N] (P : Box N k)
      (mu : Fin q → Point N k → ZMod N),
    section16WidthThreshold k q ≤ m → m ≤ P.width →
    (∀ i, IsMultilinear (mu i)) →
    ∃ M : Nat, ∃ Q : Fin M → Box N k,
      IsBoxPartition Q P ∧
      (∀ j, (m : Real) ^ section16RecurrenceExponent k q ≤ (Q j).width) ∧
      ∀ i j x, x ∈ (Q j).carrier →
        (centeredAbs (mu i x * (Q j).commonDiff) : Real) ≤
          2 * (m : Real) ^ (-section16RecurrenceExponent k q) * N

/-! ### Product relations and the main induction statement -/

/-- Extension of the product property from partial functions to relations. -/
def RelationProductProperty {N k : Nat} [NeZero N] (gamma : Real)
    (Gamma : Finset (Point N k × ZMod N)) : Prop :=
  ∀ (B : Finset (Point N k)) (phi : Point N k → ZMod N),
    GraphContained B phi Gamma → HasProductProperty B phi gamma

noncomputable def relationProjection {N k : Nat}
    (Gamma : Finset (Point N k × ZMod N)) : Finset (Point N k) := by
  classical
  exact Gamma.image Prod.fst

noncomputable def restrictRelation {N k : Nat}
    (Gamma : Finset (Point N k × ZMod N)) (J : Finset (Point N k)) :
    Finset (Point N k × ZMod N) := by
  classical
  exact Gamma.filter fun z => z.1 ∈ J

/-- The assertion of Theorem 16.2 in a fixed dimension.  The threshold is
explicit because the proof uses the large-modulus version of Lemma 15.6. -/
def Theorem162At (k : Nat) : Prop :=
  ∀ gamma theta : Real, 0 < gamma → gamma ≤ 1 →
    0 < theta → theta ≤ 1 → ∃ N0 : Nat,
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
        ∀ Gamma : Finset (Point N k × ZMod N),
          (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ k →
          RelationProductProperty gamma Gamma →
          ∃ J : Finset (Point N k),
            (1 - theta) * (N : Real) ^ k ≤ J.card ∧
            MultiplyLinear gamma (gamma ^ (-(2 : Int)) * multipleS theta gamma k)
              (restrictRelation Gamma J)

/-- **Theorem 16.2.** -/
def theorem_16_2 : Prop :=
  ∀ k : Nat, Theorem162At k

/-- **Lemma 16.3.** The base case of Theorem 16.2. -/
def lemma_16_3 : Prop :=
  Theorem162At 1

/-! ### Coordinate faces and the structured pair from Lemma 16.4 -/

/-- A parameterization of an `l`-dimensional coordinate face in dimension
`d`.  The explicit map keeps later statements independent of choices of
inverses for the coordinate embedding. -/
structure CoordinateFace (N d l : Nat) where
  free : Fin l ↪ Fin d
  anchor : Point N d
  map : Point N l → Point N d
  map_free : ∀ x i, map x (free i) = x i
  map_fixed : ∀ x j, (∀ i, free i ≠ j) → map x j = anchor j

/-- Pull a partial-function domain back to a coordinate face. -/
noncomputable def CoordinateFace.domain {N d l : Nat} [NeZero N]
    (F : CoordinateFace N d l) (B : Finset (Point N d)) :
    Finset (Point N l) := by
  classical
  exact Finset.univ.filter fun x => F.map x ∈ B

/-- Pull a function back to a coordinate face. -/
def CoordinateFace.pullback {N d l : Nat} (F : CoordinateFace N d l)
    (phi : Point N d → ZMod N) : Point N l → ZMod N :=
  fun x => phi (F.map x)

/-- Every proper coordinate cross-section has the indicated multiple-
multilinearity control. -/
def ProperCrossSectionsMultiplyLinear {N d : Nat} [NeZero N]
    (gamma r : Real) (B : Finset (Point N d))
    (phi : Point N d → ZMod N) : Prop :=
  ∀ l : Nat, l < d → ∀ F : CoordinateFace N d l,
    MultiplyLinearFunction gamma r (F.domain B) (F.pullback phi)

/-- A relation is supported over the displayed set of base points. -/
def RelationSupportedOn {N d : Nat}
    (Gamma : Finset (Point N d × ZMod N)) (H : Finset (Point N d)) : Prop :=
  ∀ z, z ∈ Gamma → z.1 ∈ H

/-- The arrangement-density parameter denoted by `theta_1` in Section 16.
The proof first passes to a set of density at least `theta/2`; Lemma 15.6 then
contributes its own factor `1/2`.  Thus the mechanically justified parameter
is `(theta*gamma/4)^E`, not either the printed `(theta*gamma)^E` or the
intermediate `(theta*gamma/2)^E` written later in the proof. -/
def section16ThetaOne (theta gamma : Real) (k : Nat) : Real :=
  (theta * gamma / 4) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5)))

/-- The three conclusions imposed on `(B,phi)` in Lemma 16.4. -/
def Section16StructuredPair {N k : Nat} [NeZero N]
    (theta gamma : Real) (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) : Prop :=
  ProperCrossSectionsMultiplyLinear gamma
      (gamma ^ (-(2 : Int)) *
        multipleS ((2 : Real) ^ (-(k + 2 : Real)) * theta) gamma k)
      B phi ∧
    section16ThetaOne theta gamma k * (N : Real) ^ (17 * k + 15) ≤
      generalArrangementCount 8 B ∧
    (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B ≤
      respectedGeneralArrangementCount 8 B phi

/-! ### Cube domains and their induced maps -/

/-- The characteristic function of a finite point set. -/
def section16PointIndicator {N d : Nat} [NeZero N]
    (B : Finset (Point N d)) : Point N d → Complex :=
  fun x => if x ∈ B then 1 else 0

/-- Cubes with fixed sidelength `h`, together with their final-coordinate
cross-section, that lie in `B`.  This is the paper's domain `X_h`. -/
noncomputable def section16CubeDomain {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (h : Point N k) :
    Finset (AxisCube N k × ZMod N) := by
  classical
  exact Finset.univ.filter fun z =>
    z.1.side = h ∧ ∀ e, appendCoordinate (z.1.vertex e) z.2 ∈ B

/-- The finite type underlying `X_h`. -/
abbrev Section16CubeElement {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (h : Point N k) :=
  {z : AxisCube N k × ZMod N // z ∈ section16CubeDomain B h}

/-- The multifunction-domain structure on `X_h`; its index is the final
cross-section coordinate. -/
def section16CubeMultifunctionDomain {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (h : Point N k) :
    MultifunctionDomain N (Section16CubeElement B h) :=
  ⟨fun z => z.1.2⟩

/-- The alternating value induced by `phi` on a cube in `X_h`. -/
def section16InducedCubeMap {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (h : Point N k)
    (phi : Point N (k + 1) → ZMod N) :
    Section16CubeElement B h → ZMod N :=
  fun z => ∑ e : Fin k → Bool,
    (-1 : ZMod N) ^ boolWeight e *
      phi (appendCoordinate (z.1.1.vertex e) z.1.2)

/-- Number of `d`-arrangements with the fixed common sidelength `h`. -/
def section16ArrangementCountAtSide {N k : Nat} [NeZero N] (d : Nat)
    (B : Finset (Point N (k + 1))) (h : Point N k) : Nat :=
  countWhere fun R : GeneralArrangement N k d => R.IsIn B ∧ R.side = h

/-- Number of respected `d`-arrangements with common sidelength `h`. -/
def section16RespectedArrangementCountAtSide {N k : Nat} [NeZero N] (d : Nat)
    (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) (h : Point N k) : Nat :=
  countWhere fun R : GeneralArrangement N k d =>
    R.IsIn B ∧ R.side = h ∧ R.IsRespected phi

/-- The parameter `delta=2^-37*(theta_1/4)^(11/2)`. -/
def section16Delta (theta1 : Real) : Real :=
  (2 : Real) ^ (-(37 : Real)) * (theta1 / 4) ^ ((11 : Real) / 2)

/-- The Bohr radius `zeta=2^-s(theta,gamma,k)`. -/
def section16Zeta (theta gamma : Real) (k : Nat) : Real :=
  (2 : Real) ^ (-multipleS theta gamma k)

/-- Large Fourier frequencies `K_h` of the cube-counting function. -/
noncomputable def section16LargeSpectrum {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (h : Point N k) (delta : Real) :
    Finset (ZMod N) := by
  classical
  exact Finset.univ.filter fun r =>
    delta * (N : Real) ^ (k + 1) ≤
      ‖fourier (higherCubeCorrelation (section16PointIndicator B) h) r‖

/-- The graph relation of all large frequencies `K_h`. -/
noncomputable def section16SpectrumRelation {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (delta : Real) :
    Finset (Point N k × ZMod N) := by
  classical
  exact Finset.univ.filter fun z => z.2 ∈ section16LargeSpectrum B z.1 delta

/-- Split off the last coordinate of a point. -/
def section16Init {N k : Nat} (x : Point N (k + 1)) : Point N k :=
  fun i => x (Fin.castSucc i)

/-- The final coordinate of a point. -/
def section16Last {N k : Nat} (x : Point N (k + 1)) : ZMod N :=
  x (Fin.last k)

/-- A `(k+1)`-box is the Cartesian product of a `k`-box and a final modular
arithmetic progression. -/
def IsLastCoordinateBoxProduct {N k : Nat} [NeZero N]
    (P : Box N (k + 1)) (Q : Box N k) (I : ModAP N) : Prop :=
  P.carrier = Finset.univ.filter (fun x =>
      section16Init x ∈ Q.carrier ∧ section16Last x ∈ I.carrier) ∧
    P.commonDiff = Q.commonDiff ∧ I.step = P.commonDiff

/-! ### Lemmas 16.4--16.5 -/

/-- **Lemma 16.4.** The inductive dichotomy.  The large-modulus threshold is
explicit because the proof invokes Lemma 15.6.  Item (ii) uses the corrected
safe factor `(theta*gamma/4)^(2^(2^(k+5)))`: the construction has density
`theta/2`, and Lemma 15.6 contributes one further division by two.  The proof
also invokes Theorem 16.2 in every positive dimension at most `k`, so that
induction family is made explicit rather than assuming only its top member. -/
def lemma_16_4 : Prop :=
  ∀ (k : Nat) (theta gamma : Real),
    0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    (∀ l : Nat, 1 ≤ l → l ≤ k → Theorem162At l) → ∃ N0 : Nat,
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N → Odd N →
        ∀ Gamma : Finset (Point N (k + 1) × ZMod N),
          (Gamma.card : Real) ≤
              gamma ^ (-(2 : Int)) * (N : Real) ^ (k + 1) →
          RelationProductProperty gamma Gamma →
          (∃ H : Finset (Point N (k + 1)),
              (H.card : Real) < theta * (N : Real) ^ (k + 1) ∧
              RelationSupportedOn Gamma H) ∨
            ∃ (B : Finset (Point N (k + 1)))
                (phi : Point N (k + 1) → ZMod N),
              GraphContained B phi Gamma ∧
              Section16StructuredPair theta gamma B phi

/-- **Lemma 16.5.** For many sidelengths, the induced cube map is an exact
homomorphism on a large subset of `X_h`.  The lower bound
`2^-27*theta_1^6` is the propagation of the corrected Theorem 10.13 bound. -/
def lemma_16_5 : Prop :=
  ∀ (N k : Nat) [NeZero N] (theta gamma : Real)
      (B : Finset (Point N (k + 1)))
      (phi : Point N (k + 1) → ZMod N),
    0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    Section16StructuredPair theta gamma B phi →
    let theta1 := section16ThetaOne theta gamma k
    let delta := section16Delta theta1
    let zeta := section16Zeta theta gamma k
    ∃ H : Finset (Point N k),
      theta1 / 4 * (N : Real) ^ (17 * k + 15) ≤
          ∑ h ∈ H, (section16ArrangementCountAtSide 8 B h : Real) ∧
      ∃ Y : (h : Point N k) → Finset (Section16CubeElement B h),
        ∃ psi : Point N k → ZMod N → ZMod N,
          ∀ h, h ∈ H →
            (2 : Real) ^ (-(27 : Real)) * theta1 ^ 6 *
                (section16CubeDomain B h).card ≤ (Y h).card ∧
            HasBohrDifferenceModel
              (section16CubeMultifunctionDomain B h)
              (section16InducedCubeMap B h phi)
              (section16LargeSpectrum B h delta) zeta (Y h) (psi h)

/-! ### The induced partial map and Lemma 16.6 -/

/-- The domain on which the fibrewise induced value `phi' (h,x)` is defined. -/
noncomputable def section16InducedDomain {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (H : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h)) :
    Finset (Point N k × ZMod N) := by
  classical
  exact Finset.univ.filter fun z =>
    z.1 ∈ H ∧ ∃ C, C ∈ Y z.1 ∧ C.1.2 = z.2

/-- The hypotheses saying that `phiPrime` is the value induced on each
nonempty fibre `Y_h(x)` and is linear along the short Bohr progressions
provided by Corollary 10.14. -/
def Section16InducedSelection {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) (H : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h))
    (K : Point N k → Finset (ZMod N)) (zeta : Real)
    (phiPrime : Point N k → ZMod N → ZMod N) : Prop :=
  (∀ h, h ∈ H → ∀ C, C ∈ Y h →
      phiPrime h C.1.2 = section16InducedCubeMap B h phi C) ∧
    ∀ h, h ∈ H → ∀ m : Nat, 0 < m → ∀ d : ZMod N,
      d ∈ bohr (K h) (zeta / m) → ∀ I : ModAP N,
        I.step = d → I.length ≤ m →
        LinearOn (I.carrier.filter fun x =>
          (h, x) ∈ section16InducedDomain B H Y) (phiPrime h)

/-- The parameter `t=delta^-2*s(theta_1/8,delta,k)`. -/
def section16T (delta theta1 : Real) (k : Nat) : Real :=
  delta ^ (-(2 : Int)) * multipleS (theta1 / 8) delta k

/-- The natural number of multilinear graphs used in Lemma 16.6 is bounded
by this real quantity. -/
def section16Lemma6QBound (sigma delta theta1 : Real) (k : Nat) : Real :=
  let t := section16T delta theta1 k
  (multipleQ (sigma / t) delta k) ^ t

/-- Corrected width in Lemma 16.6.  The denominator is
`2*K^(2^(k+1)*q)`, not the flattened OCR expression. -/
def section16Lemma6Width (m q k : Nat) (sigma delta theta1 zeta : Real) : Real :=
  let t := section16T delta theta1 k
  (zeta / 2) * (m : Real) ^
    (((multipleC (sigma / t) delta k) ^ t) /
      (2 * (section16K k : Real) ^ ((2 : Nat) ^ (k + 1) * q)))

/-- **Lemma 16.6.** Partition a product box so that the induced map is
linear in its final variable.  `q` is explicitly natural and has the bound
from multiple multilinearity.  The frequency estimate used here is the one
from Lemma 16.1 with its missing factor `N` restored. -/
def lemma_16_6 : Prop :=
  ∀ (N k m : Nat) [NeZero N] (theta gamma sigma : Real),
    0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    0 < sigma → sigma ≤ 1 →
    ∀ (B : Finset (Point N (k + 1)))
      (phi : Point N (k + 1) → ZMod N)
      (H Jbase H1 : Finset (Point N k))
      (Y : (h : Point N k) → Finset (Section16CubeElement B h))
      (phiPrime : Point N k → ZMod N → ZMod N),
    let theta1 := section16ThetaOne theta gamma k
    let delta := section16Delta theta1
    let zeta := section16Zeta theta gamma k
    let t := section16T delta theta1 k
    H1 = H ∩ Jbase →
    MultiplyLinear delta t
      (restrictRelation (section16SpectrumRelation B delta) Jbase) →
    Section16InducedSelection B phi H Y
      (fun h => section16LargeSpectrum B h delta) zeta phiPrime →
    ∀ (P : Box N (k + 1)) (Q : Box N k) (I : ModAP N),
      IsLastCoordinateBoxProduct P Q I → m ≤ P.width →
      ∃ q : Nat,
        (q : Real) ≤ section16Lemma6QBound sigma delta theta1 k ∧
        ∃ G : Finset (Point N k), ∃ M : Nat,
          ∃ S : Fin M → Box N (k + 1),
            ∃ T : Fin M → Box N k, ∃ A : Fin M → ModAP N,
              G ⊆ Q.carrier ∧
              (1 - sigma) * Q.carrier.card ≤ G.card ∧
              IsBoxPartition S P ∧
              (∀ u, IsLastCoordinateBoxProduct (S u) (T u) (A u)) ∧
              (∀ u, section16Lemma6Width m q k sigma delta theta1 zeta ≤
                (S u).width) ∧
              ∀ u h, h ∈ G → h ∈ H1 → h ∈ (T u).carrier →
                LinearOn ((A u).carrier.filter fun x =>
                  (h, x) ∈ section16InducedDomain B H Y) (phiPrime h)

/-! ### Lemmas 16.7--16.8 -/

/-- The corrected density parameter in Lemma 16.7, after propagating the
proof-supported size in Lemma 16.5. -/
def section16ThetaTwo (theta1 : Real) : Real :=
  (2 : Real) ^ (-(32 : Real)) * theta1 ^ 8

/-- The alternating value of the cube with base `x0`, sidelength `h`, and
final cross-section `x`. -/
def section16CubeValueAtBase {N k : Nat} [NeZero N]
    (phi : Point N (k + 1) → ZMod N) (x0 h : Point N k) (x : ZMod N) :
    ZMod N :=
  ∑ e : Fin k → Bool, (-1 : ZMod N) ^ boolWeight e *
    phi (appendCoordinate (fun i => x0 i + if e i then h i else 0) x)

/-- A pair `(h,x)` for which `Y_h(x)` contains the cube based at `x0`. -/
def Section16GoodInducedPair {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (H : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h))
    (x0 : Point N k) (z : Point N k × ZMod N) : Prop :=
  z.1 ∈ H ∧ ∃ C, C ∈ Y z.1 ∧ C.1.1.base = x0 ∧ C.1.2 = z.2

/-- Number of good `(h,x)` pairs for a fixed cube base. -/
def section16GoodInducedPairCount {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (H : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h))
    (x0 : Point N k) : Nat :=
  countWhere (Section16GoodInducedPair B H Y x0)

/-- **Lemma 16.7.** A common base realizes many of the induced cube values.
The parameter is the corrected `theta_2=2^-32*theta_1^8`. -/
def lemma_16_7 : Prop :=
  ∀ (N k : Nat) [NeZero N] (theta gamma : Real)
      (B : Finset (Point N (k + 1)))
      (phi : Point N (k + 1) → ZMod N)
      (H1 : Finset (Point N k))
      (Y : (h : Point N k) → Finset (Section16CubeElement B h))
      (phiPrime : Point N k → ZMod N → ZMod N),
    let theta1 := section16ThetaOne theta gamma k
    let delta := section16Delta theta1
    let zeta := section16Zeta theta gamma k
    theta1 / 8 * (N : Real) ^ k ≤ H1.card →
    (∀ h, h ∈ H1 → theta1 / 4 * (N : Real) ^ (k + 1) ≤
      (section16CubeDomain B h).card) →
    (∀ h, h ∈ H1 →
      (2 : Real) ^ (-(27 : Real)) * theta1 ^ 6 *
          (section16CubeDomain B h).card ≤ (Y h).card) →
    Section16InducedSelection B phi H1 Y
      (fun h => section16LargeSpectrum B h delta) zeta phiPrime →
    ∃ x0 : Point N k,
      section16ThetaTwo theta1 * (N : Real) ^ (k + 1) ≤
          section16GoodInducedPairCount B H1 Y x0 ∧
      ∀ z, Section16GoodInducedPair B H1 Y x0 z →
        phiPrime z.1 z.2 = section16CubeValueAtBase phi x0 z.1 z.2

/-- Union of a finite family of arbitrary finite sets. -/
noncomputable def section16FinsetUnion {ι X : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq X] (A : ι → Finset X) : Finset X := by
  classical
  exact Finset.univ.biUnion A

/-- **Lemma 16.8.** Finite unions of multiply-linear relations and finite
sums of multiply-linear partial functions preserve the property, multiplying
the iteration parameter by the number of terms. -/
def lemma_16_8 : Prop :=
  (∀ (N k r : Nat) [NeZero N] (gamma s : Real)
      (Gamma : Fin r → Finset (Point N (k + 1) × ZMod N)),
      (∀ i, MultiplyLinear gamma s (Gamma i)) →
      MultiplyLinear gamma ((r : Real) * s) (section16FinsetUnion Gamma)) ∧
  ∀ (N k r : Nat) [NeZero N] (gamma s : Real)
      (B : Finset (Point N (k + 1)))
      (phi : Fin r → Point N (k + 1) → ZMod N),
    (∀ i, MultiplyLinearFunction gamma s B (phi i)) →
    MultiplyLinearFunction gamma ((r : Real) * s) B
      (fun x => ∑ i, phi i x)

/-! ### The all-ones vertex and Lemma 16.9 -/

/-- The translated cube-vertex function `phi_epsilon(h,x)`. -/
def section16TranslatedVertex {N k : Nat}
    (phi : Point N (k + 1) → ZMod N) (x0 : Point N k)
    (e : Fin k → Bool) (z : Point N (k + 1)) : ZMod N :=
  phi (appendCoordinate
    (fun i => x0 i + if e i then section16Init z i else 0)
    (section16Last z))

/-- The all-ones vertex map `phi_1(h,x)=phi(x_0+h,x)`.  This is the corrected
indexing used in Lemmas 16.9--16.10. -/
def section16PhiOne {N k : Nat}
    (phi : Point N (k + 1) → ZMod N) (x0 : Point N k)
    (z : Point N (k + 1)) : ZMod N :=
  phi (appendCoordinate (fun i => x0 i + section16Init z i) (section16Last z))

/-- The partial domain `B_1` of good `(h,x)` pairs obtained in Lemma 16.7. -/
noncomputable def section16GoodDomain {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (H : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h))
    (x0 : Point N k) : Finset (Point N (k + 1)) := by
  classical
  exact Finset.univ.filter fun z =>
    Section16GoodInducedPair B H Y x0 (section16Init z, section16Last z)

/-- Lift `phiPrime(h,x)` to a function of a `(k+1)`-dimensional point. -/
def section16PhiPrimeLift {N k : Nat}
    (phiPrime : Point N k → ZMod N → ZMod N)
    (z : Point N (k + 1)) : ZMod N :=
  phiPrime (section16Init z) (section16Last z)

/-- The sum of the other `2^k-1` translated vertices, with the parity signs
obtained by solving the cube identity for its all-ones vertex. -/
def section16PhiRemainder {N k : Nat} [NeZero N]
    (phi : Point N (k + 1) → ZMod N) (x0 : Point N k)
    (z : Point N (k + 1)) : ZMod N :=
  -∑ e ∈ (Finset.univ.filter fun e : Fin k → Bool => e ≠ fun _ => true),
    (-1 : ZMod N) ^ (k + boolWeight e) * section16TranslatedVertex phi x0 e z

/-- The corrected alternating identity
`phi_1=(-1)^k phi' + phi''` on `B_1`. -/
def Section16PhiOneIdentity {N k : Nat} [NeZero N]
    (B1 : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) (x0 : Point N k)
    (phiPrime : Point N k → ZMod N → ZMod N) : Prop :=
  ∀ z, z ∈ B1 →
    section16PhiOne phi x0 z =
      (-1 : ZMod N) ^ k * section16PhiPrimeLift phiPrime z +
        section16PhiRemainder phi x0 z

/-- The parameter called `r` in Lemma 16.9. -/
def section16Lemma9R (theta gamma : Real) (k : Nat) : Real :=
  ((2 ^ k - 1 : Nat) : Real) * gamma ^ (-(2 : Int)) *
    multipleS ((2 : Real) ^ (-(k + 2 : Real)) * theta) gamma k

/-- Corrected natural graph-count bound for the `gamma`-controlled cover in
Lemma 16.9.  Its ambient dimension is `k+1`. -/
def section16Lemma9QBound (sigma theta gamma : Real) (k : Nat) : Real :=
  let r := section16Lemma9R theta gamma k
  (multipleQ (sigma / (2 * r)) gamma (k + 1)) ^ r

/-- The distinct graph-count bound coming from the `delta`-controlled
application of Lemma 16.6 inside Lemma 16.9. -/
def section16Lemma9DeltaQBound (sigma delta theta1 : Real) (k : Nat) : Real :=
  let t := section16T delta theta1 k
  (multipleQ (sigma / (2 * t)) delta k) ^ t

/-- Corrected width in Lemma 16.9: there is no undefined `C_(k+1)`, the
`gamma`-side control has ambient dimension `k+1`, and the denominator is
`2*K^(2^(k+1)*qDelta)`.  The denominator uses the graph count from the
`delta`-controlled Lemma 16.6, not the generally different number of graphs
in the final `gamma`-controlled line cover. -/
def section16Lemma9Width (m qDelta k : Nat)
    (sigma theta gamma delta theta1 zeta : Real) : Real :=
  let r := section16Lemma9R theta gamma k
  let t := section16T delta theta1 k
  (zeta / 2) * (m : Real) ^
    (((multipleC (sigma / (2 * r)) gamma (k + 1)) ^ r *
      (multipleC (sigma / (2 * t)) delta k) ^ t) /
      (2 * (section16K k : Real) ^ ((2 : Nat) ^ (k + 1) * qDelta)))

/-- The line-cover conclusion of Lemma 16.9 on one box. -/
def Section16LineCover {N k : Nat} [NeZero N]
    (P : Box N (k + 1)) (B1 : Finset (Point N (k + 1)))
    (phi1 : Point N (k + 1) → ZMod N)
    (sigma l : Real) (q : Nat) : Prop :=
  ∃ E : Finset (Point N (k + 1)), ∃ M : Nat,
    ∃ S : Fin M → Box N (k + 1),
      ∃ T : Fin M → Box N k, ∃ A : Fin M → ModAP N,
        ∃ ell : Fin M → Point N k → Fin q → ZMod N → ZMod N,
          E ⊆ P.carrier ∧ (1 - sigma) * P.carrier.card ≤ E.card ∧
          IsBoxPartition S P ∧
          (∀ u, IsLastCoordinateBoxProduct (S u) (T u) (A u)) ∧
          (∀ u, l ≤ (S u).width) ∧
          (∀ u h i, LinearOn Finset.univ (ell u h i)) ∧
          ∀ u h x, h ∈ (T u).carrier →
            appendCoordinate h x ∈ B1 → appendCoordinate h x ∈ E →
            appendCoordinate h x ∈ (S u).carrier →
            ∃ i, phi1 (appendCoordinate h x) = ell u h i x

/-- **Lemma 16.9.** On almost all of every box, `phi_1` is covered on each
last-coordinate fibre by at most `q(sigma/(2r),gamma,k+1)^r` linear maps.
The statement exposes the distinct natural graph counts `qGamma` for that
cover and `qDelta` for the recurrence-width loss inherited from Lemma 16.6;
the article conflates these quantities in the displayed width. -/
def lemma_16_9 : Prop :=
  ∀ (N k m : Nat) [NeZero N] (theta gamma sigma : Real),
    0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    0 < sigma → sigma ≤ 1 →
    ∀ (B : Finset (Point N (k + 1)))
      (phi : Point N (k + 1) → ZMod N)
      (H Jbase H1 : Finset (Point N k))
      (Y : (h : Point N k) → Finset (Section16CubeElement B h))
      (phiPrime : Point N k → ZMod N → ZMod N) (x0 : Point N k),
    let theta1 := section16ThetaOne theta gamma k
    let delta := section16Delta theta1
    let zeta := section16Zeta theta gamma k
    let t := section16T delta theta1 k
    let r := section16Lemma9R theta gamma k
    let B1 := section16GoodDomain B H1 Y x0
    H1 = H ∩ Jbase →
    MultiplyLinear delta t
      (restrictRelation (section16SpectrumRelation B delta) Jbase) →
    Section16InducedSelection B phi H Y
      (fun h => section16LargeSpectrum B h delta) zeta phiPrime →
    Section16PhiOneIdentity B1 phi x0 phiPrime →
    MultiplyLinearFunction gamma r B1 (section16PhiRemainder phi x0) →
    ∀ P : Box N (k + 1), m ≤ P.width →
      ∃ qGamma qDelta : Nat,
        (qGamma : Real) ≤ section16Lemma9QBound sigma theta gamma k ∧
        (qDelta : Real) ≤
          section16Lemma9DeltaQBound sigma delta theta1 k ∧
        Section16LineCover P B1 (section16PhiOne phi x0) sigma
          (section16Lemma9Width m qDelta k sigma theta gamma delta theta1 zeta)
          qGamma

/-! ### Lemma 16.10 and Corollary 16.11 -/

/-- Domain of the cross-section obtained by fixing the final coordinate. -/
noncomputable def section16FinalCoordinateSection {N k : Nat} [NeZero N]
    (B1 : Finset (Point N (k + 1))) (x : ZMod N) : Finset (Point N k) := by
  classical
  exact Finset.univ.filter fun h => appendCoordinate h x ∈ B1

/-- Restriction of a `(k+1)`-variable function after fixing its final
coordinate. -/
def section16FinalCoordinateRestriction {N k : Nat}
    (phi1 : Point N (k + 1) → ZMod N) (x : ZMod N) :
    Point N k → ZMod N :=
  fun h => phi1 (appendCoordinate h x)

/-- The proper-cross-section input used in Lemma 16.10, with the final
coordinate fixed and the remaining variables indexed by `h`. -/
def FinalCoordinateSectionsMultiplyLinear {N k : Nat} [NeZero N]
    (gamma r : Real) (B1 : Finset (Point N (k + 1)))
    (phi1 : Point N (k + 1) → ZMod N) : Prop :=
  ∀ x : ZMod N,
    MultiplyLinearFunction gamma r (section16FinalCoordinateSection B1 x)
      (section16FinalCoordinateRestriction phi1 x)

/-- The conclusion of Lemma 16.9 uniformly over all boxes and error
parameters, packaged as a standing hypothesis for Lemma 16.10. -/
def Section16AllBoxLineCovers {N k : Nat} [NeZero N]
    (theta gamma : Real) (B1 : Finset (Point N (k + 1)))
    (phi1 : Point N (k + 1) → ZMod N) : Prop :=
  let theta1 := section16ThetaOne theta gamma k
  let delta := section16Delta theta1
  let zeta := section16Zeta theta gamma k
  ∀ sigma : Real, 0 < sigma → sigma ≤ 1 → ∀ m : Nat,
    ∀ P : Box N (k + 1), m ≤ P.width →
      ∃ qGamma qDelta : Nat,
        (qGamma : Real) ≤ section16Lemma9QBound sigma theta gamma k ∧
        (qDelta : Real) ≤
          section16Lemma9DeltaQBound sigma delta theta1 k ∧
        Section16LineCover P B1 phi1 sigma
          (section16Lemma9Width m qDelta k sigma theta gamma delta theta1 zeta)
          qGamma

/-- **Lemma 16.10.** The correctly indexed all-ones vertex map on `B_1` is
itself `(gamma,1)`-multiply `(k+1)`-linear.  The two standing inputs are
packaged explicitly: multiply multilinearity of the fixed-final-coordinate
cross-sections and the line covers supplied by Lemma 16.9.

Editorial warning: this records the printed qualitative claim, but the
proof's closing quantitative comparison is not uniform in the outer
parameter `theta`.  With the displayed control functions, its auxiliary
graph count becomes unbounded as `theta` tends to zero while the target
`multipleQ` bound is fixed.  Thus this Prop-valued catalogue entry must not
be read as supplying a proof of the assertion. -/
def lemma_16_10 : Prop :=
  ∀ (N k : Nat) [NeZero N] (theta gamma : Real),
    0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    ∀ (B : Finset (Point N (k + 1)))
      (phi : Point N (k + 1) → ZMod N)
      (H1 : Finset (Point N k))
      (Y : (h : Point N k) → Finset (Section16CubeElement B h))
      (x0 : Point N k),
    let B1 := section16GoodDomain B H1 Y x0
    let phi1 := section16PhiOne phi x0
    let crossSectionR := gamma ^ (-(2 : Int)) *
      multipleS ((2 : Real) ^ (-(k + 2 : Real)) * theta) gamma k
    FinalCoordinateSectionsMultiplyLinear gamma crossSectionR B1 phi1 →
    Section16AllBoxLineCovers theta gamma B1 phi1 →
    MultiplyLinearFunction gamma 1 B1 phi1

/-- The iteration parameter used in the proof of Corollary 16.11. -/
def section16CorollaryIteration (alpha : Real) (k : Nat) : Real :=
  4 * alpha ^ (-(2 : Int)) * multipleS (alpha / 4) (alpha / 2) k

/-- The common width and density exponent actually supplied by the preceding
multiple-linearity controls in Corollary 16.11. -/
def section16CorollaryExponent (alpha : Real) (k : Nat) : Real :=
  let r := section16CorollaryIteration alpha k
  (alpha / 8) * (multipleC (r⁻¹ * (alpha / 8)) (alpha / 2) k) ^ r

/-- Number of points in a box at which a multilinear frequency selects a
large Fourier coefficient of the iterated difference. -/
def section16LargeMultilinearFrequencyCount {N k : Nat} [NeZero N]
    (f : ZMod N → Complex) (P : Box N k)
    (mu : Point N k → ZMod N) (alpha : Real) : Nat :=
  countWhere fun y : Point N k => y ∈ P.carrier ∧
    alpha / 2 * N ≤ ‖fourier (cubeDifference f y) (mu y)‖

/-- **Corollary 16.11.** Failure of degree-`k+1` uniformity yields a large
box on which many large Fourier frequencies agree with one multilinear map.

The article replaces the exponent actually obtained from Theorem 16.2 by
`(alpha/2)^(2^(2^(k+9)))`.  That replacement has the inequality in the wrong
direction: the iteration parameter itself grows as `alpha` decreases.  Both
occurrences below therefore use the safe exact exponent yielded by the
proof, namely `(alpha/8) * c(r⁻¹*(alpha/8),alpha/2,k)^r`. -/
def corollary_16_11 : Prop :=
  ∀ (k : Nat) (alpha : Real), 1 ≤ k → 0 < alpha → alpha ≤ 1 / 2 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N → Odd N →
      ∀ f : ZMod N → Complex, DiscValued f →
        ¬ UniformOfDegree f alpha (k + 1) →
        ∃ P : Box N k, ∃ mu : Point N k → ZMod N,
          IsMultilinear mu ∧
          (N : Real) ^ section16CorollaryExponent alpha k ≤ P.width ∧
          section16CorollaryExponent alpha k * P.carrier.card ≤
            section16LargeMultilinearFrequencyCount f P mu alpha

end LeanProofs.GowersSzemeredi
