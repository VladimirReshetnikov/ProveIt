import GowersSzemeredi.Sections12_13

/-!
# Gowers (2001), Sections 14--15: respected higher-dimensional arrangements

This file records all numbered results in Sections 14 and 15 of Gowers's
proof as `Prop`-valued definitions.  It also introduces the coordinatewise
product property, axis-parallel cubes and configurations, general
`d`-arrangements, and the Walsh-theoretic degeneracy notion used in Section 15.
No numbered result is asserted here.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ## Coordinate restrictions and the product property -/

/-- Replace the `j`th coordinate of a point. -/
def replaceCoordinate {N k : Nat} (y : Point N k) (j : Fin k) (x : ZMod N) :
    Point N k :=
  Function.update y j x

/-- The varying coordinates in the `j`-cross-section of `B` through `y`. -/
noncomputable def coordinateSection {N k : Nat} [NeZero N]
    (B : Finset (Point N k)) (y : Point N k) (j : Fin k) : Finset (ZMod N) := by
  classical
  exact Finset.univ.filter fun x => replaceCoordinate y j x ∈ B

/-- The restriction of a partial map to a coordinate line, represented as a
total map whose domain is separately recorded by `coordinateSection`. -/
def coordinateRestriction {N k : Nat} (phi : Point N k → ZMod N)
    (y : Point N k) (j : Fin k) : ZMod N → ZMod N :=
  fun x => phi (replaceCoordinate y j x)

/-- Weighted additive quadruples that are additive after every map in `psi`. -/
noncomputable def weightedSimultaneousAdditiveEnergy {N p : Nat} [NeZero N]
    (E : Finset (ZMod N)) (theta : ZMod N → Real)
    (psi : Fin p → ZMod N → ZMod N) : Real := by
  classical
  exact ∑ q : Fin 4 → ZMod N,
    if (∀ t, q t ∈ E) ∧ IsAdditiveQuadruple q ∧
        ∀ i, IsAdditiveQuadruple (fun t => psi i (q t)) then
      ∏ t, theta (q t)
    else 0

/-- A partial function has the product property with parameter `gamma` when
every finite family of parallel coordinate restrictions has the weighted
simultaneous-additivity lower bound from Section 14. -/
def HasProductProperty {N k : Nat} [NeZero N]
    (B : Finset (Point N k)) (phi : Point N k → ZMod N) (gamma : Real) : Prop :=
  ∀ (p : Nat) (j : Fin k) (y : Fin p → Point N k)
      (E : Finset (ZMod N)) (theta : ZMod N → Real),
    (∀ x, 0 ≤ theta x) →
    (∀ i x, x ∈ E → replaceCoordinate (y i) j x ∈ B) →
    gamma ^ (8 * p) * (N : Real)⁻¹ * (∑ x ∈ E, theta x) ^ 4 ≤
      weightedSimultaneousAdditiveEnergy E theta
        (fun i => coordinateRestriction phi (y i) j)

/-! ## The Fourier inputs to the product property -/

/-- The function `f_h(y)` used in Proposition 14.1. -/
def firstCoordinateCorrelation {N : Nat} [NeZero N]
    (f : Pair N → Complex) (h y : ZMod N) : Complex :=
  ∑ x : ZMod N, f (x + h, y) * star (f (x, y))

/-- Append a final coordinate to a point. -/
def appendCoordinate {N k : Nat} (x : Point N k) (r : ZMod N) : Point N (k + 1) :=
  fun i => if h : i.val < k then x ⟨i.val, h⟩ else r

/-- The higher-dimensional function `f_h(y)` preceding Lemma 14.3. -/
def higherCubeCorrelation {N k : Nat} [NeZero N]
    (f : Point N (k + 1) → Complex) (h : Point N k) (y : ZMod N) : Complex :=
  ∑ x : Point N k, ∏ e : Fin k → Bool,
    let z := f (appendCoordinate (fun i => x i + if e i then h i else 0) y)
    if Even (boolWeight e + k) then z else star z

/-- **Proposition 14.1.** Weighted simultaneous additivity for the Fourier
coefficients of the functions `f_h`. -/
def proposition_14_1 : Prop :=
  ∀ (N p : Nat) [NeZero N] (lambda : ZMod N → Real)
      (f : Fin p → Pair N → Complex) (sigma : Fin p → ZMod N → ZMod N)
      (alpha : Real),
    0 ≤ alpha → (∀ h, 0 ≤ lambda h) → (∀ i, DiscValued (f i)) →
    alpha * (N : Real) ^ (4 * p + 1) ≤
      ∑ h : ZMod N, lambda h *
        ∏ i : Fin p,
          ‖fourier (firstCoordinateCorrelation (f i) h) (sigma i h)‖ ^ 2 →
    alpha ^ 4 * (N : Real) ^ 3 ≤
      weightedSimultaneousAdditiveEnergy Finset.univ lambda sigma

/-- **Lemma 14.2.** Large Fourier coefficients of iterated differences imply
the product property.  Proposition 12.1 is a proof ingredient only and is not
an extra hypothesis of this statement. -/
def lemma_14_2 : Prop :=
  ∀ (N k : Nat) [NeZero N] (gamma : Real) (f : ZMod N → Complex)
      (B : Finset (Point N k)) (phi : Point N k → ZMod N),
    0 < gamma → DiscValued f →
    (∀ r, r ∈ B →
      gamma * N ≤ ‖fourier (cubeDifference f r) (phi r)‖) →
    HasProductProperty B phi gamma

/-- **Lemma 14.3.** The analogous product-property criterion for the
higher-dimensional correlations `f_z`. -/
def lemma_14_3 : Prop :=
  ∀ (N k : Nat) [NeZero N] (gamma : Real)
      (f : Point N (k + 1) → Complex) (B : Finset (Point N k))
      (phi : Point N k → ZMod N),
    0 < gamma → DiscValued f →
    (∀ z, z ∈ B →
      gamma * (N : Real) ^ (k + 1) ≤
        ‖fourier (higherCubeCorrelation f z) (phi z)‖) →
    HasProductProperty B phi gamma

/-! ## Cubes, configurations, and arrangements -/

/-- An axis-parallel `k`-cube in `ZMod N ^ k`, encoded by its base point and
its coordinate sidelengths. -/
abbrev AxisCube (N k : Nat) := Point N k × Point N k

def AxisCube.base {N k : Nat} (C : AxisCube N k) : Point N k := C.1
def AxisCube.side {N k : Nat} (C : AxisCube N k) : Point N k := C.2

/-- A vertex of an axis-parallel cube. -/
def AxisCube.vertex {N k : Nat} (C : AxisCube N k) (e : Fin k → Bool) : Point N k :=
  fun i => C.base i + if e i then C.side i else 0

/-- Every vertex of the cube belongs to `B`. -/
def AxisCube.IsIn {N k : Nat} (C : AxisCube N k) (B : Finset (Point N k)) : Prop :=
  ∀ e, C.vertex e ∈ B

/-- Two cubes are congruent when their coordinate sidelengths agree. -/
def AxisCube.IsCongruent {N k : Nat} (C D : AxisCube N k) : Prop :=
  C.side = D.side

/-- The alternating cube value `phi(C)`. -/
def AxisCube.value {N k : Nat} [NeZero N] (C : AxisCube N k)
    (phi : Point N k → ZMod N) : ZMod N :=
  ∑ e : Fin k → Bool, (-1 : ZMod N) ^ boolWeight e * phi (C.vertex e)

/-- A configuration is the coordinatewise product of `k` additive
quadruples, parameterized by a base and two sidelength vectors. -/
abbrev CubeConfiguration (N k : Nat) :=
  Point N k × Point N k × Point N k

def CubeConfiguration.base {N k : Nat} (C : CubeConfiguration N k) : Point N k := C.1
def CubeConfiguration.firstSide {N k : Nat}
    (C : CubeConfiguration N k) : Point N k := C.2.1
def CubeConfiguration.secondSide {N k : Nat}
    (C : CubeConfiguration N k) : Point N k := C.2.2

/-- A vertex of a configuration. -/
def CubeConfiguration.vertex {N k : Nat} (C : CubeConfiguration N k)
    (e u : Fin k → Bool) : Point N k :=
  fun i => C.base i + (if e i then C.firstSide i else 0) +
    (if u i then C.secondSide i else 0)

/-- Every one of the `4^k` vertices belongs to `B`. -/
def CubeConfiguration.IsIn {N k : Nat} (C : CubeConfiguration N k)
    (B : Finset (Point N k)) : Prop :=
  ∀ e u, C.vertex e u ∈ B

/-- `phi` respects every coordinate two-face of a configuration. -/
def CubeConfiguration.IsRespected {N k : Nat} (C : CubeConfiguration N k)
    (phi : Point N k → ZMod N) : Prop :=
  ∀ (j : Fin k) (e u : Fin k → Bool),
    phi (C.vertex (Function.update e j false) (Function.update u j false)) +
        phi (C.vertex (Function.update e j true) (Function.update u j true)) =
      phi (C.vertex (Function.update e j true) (Function.update u j false)) +
        phi (C.vertex (Function.update e j false) (Function.update u j true))

/-- Number of configurations in `B` respected by `phi`. -/
def respectedConfigurationCount {N k : Nat} [NeZero N]
    (B : Finset (Point N k)) (phi : Point N k → ZMod N) : Nat :=
  countWhere fun C : CubeConfiguration N k => C.IsIn B ∧ C.IsRespected phi

/-- Number of congruent cube pairs in `B` with equal alternating value. -/
def respectedCubePairCount {N k : Nat} [NeZero N]
    (B : Finset (Point N k)) (phi : Point N k → ZMod N) : Nat :=
  countWhere fun P : AxisCube N k × AxisCube N k =>
    P.1.IsIn B ∧ P.2.IsIn B ∧ P.1.IsCongruent P.2 ∧
      P.1.value phi = P.2.value phi

/-- A potential `d`-arrangement: `2d` axis-parallel cubes with one common
sidelength vector, their individual bases, and their last-coordinate
cross-sections.  The additive relation and containment are imposed by `IsIn`. -/
abbrev GeneralArrangement (N k d : Nat) :=
  Point N k × (Fin (2 * d) → Point N k) × (Fin (2 * d) → ZMod N)

def GeneralArrangement.side {N k d : Nat}
    (R : GeneralArrangement N k d) : Point N k := R.1
def GeneralArrangement.base {N k d : Nat}
    (R : GeneralArrangement N k d) : Fin (2 * d) → Point N k := R.2.1
def GeneralArrangement.crossSection {N k d : Nat}
    (R : GeneralArrangement N k d) : Fin (2 * d) → ZMod N := R.2.2

/-- The `j`th constituent cube of an arrangement. -/
def GeneralArrangement.cube {N k d : Nat} (R : GeneralArrangement N k d)
    (j : Fin (2 * d)) : AxisCube N k :=
  (R.base j, R.side)

/-- A vertex of an arrangement, including its final cross-section coordinate. -/
def GeneralArrangement.vertex {N k d : Nat} (R : GeneralArrangement N k d)
    (e : Fin k → Bool) (j : Fin (2 * d)) : Point N (k + 1) :=
  appendCoordinate ((R.cube j).vertex e) (R.crossSection j)

/-- A genuine `d`-arrangement has additive cross-sections and lies in `B`. -/
def GeneralArrangement.IsIn {N k d : Nat} (R : GeneralArrangement N k d)
    (B : Finset (Point N (k + 1))) : Prop :=
  IsAdditiveTuple R.crossSection ∧ ∀ e j, R.vertex e j ∈ B

/-- The alternating value of the `j`th constituent cube. -/
def GeneralArrangement.cubeValue {N k d : Nat} [NeZero N]
    (R : GeneralArrangement N k d) (phi : Point N (k + 1) → ZMod N)
    (j : Fin (2 * d)) : ZMod N :=
  ∑ e : Fin k → Bool, (-1 : ZMod N) ^ boolWeight e * phi (R.vertex e j)

/-- The image relation saying that `phi` respects a `d`-arrangement. -/
def GeneralArrangement.IsRespected {N k d : Nat} [NeZero N]
    (R : GeneralArrangement N k d) (phi : Point N (k + 1) → ZMod N) : Prop :=
  IsAdditiveTuple fun j => R.cubeValue phi j

/-- Number of `d`-arrangements contained in `B`. -/
def generalArrangementCount {N k : Nat} [NeZero N] (d : Nat)
    (B : Finset (Point N (k + 1))) : Nat :=
  countWhere fun R : GeneralArrangement N k d => R.IsIn B

/-- Number of contained `d`-arrangements respected by `phi`. -/
def respectedGeneralArrangementCount {N k : Nat} [NeZero N] (d : Nat)
    (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) : Nat :=
  countWhere fun R : GeneralArrangement N k d => R.IsIn B ∧ R.IsRespected phi

/-! ## Section 14: obtaining many respected arrangements -/

/-- **Lemma 14.4.** Product property gives many respected configurations. -/
def lemma_14_4 : Prop :=
  ∀ (N k : Nat) [NeZero N] (beta gamma : Real)
      (B : Finset (Point N k)) (phi : Point N k → ZMod N),
    1 ≤ k → 0 < beta → 0 < gamma → gamma ≤ 1 →
    (B.card : Real) = beta * (N : Real) ^ k →
    HasProductProperty B phi gamma →
    beta ^ (4 ^ k) * gamma ^ (2 * k * 4 ^ k) * (N : Real) ^ (3 * k) ≤
      respectedConfigurationCount B phi

/-- **Corollary 14.5.** Product property gives the same lower bound for
respected congruent cube pairs. -/
def corollary_14_5 : Prop :=
  ∀ (N k : Nat) [NeZero N] (beta gamma : Real)
      (B : Finset (Point N k)) (phi : Point N k → ZMod N),
    1 ≤ k → 0 < beta → 0 < gamma → gamma ≤ 1 →
    (B.card : Real) = beta * (N : Real) ^ k →
    HasProductProperty B phi gamma →
    beta ^ (4 ^ k) * gamma ^ (2 * k * 4 ^ k) * (N : Real) ^ (3 * k) ≤
      respectedCubePairCount B phi

/-- **Corollary 14.6.** The printed exponent `k * 4^(k+1)` on `gamma` is
not supported by its proof.  The proof gives
`2*k*4^(k+1) + 8*2^k`; for `k ≥ 1` and `gamma ≤ 1`, the exponent
`3*k*4^(k+1)` used here is a clean safe weakening. -/
def corollary_14_6 : Prop :=
  ∀ (N k : Nat) [NeZero N] (beta gamma : Real)
      (B : Finset (Point N (k + 1)))
      (phi : Point N (k + 1) → ZMod N),
    1 ≤ k → 0 < beta → 0 < gamma → gamma ≤ 1 →
    (B.card : Real) = beta * (N : Real) ^ (k + 1) →
    HasProductProperty B phi gamma →
    beta ^ (4 ^ (k + 1)) * gamma ^ (3 * k * 4 ^ (k + 1)) *
        (N : Real) ^ (5 * k + 3) ≤
      respectedGeneralArrangementCount 2 B phi

/-- **Lemma 14.7.** Many respected parallelepiped pairs yield many respected
eight-arrangements. -/
def lemma_14_7 : Prop :=
  ∀ (N k : Nat) [NeZero N] (theta : Real)
      (B : Finset (Point N (k + 1)))
      (phi : Point N (k + 1) → ZMod N),
    0 < theta →
    theta * (N : Real) ^ (5 * k + 3) ≤
        respectedGeneralArrangementCount 2 B phi →
    theta ^ 7 * (N : Real) ^ (17 * k + 15) ≤
      respectedGeneralArrangementCount 8 B phi

/-- **Lemma 14.8.** This uses the corrected safe exponent from Corollary
14.6.  Raising its lower bound to the seventh power changes the exponent on
`gamma` to `21*k*4^(k+1)`. -/
def lemma_14_8 : Prop :=
  ∀ (N k : Nat) [NeZero N] (beta gamma : Real)
      (B : Finset (Point N (k + 1)))
      (phi : Point N (k + 1) → ZMod N),
    1 ≤ k → 0 < beta → 0 < gamma → gamma ≤ 1 →
    (B.card : Real) = beta * (N : Real) ^ (k + 1) →
    HasProductProperty B phi gamma →
    beta ^ (7 * 4 ^ (k + 1)) * gamma ^ (21 * k * 4 ^ (k + 1)) *
        (N : Real) ^ (17 * k + 15) ≤
      respectedGeneralArrangementCount 8 B phi

/-! ## Walsh coefficients and degenerate arrangements -/

/-- The sign represented by a Boolean vertex, as an element of `ZMod N`. -/
def walshSign {N : Nat} (b : Bool) : ZMod N :=
  if b then 1 else -1

/-- The Walsh character belonging to a set of coordinates. -/
def walshCharacter {N k : Nat} (A : Finset (Fin k))
    (e : Fin k → Bool) : ZMod N :=
  ∏ i ∈ A, walshSign (N := N) (e i)

/-- The parity character on the Boolean cube. -/
def parityCharacter {N k : Nat} (e : Fin k → Bool) : ZMod N :=
  (-1 : ZMod N) ^ boolWeight e

/-- An integer-valued coefficient function only takes the values `-1,0,1`. -/
def IsTernaryCoefficient {X : Type*} (eta : X → Int) : Prop :=
  ∀ x, eta x = -1 ∨ eta x = 0 ∨ eta x = 1

/-- A coefficient function is a scalar multiple modulo `N` of a given
`ZMod N`-valued character. -/
def IsModularMultiple {N : Nat} {X : Type*} (eta : X → Int)
    (chi : X → ZMod N) : Prop :=
  ∃ c : ZMod N, ∀ x, (eta x : ZMod N) = c * chi x

/-- The polynomial moment in Lemma 15.1, on the sign cube `{-1,1}^k`. -/
def signedWalshMoment {N k : Nat} [NeZero N] (eta : (Fin k → Bool) → Int)
    (h y : Point N k) (A : Finset (Fin k)) : ZMod N :=
  ∑ e : Fin k → Bool, (eta e : ZMod N) *
    ∏ i ∈ A, (y i + walshSign (N := N) (e i) * h i)

/-- The polynomial moment in Corollary 15.2, on the Boolean cube. -/
def booleanWalshMoment {N k : Nat} [NeZero N] (eta : (Fin k → Bool) → Int)
    (h y : Point N k) (A : Finset (Fin k)) : ZMod N :=
  ∑ e : Fin k → Bool, (eta e : ZMod N) *
    ∏ i ∈ A, (y i + if e i then h i else 0)

/-- The distinguished coefficient `eta_0` for a `d`-arrangement. -/
def arrangementParityCoefficient {N k d : Nat} (e : Fin k → Bool)
    (j : Fin (2 * d)) : ZMod N :=
  if (j : Nat) < d then parityCharacter (N := N) e else -parityCharacter (N := N) e

/-- A coordinate monomial moment of an arrangement and a ternary coefficient. -/
def arrangementMoment {N k d : Nat} [NeZero N] (R : GeneralArrangement N k d)
    (eta : (Fin k → Bool) → Fin (2 * d) → Int)
    (A : Finset (Fin (k + 1))) : ZMod N :=
  ∑ e : Fin k → Bool, ∑ j : Fin (2 * d),
    (eta e j : ZMod N) * ∏ i ∈ A, R.vertex e j i

/-- A `d`-arrangement is degenerate when it has a ternary dependence other
than a modular scalar multiple of the defining parity dependence. -/
def GeneralArrangement.IsDegenerate {N k d : Nat} [NeZero N]
    (R : GeneralArrangement N k d) : Prop :=
  ∃ eta : (Fin k → Bool) → Fin (2 * d) → Int,
    IsTernaryCoefficient (fun z : (Fin k → Bool) × Fin (2 * d) => eta z.1 z.2) ∧
    ¬ IsModularMultiple
        (fun z : (Fin k → Bool) × Fin (2 * d) => eta z.1 z.2)
        (fun z => arrangementParityCoefficient (N := N) z.1 z.2) ∧
    ∀ A : Finset (Fin (k + 1)), arrangementMoment R eta A = 0

/-- Number of degenerate `d`-arrangements in the full ambient group. -/
def degenerateGeneralArrangementCount {N k : Nat} [NeZero N] (d : Nat) : Nat :=
  countWhere fun R : GeneralArrangement N k d =>
    IsAdditiveTuple R.crossSection ∧ R.IsDegenerate

/-! ## Section 15: increasing the respected density -/

/-- **Lemma 15.1 (Walsh basis).** The odd-prime hypothesis makes explicit
the field and `2`-invertibility assumptions used in the printed proof. -/
def lemma_15_1 : Prop :=
  ∀ (N k : Nat) [NeZero N], Nat.Prime N → Odd N →
    ∀ (h : Point N k) (eta : (Fin k → Bool) → Int),
      (∀ i, h i ≠ 0) → IsTernaryCoefficient eta →
      (∀ A : Finset (Fin k), ∀ y z : Point N k,
        signedWalshMoment eta h y A = signedWalshMoment eta h z A) →
      IsModularMultiple eta (fun e => ∏ i, walshSign (N := N) (e i))

/-- **Corollary 15.2.** The Boolean-cube version also requires an odd prime:
the reduction from Lemma 15.1 replaces every sidelength by `2*h_i`. -/
def corollary_15_2 : Prop :=
  ∀ (N k : Nat) [NeZero N], Nat.Prime N → Odd N →
    ∀ (h : Point N k) (eta : (Fin k → Bool) → Int),
      (∀ i, h i ≠ 0) → IsTernaryCoefficient eta →
      (∀ A : Finset (Fin k), ∀ y z : Point N k,
        booleanWalshMoment eta h y A = booleanWalshMoment eta h z A) →
      IsModularMultiple eta (parityCharacter (N := N))

/-- **Lemma 15.3.** Fibre bound for a nonconstant multilinear polynomial.
Primality is explicit because the claim fails over general composite moduli. -/
def lemma_15_3 : Prop :=
  ∀ (N k : Nat) [NeZero N], Nat.Prime N →
    ∀ (mu : Point N k → ZMod N) (a : ZMod N),
      IsMultilinear mu → (¬ ∃ c, ∀ y, mu y = c) →
      (countWhere fun y : Point N k => mu y = a : Real) ≤
          (N : Real) ^ k - (N - 1 : Nat) ^ k ∧
        (N : Real) ^ k - (N - 1 : Nat) ^ k ≤ k * (N : Real) ^ (k - 1)

/-- **Lemma 15.4.** There are few degenerate arrangements.  The odd-prime
assumption records the standing field hypothesis used by Lemmas 15.1--15.3. -/
def lemma_15_4 : Prop :=
  ∀ (N k d : Nat) [NeZero N], Nat.Prime N → Odd N → 1 ≤ k → 1 ≤ d →
    (degenerateGeneralArrangementCount (N := N) (k := k) d : Real) ≤
      (3 : Real) ^ (2 * d * 2 ^ k) * k *
        (N : Real) ^ ((2 * d + 1) * k + 2 * d - 2)

/-- The exponent used by the random Riesz-product selection in Lemma 15.5. -/
def arrangementSelectionExponent (k : Nat) : Nat :=
  2 ^ (2 ^ (k + 4) + k + 3)

/-- **Lemma 15.5.** The proof explicitly requires `N` to be sufficiently
large; the threshold `N0` records that omitted quantifier. -/
def lemma_15_5 : Prop :=
  ∀ (k : Nat) (alpha beta eta : Real),
    1 ≤ k → 0 < alpha → 0 < beta → 0 < eta → eta ≤ 1 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N], N0 ≤ N → Nat.Prime N → Odd N →
      ∀ (B : Finset (Point N (k + 1)))
          (phi : Point N (k + 1) → ZMod N),
        (B.card : Real) = beta * (N : Real) ^ (k + 1) →
        alpha * beta ^ 15 * (N : Real) ^ (17 * k + 15) ≤
            respectedGeneralArrangementCount 8 B phi →
        ∃ B' : Finset (Point N (k + 1)), B' ⊆ B ∧
          (alpha * eta / 4) ^ arrangementSelectionExponent k * beta ^ 15 *
              (N : Real) ^ (17 * k + 15) ≤
            generalArrangementCount 8 B' ∧
          (1 - eta) * generalArrangementCount 8 B' ≤
            respectedGeneralArrangementCount 8 B' phi

/-- **Lemma 15.6.** The sufficiently-large threshold is explicit.  In the
raw application of Lemma 15.5, the corrected exponent from Lemma 14.8 is
`21*k*4^(k+1)`, rather than the printed `7*k*4^(k+1)`.  With
`0 < beta,gamma ≤ 1`, the enormous final exponent still leaves enough slack
for the published coarse bound displayed here. -/
def lemma_15_6 : Prop :=
  ∀ (k : Nat) (beta gamma : Real),
    1 ≤ k → 0 < beta → beta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N], N0 ≤ N → Nat.Prime N → Odd N →
      ∀ (B : Finset (Point N (k + 1)))
          (phi : Point N (k + 1) → ZMod N),
        (B.card : Real) = beta * (N : Real) ^ (k + 1) →
        HasProductProperty B phi gamma →
        ∃ B' : Finset (Point N (k + 1)), B' ⊆ B ∧
          (beta * gamma / 2) ^ (2 ^ (2 ^ (k + 5))) *
              (N : Real) ^ (17 * k + 15) ≤
            generalArrangementCount 8 B' ∧
          (1 - (2 : Real)⁻¹ ^ 44) * generalArrangementCount 8 B' ≤
            respectedGeneralArrangementCount 8 B' phi

end LeanProofs.GowersSzemeredi
