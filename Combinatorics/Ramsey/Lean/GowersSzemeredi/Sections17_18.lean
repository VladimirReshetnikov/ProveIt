import GowersSzemeredi.Section05
import GowersSzemeredi.Sections01_03

/-!
# Gowers (2001), Sections 17--18: formal statements

This file records the phase-removal step and the final density-increment
argument.  Numbered results remain `Prop`-valued definitions, so no unproved
claim is added to Lean's trusted environment.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ## Section 17: The main inductive step -/

/-- Twist a function by the inverse of a polynomial phase. -/
def phaseTwist {N : Nat} [NeZero N] (f : ZMod N → Complex)
    (phi : ZMod N → ZMod N) : ZMod N → Complex :=
  fun s => f s * exponential (-(phi s))

/-- The signed sum of one-variable functions over a Boolean cube. -/
def signedCubeSum {N k : Nat} (phi : (Fin k → Bool) → ZMod N → ZMod N)
    (s : ZMod N) (x : Point N k) : ZMod N :=
  ∑ e : Fin k → Bool,
    if Even (boolWeight e) then phi e (cubeArgument s x e)
    else -phi e (cubeArgument s x e)

/-- **Lemma 17.1.** The OCR's left-hand side `phi` is corrected to the
introduced function `sigma`.  The factorial-invertibility hypothesis used by
the finite-difference argument is explicit. -/
def lemma_17_1 : Prop :=
  ∀ (N k : Nat) [NeZero N] [Fact N.Prime], k < N →
    IsUnit ((Nat.factorial k : Nat) : ZMod N) →
    ∀ sigma : Point N k → ZMod N, IsMultilinear sigma →
      ∃ phi : (Fin k → Bool) → ZMod N → ZMod N,
        (∀ e, PolynomialOn k Finset.univ (phi e)) ∧
        ∀ s x, sigma x = signedCubeSum phi s x

/-- **Proposition 17.2.** The phase polynomial has degree at most `k+1`, as
the proof obtains by applying Lemma 17.1 to `x_(k+1) * sigma(x)`. -/
def proposition_17_2 : Prop :=
  ∀ (N k : Nat) [NeZero N] [Fact N.Prime] (f : ZMod N → Complex)
      (sigma : Point N k → ZMod N) (alpha : Real),
    k + 1 < N → IsUnit ((Nat.factorial (k + 1) : Nat) : ZMod N) →
    DiscValued f → IsMultilinear sigma →
    alpha * (N : Real) ^ (k + 2) ≤
      ∑ x : Point N k, ‖fourier (cubeDifference f x) (sigma x)‖ ^ 2 →
    ∃ phi : ZMod N → ZMod N,
      PolynomialOn (k + 1) Finset.univ phi ∧
      alpha * (N : Real) ^ (k + 2) ≤
        ∑ x : Point N k,
          ‖∑ s : ZMod N, cubeDifference (phaseTwist f phi) x s‖ ^ 2

/-- An affine hyperplane in `R^k`, given by a normal and offset. -/
structure AffineHyperplane (k : Nat) where
  normal : Fin k → Real
  offset : Real

def realDot {k : Nat} (x y : Fin k → Real) : Real :=
  ∑ i, x i * y i

/-- A Boolean sign pattern realized in the complement of a hyperplane
arrangement. -/
def RealizesRegion {k m : Nat} (H : Fin m → AffineHyperplane k)
    (p : Fin m → Bool) : Prop :=
  ∃ x : Fin k → Real, ∀ i,
    (p i = true ↔ realDot (H i).normal x < (H i).offset) ∧
    (p i = false ↔ (H i).offset < realDot (H i).normal x)

/-- Number of regions cut out by a finite hyperplane arrangement. -/
def hyperplaneRegionCount {k m : Nat} (H : Fin m → AffineHyperplane k) : Nat :=
  countWhere (RealizesRegion H)

/-- Standard general-position hypotheses for affine hyperplanes. -/
def HyperplanesInGeneralPosition {k m : Nat}
    (H : Fin m → AffineHyperplane k) : Prop :=
  (∀ I : Finset (Fin m), I.card ≤ k →
    LinearIndependent Real (fun i : I => (H i).normal)) ∧
  ∀ I : Finset (Fin m), k < I.card →
    ¬ ∃ x : Fin k → Real, ∀ i, i ∈ I →
      realDot (H i).normal x = (H i).offset

/-- **Lemma 17.4.** (There is no result numbered 17.3 in the article.) -/
def lemma_17_4 : Prop :=
  ∀ (k m : Nat) (H : Fin m → AffineHyperplane k),
    hyperplaneRegionCount H ≤ ∑ j ∈ Finset.range (k + 1), Nat.choose m j ∧
    (HyperplanesInGeneralPosition H →
      hyperplaneRegionCount H = ∑ j ∈ Finset.range (k + 1), Nat.choose m j)

/-- The integer-valued floor-dot-product pattern in Corollary 17.5. -/
def floorDotPattern {k : Nat} (alpha : Fin k → Real) :
    (Fin k → Bool) → Int :=
  fun e => ⌊∑ i, if e i then alpha i else 0⌋

/-- **Corollary 17.5.** -/
def corollary_17_5 : Prop :=
  ∀ (k r : Nat), ∃ F : Finset ((Fin k → Bool) → Int),
    F.card ≤ 2 ^ (2 * r * k ^ 3) ∧
    ∀ alpha : Fin k → Real,
      (∀ i, -(r : Real) < alpha i ∧ alpha i < r) →
      floorDotPattern alpha ∈ F

/-- The affine floor pattern reduced modulo `M`. -/
def floorAffinePattern {k M : Nat} (alpha0 : Real) (alpha : Fin k → Real) :
    (Fin k → Bool) → ZMod M :=
  fun e => (⌊alpha0 + ∑ i, if e i then alpha i else 0⌋ : Int)

/-- **Corollary 17.6.** The factor `M` accounts for the unrestricted integer
part of the affine offset. -/
def corollary_17_6 : Prop :=
  ∀ (k M r : Nat), 0 < M →
    ∃ F : Finset ((Fin k → Bool) → ZMod M),
      F.card ≤ M * 2 ^ (2 * r * (k + 1) ^ 3) ∧
      ∀ (alpha0 : Real) (alpha : Fin k → Real),
        (∀ i, -(r : Real) < alpha i ∧ alpha i < r) →
        floorAffinePattern alpha0 alpha ∈ F

/-- Restrict a function to a finite cell, extending it by zero. -/
def restrictToCell {N : Nat} (Q : Finset (ZMod N)) (f : ZMod N → Complex) :
    ZMod N → Complex :=
  fun x => if x ∈ Q then f x else 0

/-- Uniformity of degree `k` relative to a progression partition, as defined
before Proposition 17.7. -/
def UniformOnPartition {N M : Nat} [NeZero N] (f : ZMod N → Complex)
    (k : Nat) (alpha : Real) (Q : Fin M → ModAP N) (m : Nat) : Prop :=
  ∑ i, (∑ x : Point N (k + 1), ∑ s : ZMod N,
      cubeDifference (restrictToCell (Q i).carrier f) x s).re ≤
    alpha * (m : Real) ^ (k + 2) * M

/-- **Proposition 17.7.** The endpoint inequalities and the use of the `M`
shifted cells are corrected from the OCR. -/
def proposition_17_7 : Prop :=
  ∀ (N k m : Nat) [NeZero N] [Fact N.Prime] (f : ZMod N → Complex)
      (P : Box N k) (sigma : Point N k → ZMod N) (alpha : Real),
    0 < k → Odd m → P.width = m →
    (∀ i, (P.axis i).length = m) → P.commonDiff != 0 →
    (m : Real) ≤ Real.sqrt N → DiscValued f → IsMultilinear sigma →
    alpha * (N : Real) ^ 2 * (m : Real) ^ k ≤
      ∑ x ∈ P.carrier, ‖fourier (cubeDifference f x) (sigma x)‖ ^ 2 →
    ∃ phi : ZMod N → ZMod N, ∃ M l : Nat,
      ∃ Q : Fin M → ModAP N,
        PolynomialOn (k + 1) Finset.univ phi ∧
        IsPartition (fun i => (Q i).carrier) Finset.univ ∧
        (∀ i, (Q i).IsProper ∧ ((Q i).length = l ∨ (Q i).length = l + 1)) ∧
        (m : Real) / (3 * k) ≤ l ∧
        ¬ UniformOnPartition (phaseTwist f phi) k
          ((2 : Real) ^ (-(2 * (k + 1) ^ 3 : Int)) * alpha) Q (l + 1)

/-! ## Section 18: Putting everything together -/

def section18Exponent (alpha : Real) (k : Nat) : Real :=
  alpha ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 10)))

/-- **Theorem 18.1.** The balanced function is made explicit, and the average
cell-size exponent is corrected to the three-level tower printed in the
article. A threshold records the large-modulus assumptions inherited from the
structural lemmas.

Editorial warning: the proof invokes the unsupported tower estimate in the
published Corollary 16.11. The catalogue preserves the intended headline
statement, but this Prop-valued entry does not claim that the displayed proof
establishes it. -/
def theorem_18_1 : Prop :=
  ∀ (k : Nat) (alpha : Real), 0 < alpha → alpha ≤ 1 / 2 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ A : Finset (ZMod N), ¬ UniformSetOfDegree A alpha k →
        ∃ M : Nat, ∃ P : Fin M → ModAP N,
          IsPartition (fun i => (P i).carrier) Finset.univ ∧
          (∀ i, (P i).IsProper) ∧
          (N : Real) ^ section18Exponent alpha k ≤
            averageCellSize (fun i => (P i).carrier) ∧
          section18Exponent alpha k * N ≤
            ∑ i, ‖∑ s ∈ (P i).carrier, balanced A s‖

/-- The right-associated power chain in Theorem 18.2. -/
def szemerediThreshold (delta : Real) (k : Nat) : Real :=
  (2 : Real) ^
    ((2 : Real) ^
      (delta⁻¹ ^ ((2 : Real) ^ ((2 : Real) ^ (k + 9 : Nat)))))

/-- **Theorem 18.2 (quantitative Szemeredi).** -/
def theorem_18_2 : Prop :=
  ∀ (delta : Real) (k N : Nat), 0 < delta → delta ≤ 1 / 2 → 0 < k →
    szemerediThreshold delta k ≤ N →
    ∀ A : Finset Nat, A ⊆ Finset.Icc 1 N → delta * N ≤ A.card →
      HasNatAP A k

/-- The five-level right-associated tower in the two-color corollary. -/
def twoColorThreshold (k : Nat) : Real :=
  (2 : Real) ^ ((2 : Real) ^ ((2 : Real) ^
    ((2 : Real) ^ ((2 : Real) ^ (k + 9 : Nat)))))

/-- **Corollary 18.7.** The source's unusual label is preserved even though
there are no numbered results 18.3--18.6. -/
def corollary_18_7 : Prop :=
  ∀ (k N : Nat), 0 < k → twoColorThreshold k ≤ N →
    ∀ color : Nat → Fin 2, HasMonochromaticAP N 2 color k

end LeanProofs.GowersSzemeredi
