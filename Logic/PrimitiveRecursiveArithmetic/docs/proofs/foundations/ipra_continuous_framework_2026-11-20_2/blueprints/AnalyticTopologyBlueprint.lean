import Mathlib

/-!
# Continuous completion and quantitative gluing: blueprint

STATUS: definitions and exact theorem targets; this file was not compiled in
the authoring environment. There are no asserted theorem proofs. A declaration
whose name ends in `Goal` defines a proposition to be proved, not a proved fact.

These are semantic Lean interfaces. The final ProveIt deliverable must also
construct the corresponding deeply embedded `Prf PRAAx` derivations. For that
layer replace Nat/Rat functions by fixed `PR` symbols, rational vector fields
by encoded lists, and each rational inequality by its cleared integer formula.
Do not quantify in the object theory over the function fields defined here.

Main proof dependencies, in order:
  rational small-error elimination; regular-name equivalence and density;
  finite extension reindexing; one-summand weighted inequality; finite summation;
  denominator cancellation; residual evaluation and uniqueness; cubic separation;
  bounded maximum-search residual; cubic diameter and output coherence.
-/

namespace ContinuousIPRABlueprint

def eps (n : ℕ) : ℚ := 1 / (2 : ℚ)^n

structure RationalPresentation where
  valid : ℕ → Bool
  dist : ℕ → ℕ → ℚ

def MetricLaws (D : RationalPresentation) : Prop :=
  (∀ x, D.valid x = true → D.dist x x = 0) ∧
  (∀ x y, D.valid x = true → D.valid y = true → 0 ≤ D.dist x y) ∧
  (∀ x y, D.valid x = true → D.valid y = true → D.dist x y = D.dist y x) ∧
  (∀ x y z, D.valid x = true → D.valid y = true → D.valid z = true →
    D.dist x z ≤ D.dist x y + D.dist y z)

def Regular (D : RationalPresentation) (a : ℕ → ℕ) : Prop :=
  (∀ n, D.valid (a n) = true) ∧
  (∀ m n, D.dist (a m) (a n) ≤ eps m + eps n)

def CompletedLE (D : RationalPresentation) (a b : ℕ → ℕ) (q : ℚ) : Prop :=
  ∀ m n, D.dist (a m) (b n) ≤ q + eps m + eps n

def NameEq (D : RationalPresentation) (a b : ℕ → ℕ) : Prop :=
  CompletedLE D a b 0

def monotoneMajorant (μ : ℕ → ℕ) (k : ℕ) : ℕ :=
  (Finset.range (k+1)).sup μ

def UniformContract (D E : RationalPresentation) (f μ : ℕ → ℕ) : Prop :=
  Monotone μ ∧
  (∀ x, D.valid x = true → E.valid (f x) = true) ∧
  (∀ k x y, D.valid x = true → D.valid y = true →
    D.dist x y ≤ eps (μ k) → E.dist (f x) (f y) ≤ eps k)

def extensionSamples (f μ a : ℕ → ℕ) (n : ℕ) : ℕ :=
  f (a (μ (n+2)+2))

def ExtensionRegularGoal (D E : RationalPresentation) (f μ a : ℕ → ℕ) : Prop :=
  MetricLaws D → MetricLaws E → UniformContract D E f μ → Regular D a →
  Regular E (extensionSamples f μ a)

def ExtensionExtensionalGoal (D E : RationalPresentation)
    (f μ a b : ℕ → ℕ) : Prop :=
  MetricLaws D → MetricLaws E → UniformContract D E f μ →
  Regular D a → Regular D b → NameEq D a b →
  NameEq E (extensionSamples f μ a) (extensionSamples f μ b)

def ExtensionContinuousGoal (D E : RationalPresentation)
    (f μ a b : ℕ → ℕ) : Prop :=
  MetricLaws D → MetricLaws E → UniformContract D E f μ →
  Regular D a → Regular D b →
  ∀ k, CompletedLE D a b (eps (μ (k+2)+2)) →
    CompletedLE E (extensionSamples f μ a) (extensionSamples f μ b) (eps k)

def diagonalSamples (a : ℕ → ℕ → ℕ) (n : ℕ) : ℕ := a (n+2) (n+2)

def DiagonalGoal (D : RationalPresentation) (a : ℕ → ℕ → ℕ) : Prop :=
  MetricLaws D →
  (∀ i, Regular D (a i)) →
  (∀ i j p q, D.dist (a i p) (a j q) ≤ eps i + eps j + eps p + eps q) →
  Regular D (diagonalSamples a) ∧
    ∀ j, CompletedLE D (diagonalSamples a) (a j) (eps j)

abbrev RatVec (d : ℕ) := Fin d → ℚ

def l1 {d : ℕ} (v : RatVec d) : ℚ := ∑ j, |v j|

structure ChartData (N d : ℕ) where
  domain : ℕ → Bool
  center : Fin N → ℕ
  radius : Fin N → ℚ
  sample : Fin N → ℕ → ℕ → RatVec d

def weight {N d : ℕ} (D : RationalPresentation) (G : ChartData N d)
    (i : Fin N) (x : ℕ) : ℚ :=
  max 0 (G.radius i - D.dist x (G.center i))

def weightSum {N d : ℕ} (D : RationalPresentation) (G : ChartData N d)
    (x : ℕ) : ℚ := ∑ i, weight D G i x

def numerator {N d : ℕ} (D : RationalPresentation) (G : ChartData N d)
    (p x : ℕ) : RatVec d := fun j =>
  ∑ i, if 0 < weight D G i x then weight D G i x * G.sample i p x j else 0

def gluedSamples {N d : ℕ} (D : RationalPresentation) (G : ChartData N d)
    (p x : ℕ) : RatVec d :=
  fun j => numerator D G p x j / weightSum D G x

def LocalContracts {N d : ℕ} (D : RationalPresentation) (G : ChartData N d)
    (δ M L : ℚ) : Prop :=
  0 < δ ∧ 0 ≤ M ∧ 0 ≤ L ∧
  (∀ x, G.domain x = true → D.valid x = true) ∧
  (∀ i, D.valid (G.center i) = true) ∧
  (∀ x, G.domain x = true → δ ≤ weightSum D G x) ∧
  (∀ i p x, G.domain x = true → 0 < weight D G i x →
    l1 (G.sample i p x) ≤ M) ∧
  (∀ i p q x y, G.domain x = true → G.domain y = true →
    0 < weight D G i x → 0 < weight D G i y →
    l1 (G.sample i p x - G.sample i q y) ≤ L * D.dist x y + eps p + eps q)

def WeightedGluingGoal {N d : ℕ} (D : RationalPresentation) (G : ChartData N d)
    (δ M L : ℚ) : Prop :=
  MetricLaws D → LocalContracts D G δ M L →
  ∀ p q x y, G.domain x = true → G.domain y = true →
    l1 (gluedSamples D G p x - gluedSamples D G q y) ≤
      (L + 2*(N : ℚ)*M/δ)*D.dist x y + eps p + eps q

def ApproximateRestrictionGoal {N d : ℕ} (D : RationalPresentation)
    (G : ChartData N d) (δ M L : ℚ) : Prop :=
  LocalContracts D G δ M L →
  ∀ p q x j η, G.domain x = true → 0 < weight D G j x →
    (∀ i, 0 < weight D G i x →
      l1 (G.sample i p x - G.sample j q x) ≤ η + eps p + eps q) →
    l1 (gluedSamples D G p x - G.sample j q x) ≤ η + eps p + eps q

def residualIndex (κ : ℕ → ℕ) (k : ℕ) : ℕ := k + monotoneMajorant κ k

def recoverySamples (a κ : ℕ → ℕ) (n : ℕ) : ℕ :=
  a (residualIndex κ (n+2))

def ResidualContract (D : RationalPresentation) (r : ℕ → ℚ)
    (a κ μ : ℕ → ℕ) : Prop :=
  (∀ x, D.valid x = true → 0 ≤ r x) ∧
  Monotone μ ∧
  (∀ k x y, D.valid x = true → D.valid y = true →
    D.dist x y ≤ eps (μ k) → |r x-r y| ≤ eps k) ∧
  (∀ n, D.valid (a n) = true ∧ r (a n) ≤ eps n) ∧
  (∀ k x y, D.valid x = true → D.valid y = true →
    r x ≤ eps (κ k) → r y ≤ eps (κ k) → D.dist x y ≤ eps k)

def residualSamples (r : ℕ → ℚ) (μ y : ℕ → ℕ) (n : ℕ) : ℚ :=
  r (y (μ (n+2)+2))

def CompletedZero (r : ℕ → ℚ) (μ y : ℕ → ℕ) : Prop :=
  ∀ n, |residualSamples r μ y n| ≤ eps n

def ResidualRecoveryGoal (D : RationalPresentation) (r : ℕ → ℚ)
    (a κ μ : ℕ → ℕ) : Prop :=
  MetricLaws D → ResidualContract D r a κ μ →
  Regular D (recoverySamples a κ) ∧
  CompletedZero r μ (recoverySamples a κ) ∧
  ∀ y, Regular D y → CompletedZero r μ y → NameEq D y (recoverySamples a κ)

def clipUnit (q : ℚ) : ℚ := max (-1) (min 1 q)

def cubicGrid (n j : ℕ) : ℚ := -1 + 2*(j : ℚ)/(2 : ℚ)^(n+5)

def cubicIndex (A : ℕ → ℚ) (n : ℕ) : ℕ :=
  ((Finset.range (2^(n+5)+1)).filter
    (fun j => (cubicGrid n j)^3 ≤ clipUnit (A (n+4)))).sup id

def cubicApprox (A : ℕ → ℚ) (n : ℕ) : ℚ := cubicGrid n (cubicIndex A n)

def CubicSeparationGoal : Prop :=
  ∀ u v : ℚ, |u-v|^3 ≤ 4*|u^3-v^3|

def UnitRegularName (A : ℕ → ℚ) : Prop :=
  (∀ m n, |A m-A n| ≤ eps m+eps n) ∧
  (∀ n, -1-eps n ≤ A n ∧ A n ≤ 1+eps n)

def CubicApproximationGoal (A : ℕ → ℚ) : Prop :=
  UnitRegularName A →
  ∀ n t, |(cubicApprox A n)^3-A t| ≤ eps (n+2)+eps t

def cubicRootSamples (A : ℕ → ℚ) (k : ℕ) : ℚ := cubicApprox A (3*k+9)

def CubicRootRegularGoal (A : ℕ → ℚ) : Prop :=
  UnitRegularName A →
  ∀ m n, |cubicRootSamples A m-cubicRootSamples A n| ≤ eps m+eps n

end ContinuousIPRABlueprint
