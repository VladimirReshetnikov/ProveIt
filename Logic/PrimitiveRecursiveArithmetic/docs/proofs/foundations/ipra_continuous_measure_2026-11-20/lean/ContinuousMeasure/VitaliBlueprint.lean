import ContinuousMeasure.ActionCompletion

/-!
# Typed blueprint for the limit-producing Vitali theorem

These declarations give the actual finite observations, schedules, and target
formulas. They contain no assertions that the target goals are proved.
`finite_vitali_unit` is the checked arithmetic engine; the remaining work is
its completion/refinement assembly and the object-iPRA compilation.
-/

namespace IPRAContinuousMeasure

/-- A bounded search for the least exponent; no unbounded minimization. -/
def exponentSearch (b : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 =>
      let e := exponentSearch b j
      if b ≤ 2 ^ e then e else j + 1

def ceilingLog2 (b : Nat) : Nat := exponentSearch b b

/-- The elementary bounded-search specification to instantiate from the
existing PR power/search backend. It is a target definition here. -/
def CeilingLog2Goal : Prop :=
  ∀ b, 1 ≤ b → ceilingLog2 b ≤ b ∧ b ≤ 2 ^ ceilingLog2 b ∧
    ∀ j, j < ceilingLog2 b → 2 ^ j < b

structure InMeasureCauchyRate {A : ProbabilityTower}
    (f : Nat → RegularL1Name A) where
  index : Nat → Nat
  bound : ∀ k m n, index k ≤ m → index k ≤ n → ∀ p,
    SimpleTable.measureDistance ((f m).sample p) ((f n).sample p) ≤
      dyadic k + 2 * dyadic p

structure VitaliData {A : ProbabilityTower} (f : Nat → RegularL1Name A) where
  ui : UniformTailControl f
  cauchy : InMeasureCauchyRate f
  cutoffMonotone : ∀ k l, k ≤ l → ui.cutoff k ≤ ui.cutoff l
  rateMonotone : ∀ k l, k ≤ l → cauchy.index k ≤ cauchy.index l

def vitaliPrecision {A : ProbabilityTower} {f : Nat → RegularL1Name A}
    (D : VitaliData f) (k : Nat) : Nat :=
  k + 2 + ceilingLog2 (2 * D.ui.cutoff (k + 2))

def vitaliIndex {A : ProbabilityTower} {f : Nat → RegularL1Name A}
    (D : VitaliData f) (k : Nat) : Nat := D.cauchy.index (vitaliPrecision D k)

def vitaliSample {A : ProbabilityTower} {f : Nat → RegularL1Name A}
    (D : VitaliData f) (k : Nat) : SimpleTable A :=
  (f (vitaliIndex D (k + 2))).sample (k + 2)

/-- Finite target asserting that the explicit output sample program is a
regular name. It does not assume an integrable limit as input. -/
def VitaliNameRegularityGoal {A : ProbabilityTower} {f : Nat → RegularL1Name A}
    (D : VitaliData f) : Prop :=
  ∀ p q, SimpleTable.distance (vitaliSample D p) (vitaliSample D q) ≤
    dyadic p + dyadic q

/-- Exact numerical convergence target including both sample errors. -/
def VitaliLiftingGoal {A : ProbabilityTower} {f : Nat → RegularL1Name A}
    (D : VitaliData f) : Prop :=
  VitaliNameRegularityGoal D ∧
    ∀ k n, vitaliIndex D k ≤ n → ∀ p,
      SimpleTable.distance ((f n).sample p) (vitaliSample D p) ≤
        (3 / 4 : Rat) * dyadic k + 2 * dyadic p

/-- Inherited clipping-tail bound for the constructed name. -/
def VitaliInheritedTailGoal {A : ProbabilityTower} {f : Nat → RegularL1Name A}
    (D : VitaliData f) : Prop :=
  ∀ k p, (vitaliSample D p).tailIntegral (D.ui.cutoff k : Rat) ≤
    dyadic k + dyadic p

end IPRAContinuousMeasure
