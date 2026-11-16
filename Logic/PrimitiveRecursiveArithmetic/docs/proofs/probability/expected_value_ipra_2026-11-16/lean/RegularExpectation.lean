import Mathlib
import «ExpectedValueFinite»

/-!
# Effective simple-function expectation

STATUS: uncompiled blueprint.  This is the effective replacement for an
unrestricted measure-theoretic universe inside first-order iPRA.
-/

namespace ExpectedValueIPRA

open scoped BigOperators

/-- A regular real by nested rational intervals. -/
structure Regular where
  lo hi : Nat -> Rat
  ordered : ∀ p, lo p <= hi p
  nestedLo : Monotone lo
  nestedHi : Antitone hi
  width : ∀ p, hi p - lo p <= (1 : Rat) / 2^p

namespace Regular

/-- Precision-wise order. -/
def Le (x y : Regular) : Prop := ∀ p, x.hi (p + 2) <= y.lo (p + 2) + (1 : Rat) / 2^p

/-- Precision-wise absolute error. -/
def AbsDiffLe (x y e : Regular) : Prop :=
  ∀ p,
    x.hi (p + 2) - y.lo (p + 2) <= e.hi p + (1 : Rat) / 2^p ∧
    y.hi (p + 2) - x.lo (p + 2) <= e.hi p + (1 : Rat) / 2^p

end Regular

/-- One finite simple approximation level. -/
structure SimpleLevel where
  law : FinLaw
  value : Fin law.card -> Rat

/-- Refinement data from a fine level to a coarse level. -/
structure Refinement (coarse fine : SimpleLevel) where
  parent : Fin fine.law.card -> Fin coarse.law.card
  mass_preserved : ∀ i,
    (∑ j, if parent j = i then fine.law.weight j else 0) = coarse.law.weight i

/-- Exact L1 distance after pulling a coarse observable to a fine refinement. -/
def refinementL1 {coarse fine : SimpleLevel} (R : Refinement coarse fine) : Rat :=
  fine.law.expect (fun j => |fine.value j - coarse.value (R.parent j)|)

/-- A primitive-recursive refining simple-law name with a built-in L1 modulus.
In the object language all fields are natural codes and evaluators. -/
structure L1SimpleName where
  level : Nat -> SimpleLevel
  refine : ∀ p, Refinement (level p) (level (p + 1))
  coherent : ∀ p, refinementL1 (refine p) <= (1 : Rat) / 2^(p + 2)

/-- A countable rational series name with an absolute-tail modulus. -/
structure AbsSeriesName where
  term : Nat -> Rat
  modulus : Nat -> Nat
  tail : ∀ p m n, modulus p <= m -> m <= n ->
    (∑ k in Finset.Ico m n, |term k|) <= (1 : Rat) / 2^p

/-- Compact integrand presentation. -/
structure IntegrandName where
  a b : Rat
  eval : Rat -> Nat -> Rat × Rat
  bound : Nat -> Rat
  modulus : Nat -> Nat
  ordered : ∀ x p, (eval x p).1 <= (eval x p).2
  width : ∀ x p, (eval x p).2 - (eval x p).1 <= (1 : Rat) / 2^p
  uniform : Prop

/-- Improper integral adds a primitive-recursive truncation/tail certificate. -/
structure ImproperIntegrandName extends IntegrandName where
  cutoff : Nat -> Nat
  tailBound : Nat -> Rat
  tailSmall : ∀ p, tailBound p <= (1 : Rat) / 2^p

/-- Proof obligations for the regular expectation layer. -/
structure RegularExpectationProofPackage where
  expectName : L1SimpleName -> Regular
  expect_cauchy : Prop
  expect_linear : Prop
  expect_monotone : Prop
  expect_abs_le : Prop
  effectiveLotus : Prop
  absSeriesSum : AbsSeriesName -> Regular
  reindexInvariant : Prop
  compactIntegral : IntegrandName -> Regular
  improperIntegral : ImproperIntegrandName -> Regular
  densityExpectation : Prop
  layerCake : Prop

/-- Explicit convergence contracts. -/
structure ConvergenceProofPackage (regular : RegularExpectationProofPackage) where
  finiteFatouKernel : Prop
  monotoneConvergenceWithTailModulus : Prop
  uniformIntegrabilityTruncation : Prop
  dominatedConvergenceWithModuli : Prop
  expectationCounterexample : Prop
  signedSigmaAdditivityCounterexample : Prop

/-- Analytic examples from the article. -/
structure DistributionProofPackage (regular : RegularExpectationProofPackage) where
  logarithmExample : Prop
  geometricMean : Prop
  poissonMean : Prop
  uniformMean : Prop
  exponentialMean : Prop
  normalMean : Prop
  paretoMean : Prop
  cauchyUndefined : Prop
  precipitationMean : Prop

end ExpectedValueIPRA
