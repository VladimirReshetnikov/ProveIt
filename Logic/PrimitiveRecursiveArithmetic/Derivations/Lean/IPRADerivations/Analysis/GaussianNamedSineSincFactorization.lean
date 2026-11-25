import IPRADerivations.Analysis.GaussianNamedSinc

/-!
# Division-free factorization of the original sine name

The named product and the original exponential-based sine both approximate
the same finite factorial expression. The argument bound and the uniform
bound for the sinc samples control the two changes of factors.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNamedSineSincFactorization

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedSincSamples
open GaussianNamedSinc
open GaussianNamedSineTaylor (imaginaryF imaginary_input rawData)
open GaussianNamedSineFromExponential (sineF sineData sine_regular)
open GaussianRadiusExponentialName (input bounded_samples_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_fast)
open GaussianNameRingLaws (normalized_to_sample multiply_sample_error through_identity)
open GaussianNameEquivalence (crossEquivalent)
open GaussianExponentialReference (dyadic_weaken)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def factorBudget (f : PR 2) (R x : PTm n) : PTm n :=
  two+sineBudget f R x+
    ((multiplyModulus f (nameF f) x (data f R x)+one+R*(modulus f R x+one))+sampleSize f R x*two)

@[simp] theorem subst_factorBudget {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (R x : PTm n) :
    Syn.subst σ (factorBudget f R x) = factorBudget f (Syn.subst σ R) (Syn.subst σ x) := by
  simp [factorBudget]

theorem diagonal_factorization (f : PR 2) (R x p : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (sineF (imaginaryF f)) p (sineData (imaginaryF f) R x))
      (ap2 (multiplyF f (nameF f)) p (multiplyData f (nameF f) x (data f R x)))
      (factorBudget f R x) (unit p) := by
  let U := unit p
  let g := sineF (imaginaryF f)
  let y := sineData (imaginaryF f) R x
  let d := data f R x
  let z := ap2 f p x
  let s := value f R x p
  let M := sampleSize f R x
  have hU := unit_positive (Γ := Γ) p
  have hs := sine_regular (imaginaryF f) R x (imaginary_input f R x h)
  have hu := name_regular f R x h
  have left := distance_triangle_same _ _ _ _ _ _ hU
    (common_late_distance g y p p (clock p) hs (le_refl p) (clock_later p))
    (dyadic_weaken _ _ _ p (clock p) (clock_later p) (sine_sample_error f R x p h))
  have sincError := distance_congr (.eqRefl _) (raw_at f R x p) (.eqRefl _) (.eqRefl _)
    (normalized_to_sample (rawF f) (modulus f R x) (rawData R x) p (raw_regular f R x h))
  have factorError := multiply_distance z _ _ R (modulus f R x+one) U hU
    (bounded_samples_at f R x p h.andE₂) sincError
  have harg := common_late_distance f x p p (argumentClock R p) h.andE₁ (le_refl p)
    (le_trans (clock_later p) (argument_clock_later R p))
  have argError := distance_congr (qmul_commutative s z) (qmul_commutative s (argument f R x p))
    (.eqRefl _) (.eqRefl _) (multiply_distance s z _ M two U hU (sample_bound f R x p h) harg)
  have right := distance_triangle_same _ _ _ _ _ _ hU
    (distance_triangle_same _ _ _ _ _ _ hU
      (multiply_sample_error f (nameF f) x d p h.andE₁ hu) factorError) argError
  exact through_identity _ _ _ _ _ _ _ hU left right (product_at f R x p).eqSymm

theorem original_sine_factors (f : PR 2) (R x : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] crossEquivalent (sineF (imaginaryF f)) (multiplyF f (nameF f))
      (sineData (imaginaryF f) R x) (multiplyData f (nameF f) x (data f R x)) := by
  apply GaussianNamedDiagonalRate.cross_of_diagonal_rate _ _ _ _ (factorBudget f R x)
    (sine_regular _ _ _ (imaginary_input f R x h))
    (multiply_fast f (nameF f) x (data f R x) h.andE₁ (name_regular f R x h))
  refine .allI ?_
  let C := Γ.map Fm.shift
  let Rt := Syn.shift R
  let xt := Syn.shift x
  have ht : C ⊢[PRAAx] input f Rt xt := by
    simpa only [Fm.shift, Syn.shift, GaussianRadiusExponentialName.subst_input, C, Rt, xt] using h.shift
  simpa only [GaussianNamedDiagonalRate.diagonalRate, Syn.shift, subst_factorBudget, subst_data,
    GaussianNameArithmetic.subst_multiplyData, GaussianNamedSineFromExponential.subst_sineData, C, Rt, xt] using
    diagonal_factorization f Rt xt (var 0) ht

theorem actual_original_named_sine_sinc_factorization_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (input f (var 0) (var 1) ⟶
        crossEquivalent (sineF (imaginaryF f)) (multiplyF f (nameF f))
          (sineData (imaginaryF f) (var 0) (var 1)) (multiplyData f (nameF f) (var 1) (data f (var 0) (var 1)))) :=
  closeUniv 2 (.impI (original_sine_factors f _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedSineSincFactorization
