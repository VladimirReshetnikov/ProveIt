import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIntegrandName
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerShift
import IPRADerivations.Analysis.Exponential.GaussianExponentialRadiusIndependence

/-!
# The actual Euler integrand on a fixed complex name

Form (f-1) log(a/b) - a/b with the original name operations, and use
the original scalar exponential. This gives a fixed-arity evaluator of
the named parameter at each positive rational time. On exact rational
inputs the resulting name agrees with the original Euler integrand.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedEulerIntegrand

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (exponential_input exponentialInputData)
open GaussianNameArithmetic (addF addData add_fast add_equivalent multiplyF multiplyData
  multiply_fast multiply_equivalent)
open GaussianEulerIntegrandName (logarithmF decayPoint coefficient)
open GaussianNameEquivalence (crossEquivalent cross_to_diagonal cross_refl cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalMetric (qnegative)
open GaussianRationalSyntheticDivision (qone)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficientF (f : PR 2) : PR 2 := addF f constantF
def coefficientData (x : PTm n) : PTm n := addData x (qnegative qone)
def powerExponentF (f : PR 2) : PR 2 := multiplyF (coefficientF f) logarithmF
def powerExponentData (f : PR 2) (x a b : PTm n) : PTm n :=
  multiplyData (coefficientF f) logarithmF (coefficientData x) (GaussianPositiveRationalLogarithm.data a b)
def exponentF (f : PR 2) : PR 2 := addF (powerExponentF f) constantF
def exponentData (f : PR 2) (x a b : PTm n) : PTm n :=
  addData (powerExponentData f x a b) (decayPoint a b)
def nameF (f : PR 2) : PR 2 := GaussianRadiusExponentialName.nameF (exponentF f)
def data (f : PR 2) (x a b : PTm n) : PTm n :=
  exponentialInputData (exponentF f) (exponentData f x a b)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x a b : PTm n) :
    Syn.subst σ (data f x a b) = data f (Syn.subst σ x) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [data,exponentialInputData,exponentData,powerExponentData,coefficientData,qone,
    ComplexLogarithmRemainder.oneCode,ComplexLogarithmRemainder.code,ZT.ofNat]

theorem coefficient_regular (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (coefficientF f) (coefficientData x) :=
  add_fast f constantF _ _ hf (constant_regular _)

theorem power_exponent_regular (f : PR 2) (x a b : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (ht : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) :
    Γ ⊢[PRAAx] pointCN (powerExponentF f) (powerExponentData f x a b) :=
  multiply_fast _ _ _ _ (coefficient_regular f x hf) (GaussianPositiveRationalLogarithm.name_regular a b ht)

theorem exponent_regular (f : PR 2) (x a b : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (ht : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) :
    Γ ⊢[PRAAx] pointCN (exponentF f) (exponentData f x a b) :=
  add_fast _ _ _ _ (power_exponent_regular f x a b hf ht) (constant_regular _)

theorem name_regular (f : PR 2) (x a b : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (ht : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data f x a b) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input _ _ (exponent_regular f x a b hf ht))

theorem original_coefficient (f : PR 2) (x z B : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (he : Γ ⊢[PRAAx] crossEquivalent f constantF x (ofGaussian z B)) :
    Γ ⊢[PRAAx] crossEquivalent (coefficientF f) constantF (coefficientData x) (coefficient z B) := by
  let v := ofGaussian z B
  let c : PTm n := qnegative qone
  have h := add_equivalent f constantF constantF constantF x v c c
    hf (constant_regular v) (constant_regular c) (constant_regular c)
    (cross_to_diagonal _ _ _ _ he) (cross_to_diagonal _ _ _ _ (cross_refl _ _ (constant_regular c)))
  exact cross_trans _ _ _ _ _ _ h (GaussianGammaEulerShift.constant_sum_cross v c)

theorem original_integrand (f : PR 2) (x z B a b : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (ht : Γ ⊢[PRAAx] GaussianEulerIntegrandName.source z B a b)
    (he : Γ ⊢[PRAAx] crossEquivalent f constantF x (ofGaussian z B)) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) GaussianEulerIntegrandName.nameF
      (data f x a b) (GaussianEulerIntegrandName.data z B a b) := by
  let l := GaussianPositiveRationalLogarithm.data a b
  let d := decayPoint a b
  have logName := GaussianPositiveRationalLogarithm.name_regular a b ht.andE₂
  have c := original_coefficient f x z B hf he
  have power := multiply_equivalent (coefficientF f) constantF logarithmF logarithmF
    (coefficientData x) (coefficient z B) l l (coefficient_regular f x hf)
    (constant_regular _) logName logName (cross_to_diagonal _ _ _ _ c)
    (cross_to_diagonal _ _ _ _ (cross_refl _ _ logName))
  have exp := add_equivalent (powerExponentF f) GaussianEulerIntegrandName.powerExponentF constantF constantF
    (powerExponentData f x a b) (GaussianEulerIntegrandName.powerExponentData z B a b) d d
    (power_exponent_regular f x a b hf ht.andE₂) (GaussianEulerIntegrandName.power_exponent_regular z B a b ht)
    (constant_regular d) (constant_regular d) (cross_to_diagonal _ _ _ _ power)
    (cross_to_diagonal _ _ _ _ (cross_refl _ _ (constant_regular d)))
  exact GaussianExponentialRadiusIndependence.independent_radii_proper _ _ _ _ _ _
    (exponential_input _ _ (exponent_regular f x a b hf ht.andE₂))
    (GaussianEulerIntegrandName.exponent_input z B a b ht) exp

/-- As in the original evaluator, time is a pair of natural numbers.
The data for the fixed parameter name is passed independently. -/
def evaluatorTerm (f : PR 2) (p t x : PTm n) : PTm n :=
  ap2 (nameF f) p (data f x (fstT t) (sndT t))
def evaluatorF (f : PR 2) : PR 3 := PTm.toPR (evaluatorTerm f (var 0) (var 1) (var 2))

theorem evaluator_at (f : PR 2) (p t x : PTm n) :
    Γ ⊢[PRAAx] ap3 (evaluatorF f) p t x ≐ evaluatorTerm f p t x := by
  simpa [evaluatorF,evaluatorTerm,ap3] using
    toPR_eq (Γ := Γ) (evaluatorTerm f (var 0) (var 1) (var 2) : PTm 3) ![p,t,x]

theorem sample_at (f : PR 2) (p x a b : PTm n) :
    Γ ⊢[PRAAx] ap3 (evaluatorF f) p (pairT a b) x ≐ ap2 (nameF f) p (data f x a b) := by
  refine (evaluator_at f p (pairT a b) x).eqTrans ?_
  have eq := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (data f (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![x,fstT (pairT a b),sndT (pairT a b)]) (σ' := ![x,a,b])
    (fun i => by fin_cases i; exact .eqRefl _; exact fst_pair _ _; exact snd_pair _ _)
  exact congrAp2 _ (.eqRefl p) (by simpa only [subst_data,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using eq)

theorem original_named_Euler_integrand_regular_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((pointCN f (var 0) ⋏ GaussianPositiveRationalLogarithm.source (var 1) (var 2)) ⟶
        pointCN (nameF f) (data f (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (name_regular f _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem original_named_Euler_integrand_encoded_input_agreement_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((pointCN f (var 0) ⋏ (GaussianEulerIntegrandName.source (var 1) (var 2) (var 3) (var 4) ⋏
          crossEquivalent f constantF (var 0) (ofGaussian (var 1) (var 2)))) ⟶
        crossEquivalent (nameF f) GaussianEulerIntegrandName.nameF
          (data f (var 0) (var 3) (var 4)) (GaussianEulerIntegrandName.data (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (original_integrand f _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

theorem original_named_Euler_integrand_program_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (ap3 (evaluatorF f) (var 0) (pairT (var 2) (var 3)) (var 1) ≐
        ap2 (nameF f) (var 0) (data f (var 1) (var 2) (var 3))) :=
  closeUniv 4 (sample_at f _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianNamedEulerIntegrand
