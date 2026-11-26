import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.GaussianGammaExponentialHorizonCoherence
import IPRADerivations.Analysis.Gamma.Taylor.FinitePolynomials.GaussianGammaFiniteCoefficientPolynomial

/-!
# A fixed literal expression for every original finite Gamma coefficient

Original finite exponential reader coherence and the actual Euler-head
convolution remove the degree and exponential cutoffs from each low
coefficient of the SAME original full polynomial. The canonical finite
expression uses degree horizon e and exponential cutoff e. The actual
cofinal polynomial at observation p+e has exactly this coefficient at
its original sampled gamma/reciprocal-power precision. A computed radius
e+1 discharges the remaining head-degree guard for every internal e.
Convergence as the original sample precision changes is still separate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaFiniteCoefficientStability

open_ipra
open GaussianGammaReciprocalDegreeCells (degree)
open GaussianGammaFiniteCoefficientPolynomial (polynomial totalDegree)
open GaussianGammaCofinalCoefficientName (coefficientPrecision degreeCutoff exponentialCutoff)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient)
open GaussianPolynomialLowJetProduct (jetEqual)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem exponential_jet (q N L M K T H : PTm n)
    (hL : Γ ⊢[PRAAx] le H (degree L)) (hM : Γ ⊢[PRAAx] le H (degree M))
    (hK : Γ ⊢[PRAAx] le H K) (hT : Γ ⊢[PRAAx] le H T) : Γ ⊢[PRAAx]
    jetEqual
      (GaussianRationalPolynomialExponential.polynomial (GaussianGammaExponentCoefficientPolynomial.polynomial q N L) (degree L) K) (K*degree L)
      (GaussianRationalPolynomialExponential.polynomial (GaussianGammaExponentCoefficientPolynomial.polynomial q N M) (degree M) T) (T*degree M) H := by
  have hl : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift H) (degree (Syn.shift L)) := by simpa [Fm.shift,Syn.shift] using hL.shift
  have hm : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift H) (degree (Syn.shift M)) := by simpa [Fm.shift,Syn.shift] using hM.shift
  have hk : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift H) (Syn.shift K) := by simpa [Fm.shift,Syn.shift] using hK.shift
  have ht : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift H) (Syn.shift T) := by simpa [Fm.shift,Syn.shift] using hT.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift H)) :: Γ.map Fm.shift
  have he : Δ ⊢[PRAAx] le (var 0) (Syn.shift H) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  simpa only [Δ,jetEqual,Syn.shift,GaussianRationalPolynomialExponential.subst_polynomial,
    GaussianGammaExponentCoefficientPolynomial.subst_polynomial,GaussianGammaReciprocalDegreeCells.subst_degree,PTm.subst_mul] using
    GaussianGammaExponentialHorizonCoherence.original_exponential_horizon (Syn.shift q) (Syn.shift N)
      (Syn.shift L) (Syn.shift M) (Syn.shift K) (Syn.shift T) (var 0)
      (le_trans he hl.wk) (le_trans he hm.wk) (le_trans he hk.wk) (le_trans he ht.wk)

theorem output_degree_bound (e K L : PTm n) (hK : Γ ⊢[PRAAx] le e K) : Γ ⊢[PRAAx] le e (K*degree L) :=
  le_congr (show Γ ⊢[PRAAx] e*one ≐ e by ipra_ring) (.eqRefl _) (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono hK
    (le_trans (le_succ_self one) (GaussianGammaZetaDegreeName.degree_positive L)))

theorem whole_horizon_reader (q R L M K T e : PTm n)
    (hHead : Γ ⊢[PRAAx] le e (succ (two*R)))
    (hL : Γ ⊢[PRAAx] le e (degree L)) (hM : Γ ⊢[PRAAx] le e (degree M))
    (hK : Γ ⊢[PRAAx] le e K) (hT : Γ ⊢[PRAAx] le e T) : Γ ⊢[PRAAx]
    exponentCoefficient (polynomial q R L K) (totalDegree R L K) e ≐
      exponentCoefficient (polynomial q R M T) (totalDegree R M T) e := by
  have head : Γ ⊢[PRAAx] jetEqual (GaussianGammaEulerHeadPolynomial.polynomial (two*R)) (succ (two*R))
      (GaussianGammaEulerHeadPolynomial.polynomial (two*R)) (succ (two*R)) e := .allI (.impI (.eqRefl _))
  exact GaussianPolynomialLowJetProduct.product_reader _ _ _ _ _ _ _ _ _ _ head
    (exponential_jet q (two*R) L M K T e hL hM hK hT) (le_refl e)
    hHead (output_degree_bound e K L hK) hHead (output_degree_bound e T M hT)

def fixedCoefficient (q R e : PTm n) : PTm n :=
  exponentCoefficient (polynomial q R e e) (totalDegree R e e) e
ipra_subst fixedCoefficient

theorem original_fixed_horizon (q R L K e : PTm n)
    (hHead : Γ ⊢[PRAAx] le e (succ (two*R)))
    (hL : Γ ⊢[PRAAx] le e (degree L)) (hK : Γ ⊢[PRAAx] le e K) : Γ ⊢[PRAAx]
    exponentCoefficient (polynomial q R L K) (totalDegree R L K) e ≐ fixedCoefficient q R e :=
  whole_horizon_reader q R L e K e e hHead hL
    (le_of_eq_add (d := two) (by unfold degree; ipra_ring)) hK (le_refl e)

def cofinalObservation (p R e : PTm n) : PTm n :=
  exponentCoefficient (polynomial (coefficientPrecision (p+e) R) R (degreeCutoff (p+e) R) (exponentialCutoff (p+e) R))
    (totalDegree R (degreeCutoff (p+e) R) (exponentialCutoff (p+e) R)) e
ipra_subst cofinalObservation [coefficientPrecision, degreeCutoff, exponentialCutoff, GaussianGammaCofinalCoefficientName.exponentClock, GaussianGammaCofinalCoefficientName.inputClock, GaussianGammaCofinalCoefficientName.outerClock]

theorem cofinal_observation_fixed (p R e : PTm n) (hHead : Γ ⊢[PRAAx] le e (succ (two*R))) : Γ ⊢[PRAAx]
    cofinalObservation p R e ≐ fixedCoefficient (coefficientPrecision (p+e) R) R e := by
  have horizon := le_trans (le_add_left e p) (GaussianGammaCofinalCoefficientName.degree_cutoff_cofinal (Γ := Γ) (p+e) R)
  exact original_fixed_horizon _ _ _ _ _ hHead
    (le_trans horizon (le_of_eq_add (d := two) (by unfold degree; ipra_ring)))
    (le_trans (le_add_left e p) (GaussianGammaCofinalCoefficientName.exponential_cutoff_cofinal (p+e) R))

theorem effective_cofinal_observation (p e : PTm n) : Γ ⊢[PRAAx]
    cofinalObservation p (succ e) e ≐ fixedCoefficient (coefficientPrecision (p+e) (succ e)) (succ e) e :=
  cofinal_observation_fixed p (succ e) e (le_of_eq_add (d := e+succ two) (by ipra_ring))

def coefficientF : PR 3 := PTm.toPR (fixedCoefficient (var 0) (var 1) (var 2))
def observationF : PR 3 := PTm.toPR (cofinalObservation (var 0) (var 1) (var 2))
theorem coefficient_program (q R e : PTm n) : Γ ⊢[PRAAx] PTm.app coefficientF ![q,R,e] ≐ fixedCoefficient q R e := by
  simpa only [coefficientF,subst_fixedCoefficient,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using toPR_eq (Γ := Γ) (fixedCoefficient (var 0) (var 1) (var 2) : PTm 3) ![q,R,e]
theorem observation_program (p R e : PTm n) : Γ ⊢[PRAAx] PTm.app observationF ![p,R,e] ≐ cofinalObservation p R e := by
  simpa only [observationF,subst_cofinalObservation,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using toPR_eq (Γ := Γ) (cofinalObservation (var 0) (var 1) (var 2) : PTm 3) ![p,R,e]

theorem original_Gamma_finite_coefficient_fixed_horizon_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (succ (two*var 1)) ⟶ le (var 4) (degree (var 2)) ⟶ le (var 4) (var 3) ⟶
      exponentCoefficient (polynomial (var 0) (var 1) (var 2) (var 3)) (totalDegree (var 1) (var 2) (var 3)) (var 4) ≐
        fixedCoefficient (var 0) (var 1) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (original_fixed_horizon _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem original_Gamma_all_degree_cofinal_fixed_expression_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (PTm.app observationF ![var 0,succ (var 1),var 1] ≐
      fixedCoefficient (coefficientPrecision (var 0+var 1) (succ (var 1))) (succ (var 1)) (var 1)) :=
  closeUniv 2 ((observation_program _ _ _).eqTrans (effective_cofinal_observation _ _))

end LeanProofs.IPRA.Analysis.GaussianGammaFiniteCoefficientStability
