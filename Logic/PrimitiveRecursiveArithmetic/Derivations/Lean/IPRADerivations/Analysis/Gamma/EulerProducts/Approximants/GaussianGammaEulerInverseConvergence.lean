import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.GaussianGammaEulerApproximationName
import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaReciprocalInverse
import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.GaussianGammaEulerReciprocalInverse
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateTransport

/-!
# The literal Gamma C15 rate

The direct Euler program Q_N has the existing C10 error D(R)/N,
where D(R)=3 M_R (R²+R). The bounded inverse construction retains
the exact C13 fraction, so its inverse error coefficient is
lambdaDenominator² D(R)/(lambdaNumerator² N), with
lambdaNumerator=a^(2R+1) and
lambdaDenominator=d^(2R+1) (2R)! 3^(2R²+2R).
Independent requested
observations retain their two ordinary dyadic errors.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerInverseConvergence

open_ipra
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianGammaFiniteApproximantName (qF qData)
open GaussianGammaReciprocalInverse (lambdaNumerator lambdaDenominator)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

@[simp] theorem subst_headRun {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    Syn.subst σ (GaussianGammaEulerHead.run z B N) =
      GaussianGammaEulerHead.run (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by
  simp only [GaussianGammaEulerHead.run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> simp

@[simp] theorem subst_directData {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    Syn.subst σ (qData z B N) = qData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [qData,GaussianGammaFiniteApproximantName.approximantData,
    GaussianGammaFiniteApproximantName.exponentialInputData,GaussianGammaFiniteApproximantName.logExponentData]

def source (z R B a d N : PTm n) : Fm PTm n :=
  GaussianGammaReciprocalInverse.source z R B a d ⋏
    (le (two*R) N ⋏ le (GaussianGammaPerturbationExponent.numerator R) N)
def coefficientNumerator (R d : PTm n) : PTm n :=
  lambdaDenominator R d*lambdaDenominator R d*GaussianGammaEulerApproximationName.rate R
def coefficientDenominator (R a N : PTm n) : PTm n := lambdaNumerator R a*lambdaNumerator R a*N

ipra_subst source
ipra_subst coefficientNumerator
ipra_subst coefficientDenominator

theorem direct_source (z R B a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B a d N) :
    Γ ⊢[PRAAx] GaussianGammaEulerConvergence.source z R B N := .andI h.andE₁.andE₁ h.andE₂

theorem cutoff_positive (z R B a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B a d N) :
    Γ ⊢[PRAAx] le one N :=
  (GaussianGammaEulerConvergence.local_source z R B N (direct_source z R B a d N h)).andE₂.andE₁

theorem direct_rate (z R B N : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaEulerConvergence.source z R B N) : Γ ⊢[PRAAx]
    independentRate qF GaussianGammaC7Name.nameF (qData z B N) (GaussianGammaC7Name.data z R B)
      (GaussianGammaEulerApproximationName.rate R) N := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] GaussianGammaEulerConvergence.source
      (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift N)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  simpa only [independentRate,rateNumerator,rateDenominator,GaussianGammaEulerApproximationName.rate,
    GaussianNamedSmallPerturbationTransport.budgetNumerator,GaussianNamedSmallPerturbationTransport.budgetDenominator,
    GaussianGammaC7Name.sample,Syn.shift,subst_directData,
    GaussianGammaC7Name.subst_data,GaussianGammaC9Bound.subst_majorant,GaussianGammaPerturbationExponent.subst_numerator,
    PTm.subst_mul,LeanProofs.IPRA.PTm.subst_num,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    GaussianGammaEulerConvergence.observation_error (var 1) (var 0)
      (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift N)) hs

theorem actual_direct_C10_independent_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianGammaEulerConvergence.source (var 0) (var 1) (var 2) (var 3) ⟶
      independentRate qF GaussianGammaC7Name.nameF (qData (var 0) (var 2) (var 3))
        (GaussianGammaC7Name.data (var 0) (var 1) (var 2)) (GaussianGammaEulerApproximationName.rate (var 1)) (var 3)) :=
  closeUniv 4 (.impI (direct_rate _ _ _ _ Prf.hyp0))

theorem euler_source (z R B a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B a d N) :
    Γ ⊢[PRAAx] GaussianGammaEulerReciprocalInverse.source z R B a d N := .andI h.andE₁ h.andE₂.andE₁

theorem inverse_input (z R B a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B a d N) : Γ ⊢[PRAAx]
    GaussianNamedInverseRate.input qF GaussianGammaC7Name.nameF GaussianGammaEulerReciprocalInverse.inverseF
      GaussianGammaReciprocalInverse.inverseF (qData z B N) (GaussianGammaC7Name.data z R B)
      (GaussianGammaEulerReciprocalInverse.inverseData z R B N) (GaussianGammaReciprocalInverse.inverseData z R B)
      (lambdaDenominator R d) (lambdaNumerator R a) (GaussianGammaEulerApproximationName.rate R) N := by
  have ps := h.andE₁
  have qs := euler_source z R B a d N h
  have fs := GaussianGammaEulerReciprocalInverse.folded_source z R B a d N qs
  have lp := GaussianGammaReciprocalInverse.lambda_positive R a d ps.andE₂.andE₁ ps.andE₂.andE₂.andE₁
  have np := cutoff_positive z R B a d N h
  exact .andI lp.andE₁ (.andI np
    (.andI (.andI (GaussianGammaFiniteApproximantName.q_regular z B N np)
      (GaussianGammaC7Name.name_regular z R B ps.andE₁))
    (.andI (.andI (GaussianGammaEulerReciprocalInverse.inverse_regular z R B N fs)
      (GaussianGammaReciprocalInverse.inverse_regular z R B ps.andE₁))
    (.andI (.andI (GaussianGammaEulerReciprocalInverse.inverse_disk z R B a d N qs)
      (GaussianGammaReciprocalInverse.inverse_disk z R B a d ps))
    (.andI (.andI (GaussianGammaEulerReciprocalInverse.inverse_product z R B a d N qs)
      (GaussianGammaReciprocalInverse.inverse_product z R B a d ps))
      (direct_rate z R B N (direct_source z R B a d N h)))))))

theorem candidate_rate (z R B a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B a d N) : Γ ⊢[PRAAx]
    independentRate GaussianGammaEulerReciprocalInverse.inverseF GaussianGammaReciprocalInverse.inverseF
      (GaussianGammaEulerReciprocalInverse.inverseData z R B N) (GaussianGammaReciprocalInverse.inverseData z R B)
      (coefficientNumerator R d) (coefficientDenominator R a N) :=
  GaussianNamedInverseRate.inverse_rate qF GaussianGammaC7Name.nameF GaussianGammaEulerReciprocalInverse.inverseF
    GaussianGammaReciprocalInverse.inverseF (qData z B N) (GaussianGammaC7Name.data z R B)
    (GaussianGammaEulerReciprocalInverse.inverseData z R B N) (GaussianGammaReciprocalInverse.inverseData z R B)
    (lambdaDenominator R d) (lambdaNumerator R a) (GaussianGammaEulerApproximationName.rate R) N
    (inverse_input z R B a d N h)

theorem coefficient_denominator_positive (z R B a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B a d N) :
    Γ ⊢[PRAAx] le one (coefficientDenominator R a N) := by
  have lp := (GaussianGammaReciprocalInverse.lambda_positive R a d h.andE₁.andE₂.andE₁ h.andE₁.andE₂.andE₂.andE₁).andE₁
  exact GaussianRationalHorner.positive_product _ _ (GaussianRationalHorner.positive_product _ _ lp lp)
    (cutoff_positive z R B a d N h)

theorem actual_rate (z R B a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B a d N) : Γ ⊢[PRAAx]
    independentRate GaussianGammaEulerReciprocalInverse.eulerF GaussianGammaReciprocalInverse.gammaF
      (GaussianGammaEulerReciprocalInverse.eulerData z R B d N) (GaussianGammaReciprocalInverse.gammaData z R B d)
      (coefficientNumerator R d) (coefficientDenominator R a N) :=
  GaussianNamedRateTransport.transport GaussianGammaEulerReciprocalInverse.inverseF GaussianGammaReciprocalInverse.inverseF
    GaussianGammaEulerReciprocalInverse.eulerF GaussianGammaReciprocalInverse.gammaF
    (GaussianGammaEulerReciprocalInverse.inverseData z R B N) (GaussianGammaReciprocalInverse.inverseData z R B)
    (GaussianGammaEulerReciprocalInverse.eulerData z R B d N) (GaussianGammaReciprocalInverse.gammaData z R B d)
    (coefficientNumerator R d) (coefficientDenominator R a N) (coefficient_denominator_positive z R B a d N h)
    (candidate_rate z R B a d N h)
    (GaussianGammaEulerReciprocalInverse.original_euler_inverse z R B a d N (euler_source z R B a d N h)).andE₂
    (GaussianGammaReciprocalInverse.original_gamma_inverse z R B a d h.andE₁).andE₂

theorem actual_observation_error (p q z R B a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B a d N) : Γ ⊢[PRAAx]
    distanceBounded
      (ap2 GaussianGammaEulerReciprocalInverse.eulerF p (GaussianGammaEulerReciprocalInverse.eulerData z R B d N))
      (ap2 GaussianGammaReciprocalInverse.gammaF q (GaussianGammaReciprocalInverse.gammaData z R B d))
      (rateNumerator (coefficientNumerator R d) (coefficientDenominator R a N) p q)
      (rateDenominator (coefficientDenominator R a N) p q) :=
  GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q (actual_rate z R B a d N h)

theorem actual_names_regular (z R B a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B a d N) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN GaussianGammaEulerReciprocalInverse.eulerF
      (GaussianGammaEulerReciprocalInverse.eulerData z R B d N) ⋏
    GaussianEuclideanDistanceName.pointCN GaussianGammaReciprocalInverse.gammaF
      (GaussianGammaReciprocalInverse.gammaData z R B d) :=
  .andI (GaussianGammaEulerReciprocalInverse.euler_regular z R B a d N (euler_source z R B a d N h))
    (GaussianGammaReciprocalInverse.gamma_regular z R B a d h.andE₁)

theorem original_Gamma_C15_exact_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      independentRate GaussianGammaEulerReciprocalInverse.eulerF GaussianGammaReciprocalInverse.gammaF
        (GaussianGammaEulerReciprocalInverse.eulerData (var 0) (var 1) (var 2) (var 4) (var 5))
        (GaussianGammaReciprocalInverse.gammaData (var 0) (var 1) (var 2) (var 4))
        (coefficientNumerator (var 1) (var 4)) (coefficientDenominator (var 1) (var 3) (var 5))) :=
  closeUniv 6 (.impI (actual_rate _ _ _ _ _ _ Prf.hyp0))

theorem original_Gamma_C15_independent_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      distanceBounded
        (ap2 GaussianGammaEulerReciprocalInverse.eulerF (var 0)
          (GaussianGammaEulerReciprocalInverse.eulerData (var 2) (var 3) (var 4) (var 6) (var 7)))
        (ap2 GaussianGammaReciprocalInverse.gammaF (var 1)
          (GaussianGammaReciprocalInverse.gammaData (var 2) (var 3) (var 4) (var 6)))
        (rateNumerator (coefficientNumerator (var 3) (var 6)) (coefficientDenominator (var 3) (var 5) (var 7)) (var 0) (var 1))
        (rateDenominator (coefficientDenominator (var 3) (var 5) (var 7)) (var 0) (var 1))) :=
  closeUniv 8 (.impI (actual_observation_error _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerInverseConvergence
