import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.ExponentCoefficients.GaussianBarnesCanonicalExponentTaylorFixedCutoff
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.ProductCoefficients.GaussianBarnesCanonicalTaylorProductCoefficientCauchy

/-!
# Retiming the actual Barnes Taylor product at a fixed finite cutoff

The fixed-cutoff exponent mass estimate propagates through the original
finite exponential and the original centered-head convolution. The
coefficient estimate only requires late prefactor samples.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorProductFixedCutoff

open_ipra
open GaussianBarnesCanonicalExponentTaylorBuffer (buffer buffer_length)
open GaussianBarnesCanonicalExponentTaylorCoefficientCauchy (linearGain)
open GaussianBarnesCanonicalExponentTaylorCoefficientMassGap (massError)
open GaussianBarnesCanonicalExponentTaylorMass (massCap mass)
open GaussianBarnesCanonicalExponentTaylorRetainedCoefficient (prefactorGain)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalTaylorProductCoefficientCauchy
  (exponential exponentialError headCap productError productCoefficient
    padded_head_coefficient_bound product_gap_of_exponential_bounds subst_headCap subst_exponentialError)
open GaussianCoefficientNameBounds (unit)
open GaussianRationalL1 (qL1)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient)
open GaussianRationalMetric (qsub)
open RationalArgmin (rationalLE)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem exponential_gap (p q t z R B r M K e : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M))
    (hq : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit q))
    (ht : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit t)) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub (exponentCoefficient (exponential q z R B r M K) (K*previous M) e)
      (exponentCoefficient (exponential t z R B r M K) (K*previous M) e))) (exponentialError p R M K) :=
  GaussianPolynomialExponentialCoefficientVariation.original_coefficient_variation
    (buffer q z R B r M) (buffer t z R B r M) (previous M) K (massCap R M) (massError p M) e
    (buffer_length q z R B r M) (buffer_length t z R B r M) (mass q z R B r M hz) (mass t z R B r M hz)
    (GaussianBarnesCanonicalExponentTaylorFixedCutoff.late_mass_gap p q t z R B r M hz hq ht) he

theorem late_product_gap (p q t z R B r M e : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M))
    (hq : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit q))
    (ht : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit t)) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub (productCoefficient q z R B r M e) (productCoefficient t z R B r M e))) (productError p z R B M e) := by
  refine product_gap_of_exponential_bounds q t z R B r r M e (headCap z R B)
    (exponentialError p R M (previous M)) he ?_
  intro sh Δ N j hj
  have hz' : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hz.shift.wk
  have clock_budget {w : PTm n} (h : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit w)) :
      Δ ⊢[PRAAx] le (prefactorGain (sh R)*unit (sh p)) (unit (sh w)) := by
    simpa [Δ,sh,Fm.shift,Syn.shift,prefactorGain,linearGain,GaussianBarnesCanonicalPrefactorLipschitz.halfGain,
      GaussianBarnesCanonicalPrefactor.negativeHalf,one,two] using h.shift.wk
  refine .andI ?_ ?_
  · simpa only [Δ,sh,Syn.shift,subst_headCap] using
      padded_head_coefficient_bound (Γ := Δ) (sh z) (sh R) (sh B) (sh e) (var 0)
  · simpa only [Δ,sh,N,Syn.shift,subst_exponentialError,GaussianBarnesCanonicalHigherRows.subst_previous] using
      exponential_gap (sh p) (sh q) (sh t) (sh z) (sh R) (sh B) (sh r) (sh M) N j hz' hj
        (clock_budget hq) (clock_budget ht)

theorem actual_Barnes_fixed_cutoff_Taylor_product_coefficient_Cauchy_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (let p := var 0
     let q := var 1
     let t := var 2
     let z := var 3
     let R := var 4
     let B := var 5
     let r := var 6
     let M := var 7
     let e := var 8
     (source z R B ⋏ (le e (previous M) ⋏ (le (prefactorGain R*unit p) (unit q) ⋏ le (prefactorGain R*unit p) (unit t)))) ⟶
       rationalLE (qL1 (qsub (productCoefficient q z R B r M e) (productCoefficient t z R B r M e))) (productError p z R B M e)) :=
  closeUniv 9 (.impI (late_product_gap (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorProductFixedCutoff
