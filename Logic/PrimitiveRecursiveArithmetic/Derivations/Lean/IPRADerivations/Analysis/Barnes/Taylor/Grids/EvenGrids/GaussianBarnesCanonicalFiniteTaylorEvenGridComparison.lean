import IPRADerivations.Analysis.Barnes.Taylor.Grids.Finite.GaussianBarnesCanonicalFiniteTaylorGridObservations
import IPRADerivations.Analysis.Polynomials.FiniteDifferences.GaussianPolynomialForwardDifferenceGridEvenError

/-!
# Actual finite Barnes observations on opposite grids

The native displacement and its negative use one finite scalar and one
polynomial of degree one higher than the difference order. The signed
grid comparison preserves both actual Taylor error numerators through
normalization.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorEvenGridComparison

open_ipra
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Analysis.Products (fact)
open ComplexLogarithmRemainder (bounded bounded_neg)
open GaussianBarnesCanonicalFiniteTaylorGridObservations
  (literalGrid polynomialGrid scaledPolynomial denominator denominator_positive scaled_polynomial_length)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor)
open GaussianPolynomialForwardDifferenceGrid (samples)
open GaussianPolynomialForwardDifferenceGridError (rowBound subst_rowBound)
open GaussianPolynomialForwardDifferenceGridEvenError (observedDouble even_coefficient_error)
open GaussianRationalHorner (qzero ofGaussian ofGaussian_canonical ofGaussian_represents canonical_unique)
open GaussianRationalLowerBounds (lower)
open GaussianRationalMetric (qnegative qnegative_canonical qnegative_represents distanceBounded)
open GaussianRationalNaturalScale (natScale)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def observed (t z h R B r e : PTm n) : PTm n :=
  observedDouble (literalGrid t z h R B r e) (literalGrid t z (ComplexLogarithmRemainder.neg h) R B r e) e (ofGaussian h B)

def target (s p z R B H r M e : PTm n) : PTm n :=
  natScale two (natScale (fact e) (entry (scaledPolynomial s p z R B H r M e) one))

abbrev rowNumerator (t s p z h R B H r M e : PTm n) : PTm n :=
  GaussianBarnesCanonicalFiniteTaylorGridObservations.numerator t s p z h R B H r M e

def errorNumerator (t s p z h R B H r M e D : PTm n) : PTm n :=
  pw D e*(pw two e*(rowNumerator t s p z h R B H r M e+rowNumerator t s p z (ComplexLogarithmRemainder.neg h) R B H r M e))

def errorDenominator (t s p R B M e L : PTm n) : PTm n :=
  pw L e*denominator t s p R B M

@[simp] theorem subst_observed {m : ℕ} (σ : Fin n → PTm m) (t z h R B r e : PTm n) :
    Syn.subst σ (observed t z h R B r e) = observed (Syn.subst σ t) (Syn.subst σ z) (Syn.subst σ h)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ r) (Syn.subst σ e) := by simp [observed]

@[simp] theorem subst_target {m : ℕ} (σ : Fin n → PTm m) (s p z R B H r M e : PTm n) :
    Syn.subst σ (target s p z R B H r M e) = target (Syn.subst σ s) (Syn.subst σ p) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ H) (Syn.subst σ r) (Syn.subst σ M) (Syn.subst σ e) :=
  by simp [target,one,two,fact]

@[simp] theorem subst_errorNumerator {m : ℕ} (σ : Fin n → PTm m) (t s p z h R B H r M e D : PTm n) :
    Syn.subst σ (errorNumerator t s p z h R B H r M e D) =
      errorNumerator (Syn.subst σ t) (Syn.subst σ s) (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ h)
        (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ H) (Syn.subst σ r) (Syn.subst σ M) (Syn.subst σ e) (Syn.subst σ D) :=
  by simp [errorNumerator,rowNumerator,pw,two,one]

@[simp] theorem subst_errorDenominator {m : ℕ} (σ : Fin n → PTm m) (t s p R B M e L : PTm n) :
    Syn.subst σ (errorDenominator t s p R B M e L) =
      errorDenominator (Syn.subst σ t) (Syn.subst σ s) (Syn.subst σ p) (Syn.subst σ R)
        (Syn.subst σ B) (Syn.subst σ M) (Syn.subst σ e) (Syn.subst σ L) := by simp [errorDenominator,pw]

theorem native_negative (h B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] ofGaussian (ComplexLogarithmRemainder.neg h) B ≐ qnegative (ofGaussian h B) :=
  canonical_unique (ofGaussian (ComplexLogarithmRemainder.neg h) B) (qnegative (ofGaussian h B)) (ComplexLogarithmRemainder.neg h) B
    (ofGaussian_canonical (ComplexLogarithmRemainder.neg h) B hB) (qnegative_canonical (ofGaussian h B)) hB
    (ofGaussian_represents (ComplexLogarithmRemainder.neg h) B hB) (qnegative_represents (ofGaussian h B) h B (ofGaussian_represents h B hB))

theorem backward_samples (s p z h R B H r M e : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] polynomialGrid s p z (ComplexLogarithmRemainder.neg h) R B H r M e ≐
      samples (scaledPolynomial s p z R B H r M e) (succ e) qzero (qnegative (ofGaussian h B)) := by
  ipra_congr (samples (var 0) (var 1) qzero (var 2) : PTm 3)
    with [.eqRefl (scaledPolynomial s p z R B H r M e), .eqRefl (succ e), native_negative h B hB] using [polynomialGrid]

private theorem row_target_congr {V P Q N A B : PTm n} (he : Γ ⊢[PRAAx] P ≐ Q)
    (hrow : Γ ⊢[PRAAx] rowBound V P N A B) : Γ ⊢[PRAAx] rowBound V Q N A B := by
  have moved := Prf.eqSubst1 (Γ := Γ) (rowBound (Syn.shift V) (var 0) (Syn.shift N) (Syn.shift A) (Syn.shift B)) he
    (by simpa only [subst_rowBound,Syn.subst_inst_shift,Syn.subst_var,Syn.inst_zero] using hrow)
  simpa only [subst_rowBound,Syn.subst_inst_shift,Syn.subst_var,Syn.inst_zero] using moved

theorem compare_from_rows (t s p z h R B H r M e L D A C : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (he : Γ ⊢[PRAAx] previous M ≐ succ e)
    (hL : Γ ⊢[PRAAx] le one L) (hD : Γ ⊢[PRAAx] le one D) (hh : Γ ⊢[PRAAx] lower (ofGaussian h B) L D)
    (hplus : Γ ⊢[PRAAx] rowBound (literalGrid t z h R B r e) (polynomialGrid s p z h R B H r M e)
      (succ e) A (denominator t s p R B M))
    (hminus : Γ ⊢[PRAAx] rowBound (literalGrid t z (ComplexLogarithmRemainder.neg h) R B r e) (polynomialGrid s p z (ComplexLogarithmRemainder.neg h) R B H r M e)
      (succ e) C (denominator t s p R B M)) :
    Γ ⊢[PRAAx] distanceBounded (observed t z h R B r e) (target s p z R B H r M e)
      (pw D e*(pw two e*(A+C))) (errorDenominator t s p R B M e L) := by
  let V := literalGrid t z h R B r e
  let W := literalGrid t z (ComplexLogarithmRemainder.neg h) R B r e
  let P := scaledPolynomial s p z R B H r M e
  let u := ofGaussian h B
  let N := denominator t s p R B M
  have shape : Γ ⊢[PRAAx] length P ≐ succ (succ e) :=
    (scaled_polynomial_length s p z R B H r M e).eqTrans (congrSucc he)
  have backward : Γ ⊢[PRAAx] rowBound W (samples P (succ e) qzero (qnegative u)) (succ e) C N :=
    row_target_congr (backward_samples s p z h R B H r M e hB) hminus
  change Γ ⊢[PRAAx] distanceBounded (observedDouble V W e u) (natScale two (natScale (fact e) (entry P one)))
    (pw D e*(pw two e*(A+C))) (pw L e*N)
  exact even_coefficient_error V W P e u L D A C N shape hL hD hh (denominator_positive t s p R B M hB) hplus backward

theorem compare (t s p z h R B H r M e L D : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hsmall : Γ ⊢[PRAAx] le ((e*stepDivisor R)*H) B)
    (he : Γ ⊢[PRAAx] previous M ≐ succ e) (hL : Γ ⊢[PRAAx] le one L) (hD : Γ ⊢[PRAAx] le one D)
    (hstep : Γ ⊢[PRAAx] lower (ofGaussian h B) L D) :
    Γ ⊢[PRAAx] distanceBounded (observed t z h R B r e) (target s p z R B H r M e)
      (errorNumerator t s p z h R B H r M e D) (errorDenominator t s p R B M e L) :=
  compare_from_rows t s p z h R B H r M e L D _ _ hz.andE₁ he hL hD hstep
    (GaussianBarnesCanonicalFiniteTaylorGridObservations.row_bound t s p z h R B H r M e hz hh hsmall)
    (GaussianBarnesCanonicalFiniteTaylorGridObservations.row_bound t s p z (ComplexLogarithmRemainder.neg h) R B H r M e hz (bounded_neg hh) hsmall)

theorem actual_Barnes_finite_Taylor_even_grid_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
    (let t := var 0
     let s := var 1
     let p := var 2
     let z := var 3
     let h := var 4
     let R := var 5
     let B := var 6
     let H := var 7
     let r := var 8
     let M := var 9
     let e := var 10
     let L := var 11
     let D := var 12
     (source z R B ⋏ (bounded h H ⋏ (le ((e*stepDivisor R)*H) B ⋏ (previous M ≐ succ e ⋏
       (le one L ⋏ (le one D ⋏ lower (ofGaussian h B) L D)))))) ⟶
       distanceBounded (observed t z h R B r e) (target s p z R B H r M e)
         (errorNumerator t s p z h R B H r M e D) (errorDenominator t s p R B M e L)) :=
  closeUniv 13 (.impI (compare (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)
    (var 8) (var 9) (var 10) (var 11) (var 12) Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorEvenGridComparison
