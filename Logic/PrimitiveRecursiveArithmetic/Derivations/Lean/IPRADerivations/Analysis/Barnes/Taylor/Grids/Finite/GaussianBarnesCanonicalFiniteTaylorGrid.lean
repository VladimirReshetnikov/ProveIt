import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalFiniteWeightedTaylorValue
import IPRADerivations.Analysis.Polynomials.FiniteDifferences.Grids.GaussianPolynomialForwardDifferenceGrid

/-!
# The original finite Barnes Taylor comparison on a forward grid

Use one finite scalar and one stored polynomial at every point of the
forward grid. The common admission radius is the maximum displacement
bound. It enters the original power remainder unchanged.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorGrid

open_ipra
open ComplexLogarithmRemainder (add bounded bounded_mono bounded_scale scale)
open GaussianBarnesCanonicalFiniteCentralExponential (finiteNameF finiteData)
open GaussianBarnesCanonicalFiniteWeightedTaylorValue (nameF numerator denominator)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor)
open GaussianCoefficientNameBounds (unit_positive)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNameArithmetic (multiplyData)
open GaussianNamedInverseRate (independentRate subst_independentRate)
open GaussianPolynomialForwardDifferenceGrid (point samples sample_lookup)
open GaussianRationalHorner
  (canonical_unique evaluate ofGaussian ofGaussian_canonical ofGaussian_represents positive_product
    qzero qadd_canonical qadd_represents)
open GaussianRationalNaturalScale (natScale natScale_canonical natScale_represents)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "V" => GaussianBarnesCanonicalValue.prefixF
local notation "literal" => GaussianBarnesCanonicalProduct.literalData

def literalData (z h R B r j : PTm n) : PTm n :=
  literal (add z (scale j h)) (R+one) B (initial (R+one)+r)

def polynomial (p z R B H r M e : PTm n) : PTm n :=
  GaussianBarnesCanonicalFiniteWeightedTaylorValue.polynomial p z (R+one) B (e*H) r M

def gridData (p z h R B H r M e j : PTm n) : PTm n :=
  multiplyData finiteNameF constantF (finiteData z (R+one) B r)
    (evaluate (polynomial p z R B H r M e) (point qzero (ofGaussian h B) j))

theorem scale_step (h B j : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] ofGaussian (scale j h) B ≐ natScale j (ofGaussian h B) :=
  canonical_unique _ _ _ _ (ofGaussian_canonical _ _ hB)
    (natScale_canonical _ _) hB (ofGaussian_represents _ _ hB)
    (natScale_represents _ _ _ _ hB (ofGaussian_represents _ _ hB))

theorem shifted_point (z h B j : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] ofGaussian (add z (scale j h)) B ≐ point (ofGaussian z B) (ofGaussian h B) j :=
  canonical_unique _ _ _ _ (ofGaussian_canonical _ _ hB)
    (qadd_canonical _ _) hB (ofGaussian_represents _ _ hB)
    (qadd_represents _ _ _ _ _ hB (ofGaussian_represents z B hB)
      (natScale_represents _ _ _ _ hB (ofGaussian_represents h B hB)))

theorem displacement_point (h B j : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] ofGaussian (scale j h) B ≐ point qzero (ofGaussian h B) j := by
  have zero := (GaussianReciprocalHorner.qadd_commutative (Γ := Γ) qzero (natScale j (ofGaussian h B))).eqTrans
    (GaussianReciprocalHorner.qadd_zero_right _ (natScale_canonical _ _))
  exact (scale_step h B j hB).eqTrans zero.eqSymm

theorem data_binding (p z h R B H r M e j : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalFiniteWeightedTaylorValue.data p z (scale j h) (R+one) B (e*H) r M ≐
      gridData p z h R B H r M e j := by
  ipra_congr (multiplyData finiteNameF constantF (var 0) (evaluate (var 1) (var 2)) : PTm 3) with
    [.eqRefl (finiteData z (R+one) B r), .eqRefl (polynomial p z R B H r M e), displacement_point h B j hB]
    using [GaussianBarnesCanonicalFiniteWeightedTaylorValue.data,gridData,polynomial]

theorem grid_sample (p z h R B H r M e j : PTm n) (hj : Γ ⊢[PRAAx] le j e) :
    Γ ⊢[PRAAx] gridData p z h R B H r M e j ≐
      multiplyData finiteNameF constantF (finiteData z (R+one) B r)
        (entry (samples (polynomial p z R B H r M e) (succ e) qzero (ofGaussian h B)) j) := by
  have read := sample_lookup (polynomial p z R B H r M e) (succ e) qzero (ofGaussian h B) j
    (Common.lt_succ_of_le hj)
  ipra_congr (multiplyData finiteNameF constantF (var 0) (var 1) : PTm 2)
    with [.eqRefl (finiteData z (R+one) B r), read.eqSymm] using [gridData]

theorem denominator_positive (p R B M : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (denominator p (R+one) B M) :=
  positive_product _ _ (positive_product _ _
    (GaussianBarnesCanonicalCorrectedMercatorCofinal.analytic_denominator_positive (previous M) (R+one) B hB)
    (unit_positive p)) (GaussianFactorBudget.power_positive B (succ (previous M)) hB)

theorem step_bound (h H e j : PTm n) (hh : Γ ⊢[PRAAx] bounded h H) (hj : Γ ⊢[PRAAx] le j e) :
    Γ ⊢[PRAAx] bounded (scale j h) (e*H) :=
  bounded_mono (bounded_scale j hh) (mul_le_mul_right H hj)

theorem rate (p z h R B H r M e j : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hsmall : Γ ⊢[PRAAx] le ((e*stepDivisor R)*H) B)
    (hj : Γ ⊢[PRAAx] le j e) :
    Γ ⊢[PRAAx] independentRate V nameF (literalData z h R B r j) (gridData p z h R B H r M e j)
      (numerator p z (R+one) B (e*H) M) (denominator p (R+one) B M) := by
  let K := numerator p z (R+one) B (e*H) M
  let D := denominator p (R+one) B M
  let x := literalData z h R B r j
  have small : Γ ⊢[PRAAx] le (stepDivisor R*(e*H)) B := le_congr (by ipra_ring) (.eqRefl _) hsmall
  have raw : Γ ⊢[PRAAx] independentRate V nameF x
      (GaussianBarnesCanonicalFiniteWeightedTaylorValue.data p z (scale j h) (R+one) B (e*H) r M) K D :=
    GaussianBarnesCanonicalFiniteWeightedTaylorValue.shared_rate p z (scale j h) R B (e*H) r M
      hz (step_bound h H e j hh hj) small
  have move := Prf.eqSubst1 (Γ := Γ) (independentRate V nameF (Syn.shift x) (var 0) (Syn.shift K) (Syn.shift D))
    (data_binding p z h R B H r M e j hz.andE₁)
    (by simpa only [subst_independentRate,Syn.subst_inst_shift,Syn.subst_var,Syn.inst_zero] using raw)
  simpa only [subst_independentRate,Syn.subst_inst_shift,Syn.subst_var,Syn.inst_zero] using move

def allRate (p z h R B H r M e : PTm n) : Fm PTm n :=
  let sh (u : PTm n) := Syn.shift u
  .all (le (var 0) (sh e) ⟶
    independentRate V nameF (literalData (sh z) (sh h) (sh R) (sh B) (sh r) (var 0))
      (gridData (sh p) (sh z) (sh h) (sh R) (sh B) (sh H) (sh r) (sh M) (sh e) (var 0))
      (numerator (sh p) (sh z) (sh R+one) (sh B) (sh e*sh H) (sh M)) (denominator (sh p) (sh R+one) (sh B) (sh M)))

theorem rate_all (p z h R B H r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hsmall : Γ ⊢[PRAAx] le ((e*stepDivisor R)*H) B) :
    Γ ⊢[PRAAx] allRate p z h R B H r M e := by
  let sh (u : PTm n) := Syn.shift u
  let Δ := Γ.map Fm.shift
  have z' : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hz.shift
  have h' : Δ ⊢[PRAAx] bounded (sh h) (sh H) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hh.shift
  have small' : Δ ⊢[PRAAx] le ((sh e*stepDivisor (sh R))*sh H) (sh B) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hsmall.shift
  exact .allI (.impI (rate (sh p) (sh z) (sh h) (sh R) (sh B) (sh H) (sh r) (sh M) (sh e) (var 0)
    z'.wk h'.wk small'.wk Prf.hyp0))

theorem actual_Barnes_finite_Taylor_forward_grid_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (let p := var 0
     let z := var 1
     let h := var 2
     let R := var 3
     let B := var 4
     let H := var 5
     let r := var 6
     let M := var 7
     let e := var 8
     source z R B ⟶ bounded h H ⟶ le ((e*stepDivisor R)*H) B ⟶ allRate p z h R B H r M e) :=
  closeUniv 9 (.impI (.impI (.impI (rate_all _ _ _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorGrid
