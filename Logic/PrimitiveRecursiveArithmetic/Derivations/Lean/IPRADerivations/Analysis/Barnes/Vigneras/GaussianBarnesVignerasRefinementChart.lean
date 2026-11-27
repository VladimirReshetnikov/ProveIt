import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasRefinementJet
import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasAdjacentObservation
import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasThirdJetFloor
import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.Certificates.GaussianDiscretePeriodicUniformCertificate
import IPRADerivations.DiophantineNumberTheory.AperyMultibound

/-! The fine grid stays in one positive compact strip with a disk radius
independent of the fine denominator. Its translation pays the cubic floor. -/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesVignerasRefinementChart

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Common
open ComplexLogarithmRemainder (normSq eval_re_code eval_im_code)
open GaussianBarnesCanonicalThirdDerivativePositiveMargin (step)
open GaussianBarnesCanonicalThirdLogarithmRows (center)
open GaussianBarnesVignerasRefinementWrap (translation numerator observationClock)
open GaussianBarnesVignerasRefinementJet (radius successor_numerator)
open GaussianCoefficientNameBounds (unit)
open GaussianDiscretePeriodicUniformCertificate (window)
open GaussianRationalHorner (positive_product)
open GaussianRootAlgebra (equal equal_of_values normSq_equal)
open SignedDiscreteDerivativeOperators (width divisor)
open LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound (pw_num)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "calc_source" => GaussianBarnesCanonicalPositiveLogarithmCalculus.source
local notation "budget" => GaussianBarnesCanonicalPositiveLogarithmCalculus.budget
local notation "far" => GaussianBarnesVignerasCubicForce.translation

def precision (p : PTm n) : PTm n := p+num 5

def scheduled (x p : PTm n) : Fm PTm n :=
  le (budget (precision p) (radius x) one) (divisor x) ⋏
    (translation x ≐ far (precision p) ⋏
      observationClock x ≐ GaussianBarnesVignerasAdjacentObservation.clock (divisor x) (precision p))

@[simp] theorem subst_precision {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) :
    Syn.subst σ (precision p) = precision (Syn.subst σ p) := by simp [precision]

@[simp] theorem subst_scheduled {m : ℕ} (σ : Fin n → PTm m) (x p : PTm n) :
    (scheduled x p).subst σ = scheduled (Syn.subst σ x) (Syn.subst σ p) := by
  simp [scheduled,GaussianBarnesCanonicalPositiveLogarithmCalculus.budget,GaussianBarnesCanonicalPositiveLogarithmDyadicDerivative.budget,
    GaussianBarnesCanonicalPositiveRelativeLogarithmChart.threshold,
    GaussianBarnesCanonicalPositiveRelativeLogarithmChart.margin,
    GaussianBarnesCanonicalPositiveRelativeLogarithmDerivative.gain,
    translation,one,two]

theorem precision_unit (p : PTm n) : Γ ⊢[PRAAx] unit (precision p) ≐ num 32*unit p := by
  have factor : Γ ⊢[PRAAx] pw two (num 5 : PTm n) ≐ num 32 := pw_num 2 5
  exact (pw_add two p (num 5)).eqTrans ((congrMul (.eqRefl _) factor).eqTrans (mul_comm _ _))

theorem observation_late (x p : PTm n) (h : Γ ⊢[PRAAx] scheduled x p) :
    Γ ⊢[PRAAx] le (precision p) (observationClock x) :=
  le_congr (.eqRefl _) h.andE₂.andE₂.eqSymm (le_add_right _ _)

theorem window_bound (x N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hM : Γ ⊢[PRAAx] le one (width x)) (hD : Γ ⊢[PRAAx] divisor x ≐ N*width x) :
    Γ ⊢[PRAAx] le (window x N) (num 4*divisor x) := by
  let M := width x
  let D := divisor x
  have d : Γ ⊢[PRAAx] le one D := le_congr (.eqRefl _) hD.eqSymm (positive_product N M hN hM)
  have md : Γ ⊢[PRAAx] le M D := le_congr (one_mul M) hD.eqSymm (mul_le_mul_right M hN)
  have raw := add_le_add (le_refl (N*M)) (add_le_add (mul_le_mul_right two md) d)
  have rhs : Γ ⊢[PRAAx] N*M+(D*two+D) ≐ num 4*D := by
    ipra_lc -natEq hD
  have lhs : Γ ⊢[PRAAx] N*M+(M*two+one) ≐ window x N := by
    dsimp only [M,window]
    ipra_ring
  exact le_congr lhs rhs raw

theorem lower_numerator (x k : PTm n) : Γ ⊢[PRAAx] le (divisor x) (numerator x k) :=
  le_trans (le_add_right _ _) (le_add_right _ _)

theorem far_numerator (x k p : PTm n) (h : Γ ⊢[PRAAx] scheduled x p) :
    Γ ⊢[PRAAx] le (far (precision p)*divisor x) (numerator x k) :=
  le_congr (congrMul h.andE₂.andE₁ (.eqRefl _)) (.eqRefl _) (le_add_left _ _)

private theorem numerator_bound (x k : PTm n) (hk : Γ ⊢[PRAAx] le k (num 4*divisor x)) :
    Γ ⊢[PRAAx] le (numerator x k) (radius x*divisor x) := by
  have a := add_le_add (add_le_add (le_refl (divisor x)) hk) (le_refl (translation x*divisor x))
  apply le_trans a
  apply le_of_eq_add (d := divisor x)
  unfold radius
  ipra_ring

private theorem disk_of_bounds (A D R : PTm n) (hd : Γ ⊢[PRAAx] le one D)
    (hl : Γ ⊢[PRAAx] le D A) (hu : Γ ⊢[PRAAx] le A (R*D)) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalLogCofinal.source (center A D) R D := by
  let m := monus A D
  let v := GaussianDominantPairAlgebra.radiusNumerator m
  have e : Γ ⊢[PRAAx] equal (center A D) v := by
    apply equal_of_values
    · have h := natEq (eq_add_of_le hl)
      simp only [center,v,GaussianDominantPairAlgebra.radiusNumerator,eval_re_code,ZT.toZ_sub,ZT.toZ_ofNat,m]
      ipra_simps
      linear_combination h
    · simp only [center,v,GaussianDominantPairAlgebra.radiusNumerator,eval_im_code]
  have norm := (normSq_equal e).eqTrans (GaussianDominantPairAlgebra.radius_numerator_norm m)
  have cap := le_trans (monus_le_self A D) hu
  exact .andI hd (le_congr norm.eqSymm (.eqRefl _) (Common.mul_le_mul cap cap))

theorem strip_bounds (x N k : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hM : Γ ⊢[PRAAx] le one (width x))
    (hD : Γ ⊢[PRAAx] divisor x ≐ N*width x) (hk : Γ ⊢[PRAAx] lt k (window x N)) :
    Γ ⊢[PRAAx] le ((translation x+one)*divisor x) (numerator x k) ⋏
      le (succ (numerator x k)) (radius x*divisor x) := by
  have lo : Γ ⊢[PRAAx] le ((translation x+one)*divisor x) (numerator x k) :=
    le_of_eq_add (d := k) (by unfold numerator GaussianBarnesVignerasIntegerPeriod.advance; ipra_ring)
  have hi := numerator_bound x (succ k) (le_trans hk (window_bound x N hN hM hD))
  exact .andI lo (le_congr (successor_numerator x k) (.eqRefl _) hi)

theorem admitted (x N k p : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hM : Γ ⊢[PRAAx] le one (width x))
    (hD : Γ ⊢[PRAAx] divisor x ≐ N*width x) (h : Γ ⊢[PRAAx] scheduled x p)
    (hk : Γ ⊢[PRAAx] lt k (window x N)) :
    Γ ⊢[PRAAx] calc_source (precision p) (numerator x k) (succ (numerator x k)) (divisor x) (radius x) one := by
  let A := numerator x k
  let C := succ A
  let D := divisor x
  let R := radius x
  let a := step A C
  let H := GaussianL1.norm1 a
  have hd : Γ ⊢[PRAAx] le one D :=
    le_congr (.eqRefl _) hD.eqSymm (positive_product _ _ hN hM)
  have low := lower_numerator (Γ := Γ) x k
  have lowC : Γ ⊢[PRAAx] le D C := le_trans low (le_succ_self A)
  have top := window_bound x N hN hM hD
  have ha := disk_of_bounds A D R hd low (numerator_bound x k (le_trans (le_of_lt hk) top))
  have hc := disk_of_bounds C D R hd lowC
    (le_congr (successor_numerator x k) (.eqRefl _) (numerator_bound x (succ k) (le_trans hk top)))
  have stepOne := GaussianBarnesVignerasAdjacentObservation.successor_step (Γ := Γ) A
  have hn : Γ ⊢[PRAAx] normSq a ≐ one := (normSq_equal stepOne).eqTrans ComplexLogarithmRemainder.normSq_one
  have hH : Γ ⊢[PRAAx] H ≐ one := (GaussianL1.norm1_equal stepOne).eqTrans GaussianL1.norm1_one
  have margin : Γ ⊢[PRAAx] GaussianBarnesCanonicalThirdDerivativePositiveMargin.source A C D H one :=
    .andI hd (.andI (le_trans hd low) (.andI (le_trans hd lowC) (.andI (le_refl one)
      (.andI (le_congr (.eqRefl _) (one_mul A).eqSymm low)
        (.andI (le_congr (.eqRefl _) (one_mul C).eqSymm lowC)
          (le_congr hn.eqSymm ((one_mul one).eqSymm.eqTrans (congrMul hH.eqSymm hH.eqSymm)) (le_refl one)))))))
  have small := le_congr ((mul_one_right _).eqSymm.eqTrans (congrMul (.eqRefl _) hH.eqSymm)) (.eqRefl _) h.andE₁
  exact .andI (.andI margin (.andI ha hc))
    (.andI (le_congr (.eqRefl _) hn.eqSymm (le_refl one)) small)

end LeanProofs.IPRA.Analysis.GaussianBarnesVignerasRefinementChart
