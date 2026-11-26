import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.GaussianSignedObservationGrid
import IPRADerivations.Analysis.RationalArithmetic.Scaling.GaussianRationalNaturalScale
import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.SignedDiscreteDerivativeOperators

/-!
# Actual Gaussian finite derivative rates on a common signed lattice

First clear the metric comparison at the original three raw
denominators. Then pay one rounding unit for each function value
and for the derivative value. The first two costs are multiplied
by the finite difference scale D, giving E+2D+1 lattice units.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace LeanProofs.IPRA.Analysis.GaussianDiscreteDerivativeRounding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianSignedObservationGrid (rounded subst_rounded clearedError rounding_band band_of_absolute scaled_real_absolute)
open GaussianRationalNaturalScale (natScale natScale_represents)
open GaussianRationalHorner (represents represents_rescale represents_congr positive_product)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalMetric (distanceBounded bounded_difference_iff qsub qsub_represents)
open GaussianRootAlgebra (sub equal_refl re_sub re_scale)
open ComplexLogarithmRemainder (scale normSq re)
open LeanProofs.IPRA.Foundations.GapDecision (zabs)
open SignedGridStepBounds (difference_value)
open PeriodicThirdDifferenceConstancy (band band_add band_congr band_neg band_scale band_scale_cancel)
open SignedDiscreteDerivativeOperators (divisor subst_divisor)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def allowance (D E : PTm n) : PTm n := E+two*D+one

def signedResidual (a b g D S : PTm n) : ZT n :=
  ZT.ofNat D*(rounded b S-rounded a S)-rounded g S

theorem residual_bound (a b g D S E : PTm n) (hS : Γ ⊢[PRAAx] le one S)
    (h : Γ ⊢[PRAAx] distanceBounded (natScale D (qsub b a)) g E S) :
    Γ ⊢[PRAAx] band (signedResidual a b g D S) (allowance D E) := by
  let A := rawDen a
  let B := rawDen b
  let C := rawDen g
  let K := A*(B*C)
  let a' := scale (B*C) (rawGaussian a)
  let b' := scale (A*C) (rawGaussian b)
  let g' := scale (A*B) (rawGaussian g)
  let d := scale D (sub b' a')
  let v := sub d g'
  have hA := raw_den_positive (Γ := Γ) a
  have hB := raw_den_positive (Γ := Γ) b
  have hC := raw_den_positive (Γ := Γ) g
  have hK : Γ ⊢[PRAAx] le one K := positive_product _ _ hA (positive_product _ _ hB hC)
  have ar : Γ ⊢[PRAAx] represents a a' K := represents_rescale _ _ _ _ (raw_represents a)
  have br : Γ ⊢[PRAAx] represents b b' K := by
    have eq : Γ ⊢[PRAAx] B*(A*C) ≐ K := by unfold K; ipra_ring
    exact represents_congr (.eqRefl _) (equal_refl _) eq (represents_rescale _ _ _ _ (raw_represents b))
  have gr : Γ ⊢[PRAAx] represents g g' K := by
    have eq : Γ ⊢[PRAAx] C*(A*B) ≐ K := by unfold K; ipra_ring
    exact represents_congr (.eqRefl _) (equal_refl _) eq (represents_rescale _ _ _ _ (raw_represents g))
  have dr : Γ ⊢[PRAAx] represents (natScale D (qsub b a)) d K :=
    natScale_represents _ _ _ _ hK (qsub_represents _ _ _ _ _ hK br ar)
  have raw : Γ ⊢[PRAAx] le ((S*S)*normSq v) ((E*E)*(K*K)) :=
    (bounded_difference_iff _ _ _ _ _ _ _ hK hS dr gr).iffMp h
  have eabs : Γ ⊢[PRAAx] zabs (ZT.ofNat S*re v) ≐ S*zabs (re v) :=
    (GaussianL1.abs_multiply _ _).eqTrans (congrMul (GaussianL1.abs_ofNat S) (.eqRefl _))
  have axis : Γ ⊢[PRAAx] band (ZT.ofNat S*re v) (K*E) :=
    band_of_absolute _ _ (le_congr eabs.eqSymm (.eqRefl _) (scaled_real_absolute v S E K raw))
  have next := band_scale (D*(A*C)) (rounding_band (Γ := Γ) b S)
  have prev := band_scale (D*(B*C)) (band_neg (rounding_band (Γ := Γ) a S))
  have deriv := band_scale (A*B) (band_neg (rounding_band (Γ := Γ) g S))
  apply band_scale_cancel hK
  refine band_congr ?_ ?_ (band_add (band_add (band_add axis next) prev) deriv)
  · simp only [signedResidual,clearedError,v,d,b',a',g',K,A,B,C,
      re_sub,re_scale,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_neg,ZT.toZ_ofNat,Q.mk_mul,map_mul]
    ring
  · unfold allowance K A B C
    ipra_ring

def latticeScale (x : PTm n) : PTm n := fstT (sndT (sndT x))

@[simp] theorem subst_latticeScale {m : ℕ} (σ : Fin n → PTm m) (x : PTm n) :
    Syn.subst σ (latticeScale x) = latticeScale (Syn.subst σ x) := by simp [latticeScale]

def body (f : PTm 2) : ZB :=
  let a := rounded f (latticeScale (var 1))
  ⟨a.pos,a.neg⟩

theorem sample_at (f : PTm 2) (x i : PTm n) :
    (body f).val i x = rounded (inst2 f i x) (latticeScale x) := by
  let u : ZT 2 := rounded f (latticeScale (var 1))
  change u.subst ![i,x] = _
  simp [u,inst2]

def source (f g : PTm 2) (x L E : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift L) ⟶ distanceBounded
    (natScale (divisor (Syn.shift x))
      (qsub (inst2 f (ConciseIPRA.PTm.succ (var 0)) (Syn.shift x)) (inst2 f (var 0) (Syn.shift x))))
    (inst2 g (var 0) (Syn.shift x)) (Syn.shift E) (latticeScale (Syn.shift x)))

theorem signed_source (f g : PTm 2) (x L E : PTm n) (hS : Γ ⊢[PRAAx] le one (latticeScale x))
    (h : Γ ⊢[PRAAx] source f g x L E) :
    Γ ⊢[PRAAx] SignedDiscreteDerivativeBlock.source (body f) (body g) x L (divisor x) (allowance (divisor x) E) := by
  refine .allI (.impI ?_)
  let X := Syn.shift x
  let i : PTm (n+1) := var 0
  let Δ := lt i (Syn.shift L) :: Γ.map Fm.shift
  have HS : Δ ⊢[PRAAx] le one (latticeScale X) := by
    simpa only [Δ,i,X,Fm.shift,Syn.shift,subst_le,subst_latticeScale,one,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] using hS.shift.wk
  have raw : Δ ⊢[PRAAx] distanceBounded
      (natScale (divisor X) (qsub (inst2 f (ConciseIPRA.PTm.succ i) X) (inst2 f i X)))
      (inst2 g i X) (Syn.shift E) (latticeScale X) := .impE h.allOpen.wk Prf.hyp0
  have band' := residual_bound _ _ _ _ _ _ HS raw
  have he : ZT.toZ Δ (signedResidual (inst2 f i X) (inst2 f (ConciseIPRA.PTm.succ i) X)
      (inst2 g i X) (divisor X) (latticeScale X)) =
    ZT.toZ Δ (SignedDiscreteDerivativeBlock.stepError (body f) (body g) X (divisor X) i) := by
    simp only [signedResidual,SignedDiscreteDerivativeBlock.stepError,ZT.toZ_sub,ZT.toZ_mul,
      difference_value (Γ := Δ) (body f) i X,sample_at]
  have result : Δ ⊢[PRAAx] band
      (SignedDiscreteDerivativeBlock.stepError (body f) (body g) X (divisor X) i) (allowance (divisor X) (Syn.shift E)) :=
    band_congr he (.eqRefl _) band'
  simpa only [Δ,i,X,allowance,Syn.shift,subst_divisor,LeanProofs.IPRA.PTm.subst_add,
    LeanProofs.IPRA.PTm.subst_mul,two,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using result

theorem actual_Gaussian_discrete_derivative_rounding_closed (f g : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (let x := var 0
       let L := var 1
       let E := var 2
       le one (latticeScale x) ⟶ source f g x L E ⟶
         SignedDiscreteDerivativeBlock.source (body f) (body g) x L (divisor x) (allowance (divisor x) E)) :=
  closeUniv 3 (.impI (.impI (signed_source f g _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianDiscreteDerivativeRounding
