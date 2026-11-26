import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.GaussianSignedObservationGrid
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalNaturalScale
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
open GaussianSignedObservationGrid (rounded subst_rounded clearedError rounding_band)
open GaussianRationalNaturalScale (natScale natScale_represents)
open GaussianRationalHorner (represents represents_rescale represents_congr positive_product)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalMetric (distanceBounded bounded_difference_iff qsub qsub_represents)
open GaussianRootAlgebra (sub equal_refl re_sub re_scale)
open ComplexLogarithmRemainder (scale normSq normSq_eval re im)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_sq zabs_neg zabs_congr)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open PolynomialBisection (zle_add zle_congr zle_trans zle_scale zle_scale_cancel)
open SignedGridStepBounds (neg_order difference_value)
open PeriodicThirdDifferenceConstancy (band)
open SignedDiscreteDerivativeOperators (divisor subst_divisor)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def allowance (D E : PTm n) : PTm n := E+two*D+one

def signedResidual (a b g D S : PTm n) : ZT n :=
  ZT.ofNat D*(rounded b S-rounded a S)-rounded g S

private theorem band_of_absolute (z : ZT n) (E : PTm n)
    (h : Γ ⊢[PRAAx] le (zabs z) E) : Γ ⊢[PRAAx] band z E := by
  have hn : Γ ⊢[PRAAx] zle (ZT.ofNat (zabs z)) (ZT.ofNat E) :=
    le_congr (add_zero _).eqSymm (add_zero _).eqSymm h
  have a := GaussianRelativeNormTriangle.signed_le_absolute (Γ := Γ) z
  have b := GaussianRelativeNormTriangle.signed_le_absolute (Γ := Γ) (-z)
  have lower := neg_order (zle_trans b (zle_congr (by rw [ZT.toZ_ofNat,ZT.toZ_ofNat,natEq (zabs_neg z)]) rfl hn))
  exact .andI (zle_congr rfl (by simp only [ZT.toZ_neg,neg_neg]) lower) (zle_trans a hn)

private theorem real_square (z : PTm n) : Γ ⊢[PRAAx] le (zabs (re z)*zabs (re z)) (normSq z) := by
  apply le_of_eq_add (d := zabs (im z)*zabs (im z))
  apply deriveNat
  rw [Q.mk_add,map_add,normSq_eval,zabs_sq,zabs_sq]
  simp only [pow_two]

private theorem band_plus (a b : ZT n) (A B : PTm n)
    (ha : Γ ⊢[PRAAx] band a A) (hb : Γ ⊢[PRAAx] band b B) :
    Γ ⊢[PRAAx] band (a+b) (A+B) :=
  .andI (zle_congr (by simp only [ZT.toZ_add,ZT.toZ_neg,ZT.toZ_ofNat,Q.mk_add,map_add]; ring)
    rfl (zle_add ha.andE₁ hb.andE₁))
    (zle_congr rfl (by simp only [ZT.toZ_add,ZT.toZ_ofNat,Q.mk_add,map_add]) (zle_add ha.andE₂ hb.andE₂))

private theorem band_neg (a : ZT n) (A : PTm n) (h : Γ ⊢[PRAAx] band a A) :
    Γ ⊢[PRAAx] band (-a) A :=
  .andI (neg_order h.andE₂) (zle_congr rfl (by simp only [ZT.toZ_neg,neg_neg]) (neg_order h.andE₁))

private theorem band_scale (a : ZT n) (A K : PTm n) (h : Γ ⊢[PRAAx] band a A) :
    Γ ⊢[PRAAx] band (ZT.ofNat K*a) (K*A) :=
  .andI (zle_congr (by simp only [ZT.toZ_mul,ZT.toZ_neg,ZT.toZ_ofNat,Q.mk_mul,map_mul]; ring)
    rfl (zle_scale K h.andE₁))
    (zle_congr rfl (by simp only [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul]) (zle_scale K h.andE₂))

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
  have ordered : Γ ⊢[PRAAx] le ((S*zabs (re v))*(S*zabs (re v))) ((K*E)*(K*E)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (le_trans (le_mul_mono (le_refl (S*S)) (real_square v)) raw)
  have eabs : Γ ⊢[PRAAx] zabs (ZT.ofNat S*re v) ≐ S*zabs (re v) :=
    (GaussianL1.abs_multiply _ _).eqTrans (congrMul (GaussianL1.abs_ofNat S) (.eqRefl _))
  have axis : Γ ⊢[PRAAx] band (ZT.ofNat S*re v) (K*E) :=
    band_of_absolute _ _ (le_congr eabs.eqSymm (.eqRefl _) (nat_sqrt_mono ordered))
  have next := band_scale _ _ (D*(A*C)) (rounding_band (Γ := Γ) b S)
  have prev := band_scale _ _ (D*(B*C)) (band_neg _ _ (rounding_band (Γ := Γ) a S))
  have deriv := band_scale _ _ (A*B) (band_neg _ _ (rounding_band (Γ := Γ) g S))
  have total := band_plus _ _ _ _ (band_plus _ _ _ _ (band_plus _ _ _ _ axis next) prev) deriv
  let target := ZT.ofNat K*signedResidual a b g D S
  have shiftLower : Γ ⊢[PRAAx] zle (ZT.ofNat K*(-ZT.ofNat (allowance D E))) target := by
    refine zle_congr ?_ ?_ total.andE₁
    · simp only [allowance,K,A,B,C,ZT.toZ_mul,ZT.toZ_neg,ZT.toZ_ofNat,Q.mk_add,map_add,Q.mk_mul,map_mul]
      ipra_simps
      ring
    · simp only [target,signedResidual,clearedError,v,d,b',a',g',K,A,B,C,
        re_sub,re_scale,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_neg,ZT.toZ_ofNat,Q.mk_mul,map_mul]
      ring
  have shiftUpper : Γ ⊢[PRAAx] zle target (ZT.ofNat K*ZT.ofNat (allowance D E)) := by
    refine zle_congr ?_ ?_ total.andE₂
    · simp only [target,signedResidual,clearedError,v,d,b',a',g',K,A,B,C,
        re_sub,re_scale,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_neg,ZT.toZ_ofNat,Q.mk_mul,map_mul]
      ring
    · simp only [allowance,K,A,B,C,ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_add,map_add,Q.mk_mul,map_mul]
      ipra_simps
      ring
  exact .andI (zle_scale_cancel hK shiftLower) (zle_scale_cancel hK shiftUpper)

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
    .andI (zle_congr rfl he band'.andE₁) (zle_congr he rfl band'.andE₂)
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
