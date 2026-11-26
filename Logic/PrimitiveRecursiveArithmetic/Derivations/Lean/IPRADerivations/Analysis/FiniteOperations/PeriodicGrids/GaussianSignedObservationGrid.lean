import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.PeriodicThirdDifferenceModulo
import IPRADerivations.Analysis.Geometry.Distances.GaussianRelativeNormTriangle
import IPRADerivations.Analysis.Logarithm.DyadicComplexLogarithm
import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalL1
import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalDistanceOrder
import IPRADerivations.Core.CongruenceTactic

/-!
# Signed lattice samples from actual Gaussian observations

Round the projected real numerator with the existing signed quotient code.
All samples share a prescribed positive denominator S. If a Gaussian
observation is within E/S of a real lattice point, the rounded numerator
is within E+1 of that point's numerator. The construction also applies
when the Gaussian observation has a nonzero imaginary component.
-/

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace LeanProofs.IPRA.Analysis.GaussianSignedObservationGrid

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (code re im scale normSq normSq_eval eval_re_code)
open DyadicComplexLogarithm (roundedCoordinate coordinate_error remainder_bound)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product represents_congr represents_rescale)
open GaussianRationalMetric (distanceBounded bounded_difference_iff)
open GaussianRootAlgebra (sub re_sub re_scale)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_congr zabs_sq)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open PolynomialBisection (zle_add zle_congr zle_scale_cancel zle_trans)
open SignedGridStepBounds (neg_order)
open PeriodicThirdDifferenceConstancy (band)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rounded (q S : PTm n) : ZT n := roundedCoordinate (re (rawGaussian q)) (rawDen q) S

def realPoint (a : ZT n) (S : PTm n) : PTm n := ofGaussian (code a (ZT.ofNat zero)) S

def clearedError (q S : PTm n) : ZT n :=
  ZT.ofNat (rawDen q)*rounded q S-ZT.ofNat S*re (rawGaussian q)

@[simp] theorem subst_rounded {m : ℕ} (σ : Fin n → PTm m) (q S : PTm n) :
    (rounded q S).subst σ = rounded (Syn.subst σ q) (Syn.subst σ S) := by simp [rounded]

@[simp] private theorem subst_rounded_pos {m : ℕ} (σ : Fin n → PTm m) (q S : PTm n) :
    Syn.subst σ (rounded q S).pos = (rounded (Syn.subst σ q) (Syn.subst σ S)).pos :=
  congrArg ZT.pos (subst_rounded σ q S)

@[simp] private theorem subst_rounded_neg {m : ℕ} (σ : Fin n → PTm m) (q S : PTm n) :
    Syn.subst σ (rounded q S).neg = (rounded (Syn.subst σ q) (Syn.subst σ S)).neg :=
  congrArg ZT.neg (subst_rounded σ q S)

@[simp] theorem subst_realPoint {m : ℕ} (σ : Fin n → PTm m) (a : ZT n) (S : PTm n) :
    Syn.subst σ (realPoint a S) = realPoint (a.subst σ) (Syn.subst σ S) := by simp [realPoint]

private theorem signed_band_of_absolute (a : ZT n) (E : PTm n)
    (h : Γ ⊢[PRAAx] le (zabs a) E) : Γ ⊢[PRAAx] band a E := by
  have hn : Γ ⊢[PRAAx] zle (ZT.ofNat (zabs a)) (ZT.ofNat E) :=
    le_congr (add_zero _).eqSymm (add_zero _).eqSymm h
  have upper := zle_trans (GaussianRelativeNormTriangle.signed_le_absolute a) hn
  have e : Γ ⊢[PRAAx] zabs (-a) ≐ zabs a := Foundations.GapDecision.zabs_neg a
  have lower := neg_order (zle_trans (GaussianRelativeNormTriangle.signed_le_absolute (-a))
    (zle_congr (by rw [ZT.toZ_ofNat,ZT.toZ_ofNat,natEq e]) rfl hn))
  exact .andI (zle_congr rfl (by simp only [ZT.toZ_neg,neg_neg]) lower) upper

theorem rounding_error (q S : PTm n) :
    Γ ⊢[PRAAx] le (zabs (clearedError q S)) (rawDen q) := by
  let a := re (rawGaussian q)
  let D := rawDen q
  have e : ZT.toZ Γ (clearedError q S) = ZT.toZ Γ (DyadicComplexLogarithm.remainderCoordinate a D S) := by
    simpa only [clearedError,rounded,ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_ofNat] using
      coordinate_error (Γ := Γ) a D S (raw_den_positive q)
  exact le_congr (zabs_congr e).eqSymm (.eqRefl _) (remainder_bound a D S (raw_den_positive q))

theorem rounding_band (q S : PTm n) : Γ ⊢[PRAAx] band (clearedError q S) (rawDen q) :=
  signed_band_of_absolute _ _ (rounding_error q S)

private theorem real_abs_square (a : PTm n) :
    Γ ⊢[PRAAx] le (zabs (re a)*zabs (re a)) (normSq a) := by
  apply le_of_eq_add (d := zabs (im a)*zabs (im a))
  apply deriveNat
  rw [Q.mk_add,map_add,normSq_eval,zabs_sq,zabs_sq]
  simp only [pow_two]

private theorem original_coordinate_error (q : PTm n) (a : ZT n) (S E : PTm n)
    (hS : Γ ⊢[PRAAx] le one S) (h : Γ ⊢[PRAAx] distanceBounded q (realPoint a S) E S) :
    Γ ⊢[PRAAx] band (ZT.ofNat S*re (rawGaussian q)-ZT.ofNat (rawDen q)*a) (rawDen q*E) := by
  let D := rawDen q
  let Q := rawGaussian q
  let y := code a (ZT.ofNat zero)
  let d := sub (scale S Q) (scale D y)
  have hD := raw_den_positive (Γ := Γ) q
  have hq := represents_rescale q Q D S (raw_represents (Γ := Γ) q)
  have hy0 := represents_rescale (realPoint a S) y S D (ofGaussian_represents y S hS)
  have hy := represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (mul_comm S D) hy0
  have raw : Γ ⊢[PRAAx] le ((S*S)*normSq d) ((E*E)*((D*S)*(D*S))) :=
    (bounded_difference_iff _ _ _ _ _ _ _ (positive_product D S hD hS) hS hq hy).iffMp h
  have square : Γ ⊢[PRAAx] le ((S*zabs (re d))*(S*zabs (re d))) ((S*(D*E))*(S*(D*E))) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (le_trans (le_mul_mono (le_refl (S*S)) (real_abs_square d)) raw)
  have small := RationalValueBounds.positive_cancel hS (nat_sqrt_mono square)
  have eq : ZT.toZ Γ (re d) = ZT.toZ Γ (ZT.ofNat S*re Q-ZT.ofNat D*a) := by
    simp only [d,y,re_sub,re_scale,eval_re_code,ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_ofNat]
  exact signed_band_of_absolute _ _
    (le_congr (zabs_congr eq) (.eqRefl _) small)

/-- An actual observation incurs at most one additional lattice unit. -/
theorem near_lattice (q : PTm n) (a : ZT n) (S E : PTm n)
    (hS : Γ ⊢[PRAAx] le one S) (h : Γ ⊢[PRAAx] distanceBounded q (realPoint a S) E S) :
    Γ ⊢[PRAAx] band (rounded q S-a) (E+one) := by
  let D := rawDen q
  let d := rounded q S-a
  have rb := rounding_band (Γ := Γ) q S
  have cb := original_coordinate_error q a S E hS h
  have sum := zle_add rb.andE₁ cb.andE₁
  have sum' := zle_add rb.andE₂ cb.andE₂
  have low : Γ ⊢[PRAAx] zle (ZT.ofNat D*(-ZT.ofNat (E+one))) (ZT.ofNat D*d) := by
    refine zle_congr ?_ ?_ sum
    · simp only [ZT.toZ_add,ZT.toZ_neg,ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_add,map_add,Q.mk_mul,map_mul]
      ipra_simps
      ring
    · simp only [clearedError,d,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_ofNat]
      ring
  have high : Γ ⊢[PRAAx] zle (ZT.ofNat D*d) (ZT.ofNat D*ZT.ofNat (E+one)) := by
    refine zle_congr ?_ ?_ sum'
    · simp only [clearedError,d,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_ofNat]
      ring
    · simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_add,map_add,Q.mk_mul,map_mul]
      ipra_simps
      ring
  exact .andI (zle_scale_cancel (raw_den_positive q) low) (zle_scale_cancel (raw_den_positive q) high)

theorem near_lattice_ratio (q : PTm n) (a : ZT n) (S A B E : PTm n)
    (hS : Γ ⊢[PRAAx] le one S) (hB : Γ ⊢[PRAAx] le one B)
    (hrad : Γ ⊢[PRAAx] le (A*S) (E*B)) (h : Γ ⊢[PRAAx] distanceBounded q (realPoint a S) A B) :
    Γ ⊢[PRAAx] band (rounded q S-a) (E+one) :=
  near_lattice q a S E hS (GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _ hB hS hrad h)

def data (x S : PTm n) : PTm n := pairT S x

def body (f : PTm 2) : ZB :=
  let a := rounded (inst2 f (var 0) (sndT (var 1))) (fstT (var 1))
  ⟨a.pos,a.neg⟩

theorem sample_at (f : PTm 2) (x S i : PTm n) :
    Γ ⊢[PRAAx] ZT.eq ((body f).val i (data x S)) (rounded (inst2 f i x) S) := by
  have q : Γ ⊢[PRAAx] inst2 f i (sndT (data x S)) ≐ inst2 f i x :=
    congrInst2 f (.eqRefl i) (snd_pair S x)
  have s : Γ ⊢[PRAAx] fstT (data x S) ≐ S := fst_pair S x
  have hp : Γ ⊢[PRAAx] (rounded (inst2 f i (sndT (data x S))) (fstT (data x S))).pos ≐
      (rounded (inst2 f i x) S).pos := by
    ipra_congr ((rounded (var 0) (var 1)).pos : PTm 2) with [q,s]
  have hn : Γ ⊢[PRAAx] (rounded (inst2 f i (sndT (data x S))) (fstT (data x S))).neg ≐
      (rounded (inst2 f i x) S).neg := by
    ipra_congr ((rounded (var 0) (var 1)).neg : PTm 2) with [q,s]
  let u : ZT 2 := rounded (inst2 f (var 0) (sndT (var 1))) (fstT (var 1))
  let σ : Fin 2 → PTm n := ![i,data x S]
  have e : u.subst σ = rounded (inst2 f i (sndT (data x S))) (fstT (data x S)) := by
    simp [u,σ,subst_inst2]
  apply ZT.derive
  change ZT.toZ Γ (u.subst σ) = ZT.toZ Γ (rounded (inst2 f i x) S)
  rw [e]
  simp only [ZT.toZ,natEq hp,natEq hn]

theorem wrapped_sample_at (f : PTm 2) (x S i N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    ZT.eq ((PeriodicThirdDifferenceModulo.wrapped (body f)).val i
      (PeriodicThirdDifferenceModulo.data (data x S) N)) (rounded (inst2 f i x) S) := by
  apply ZT.derive
  exact (ZT.toZ_eq (PeriodicThirdDifferenceModulo.sample_inside (body f) (data x S) N i hN hi)).trans
    (ZT.toZ_eq (sample_at f x S i))

theorem wrapped_sample_mod (f : PTm 2) (x S i N : PTm n) : Γ ⊢[PRAAx]
    ZT.eq ((PeriodicThirdDifferenceModulo.wrapped (body f)).val i
      (PeriodicThirdDifferenceModulo.data (data x S) N)) (rounded (inst2 f (rem i N) x) S) := by
  apply ZT.derive
  exact (ZT.toZ_eq (PeriodicThirdDifferenceModulo.sample_at (body f) (data x S) N i)).trans
    (ZT.toZ_eq (sample_at f x S (rem i N)))

theorem wrapped_near_lattice (f : PTm 2) (x S i N E : PTm n) (a : ZT n)
    (hS : Γ ⊢[PRAAx] le one S) (h : Γ ⊢[PRAAx] distanceBounded (inst2 f (rem i N) x) (realPoint a S) E S) :
    Γ ⊢[PRAAx] band ((PeriodicThirdDifferenceModulo.wrapped (body f)).val i
      (PeriodicThirdDifferenceModulo.data (data x S) N)-a) (E+one) := by
  have e := ZT.toZ_eq (wrapped_sample_mod (Γ := Γ) f x S i N)
  have b := near_lattice _ a S E hS h
  exact .andI (zle_congr rfl (by simp only [ZT.toZ_sub,e]) b.andE₁)
    (zle_congr (by simp only [ZT.toZ_sub,e]) rfl b.andE₂)

theorem actual_gaussian_signed_rounding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let q := var 0
     let a : ZT 5 := ⟨var 1,var 2⟩
     let S := var 3
     let E := var 4
     le one S ⟶ distanceBounded q (realPoint a S) E S ⟶ band (rounded q S-a) (E+one)) :=
  closeUniv 5 (.impI (.impI (near_lattice _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianSignedObservationGrid
