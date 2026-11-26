import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalDirectionConstruction
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianDominantAlpha
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalRelativeNormAlgebra
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Core.LinearCombination

/-!
# Actual Gaussian algebra for the dominant constant/coefficient pair

The radius is an actual real Gaussian-rational code. Its numerical powers
and multiplication by the computed unit direction are verified through
the original normalizing programs. Every coefficient, radius and exponent
is internal; zero radii and degree zero remain valid algebraic inputs.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianDominantPairAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (code normSq scale oneCode)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (ofGaussian qadd qmul represents positive_product represents_congr canonical_unique)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal
  (power powerF qone power_zero power_succ bound_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def radiusNumerator (A : PTm n) : PTm n := code (ZT.ofNat A) (ZT.ofNat zero)
def radiusPoint (A B : PTm n) : PTm n := ofGaussian (radiusNumerator A) B
def delta (A B w : PTm n) : PTm n := qmul (radiusPoint A B) w
def radialTerm (bk A B k : PTm n) : PTm n := qmul bk (power (radiusPoint A B) k)
def dominantTerm (bk A B w k : PTm n) : PTm n := qmul bk (power (delta A B w) k)

@[simp] theorem subst_radiusNumerator {m : ℕ} (σ : Fin n → PTm m) (A : PTm n) :
    Syn.subst σ (radiusNumerator A) = radiusNumerator (Syn.subst σ A) := by simp [radiusNumerator]
@[simp] theorem subst_radiusPoint {m : ℕ} (σ : Fin n → PTm m) (A B : PTm n) :
    Syn.subst σ (radiusPoint A B) = radiusPoint (Syn.subst σ A) (Syn.subst σ B) := by simp [radiusPoint]
@[simp] theorem subst_delta {m : ℕ} (σ : Fin n → PTm m) (A B w : PTm n) :
    Syn.subst σ (delta A B w) = delta (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ w) := by simp [delta]
@[simp] theorem subst_radialTerm {m : ℕ} (σ : Fin n → PTm m) (bk A B k : PTm n) :
    Syn.subst σ (radialTerm bk A B k) = radialTerm (Syn.subst σ bk) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) := by simp [radialTerm]
@[simp] theorem subst_dominantTerm {m : ℕ} (σ : Fin n → PTm m) (bk A B w k : PTm n) :
    Syn.subst σ (dominantTerm bk A B w k) = dominantTerm (Syn.subst σ bk) (Syn.subst σ A) (Syn.subst σ B)
      (Syn.subst σ w) (Syn.subst σ k) := by simp [dominantTerm]

theorem radius_congr {A B C D : PTm n} (hA : Γ ⊢[PRAAx] A ≐ C) (hB : Γ ⊢[PRAAx] B ≐ D) :
    Γ ⊢[PRAAx] radiusPoint A B ≐ radiusPoint C D := by
  ipra_congr (radiusPoint (var 0) (var 1) : PTm 2) with [hA, hB]

theorem radius_represents (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    represents (radiusPoint A B) (radiusNumerator A) B := GaussianRationalHorner.ofGaussian_represents _ _ hB

theorem radius_numerator_norm (A : PTm n) : Γ ⊢[PRAAx] normSq (radiusNumerator A) ≐ A*A := by
  apply deriveNat
  rw [radiusNumerator,ComplexLogarithmRemainder.normSq_code]
  simp only [ZT.toZ_ofNat]
  ipra_simps
  ring

theorem radius_bounded (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] bounded (radiusPoint A B) A B := by
  apply GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ hB hB (radius_represents A B hB)
  exact le_congr ((congrMul (.eqRefl _) (radius_numerator_norm A)).eqTrans (by ipra_ring)).eqSymm
    (.eqRefl _) (le_refl _)

theorem radius_multiply (A B C D : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    qmul (radiusPoint A B) (radiusPoint C D) ≐ radiusPoint (A*C) (B*D) := by
  have bd := positive_product B D hB hD
  apply canonical_unique _ _ _ _ (GaussianRationalHorner.qmul_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ bd) bd
    (hrv := radius_represents (A*C) (B*D) bd)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _)
    (h := GaussianRationalHorner.qmul_represents _ _ _ _ _ _ hB hD (radius_represents A B hB) (radius_represents C D hD))
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [radiusNumerator,GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,
      ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat] <;> ipra_simps <;> ring

theorem radius_one : Γ ⊢[PRAAx] radiusPoint (one : PTm n) one ≐ qone := .eqRefl _

def powerLaw (A B k : PTm n) : Fm PTm n := power (radiusPoint A B) k ≐ radiusPoint (pw A k) (pw B k)
@[simp] theorem subst_powerLaw {m : ℕ} (σ : Fin n → PTm m) (A B k : PTm n) :
    (powerLaw A B k).subst σ = powerLaw (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) := by simp [powerLaw]

theorem radius_power (A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    power (radiusPoint A B) k ≐ radiusPoint (pw A k) (pw B k) := by
  have bShift : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hB.shift
  have all : Γ ⊢[PRAAx] .all (powerLaw (Syn.shift A) (Syn.shift B) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_powerLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (power_zero _).eqTrans ((radius_congr (pw_zero A) (pw_zero B)).eqTrans radius_one).eqSymm
    · simp only [subst_powerLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact (power_succ _ _).eqTrans ((qmul_congr Prf.hyp0 (.eqRefl _)).eqTrans
        ((radius_multiply _ _ _ _ (GaussianPolynomialPerturbation.power_positive _ _ bShift.wk) bShift.wk).eqTrans
          (radius_congr (pw_succ _ _).eqSymm (pw_succ _ _).eqSymm)))
  change Γ ⊢[PRAAx] powerLaw A B k
  simpa only [subst_powerLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

theorem radius_power_represents (A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    represents (power (radiusPoint A B) k) (radiusNumerator (pw A k)) (pw B k) :=
  represents_congr (radius_power A B k hB).eqSymm (GaussianRootAlgebra.equal_refl _) (.eqRefl _)
    (radius_represents _ _ (GaussianPolynomialPerturbation.power_positive _ _ hB))

theorem within_radius (A B w : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hUnit : Γ ⊢[PRAAx] GaussianRationalHalfAngle.unit w) : Γ ⊢[PRAAx] bounded (delta A B w) A B :=
  bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ hB (le_refl one)
      (radius_bounded A B hB) (GaussianRationalPowerAlgebra.unit_bounded w hUnit))

theorem term_identity (bk A B w k : PTm n) : Γ ⊢[PRAAx]
    dominantTerm bk A B w k ≐ qmul (radialTerm bk A B k) (power w k) :=
  (qmul_congr (.eqRefl _) (GaussianRationalPowerAlgebra.power_product (radiusPoint A B) w k)).eqTrans
    (GaussianReciprocalHorner.qmul_associative bk (power (radiusPoint A B) k) (power w k)).eqSymm

theorem radial_represents (bk A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    represents (radialTerm bk A B k) (scale (pw A k) (rawGaussian bk)) (rawDen bk*pw B k) := by
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _)
    (h := GaussianRationalHorner.qmul_represents _ _ _ _ _ _ (raw_den_positive bk)
      (GaussianPolynomialPerturbation.power_positive _ _ hB) (raw_represents bk) (radius_power_represents A B k hB))
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_scale,
      GaussianRootAlgebra.im_scale,radiusNumerator,ComplexLogarithmRemainder.eval_re_code,
      ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat] <;> ipra_simps <;> ring

theorem scalar_representation_cross (q : PTm n) (a b : ZT n) (A B : PTm n)
    (ha : Γ ⊢[PRAAx] RationalArithmetic.represents q a A)
    (hb : Γ ⊢[PRAAx] RationalArithmetic.represents q b B) : Γ ⊢[PRAAx]
    ZT.eq (a*ZT.ofNat B) (b*ZT.ofNat A) := by
  apply RationalNormalForm.positive_integer_cancel (RationalSupMetric.denominatorOf q) _ _
    (RationalArgmin.denominator_positive q)
  ipra_lc [RationalArithmetic.represents] 𝔞(B)*ZT.toZ_eq ha-𝔞(A)*ZT.toZ_eq hb

theorem represents_cross (q a b A B : PTm n) (ha : Γ ⊢[PRAAx] represents q a A)
    (hb : Γ ⊢[PRAAx] represents q b B) : Γ ⊢[PRAAx]
    GaussianRootAlgebra.equal (scale B a) (scale A b) := by
  apply GaussianRootAlgebra.equal_of_values
  · have e := ZT.toZ_eq (scalar_representation_cross _ _ _ _ _ (Prf.andE₁ ha) (Prf.andE₁ hb))
    simp only [ZT.toZ_mul,ZT.toZ_ofNat] at e
    simp only [GaussianRootAlgebra.re_scale]
    linear_combination e
  · have e := ZT.toZ_eq (scalar_representation_cross _ _ _ _ _ (Prf.andE₂ ha) (Prf.andE₂ hb))
    simp only [ZT.toZ_mul,ZT.toZ_ofNat] at e
    simp only [GaussianRootAlgebra.im_scale]
    linear_combination e

theorem phase_cross_value (b0 bk : PTm n) : Γ ⊢[PRAAx]
    GaussianRootAlgebra.equal
      (scale (rawDen b0*rawDen bk) (rawGaussian (GaussianDominantAlpha.phase b0 bk)))
      (scale (rawDen (GaussianDominantAlpha.phase b0 bk))
        (ComplexLogarithmRemainder.neg (ComplexLogarithmRemainder.mul (rawGaussian b0)
          (GaussianRationalReciprocal.conjugate (rawGaussian bk))))) :=
  represents_cross _ _ _ _ _ (raw_represents _) (GaussianDominantAlpha.phase_represents b0 bk)

theorem phase_product_value (b0 bk : PTm n) : Γ ⊢[PRAAx]
    GaussianRootAlgebra.equal
      (scale (rawDen b0*rawDen bk) (ComplexLogarithmRemainder.mul (rawGaussian bk)
        (rawGaussian (GaussianDominantAlpha.phase b0 bk))))
      (ComplexLogarithmRemainder.neg (scale
        (rawDen (GaussianDominantAlpha.phase b0 bk)*normSq (rawGaussian bk)) (rawGaussian b0))) := by
  have er := GaussianRootAlgebra.equal_re (phase_cross_value (Γ := Γ) b0 bk)
  have ei := GaussianRootAlgebra.equal_im (phase_cross_value (Γ := Γ) b0 bk)
  apply GaussianRootAlgebra.equal_of_values
  all_goals
    simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_mul,
      GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.im_neg,
      GaussianRationalReciprocal.re_conjugate,GaussianRationalReciprocal.im_conjugate] at er ei ⊢
    ipra_simps
    rw [ComplexLogarithmRemainder.normSq_eval]
  · linear_combination ZT.toZ Γ (ComplexLogarithmRemainder.re (rawGaussian bk))*er-
      ZT.toZ Γ (ComplexLogarithmRemainder.im (rawGaussian bk))*ei
  · linear_combination ZT.toZ Γ (ComplexLogarithmRemainder.im (rawGaussian bk))*er+
      ZT.toZ Γ (ComplexLogarithmRemainder.re (rawGaussian bk))*ei

def alphaPoint (b0 bk A B k H : PTm n) : PTm n :=
  radiusPoint (GaussianDominantAlpha.P b0 bk A k H) (GaussianDominantAlpha.Q b0 bk B k H)
def phaseTarget (b0 bk H : PTm n) : PTm n :=
  GaussianRationalDirectionNormalizer.target (GaussianDominantAlpha.phase b0 bk) H

@[simp] theorem subst_alphaPoint {m : ℕ} (σ : Fin n → PTm m) (b0 bk A B k H : PTm n) :
    Syn.subst σ (alphaPoint b0 bk A B k H) = alphaPoint (Syn.subst σ b0) (Syn.subst σ bk)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) (Syn.subst σ H) := by simp [alphaPoint]
@[simp] theorem subst_phaseTarget {m : ℕ} (σ : Fin n → PTm m) (b0 bk H : PTm n) :
    Syn.subst σ (phaseTarget b0 bk H) = phaseTarget (Syn.subst σ b0) (Syn.subst σ bk) (Syn.subst σ H) := by simp [phaseTarget]

/-- Exact cancellation against the actual computed normalized phase.
Only the radius denominator is guarded; zero coefficients/radii/exponents
and zero H remain legitimate total algebraic cases. -/
theorem target_product (b0 bk A B k H : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qmul (radialTerm bk A B k) (phaseTarget b0 bk H) ≐
      GaussianRationalMetric.qnegative (qmul (alphaPoint b0 bk A B k H) b0) := by
  let c := GaussianDominantAlpha.phase b0 bk
  let f := GaussianRationalDirectionNormalizer.factor c H
  let s := GaussianRationalDirectionNormalizer.S c H
  let L := (rawDen bk*pw B k)*s
  let R := GaussianDominantAlpha.Q b0 bk B k H*rawDen b0
  have hs := GaussianRationalDirectionNormalizer.S_positive (Γ := Γ) c H
  have bp := GaussianPolynomialPerturbation.power_positive (Γ := Γ) B k hB
  have hQ : Γ ⊢[PRAAx] le one (GaussianDominantAlpha.Q b0 bk B k H) :=
    positive_product _ _ (positive_product _ _ bp (positive_product _ _ (raw_den_positive bk) (raw_den_positive bk))) hs
  have hL : Γ ⊢[PRAAx] le one L := positive_product _ _ (positive_product _ _ (raw_den_positive bk) bp) hs
  have hR : Γ ⊢[PRAAx] le one R := positive_product _ _ hQ (raw_den_positive b0)
  have left := GaussianRationalHorner.qmul_represents _ _ _ _ _ _
    (positive_product _ _ (raw_den_positive bk) bp) hs (radial_represents bk A B k hB)
    (GaussianRationalDirectionNormalizer.target_represents c H)
  have right := GaussianRationalMetric.qnegative_represents _ _ _
    (GaussianRationalHorner.qmul_represents _ _ _ _ _ _ hQ (raw_den_positive b0)
      (radius_represents (GaussianDominantAlpha.P b0 bk A k H) (GaussianDominantAlpha.Q b0 bk B k H) hQ) (raw_represents b0))
  have lhs := GaussianRationalHorner.represents_rescale _ _ _ R left
  have rhs := represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (mul_comm R L)
    (GaussianRationalHorner.represents_rescale _ _ _ L right)
  apply canonical_unique _ _ _ _ (GaussianRationalHorner.qmul_canonical _ _)
    (GaussianRationalMetric.qnegative_canonical _) (positive_product _ _ hL hR) (hrv := rhs)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
  have er := GaussianRootAlgebra.equal_re (phase_product_value (Γ := Γ) b0 bk)
  have ei := GaussianRootAlgebra.equal_im (phase_product_value (Γ := Γ) b0 bk)
  apply GaussianRootAlgebra.equal_of_values
  all_goals
    simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_mul,
      GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.im_neg,
      radiusNumerator,ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,
      ZT.toZ_ofNat] at er ei ⊢
    simp only [R,L,s,f,c,GaussianDominantAlpha.Q,GaussianDominantAlpha.P,
      GaussianRationalDirectionNormalizer.norm]
    ipra_simps
  · linear_combination 𝔞(pw A k)*𝔞(GaussianRationalDirectionNormalizer.factor (GaussianDominantAlpha.phase b0 bk) H)*
      𝔞(rawDen bk)*𝔞(pw B k)*𝔞(GaussianRationalDirectionNormalizer.S (GaussianDominantAlpha.phase b0 bk) H)*er
  · linear_combination 𝔞(pw A k)*𝔞(GaussianRationalDirectionNormalizer.factor (GaussianDominantAlpha.phase b0 bk) H)*
      𝔞(rawDen bk)*𝔞(pw B k)*𝔞(GaussianRationalDirectionNormalizer.S (GaussianDominantAlpha.phase b0 bk) H)*ei

theorem split_pair_from_representations (b t u v G T U V E : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hb : Γ ⊢[PRAAx] represents b G E)
    (ht : Γ ⊢[PRAAx] represents t T E) (hu : Γ ⊢[PRAAx] represents u U E)
    (hv : Γ ⊢[PRAAx] represents v V E) : Γ ⊢[PRAAx]
    qadd b (qmul t u) ≐ qadd (qadd b (qmul t v)) (qmul t (GaussianRationalMetric.qsub u v)) := by
  have e2 := positive_product E E hE hE
  have br := GaussianRationalHorner.represents_rescale b G E E hb
  have lhs := GaussianRationalHorner.qadd_represents _ _ _ _ _ e2 br
    (GaussianRationalHorner.qmul_represents _ _ _ _ _ _ hE hE ht hu)
  have rhs := GaussianRationalHorner.qadd_represents _ _ _ _ _ e2
    (GaussianRationalHorner.qadd_represents _ _ _ _ _ e2 br
      (GaussianRationalHorner.qmul_represents _ _ _ _ _ _ hE hE ht hv))
    (GaussianRationalHorner.qmul_represents _ _ _ _ _ _ hE hE ht
      (GaussianRationalMetric.qsub_represents _ _ _ _ _ hE hu hv))
  apply canonical_unique _ _ _ _ (GaussianRationalHorner.qadd_canonical _ _)
    (GaussianRationalHorner.qadd_canonical _ _) e2 (hrv := rhs)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,GaussianRootAlgebra.re_mul,
      GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
      GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub] <;> ring

theorem split_pair (b t u v : PTm n) : Γ ⊢[PRAAx]
    qadd b (qmul t u) ≐ qadd (qadd b (qmul t v)) (qmul t (GaussianRationalMetric.qsub u v)) := by
  let E := GaussianRationalSyntheticDivision.remainingDen b t u v
  have hb := GaussianRationalSyntheticDivision.rescale_to b (rawGaussian b) (rawDen b)
    (rawDen t*rawDen u*rawDen v) E (raw_represents (Γ := Γ) b) (by unfold E GaussianRationalSyntheticDivision.remainingDen; ipra_ring)
  have ht := GaussianRationalSyntheticDivision.rescale_to t (rawGaussian t) (rawDen t)
    (rawDen b*rawDen u*rawDen v) E (raw_represents (Γ := Γ) t) (by unfold E GaussianRationalSyntheticDivision.remainingDen; ipra_ring)
  have hu := GaussianRationalSyntheticDivision.rescale_to u (rawGaussian u) (rawDen u)
    (rawDen b*rawDen t*rawDen v) E (raw_represents (Γ := Γ) u) (by unfold E GaussianRationalSyntheticDivision.remainingDen; ipra_ring)
  have hv := GaussianRationalSyntheticDivision.rescale_to v (rawGaussian v) (rawDen v)
    (rawDen b*rawDen t*rawDen u) E (raw_represents (Γ := Γ) v) (by unfold E GaussianRationalSyntheticDivision.remainingDen; ipra_ring)
  exact split_pair_from_representations _ _ _ _ _ _ _ _ E
    (GaussianRationalSyntheticDivision.remaining_den_positive b t u v) hb ht hu hv

theorem one_minus_multiply_from_representations (a b A G E : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (ha : Γ ⊢[PRAAx] represents a A E)
    (hb : Γ ⊢[PRAAx] represents b G E) : Γ ⊢[PRAAx]
    qmul (GaussianRationalMetric.qsub qone a) b ≐ qadd b (GaussianRationalMetric.qnegative (qmul a b)) := by
  have e2 := positive_product E E hE hE
  have lhs := GaussianRationalHorner.qmul_represents _ _ _ _ _ _ hE hE
    (GaussianRationalMetric.qsub_represents _ _ _ _ _ hE (GaussianRationalReciprocal.qone_represents_scaled E) ha) hb
  have rhs := GaussianRationalHorner.qadd_represents _ _ _ _ _ e2
    (GaussianRationalHorner.represents_rescale _ _ _ E hb)
    (GaussianRationalMetric.qnegative_represents _ _ _ (GaussianRationalHorner.qmul_represents _ _ _ _ _ _ hE hE ha hb))
  apply canonical_unique _ _ _ _ (GaussianRationalHorner.qmul_canonical _ _)
    (GaussianRationalHorner.qadd_canonical _ _) e2 (hrv := rhs)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,GaussianRootAlgebra.re_mul,
      GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
      GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_neg,
      GaussianRootAlgebra.im_neg,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> ring

theorem one_minus_multiply (a b : PTm n) : Γ ⊢[PRAAx]
    qmul (GaussianRationalMetric.qsub qone a) b ≐ qadd b (GaussianRationalMetric.qnegative (qmul a b)) := by
  let E := rawDen a*rawDen b
  have ha := GaussianRationalSyntheticDivision.rescale_to a (rawGaussian a) (rawDen a) (rawDen b) E
    (raw_represents (Γ := Γ) a) (.eqRefl _)
  have hb := GaussianRationalSyntheticDivision.rescale_to b (rawGaussian b) (rawDen b) (rawDen a) E
    (raw_represents (Γ := Γ) b) (by unfold E; ipra_ring)
  exact one_minus_multiply_from_representations _ _ _ _ E
    (positive_product _ _ (raw_den_positive a) (raw_den_positive b)) ha hb

def errorTerm (b0 bk A B w k H : PTm n) : PTm n :=
  qmul (radialTerm bk A B k) (GaussianRationalMetric.qsub (power w k) (phaseTarget b0 bk H))
@[simp] theorem subst_errorTerm {m : ℕ} (σ : Fin n → PTm m) (b0 bk A B w k H : PTm n) :
    Syn.subst σ (errorTerm b0 bk A B w k H) = errorTerm (Syn.subst σ b0) (Syn.subst σ bk)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ w) (Syn.subst σ k) (Syn.subst σ H) := by simp [errorTerm]

theorem algebraic_decomposition (b0 bk A B w k H : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qadd b0 (dominantTerm bk A B w k) ≐
      qadd (qmul (GaussianRationalMetric.qsub qone (alphaPoint b0 bk A B k H)) b0) (errorTerm b0 bk A B w k H) :=
  (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (term_identity bk A B w k)).eqTrans
    ((split_pair b0 (radialTerm bk A B k) (power w k) (phaseTarget b0 bk H)).eqTrans
      (GaussianRationalSyntheticDivision.qadd_congr
        ((GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (target_product b0 bk A B k H hB)).eqTrans
          (one_minus_multiply (alphaPoint b0 bk A B k H) b0).eqSymm) (.eqRefl _)))

theorem one_minus_radius_scaled (P Q b0 : PTm n) (hQ : Γ ⊢[PRAAx] le one Q)
    (hPQ : Γ ⊢[PRAAx] le P Q) : Γ ⊢[PRAAx]
    qmul (GaussianRationalMetric.qsub qone (radiusPoint P Q)) b0 ≐
      GaussianRationalRelativeNormAlgebra.scaledPoint (monus Q P) Q b0 := by
  have d := raw_den_positive (Γ := Γ) b0
  have qd := positive_product Q (rawDen b0) hQ d
  have lhs := GaussianRationalHorner.qmul_represents _ _ _ _ _ _ hQ d
    (GaussianRationalMetric.qsub_represents _ _ _ _ _ hQ (GaussianRationalReciprocal.qone_represents_scaled Q)
      (radius_represents P Q hQ)) (raw_represents b0)
  apply canonical_unique _ _ _ _ (GaussianRationalHorner.qmul_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ qd) qd
    (hrv := GaussianRationalHorner.ofGaussian_represents _ _ qd)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
  have e := natEq (eq_add_of_le hPQ)
  apply GaussianRootAlgebra.equal_of_values
  all_goals
    simp only [GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_sub,
      GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
      GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,radiusNumerator,
      ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat]
    ipra_simps
  · linear_combination ZT.toZ Γ (ComplexLogarithmRemainder.re (rawGaussian b0))*e
  · linear_combination ZT.toZ Γ (ComplexLogarithmRemainder.im (rawGaussian b0))*e

def mainTerm (b0 bk A B k H : PTm n) : PTm n :=
  GaussianRationalRelativeNormAlgebra.scaledPoint
    (monus (GaussianDominantAlpha.Q b0 bk B k H) (GaussianDominantAlpha.P b0 bk A k H))
    (GaussianDominantAlpha.Q b0 bk B k H) b0
def direction (b0 bk k : PTm n) : PTm n :=
  GaussianRationalDirectionConstruction.direction (GaussianDominantAlpha.phase b0 bk) k (num 16)
def actualDelta (b0 bk A B k : PTm n) : PTm n := delta A B (direction b0 bk k)
def height (k : PTm n) : PTm n := GaussianRationalDirectionClock.height k (num 16)

@[simp] theorem subst_mainTerm {m : ℕ} (σ : Fin n → PTm m) (b0 bk A B k H : PTm n) :
    Syn.subst σ (mainTerm b0 bk A B k H) = mainTerm (Syn.subst σ b0) (Syn.subst σ bk)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) (Syn.subst σ H) := by simp [mainTerm]
@[simp] theorem subst_direction {m : ℕ} (σ : Fin n → PTm m) (b0 bk k : PTm n) :
    Syn.subst σ (direction b0 bk k) = direction (Syn.subst σ b0) (Syn.subst σ bk) (Syn.subst σ k) := by simp [direction]
@[simp] theorem subst_actualDelta {m : ℕ} (σ : Fin n → PTm m) (b0 bk A B k : PTm n) :
    Syn.subst σ (actualDelta b0 bk A B k) = actualDelta (Syn.subst σ b0) (Syn.subst σ bk)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) := by simp [actualDelta]
@[simp] theorem subst_height {m : ℕ} (σ : Fin n → PTm m) (k : PTm n) :
    Syn.subst σ (height k) = height (Syn.subst σ k) := by simp [height]

theorem pair_decomposition (b0 bk A B w k H : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hPQ : Γ ⊢[PRAAx] le (GaussianDominantAlpha.P b0 bk A k H) (GaussianDominantAlpha.Q b0 bk B k H)) : Γ ⊢[PRAAx]
    qadd b0 (dominantTerm bk A B w k) ≐ qadd (mainTerm b0 bk A B k H) (errorTerm b0 bk A B w k H) :=
  (algebraic_decomposition b0 bk A B w k H hB).eqTrans
    (GaussianRationalSyntheticDivision.qadd_congr
      (one_minus_radius_scaled _ _ _ (GaussianDominantAlpha.denominator_positive b0 bk B k H hB) hPQ) (.eqRefl _))

theorem actual_within_radius (b0 bk A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    bounded (actualDelta b0 bk A B k) A B :=
  within_radius A B (direction b0 bk k) hB (GaussianRationalDirectionConstruction.output_unit _ _ _)

theorem actual_pair_decomposition (b0 bk A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hPQ : Γ ⊢[PRAAx] le (GaussianDominantAlpha.P b0 bk A k (height k)) (GaussianDominantAlpha.Q b0 bk B k (height k))) : Γ ⊢[PRAAx]
    qadd b0 (qmul bk (power (actualDelta b0 bk A B k) k)) ≐
      qadd (mainTerm b0 bk A B k (height k)) (errorTerm b0 bk A B (direction b0 bk k) k (height k)) :=
  pair_decomposition b0 bk A B (direction b0 bk k) k (height k) hB hPQ

def output (b0 bk A B k : PTm n) : PTm n := pairT (actualDelta b0 bk A B k)
  (pairT (mainTerm b0 bk A B k (height k))
    (pairT (errorTerm b0 bk A B (direction b0 bk k) k (height k))
      (pairT (GaussianDominantAlpha.P b0 bk A k (height k)) (GaussianDominantAlpha.Q b0 bk B k (height k)))))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (b0 bk A B k : PTm n) : PTm n := PTm.app outputF ![b0,bk,A,B,k]

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (b0 bk A B k : PTm n) :
    Syn.subst σ (output b0 bk A B k) = output (Syn.subst σ b0) (Syn.subst σ bk)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (b0 bk A B k : PTm n) :
    Syn.subst σ (run b0 bk A B k) = run (Syn.subst σ b0) (Syn.subst σ bk)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (b0 bk A B k : PTm n) : Γ ⊢[PRAAx] run b0 bk A B k ≐ output b0 bk A B k := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![b0,bk,A,B,k]
theorem returned_delta (b0 bk A B k : PTm n) : Γ ⊢[PRAAx] fstT (run b0 bk A B k) ≐ actualDelta b0 bk A B k :=
  (congrFst (program_at b0 bk A B k)).eqTrans (fst_pair _ _)
theorem returned_main (b0 bk A B k : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run b0 bk A B k)) ≐ mainTerm b0 bk A B k (height k) :=
  (congrFst ((congrSnd (program_at b0 bk A B k)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_error (b0 bk A B k : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run b0 bk A B k))) ≐ errorTerm b0 bk A B (direction b0 bk k) k (height k) :=
  (congrFst ((congrSnd ((congrSnd (program_at b0 bk A B k)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_numerator (b0 bk A B k : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (run b0 bk A B k)))) ≐ GaussianDominantAlpha.P b0 bk A k (height k) :=
  (congrFst ((congrSnd ((congrSnd ((congrSnd (program_at b0 bk A B k)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_denominator (b0 bk A B k : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (sndT (run b0 bk A B k)))) ≐ GaussianDominantAlpha.Q b0 bk B k (height k) :=
  (congrSnd ((congrSnd ((congrSnd ((congrSnd (program_at b0 bk A B k)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

def returnedCorrect (b0 bk A B k : PTm n) : Fm PTm n :=
  bounded (fstT (run b0 bk A B k)) A B ⋏
    qadd b0 (qmul bk (power (fstT (run b0 bk A B k)) k)) ≐
      qadd (fstT (sndT (run b0 bk A B k))) (fstT (sndT (sndT (run b0 bk A B k))))
@[simp] theorem subst_returnedCorrect {m : ℕ} (σ : Fin n → PTm m) (b0 bk A B k : PTm n) :
    (returnedCorrect b0 bk A B k).subst σ = returnedCorrect (Syn.subst σ b0) (Syn.subst σ bk)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) := by simp [returnedCorrect]

theorem returned_decomposition (b0 bk A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hPQ : Γ ⊢[PRAAx] le (GaussianDominantAlpha.P b0 bk A k (height k)) (GaussianDominantAlpha.Q b0 bk B k (height k))) : Γ ⊢[PRAAx]
    bounded (fstT (run b0 bk A B k)) A B ⋏
      qadd b0 (qmul bk (power (fstT (run b0 bk A B k)) k)) ≐
        qadd (fstT (sndT (run b0 bk A B k))) (fstT (sndT (sndT (run b0 bk A B k)))) := by
  have lhs := GaussianRationalSyntheticDivision.qadd_congr (Γ := Γ) (.eqRefl b0)
    (qmul_congr (.eqRefl bk) (congrAp2 powerF (.eqRefl k) (returned_delta b0 bk A B k)))
  exact .andI (bound_congr (returned_delta b0 bk A B k).eqSymm (.eqRefl _) (.eqRefl _)
      (actual_within_radius b0 bk A B k hB))
    (lhs.eqTrans ((actual_pair_decomposition b0 bk A B k hB hPQ).eqTrans
      (GaussianRationalSyntheticDivision.qadd_congr (returned_main b0 bk A B k).eqSymm (returned_error b0 bk A B k).eqSymm)))

theorem actual_radius_power_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ power (radiusPoint (var 0) (var 1)) (var 2) ≐ radiusPoint (pw (var 0) (var 2)) (pw (var 1) (var 2))) :=
  closeUniv 3 (.impI (radius_power _ _ _ Prf.hyp0))
theorem dominant_term_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (dominantTerm (var 0) (var 1) (var 2) (var 3) (var 4) ≐ qmul (radialTerm (var 0) (var 1) (var 2) (var 4)) (power (var 3) (var 4))) :=
  closeUniv 5 (term_identity _ _ _ _ _)
theorem dominant_target_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 3) ⟶ qmul (radialTerm (var 1) (var 2) (var 3) (var 4)) (phaseTarget (var 0) (var 1) (var 5)) ≐
      GaussianRationalMetric.qnegative (qmul (alphaPoint (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 0))) :=
  closeUniv 6 (.impI (target_product _ _ _ _ _ _ Prf.hyp0))
theorem dominant_pair_decomposition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 3) ⟶ le (GaussianDominantAlpha.P (var 0) (var 1) (var 2) (var 5) (var 6))
      (GaussianDominantAlpha.Q (var 0) (var 1) (var 3) (var 5) (var 6)) ⟶
        qadd (var 0) (dominantTerm (var 1) (var 2) (var 3) (var 4) (var 5)) ≐
          qadd (mainTerm (var 0) (var 1) (var 2) (var 3) (var 5) (var 6))
            (errorTerm (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))) :=
  closeUniv 7 (.impI (.impI (pair_decomposition _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_dominant_delta_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ bounded (actualDelta (var 0) (var 1) (var 2) (var 3) (var 4)) (var 2) (var 3)) :=
  closeUniv 5 (.impI (actual_within_radius _ _ _ _ _ Prf.hyp0))
theorem actual_dominant_pair_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ le (GaussianDominantAlpha.P (var 0) (var 1) (var 2) (var 4) (height (var 4)))
      (GaussianDominantAlpha.Q (var 0) (var 1) (var 3) (var 4) (height (var 4))) ⟶
        qadd (var 0) (qmul (var 1) (power (actualDelta (var 0) (var 1) (var 2) (var 3) (var 4)) (var 4))) ≐
          qadd (mainTerm (var 0) (var 1) (var 2) (var 3) (var 4) (height (var 4)))
            (errorTerm (var 0) (var 1) (var 2) (var 3) (direction (var 0) (var 1) (var 4)) (var 4) (height (var 4)))) :=
  closeUniv 5 (.impI (.impI (actual_pair_decomposition _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem dominant_pair_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (program_at _ _ _ _ _)
theorem returned_dominant_pair_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ le (GaussianDominantAlpha.P (var 0) (var 1) (var 2) (var 4) (height (var 4)))
      (GaussianDominantAlpha.Q (var 0) (var 1) (var 3) (var 4) (height (var 4))) ⟶
        returnedCorrect (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (returned_decomposition _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianDominantPairAlgebra
