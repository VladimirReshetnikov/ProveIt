import IPRADerivations.Analysis.Euler.Logarithms.ParameterRates.GaussianEulerLogarithmicPathCompactTaylor
import IPRADerivations.Analysis.Series.GaussianRationalParameterTelescope

/-!
# Actual compact path samples as finite parameter-telescope rows

One fixed two-variable term samples the original compact program at a
runtime path index and explicitly packed original data. Its forward and
slope rows retain independent requested precisions. The original path
source discharges every bounded row of the finite telescope; no local
Taylor or output estimate is supplied.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicPathCompactRows

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerLogarithmicPathCompactTaylor (point numerator denominator)
open GaussianEulerDerivativeParameterPath (increment)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalSyntheticDivision (qsub_congr qmul_congr)
open GaussianRationalParameterTelescope (localRows forward)
open GaussianRationalFiniteSum (multiply_body_at)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B A h D a C E T N : PTm n) : Fm PTm n :=
  GaussianEulerDerivativeParameterPath.source z R B A h D ⋏
    (le one E ⋏ (le one a ⋏ (le (a+C) (E*T) ⋏ le (GaussianEulerLogarithmicMultiplier.logRadius E T) N)))
def fixedData (p j z R B h D N a C E T : PTm n) : PTm n :=
  pairT (pairT (pairT p j) (pairT z R))
    (pairT (pairT (pairT B h) (pairT D N)) (pairT (pairT a C) (pairT E T)))
def bodyTerm (i x : PTm n) : PTm n := point
  (fstT (fstT (fstT x))) i (sndT (fstT (fstT x))) (fstT (sndT (fstT x))) (sndT (sndT (fstT x)))
  (fstT (fstT (fstT (sndT x)))) (sndT (fstT (fstT (sndT x))))
  (fstT (sndT (fstT (sndT x)))) (sndT (sndT (fstT (sndT x))))
  (fstT (fstT (sndT (sndT x)))) (sndT (fstT (sndT (sndT x))))
  (fstT (sndT (sndT (sndT x)))) (sndT (sndT (sndT (sndT x))))
def body : PTm 2 := bodyTerm (var 0) (var 1)
def bodyF : PR 2 := PTm.toPR body

@[simp] theorem subst_point {m : ℕ} (σ : Fin n → PTm m) (p i j z R B h D N a C E T : PTm n) :
    Syn.subst σ (point p i j z R B h D N a C E T) = point (Syn.subst σ p) (Syn.subst σ i) (Syn.subst σ j)
      (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ h) (Syn.subst σ D) (Syn.subst σ N)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) := by simp [GaussianEulerLogarithmicPathCompactTaylor.point]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B A h D a C E T N : PTm n) :
    (source z R B A h D a C E T N).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ A) (Syn.subst σ h) (Syn.subst σ D) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E)
      (Syn.subst σ T) (Syn.subst σ N) := by simp [source]
@[simp] theorem subst_fixedData {m : ℕ} (σ : Fin n → PTm m) (p j z R B h D N a C E T : PTm n) :
    Syn.subst σ (fixedData p j z R B h D N a C E T) = fixedData (Syn.subst σ p) (Syn.subst σ j) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ h) (Syn.subst σ D) (Syn.subst σ N) (Syn.subst σ a)
      (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) := by simp [fixedData]
@[simp] theorem subst_bodyTerm {m : ℕ} (σ : Fin n → PTm m) (i x : PTm n) :
    Syn.subst σ (bodyTerm i x) = bodyTerm (Syn.subst σ i) (Syn.subst σ x) := by simp [bodyTerm]

theorem body_term_at (i p j z R B h D N a C E T : PTm n) : Γ ⊢[PRAAx]
    bodyTerm i (fixedData p j z R B h D N a C E T) ≐ point p i j z R B h D N a C E T := by
  let x := fixedData p j z R B h D N a C E T
  have l := fst_pair (Γ := Γ) (pairT (pairT p j) (pairT z R))
    (pairT (pairT (pairT B h) (pairT D N)) (pairT (pairT a C) (pairT E T)))
  have r := snd_pair (Γ := Γ) (pairT (pairT p j) (pairT z R))
    (pairT (pairT (pairT B h) (pairT D N)) (pairT (pairT a C) (pairT E T)))
  have pj := (congrFst l).eqTrans (fst_pair _ _)
  have zr := (congrSnd l).eqTrans (snd_pair _ _)
  have bd := (congrFst r).eqTrans (fst_pair _ _)
  have ae := (congrSnd r).eqTrans (snd_pair _ _)
  have bh := (congrFst bd).eqTrans (fst_pair _ _)
  have dn := (congrSnd bd).eqTrans (snd_pair _ _)
  have ac := (congrFst ae).eqTrans (fst_pair _ _)
  have et := (congrSnd ae).eqTrans (snd_pair _ _)
  have step0 : Γ ⊢[PRAAx]
      point (fstT (fstT (fstT x))) (i) (sndT (fstT (fstT x))) (fstT (sndT (fstT x))) (sndT (sndT (fstT x))) (fstT (fstT (fstT (sndT x)))) (sndT (fstT (fstT (sndT x)))) (fstT (sndT (fstT (sndT x)))) (sndT (sndT (fstT (sndT x)))) (fstT (fstT (sndT (sndT x)))) (sndT (fstT (sndT (sndT x)))) (fstT (sndT (sndT (sndT x)))) (sndT (sndT (sndT (sndT x)))) ≐
      point (p) (i) (sndT (fstT (fstT x))) (fstT (sndT (fstT x))) (sndT (sndT (fstT x))) (fstT (fstT (fstT (sndT x)))) (sndT (fstT (fstT (sndT x)))) (fstT (sndT (fstT (sndT x)))) (sndT (sndT (fstT (sndT x)))) (fstT (fstT (sndT (sndT x)))) (sndT (fstT (sndT (sndT x)))) (fstT (sndT (sndT (sndT x)))) (sndT (sndT (sndT (sndT x)))) := by
    simpa only [subst_point,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,x,fixedData] using
      Prf.eqCongr1 (point (var 0) (Syn.shift (i)) (Syn.shift (sndT (fstT (fstT x)))) (Syn.shift (fstT (sndT (fstT x)))) (Syn.shift (sndT (sndT (fstT x)))) (Syn.shift (fstT (fstT (fstT (sndT x))))) (Syn.shift (sndT (fstT (fstT (sndT x))))) (Syn.shift (fstT (sndT (fstT (sndT x))))) (Syn.shift (sndT (sndT (fstT (sndT x))))) (Syn.shift (fstT (fstT (sndT (sndT x))))) (Syn.shift (sndT (fstT (sndT (sndT x))))) (Syn.shift (fstT (sndT (sndT (sndT x))))) (Syn.shift (sndT (sndT (sndT (sndT x)))))) ((congrFst pj).eqTrans (fst_pair _ _))
  have step2 : Γ ⊢[PRAAx]
      point (p) (i) (sndT (fstT (fstT x))) (fstT (sndT (fstT x))) (sndT (sndT (fstT x))) (fstT (fstT (fstT (sndT x)))) (sndT (fstT (fstT (sndT x)))) (fstT (sndT (fstT (sndT x)))) (sndT (sndT (fstT (sndT x)))) (fstT (fstT (sndT (sndT x)))) (sndT (fstT (sndT (sndT x)))) (fstT (sndT (sndT (sndT x)))) (sndT (sndT (sndT (sndT x)))) ≐
      point (p) (i) (j) (fstT (sndT (fstT x))) (sndT (sndT (fstT x))) (fstT (fstT (fstT (sndT x)))) (sndT (fstT (fstT (sndT x)))) (fstT (sndT (fstT (sndT x)))) (sndT (sndT (fstT (sndT x)))) (fstT (fstT (sndT (sndT x)))) (sndT (fstT (sndT (sndT x)))) (fstT (sndT (sndT (sndT x)))) (sndT (sndT (sndT (sndT x)))) := by
    simpa only [subst_point,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,x,fixedData] using
      Prf.eqCongr1 (point (Syn.shift (p)) (Syn.shift (i)) (var 0) (Syn.shift (fstT (sndT (fstT x)))) (Syn.shift (sndT (sndT (fstT x)))) (Syn.shift (fstT (fstT (fstT (sndT x))))) (Syn.shift (sndT (fstT (fstT (sndT x))))) (Syn.shift (fstT (sndT (fstT (sndT x))))) (Syn.shift (sndT (sndT (fstT (sndT x))))) (Syn.shift (fstT (fstT (sndT (sndT x))))) (Syn.shift (sndT (fstT (sndT (sndT x))))) (Syn.shift (fstT (sndT (sndT (sndT x))))) (Syn.shift (sndT (sndT (sndT (sndT x)))))) ((congrSnd pj).eqTrans (snd_pair _ _))
  have step3 : Γ ⊢[PRAAx]
      point (p) (i) (j) (fstT (sndT (fstT x))) (sndT (sndT (fstT x))) (fstT (fstT (fstT (sndT x)))) (sndT (fstT (fstT (sndT x)))) (fstT (sndT (fstT (sndT x)))) (sndT (sndT (fstT (sndT x)))) (fstT (fstT (sndT (sndT x)))) (sndT (fstT (sndT (sndT x)))) (fstT (sndT (sndT (sndT x)))) (sndT (sndT (sndT (sndT x)))) ≐
      point (p) (i) (j) (z) (sndT (sndT (fstT x))) (fstT (fstT (fstT (sndT x)))) (sndT (fstT (fstT (sndT x)))) (fstT (sndT (fstT (sndT x)))) (sndT (sndT (fstT (sndT x)))) (fstT (fstT (sndT (sndT x)))) (sndT (fstT (sndT (sndT x)))) (fstT (sndT (sndT (sndT x)))) (sndT (sndT (sndT (sndT x)))) := by
    simpa only [subst_point,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,x,fixedData] using
      Prf.eqCongr1 (point (Syn.shift (p)) (Syn.shift (i)) (Syn.shift (j)) (var 0) (Syn.shift (sndT (sndT (fstT x)))) (Syn.shift (fstT (fstT (fstT (sndT x))))) (Syn.shift (sndT (fstT (fstT (sndT x))))) (Syn.shift (fstT (sndT (fstT (sndT x))))) (Syn.shift (sndT (sndT (fstT (sndT x))))) (Syn.shift (fstT (fstT (sndT (sndT x))))) (Syn.shift (sndT (fstT (sndT (sndT x))))) (Syn.shift (fstT (sndT (sndT (sndT x))))) (Syn.shift (sndT (sndT (sndT (sndT x)))))) ((congrFst zr).eqTrans (fst_pair _ _))
  have step4 : Γ ⊢[PRAAx]
      point (p) (i) (j) (z) (sndT (sndT (fstT x))) (fstT (fstT (fstT (sndT x)))) (sndT (fstT (fstT (sndT x)))) (fstT (sndT (fstT (sndT x)))) (sndT (sndT (fstT (sndT x)))) (fstT (fstT (sndT (sndT x)))) (sndT (fstT (sndT (sndT x)))) (fstT (sndT (sndT (sndT x)))) (sndT (sndT (sndT (sndT x)))) ≐
      point (p) (i) (j) (z) (R) (fstT (fstT (fstT (sndT x)))) (sndT (fstT (fstT (sndT x)))) (fstT (sndT (fstT (sndT x)))) (sndT (sndT (fstT (sndT x)))) (fstT (fstT (sndT (sndT x)))) (sndT (fstT (sndT (sndT x)))) (fstT (sndT (sndT (sndT x)))) (sndT (sndT (sndT (sndT x)))) := by
    simpa only [subst_point,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,x,fixedData] using
      Prf.eqCongr1 (point (Syn.shift (p)) (Syn.shift (i)) (Syn.shift (j)) (Syn.shift (z)) (var 0) (Syn.shift (fstT (fstT (fstT (sndT x))))) (Syn.shift (sndT (fstT (fstT (sndT x))))) (Syn.shift (fstT (sndT (fstT (sndT x))))) (Syn.shift (sndT (sndT (fstT (sndT x))))) (Syn.shift (fstT (fstT (sndT (sndT x))))) (Syn.shift (sndT (fstT (sndT (sndT x))))) (Syn.shift (fstT (sndT (sndT (sndT x))))) (Syn.shift (sndT (sndT (sndT (sndT x)))))) ((congrSnd zr).eqTrans (snd_pair _ _))
  have step5 : Γ ⊢[PRAAx]
      point (p) (i) (j) (z) (R) (fstT (fstT (fstT (sndT x)))) (sndT (fstT (fstT (sndT x)))) (fstT (sndT (fstT (sndT x)))) (sndT (sndT (fstT (sndT x)))) (fstT (fstT (sndT (sndT x)))) (sndT (fstT (sndT (sndT x)))) (fstT (sndT (sndT (sndT x)))) (sndT (sndT (sndT (sndT x)))) ≐
      point (p) (i) (j) (z) (R) (B) (sndT (fstT (fstT (sndT x)))) (fstT (sndT (fstT (sndT x)))) (sndT (sndT (fstT (sndT x)))) (fstT (fstT (sndT (sndT x)))) (sndT (fstT (sndT (sndT x)))) (fstT (sndT (sndT (sndT x)))) (sndT (sndT (sndT (sndT x)))) := by
    simpa only [subst_point,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,x,fixedData] using
      Prf.eqCongr1 (point (Syn.shift (p)) (Syn.shift (i)) (Syn.shift (j)) (Syn.shift (z)) (Syn.shift (R)) (var 0) (Syn.shift (sndT (fstT (fstT (sndT x))))) (Syn.shift (fstT (sndT (fstT (sndT x))))) (Syn.shift (sndT (sndT (fstT (sndT x))))) (Syn.shift (fstT (fstT (sndT (sndT x))))) (Syn.shift (sndT (fstT (sndT (sndT x))))) (Syn.shift (fstT (sndT (sndT (sndT x))))) (Syn.shift (sndT (sndT (sndT (sndT x)))))) ((congrFst bh).eqTrans (fst_pair _ _))
  have step6 : Γ ⊢[PRAAx]
      point (p) (i) (j) (z) (R) (B) (sndT (fstT (fstT (sndT x)))) (fstT (sndT (fstT (sndT x)))) (sndT (sndT (fstT (sndT x)))) (fstT (fstT (sndT (sndT x)))) (sndT (fstT (sndT (sndT x)))) (fstT (sndT (sndT (sndT x)))) (sndT (sndT (sndT (sndT x)))) ≐
      point (p) (i) (j) (z) (R) (B) (h) (fstT (sndT (fstT (sndT x)))) (sndT (sndT (fstT (sndT x)))) (fstT (fstT (sndT (sndT x)))) (sndT (fstT (sndT (sndT x)))) (fstT (sndT (sndT (sndT x)))) (sndT (sndT (sndT (sndT x)))) := by
    simpa only [subst_point,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,x,fixedData] using
      Prf.eqCongr1 (point (Syn.shift (p)) (Syn.shift (i)) (Syn.shift (j)) (Syn.shift (z)) (Syn.shift (R)) (Syn.shift (B)) (var 0) (Syn.shift (fstT (sndT (fstT (sndT x))))) (Syn.shift (sndT (sndT (fstT (sndT x))))) (Syn.shift (fstT (fstT (sndT (sndT x))))) (Syn.shift (sndT (fstT (sndT (sndT x))))) (Syn.shift (fstT (sndT (sndT (sndT x))))) (Syn.shift (sndT (sndT (sndT (sndT x)))))) ((congrSnd bh).eqTrans (snd_pair _ _))
  have step7 : Γ ⊢[PRAAx]
      point (p) (i) (j) (z) (R) (B) (h) (fstT (sndT (fstT (sndT x)))) (sndT (sndT (fstT (sndT x)))) (fstT (fstT (sndT (sndT x)))) (sndT (fstT (sndT (sndT x)))) (fstT (sndT (sndT (sndT x)))) (sndT (sndT (sndT (sndT x)))) ≐
      point (p) (i) (j) (z) (R) (B) (h) (D) (sndT (sndT (fstT (sndT x)))) (fstT (fstT (sndT (sndT x)))) (sndT (fstT (sndT (sndT x)))) (fstT (sndT (sndT (sndT x)))) (sndT (sndT (sndT (sndT x)))) := by
    simpa only [subst_point,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,x,fixedData] using
      Prf.eqCongr1 (point (Syn.shift (p)) (Syn.shift (i)) (Syn.shift (j)) (Syn.shift (z)) (Syn.shift (R)) (Syn.shift (B)) (Syn.shift (h)) (var 0) (Syn.shift (sndT (sndT (fstT (sndT x))))) (Syn.shift (fstT (fstT (sndT (sndT x))))) (Syn.shift (sndT (fstT (sndT (sndT x))))) (Syn.shift (fstT (sndT (sndT (sndT x))))) (Syn.shift (sndT (sndT (sndT (sndT x)))))) ((congrFst dn).eqTrans (fst_pair _ _))
  have step8 : Γ ⊢[PRAAx]
      point (p) (i) (j) (z) (R) (B) (h) (D) (sndT (sndT (fstT (sndT x)))) (fstT (fstT (sndT (sndT x)))) (sndT (fstT (sndT (sndT x)))) (fstT (sndT (sndT (sndT x)))) (sndT (sndT (sndT (sndT x)))) ≐
      point (p) (i) (j) (z) (R) (B) (h) (D) (N) (fstT (fstT (sndT (sndT x)))) (sndT (fstT (sndT (sndT x)))) (fstT (sndT (sndT (sndT x)))) (sndT (sndT (sndT (sndT x)))) := by
    simpa only [subst_point,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,x,fixedData] using
      Prf.eqCongr1 (point (Syn.shift (p)) (Syn.shift (i)) (Syn.shift (j)) (Syn.shift (z)) (Syn.shift (R)) (Syn.shift (B)) (Syn.shift (h)) (Syn.shift (D)) (var 0) (Syn.shift (fstT (fstT (sndT (sndT x))))) (Syn.shift (sndT (fstT (sndT (sndT x))))) (Syn.shift (fstT (sndT (sndT (sndT x))))) (Syn.shift (sndT (sndT (sndT (sndT x)))))) ((congrSnd dn).eqTrans (snd_pair _ _))
  have step9 : Γ ⊢[PRAAx]
      point (p) (i) (j) (z) (R) (B) (h) (D) (N) (fstT (fstT (sndT (sndT x)))) (sndT (fstT (sndT (sndT x)))) (fstT (sndT (sndT (sndT x)))) (sndT (sndT (sndT (sndT x)))) ≐
      point (p) (i) (j) (z) (R) (B) (h) (D) (N) (a) (sndT (fstT (sndT (sndT x)))) (fstT (sndT (sndT (sndT x)))) (sndT (sndT (sndT (sndT x)))) := by
    simpa only [subst_point,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,x,fixedData] using
      Prf.eqCongr1 (point (Syn.shift (p)) (Syn.shift (i)) (Syn.shift (j)) (Syn.shift (z)) (Syn.shift (R)) (Syn.shift (B)) (Syn.shift (h)) (Syn.shift (D)) (Syn.shift (N)) (var 0) (Syn.shift (sndT (fstT (sndT (sndT x))))) (Syn.shift (fstT (sndT (sndT (sndT x))))) (Syn.shift (sndT (sndT (sndT (sndT x)))))) ((congrFst ac).eqTrans (fst_pair _ _))
  have step10 : Γ ⊢[PRAAx]
      point (p) (i) (j) (z) (R) (B) (h) (D) (N) (a) (sndT (fstT (sndT (sndT x)))) (fstT (sndT (sndT (sndT x)))) (sndT (sndT (sndT (sndT x)))) ≐
      point (p) (i) (j) (z) (R) (B) (h) (D) (N) (a) (C) (fstT (sndT (sndT (sndT x)))) (sndT (sndT (sndT (sndT x)))) := by
    simpa only [subst_point,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,x,fixedData] using
      Prf.eqCongr1 (point (Syn.shift (p)) (Syn.shift (i)) (Syn.shift (j)) (Syn.shift (z)) (Syn.shift (R)) (Syn.shift (B)) (Syn.shift (h)) (Syn.shift (D)) (Syn.shift (N)) (Syn.shift (a)) (var 0) (Syn.shift (fstT (sndT (sndT (sndT x))))) (Syn.shift (sndT (sndT (sndT (sndT x)))))) ((congrSnd ac).eqTrans (snd_pair _ _))
  have step11 : Γ ⊢[PRAAx]
      point (p) (i) (j) (z) (R) (B) (h) (D) (N) (a) (C) (fstT (sndT (sndT (sndT x)))) (sndT (sndT (sndT (sndT x)))) ≐
      point (p) (i) (j) (z) (R) (B) (h) (D) (N) (a) (C) (E) (sndT (sndT (sndT (sndT x)))) := by
    simpa only [subst_point,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,x,fixedData] using
      Prf.eqCongr1 (point (Syn.shift (p)) (Syn.shift (i)) (Syn.shift (j)) (Syn.shift (z)) (Syn.shift (R)) (Syn.shift (B)) (Syn.shift (h)) (Syn.shift (D)) (Syn.shift (N)) (Syn.shift (a)) (Syn.shift (C)) (var 0) (Syn.shift (sndT (sndT (sndT (sndT x)))))) ((congrFst et).eqTrans (fst_pair _ _))
  have step12 : Γ ⊢[PRAAx]
      point (p) (i) (j) (z) (R) (B) (h) (D) (N) (a) (C) (E) (sndT (sndT (sndT (sndT x)))) ≐
      point (p) (i) (j) (z) (R) (B) (h) (D) (N) (a) (C) (E) (T) := by
    simpa only [subst_point,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,x,fixedData] using
      Prf.eqCongr1 (point (Syn.shift (p)) (Syn.shift (i)) (Syn.shift (j)) (Syn.shift (z)) (Syn.shift (R)) (Syn.shift (B)) (Syn.shift (h)) (Syn.shift (D)) (Syn.shift (N)) (Syn.shift (a)) (Syn.shift (C)) (Syn.shift (E)) (var 0)) ((congrSnd et).eqTrans (snd_pair _ _))
  exact step0.eqTrans (step2.eqTrans (step3.eqTrans (step4.eqTrans (step5.eqTrans (step6.eqTrans (step7.eqTrans (step8.eqTrans (step9.eqTrans (step10.eqTrans (step11.eqTrans (step12)))))))))))

theorem body_at (i p j z R B h D N a C E T : PTm n) : Γ ⊢[PRAAx]
    inst2 body i (fixedData p j z R B h D N a C E T) ≐ point p i j z R B h D N a C E T := by
  simpa only [body,inst2,subst_bodyTerm,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    body_term_at (Γ := Γ) i p j z R B h D N a C E T

theorem program_at (i p j z R B h D N a C E T : PTm n) : Γ ⊢[PRAAx]
    ap2 bodyF i (fixedData p j z R B h D N a C E T) ≐ point p i j z R B h D N a C E T :=
  (toPR_eq (Γ := Γ) body ![i,fixedData p j z R B h D N a C E T]).eqTrans (body_at i p j z R B h D N a C E T)

theorem row_source (i z R B A h D a C E T N : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A h D a C E T N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    GaussianEulerLogarithmicPathCompactTaylor.source z R B A h D a C E T N i :=
  .andI hs.andE₁ (.andI hs.andE₂.andE₁ (.andI hs.andE₂.andE₂.andE₁
    (.andI hs.andE₂.andE₂.andE₂.andE₁ (.andI hi hs.andE₂.andE₂.andE₂.andE₂))))

theorem row_bound (i p r j z R B A h D a C E T N : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A h D a C E T N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    distanceBounded (inst2 (forward body) i (fixedData p j z R B h D N a C E T))
      (inst2 (GaussianRationalFiniteSum.multiplyBody body) i (pairT (increment h D N) (fixedData r (succ j) z R B h D N a C E T)))
      (numerator p p r j R C E T N) (denominator p p r E N) := by
  rw [GaussianRationalParameterTelescope.forward_at]
  have exactLeft := qsub_congr (Γ := Γ) (body_at (succ i) p j z R B h D N a C E T) (body_at i p j z R B h D N a C E T)
  have exactRight := (multiply_body_at (Γ := Γ) body (increment h D N) i (fixedData r (succ j) z R B h D N a C E T)).eqTrans
    (qmul_congr (.eqRefl _) (body_at i r (succ j) z R B h D N a C E T))
  exact distance_congr exactLeft.eqSymm exactRight.eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianEulerLogarithmicPathCompactTaylor.original_difference_observations p p r j z R B A h D a C E T N i (row_source i z R B A h D a C E T N hs hi))

/-- Every genuine bounded row of the finite parameter telescope follows
from the original path source at the actual compact precision pair. -/
theorem original_local_rows (p r j z R B A h D a C E T N : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A h D a C E T N) : Γ ⊢[PRAAx]
    localRows body body N (fixedData p j z R B h D N a C E T) (fixedData r (succ j) z R B h D N a C E T)
      (increment h D N) (numerator p p r j R C E T N) (denominator p p r E N) := by
  let sh (x : PTm n) := Syn.shift x
  have hh : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh A) (sh h) (sh D) (sh a) (sh C) (sh E) (sh T) (sh N) :=
    by simpa only [Fm.shift,subst_source,Syn.shift,sh] using hs.shift
  refine .allI (.impI ?_)
  simpa [localRows,GaussianRationalRiemannRefinement.termsDistance,GaussianEulerLogarithmicPathCompactTaylor.numerator,
    GaussianEulerLogarithmicPathCompactTaylor.denominator,GaussianEulerLogarithmicPathCompactTaylor.quadraticNumerator,
    GaussianEulerLogarithmicPathCompactTaylor.quadraticDenominator,Syn.shift,sh] using
    row_bound (var 0) (sh p) (sh r) (sh j) (sh z) (sh R) (sh B) (sh A) (sh h) (sh D) (sh a) (sh C) (sh E) (sh T) (sh N) hh.wk Prf.hyp0

theorem actual_original_path_compact_local_telescope_rows_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14
    (source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) ⟶
      localRows body body (var 13) (fixedData (var 0) (var 2) (var 3) (var 4) (var 5) (var 7) (var 8) (var 13) (var 9) (var 10) (var 11) (var 12))
        (fixedData (var 1) (succ (var 2)) (var 3) (var 4) (var 5) (var 7) (var 8) (var 13) (var 9) (var 10) (var 11) (var 12))
        (increment (var 7) (var 8) (var 13))
        (numerator (var 0) (var 0) (var 1) (var 2) (var 4) (var 10) (var 11) (var 12) (var 13))
        (denominator (var 0) (var 0) (var 1) (var 11) (var 13))) :=
  closeUniv 14 (.impI (original_local_rows _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicPathCompactRows
