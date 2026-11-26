import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCutoffCauchyComparison
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual varying-cutoff Euler name, conditional only on the lower tail

The same original eta/top cutoffs at outer p are sampled by the actual
compact name at p+4. The genuine lowerData lower-tail bound is the sole
additional input. True original split and upper estimates derive output
regularity. This is a conditional name construction; no improper-integral
identity or unchecked lower-tail theorem is asserted. The verified
conservative local modulus is retained rather than the sharper paper mesh.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerVaryingCutoffName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerCutoffCauchyComparison (input observation clock)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianEulerIntegrandName (evaluatorF fixedData)
open GaussianCompactRiemannName (quadrature mesh)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (positive_product)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (z R B A : PTm n) : PTm n := pairT z (pairT R (pairT B A))
def sample (p z R B A : PTm n) : PTm n := observation (clock p) z R B p A
def reader (p d : PTm n) : PTm n := sample p (fstT d) (fstT (sndT d)) (fstT (sndT (sndT d))) (sndT (sndT (sndT d)))
def nameF : PR 2 := PTm.toPR (reader (var 0) (var 1))
def cells (p A R : PTm n) : PTm n := mesh (clock p) (GaussianGammaEulerCompactQuadrature.localFactor p A R) (top p A R)
def evaluationPrecision (p A R : PTm n) : PTm n := p+top p A R+num 10

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B A : PTm n) :
    Syn.subst σ (data z R B A) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) := by simp [data]
@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (p z R B A : PTm n) :
    Syn.subst σ (sample p z R B A) = sample (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) := by simp [sample]
@[simp] theorem subst_reader {m : ℕ} (σ : Fin n → PTm m) (p d : PTm n) :
    Syn.subst σ (reader p d) = reader (Syn.subst σ p) (Syn.subst σ d) := by simp [reader]
@[simp] theorem subst_cells {m : ℕ} (σ : Fin n → PTm m) (p A R : PTm n) :
    Syn.subst σ (cells p A R) = cells (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ R) := by
  simp [cells,top,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] theorem subst_evaluationPrecision {m : ℕ} (σ : Fin n → PTm m) (p A R : PTm n) :
    Syn.subst σ (evaluationPrecision p A R) = evaluationPrecision (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ R) := by
  simp [evaluationPrecision,top,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]

theorem data_z (z R B A : PTm n) : Γ ⊢[PRAAx] fstT (data z R B A) ≐ z := fst_pair _ _
theorem data_R (z R B A : PTm n) : Γ ⊢[PRAAx] fstT (sndT (data z R B A)) ≐ R :=
  (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
theorem data_B (z R B A : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (data z R B A))) ≐ B :=
  (congrFst (congrSnd (snd_pair _ _))).eqTrans ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
theorem data_A (z R B A : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (data z R B A))) ≐ A :=
  (congrSnd (congrSnd (snd_pair _ _))).eqTrans ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))

theorem name_at (p z R B A : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data z R B A) ≐ sample p z R B A := by
  have prog : Γ ⊢[PRAAx] ap2 nameF p (data z R B A) ≐ reader p (data z R B A) := by
    simpa [nameF,ap2] using toPR_eq (Γ := Γ) (reader (var 0) (var 1) : PTm 2) ![p,data z R B A]
  refine prog.eqTrans ?_
  ipra_congr (sample (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with
    [.eqRefl p, data_z _ _ _ _, data_R _ _ _ _, data_B _ _ _ _, data_A _ _ _ _] using [reader]

theorem sample_canonical (p z R B A : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (sample p z R B A) :=
  GaussianEulerCutoffCauchyComparison.observation_canonical _ _ _ _ _ _
theorem name_canonical (p z R B A : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (ap2 nameF p (data z R B A)) :=
  GaussianRationalHorner.canonical_congr (name_at p z R B A) (sample_canonical p z R B A)

/-- Original output observations at arbitrary independent precisions.
The varying name's regularity is derived, never supplied. -/
theorem sample_regularity (p q z R B A : PTm n) (h : Γ ⊢[PRAAx] input z R B A) : Γ ⊢[PRAAx]
    distanceBounded (sample p z R B A) (sample q z R B A) (unit p+unit q) (unit p*unit q) := by
  refine .orE (le_total p q) ?_ ?_
  · exact distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive q))
      (GaussianEulerCutoffCauchyComparison.ordered_clock_comparison p q z R B A h.wk Prf.hyp0)
  · exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (GaussianEulerCutoffCauchyComparison.ordered_clock_comparison q p z R B A h.wk Prf.hyp0)

theorem name_observations (p q z R B A : PTm n) (h : Γ ⊢[PRAAx] input z R B A) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z R B A)) (ap2 nameF q (data z R B A)) (unit p+unit q) (unit p*unit q) :=
  distance_congr (name_at p z R B A).eqSymm (name_at q z R B A).eqSymm (.eqRefl _) (.eqRefl _)
    (sample_regularity p q z R B A h)

theorem conditional_name_regular (z R B A : PTm n) (h : Γ ⊢[PRAAx] input z R B A) : Γ ⊢[PRAAx]
    pointCN nameF (data z R B A) := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] input (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R))
      (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift A)) := by simpa [Fm.shift,Syn.shift] using h.shift.shift
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,unit,Syn.shift,subst_data] using
    name_observations (var 1) (var 0) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R))
      (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift A)) hs

/-- The actual original quadrature changes only its observation schedule.
Its outer eta/top cutoff remains p. -/
theorem quadrature_precision_congr (F : PR 3) (p p' N a C E x : PTm n) (hp : Γ ⊢[PRAAx] p ≐ p') : Γ ⊢[PRAAx]
    quadrature F p N a C E x ≐ quadrature F p' N a C E x :=
  GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _)
    (GaussianRationalFiniteSum.sum_index_congr (GaussianCompactRiemannName.sampleBody F) (.eqRefl N) (congrPairT hp (.eqRefl _)))

theorem actual_sampler (p z R B A : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data z R B A) ≐ quadrature evaluatorF (evaluationPrecision p A R) (cells p A R)
      one (width p A R) (etaDen p A R) (fixedData z B) :=
  (name_at p z R B A).eqTrans ((GaussianGammaEulerCompactQuadrature.original_sample (clock p) z R B p A).eqTrans
    (quadrature_precision_congr _ _ _ _ _ _ _ _ (by unfold clock evaluationPrecision; ipra_ring)))

def output (p z R B A : PTm n) : PTm n := pairT (ap2 nameF p (data z R B A))
  (pairT (clock p) (pairT (cells p A R) (evaluationPrecision p A R)))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (p z R B A : PTm n) : PTm n := PTm.app outputF ![p,z,R,B,A]
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (p z R B A : PTm n) :
    Syn.subst σ (output p z R B A) = output (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) := by simp [output]
theorem program_at (p z R B A : PTm n) : Γ ⊢[PRAAx] run p z R B A ≐ output p z R B A := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![p,z,R,B,A]
theorem returned_point (p z R B A : PTm n) : Γ ⊢[PRAAx] fstT (run p z R B A) ≐ ap2 nameF p (data z R B A) :=
  (congrFst (program_at p z R B A)).eqTrans (fst_pair _ _)
theorem returned_tail (p z R B A : PTm n) : Γ ⊢[PRAAx] sndT (run p z R B A) ≐ pairT (clock p) (pairT (cells p A R) (evaluationPrecision p A R)) :=
  (congrSnd (program_at p z R B A)).eqTrans (snd_pair _ _)
theorem returned_clock (p z R B A : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run p z R B A)) ≐ p+num 4 :=
  (congrFst (returned_tail p z R B A)).eqTrans (fst_pair _ _)
theorem returned_last (p z R B A : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run p z R B A)) ≐ pairT (cells p A R) (evaluationPrecision p A R) :=
  (congrSnd (returned_tail p z R B A)).eqTrans (snd_pair _ _)
theorem returned_cells (p z R B A : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run p z R B A))) ≐ cells p A R :=
  (congrFst (returned_last p z R B A)).eqTrans (fst_pair _ _)
theorem returned_evaluation_precision (p z R B A : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run p z R B A))) ≐ p+top p A R+num 10 :=
  (congrSnd (returned_last p z R B A)).eqTrans (snd_pair _ _)

theorem returned_original_observation (p z R B A : PTm n) : Γ ⊢[PRAAx]
    fstT (run p z R B A) ≐ ap2 GaussianGammaEulerCompactQuadrature.nameF (p+num 4)
      (GaussianGammaEulerCompactQuadrature.data z R B p A) :=
  (returned_point p z R B A).eqTrans (name_at p z R B A)
theorem returned_sampler (p z R B A : PTm n) : Γ ⊢[PRAAx]
    fstT (run p z R B A) ≐ quadrature evaluatorF (evaluationPrecision p A R) (cells p A R)
      one (width p A R) (etaDen p A R) (fixedData z B) :=
  (returned_point p z R B A).eqTrans (actual_sampler p z R B A)

theorem actual_varying_cutoff_name_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4)) ≐ sample (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (name_at _ _ _ _ _)
theorem conditional_actual_varying_cutoff_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) (var 3) ⟶ pointCN nameF (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (conditional_name_regular _ _ _ _ Prf.hyp0))
theorem conditional_actual_varying_cutoff_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 2) (var 3) (var 4) (var 5) ⟶ distanceBounded
      (ap2 nameF (var 0) (data (var 2) (var 3) (var 4) (var 5)))
      (ap2 nameF (var 1) (data (var 2) (var 3) (var 4) (var 5)))
      (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 6 (.impI (name_observations _ _ _ _ _ _ Prf.hyp0))
theorem actual_varying_cutoff_Euler_quadrature_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4)) ≐
      quadrature evaluatorF (evaluationPrecision (var 0) (var 4) (var 2)) (cells (var 0) (var 4) (var 2)) one
        (width (var 0) (var 4) (var 2)) (etaDen (var 0) (var 4) (var 2)) (fixedData (var 1) (var 3))) :=
  closeUniv 5 (actual_sampler _ _ _ _ _)
theorem actual_varying_cutoff_returned_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)
theorem actual_returned_original_cutoff_observation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐
      ap2 GaussianGammaEulerCompactQuadrature.nameF (var 0+num 4)
        (GaussianGammaEulerCompactQuadrature.data (var 1) (var 2) (var 3) (var 0) (var 4))) :=
  closeUniv 5 (returned_original_observation _ _ _ _ _)
theorem actual_returned_original_Euler_precision_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) ≐
      var 0+top (var 0) (var 4) (var 2)+num 10) :=
  closeUniv 5 (returned_evaluation_precision _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerVaryingCutoffName
