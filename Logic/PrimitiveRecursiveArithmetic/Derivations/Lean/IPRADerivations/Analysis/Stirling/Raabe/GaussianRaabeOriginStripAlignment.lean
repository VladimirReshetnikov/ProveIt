import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeLogGammaAlignedTime
import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeStripGridRecurrence
import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeUnitStripBound
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactAlignedSplit

/-!
# Align the two truncated Raabe strips with the original [1,2] grid

At `η=1/2^h`, a common physical step splits [1,2] into a
prefix of width η and the shifted strip [1+η,2]. The prefix has a
uniform physical norm bound. The other strip [η,1] keeps exactly the
same mesh as its unit translate.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeOriginStripAlignment

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (quadrature sampleBody sampleData sample_body_at)
open GaussianCompactAlignedSplit (quadrature_congr)
open GaussianRaabeUnitGridRecurrence (logGammaEvaluator logEvaluator log_gamma_at)
open GaussianRaabeUnitStripBound (cost)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianRationalHorner (qadd qmul qzero positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalRiemannRefinement (termsDistance constantBody weight)
open GaussianRationalSyntheticDivision (qadd_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def width (h : PTm n) : PTm n := monus (unit h) one
def mesh (h K : PTm n) : PTm n := width h*K
def full (p h K : PTm n) : PTm n := quadrature logGammaEvaluator p (unit h*K) (unit h) (unit h) (unit h) zero
def initialStrip (p h K : PTm n) : PTm n := quadrature logGammaEvaluator p K (unit h) one (unit h) zero
def shifted (p h K : PTm n) : PTm n :=
  quadrature logGammaEvaluator p (mesh h K) (one+unit h) (width h) (unit h) zero
def truncated (p h K : PTm n) : PTm n :=
  quadrature logGammaEvaluator p (mesh h K) one (width h) (unit h) zero
def logStrip (p h K : PTm n) : PTm n :=
  quadrature logEvaluator p (mesh h K) one (width h) (unit h) zero

theorem total_width (h : PTm n) : Γ ⊢[PRAAx] unit h ≐ one+width h := eq_add_of_le (unit_positive h)

theorem width_positive (h : PTm n) (hh : Γ ⊢[PRAAx] le two (unit h)) : Γ ⊢[PRAAx] le one (width h) := by
  have e := natEq (total_width (Γ := Γ) h)
  ipra_le sl hh using linear_combination -e

theorem mesh_positive (h K : PTm n) (hh : Γ ⊢[PRAAx] le two (unit h)) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] le one (mesh h K) :=
  positive_product _ _ (width_positive h hh) hK

theorem shift_error (p h K : PTm n) (hh : Γ ⊢[PRAAx] le two (unit h)) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] distanceBounded (qsub (shifted p h K) (truncated p h K)) (logStrip p h K)
      (width h*num 8) (unit h*unit p) :=
  GaussianRaabeStripGridRecurrence.quadrature_error p (mesh h K) one (width h) (unit h)
    (mesh_positive h K hh hK) (le_refl one) (unit_positive h)

theorem split_error (p h K : PTm n) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] distanceBounded (full p h K) (qadd (initialStrip p h K) (shifted p h K))
      (two*unit h) (unit h*unit p) := by
  let D := unit h
  let C := width h
  have hD := unit_positive (Γ := Γ) h
  have ht : Γ ⊢[PRAAx] GaussianCompactAlignedSplit.input logGammaEvaluator D one C D K zero :=
    .andI hD (.andI hD (.andI hK (GaussianRaabeLogGammaAlignedTime.aligned D (one+C) D zero)))
  have identity := GaussianCompactAlignedSplit.shared_step_additivity logGammaEvaluator p D one C D K zero ht
  have e := total_width (Γ := Γ) h
  have fullEq := quadrature_congr (Γ := Γ) logGammaEvaluator (.eqRefl p) (congrMul e.eqSymm (.eqRefl K))
    (.eqRefl D) e.eqSymm (.eqRefl D) (.eqRefl zero)
  have prefixEq := quadrature_congr (Γ := Γ) logGammaEvaluator (.eqRefl p) (one_mul K)
    (.eqRefl D) (.eqRefl one) (.eqRefl D) (.eqRefl zero)
  have shiftEq := quadrature_congr (Γ := Γ) logGammaEvaluator (.eqRefl p) (.eqRefl (C*K))
    (add_comm D one) (.eqRefl C) (.eqRefl D) (.eqRefl zero)
  exact distance_congr fullEq (qadd_congr prefixEq shiftEq) (congrMul (.eqRefl two) e.eqSymm)
    (.eqRefl _) identity

private theorem prefix_row (i p h K w : PTm n) (hK : Γ ⊢[PRAAx] le one K) (hi : Γ ⊢[PRAAx] lt i K) :
    Γ ⊢[PRAAx] distanceBounded
      (inst2 (sampleBody logGammaEvaluator) i (sampleData p K (unit h) one (unit h) zero))
      qzero (cost w) one := by
  let d := unit h*K
  let a := d+one*i
  have hd : Γ ⊢[PRAAx] le one d := positive_product _ _ (unit_positive h) hK
  have low : Γ ⊢[PRAAx] le d a := le_add_right _ _
  have hk : Γ ⊢[PRAAx] le K d :=
    le_congr (one_mul K) (.eqRefl _) (mul_le_mul_right K (unit_positive h))
  have hi' : Γ ⊢[PRAAx] le (one*i) d := le_congr (one_mul i).eqSymm (.eqRefl _) (le_trans (le_of_lt hi) hk)
  have high : Γ ⊢[PRAAx] le a (two*d) :=
    le_congr (add_comm _ _) (by ipra_ring) (add_le_add_right d hi')
  have r := (sample_body_at (Γ := Γ) logGammaEvaluator i p K (unit h) one (unit h) zero).eqTrans
    (log_gamma_at p a d zero)
  exact distance_congr r.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    ((GaussianReconstructionRoots.distance_zero_iff _ _ _ (le_refl one)).iffMpr
      (GaussianRaabeUnitStripBound.sample_bound p a d w hd low high))

theorem prefix_bound (p h K w : PTm n) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] bounded (initialStrip p h K) (cost w) (unit h) := by
  let f := sampleBody logGammaEvaluator
  let x := sampleData p K (unit h) one (unit h) zero
  have rows : Γ ⊢[PRAAx] termsDistance f constantBody K x qzero (cost w) one := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s K)::Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] le one (s K) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hK.shift.wk
    have center : inst2 constantBody (var 0 : PTm (n+1)) qzero = qzero := rfl
    simpa only [x,f,Δ,s,Syn.shift,GaussianCompactRiemannName.subst_sampleData,
      GaussianCoefficientNameBounds.subst_unit,GaussianRaabeUnitStripBound.subst_cost,
      GaussianRationalHorner.subst_qzero,ConciseIPRA.PTm.subst_zero,one,ConciseIPRA.PTm.subst_succ,center] using
      prefix_row (var 0) (s p) (s h) (s K) (s w) hs Prf.hyp0
  have raw := GaussianCompactScalarMajorant.common_mesh_distance f constantBody K x qzero one (unit h)
    (cost w) one hK (unit_positive h) (le_refl one) rows
  let W := weight one (unit h) K
  have center : Γ ⊢[PRAAx] GaussianRationalRiemannRefinement.leftSum constantBody K qzero one (unit h) ≐ qzero :=
    (GaussianRationalParameterTelescope.constant_slope_product K W qzero).eqTrans
      (GaussianRationalSyntheticDivision.qmul_zero_right _)
  exact (GaussianReconstructionRoots.distance_zero_iff _ _ _ (unit_positive h)).iffMp
    (distance_congr (.eqRefl _) center (one_mul _) (by ipra_ring) raw)

def transferNumerator (p h w : PTm n) : PTm n := two*unit h+cost w*unit p

theorem shifted_to_full (p h K w : PTm n) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] distanceBounded (full p h K) (shifted p h K) (transferNumerator p h w) (unit h*unit p) := by
  let D := unit h
  let U := unit p
  let B := initialStrip p h K
  let S := shifted p h K
  have hD := unit_positive (Γ := Γ) h
  have hU := unit_positive (Γ := Γ) p
  have den := positive_product _ _ hD hU
  have b := (GaussianReconstructionRoots.distance_zero_iff _ _ _ hD).iffMpr (prefix_bound p h K w hK)
  have b' : Γ ⊢[PRAAx] distanceBounded B qzero (cost w*U) (D*U) :=
    GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _ hD den
      (le_of_eq_add (d := zero) (by ipra_ring)) b
  have cs : Γ ⊢[PRAAx] GaussianRationalHorner.canonical S := GaussianRationalHorner.qmul_canonical _ _
  have diff : Γ ⊢[PRAAx] distanceBounded (qadd B S) S (cost w*U) (D*U) :=
    distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qzero_add _ cs) (by ipra_ring) (.eqRefl _)
      (GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ den b'
        (GaussianRationalPowerDifference.distance_refl_zero S _ den))
  exact distance_triangle_same _ _ _ _ _ _ den (split_error p h K hK) diff

theorem actual_shifted_Raabe_truncation_near_full_grid_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (var 2) ⟶ distanceBounded (full (var 0) (var 1) (var 2)) (shifted (var 0) (var 1) (var 2))
        (transferNumerator (var 0) (var 1) (var 3)) (unit (var 1)*unit (var 0))) :=
  closeUniv 4 (.impI (shifted_to_full _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRaabeOriginStripAlignment
