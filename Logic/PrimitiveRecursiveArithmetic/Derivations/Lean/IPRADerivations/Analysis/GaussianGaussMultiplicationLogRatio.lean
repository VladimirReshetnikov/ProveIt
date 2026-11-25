import IPRADerivations.Analysis.GaussianGaussMultiplicationLogarithm
import IPRADerivations.Analysis.GaussianNamedLipschitzRate
import IPRADerivations.Analysis.RationalHarmonicIntervalProduct

/-!
# Relative logarithm error for the Gauss multiplication powers

The finite harmonic product telescope transfers the integer logarithm
comparison to the original positive rational logarithm program at
(N/(m(N+1)-1)) and (1/m). The finite slack-removal principle gives
the same leading bound with independent observation clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationLogRatio

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGaussMultiplicationLogarithm (top top_positive)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianPositiveRationalLogarithm (logF data sample name_regular)
open GaussianRationalHorner (qadd qzero)
open GaussianRationalMetric (bounded distanceBounded qnegative qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open RationalGaussianEmbedding (embed)
open RationalHarmonicInterval (interval)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem reversed_interval (a b Q : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx] qnegative (embed (interval a b Q)) ≐ embed (interval b a Q) := by
  let u := embed (GammaMeshRobinLogBridge.harmonicLog a Q)
  let v := embed (GammaMeshRobinLogBridge.harmonicLog b Q)
  have forward : Γ ⊢[PRAAx] qsub u v ≐ embed (interval a b Q) :=
    GaussianPositiveRationalLogarithmProperness.original_finite_difference a b Q ha hb
  have reverse : Γ ⊢[PRAAx] qsub v u ≐ embed (interval b a Q) :=
    GaussianPositiveRationalLogarithmProperness.original_finite_difference b a Q hb ha
  have neg := Prf.eqCongr (qnegative (var 0) : PTm 1) (σ := ![embed (interval a b Q)])
    (σ' := ![qsub u v]) (fun i => by fin_cases i; exact forward.eqSymm)
  have hneg : Γ ⊢[PRAAx] qnegative (embed (interval a b Q)) ≐ qnegative (qsub u v) := by
    simpa only [GaussianRationalMetric.subst_qnegative,Syn.subst_var,Matrix.cons_val_zero] using neg
  exact hneg.eqTrans ((GaussianRationalDistanceOrder.reversed_difference u v).eqTrans reverse)

private theorem integer_interval_bound (m N p : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (embed (interval (N*m) (top m N*one) (GammaEulerConstantName.mesh p))) qzero one N := by
  let L := top m N
  let Q := GammaEulerConstantName.mesh p
  let F := GaussianGammaFiniteApproximantName.logF
  have hL := top_positive m N hm hN
  have hM := RationalAlgebra.positive_product hm hN
  have eq : Γ ⊢[PRAAx] qsub (ap2 F p (m*N)) (ap2 F p L) ≐ embed (interval (m*N) L Q) :=
    (GaussianRationalSyntheticDivision.qsub_congr (GaussianGammaFiniteApproximantName.log_sample_at p (m*N))
      (GaussianGammaFiniteApproximantName.log_sample_at p L)).eqTrans
      (GaussianPositiveRationalLogarithmProperness.original_finite_difference (m*N) L Q hM hL)
  have he := Prf.eqCongr (Γ := Γ) (embed (interval (var 0) (var 1) (var 2)) : PTm 3)
    (σ := ![m*N,L,Q]) (σ' := ![N*m,L*one,Q])
    (fun i => by
      fin_cases i
      · exact mul_comm _ _
      · change Γ ⊢[PRAAx] L ≐ L*one
        ipra_ring
      · exact .eqRefl _)
  have shift : Γ ⊢[PRAAx] embed (interval (m*N) L Q) ≐ embed (interval (N*m) (L*one) Q) := by
    simpa only [RationalGaussianEmbedding.subst_embed,RationalHarmonicInterval.subst_interval,
      Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] using he
  apply (GaussianReconstructionRoots.distance_zero_iff _ one N hN).andE₂.impE
  exact GaussianRationalReciprocal.bound_congr (eq.eqTrans shift) (.eqRefl _) (.eqRefl _)
    (distance_symmetric _ _ _ _ hN (GaussianGaussMultiplicationLogarithm.log_distance_at m N p hm hN))

private theorem finite_ratio_distance (m N p : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (embed (interval N (top m N) (GammaEulerConstantName.mesh p)))
      (embed (interval one m (GammaEulerConstantName.mesh p))) (one*unit p+two*N) (N*unit p) := by
  let L := top m N
  let Q := GammaEulerConstantName.mesh p
  let a := embed (interval N L Q)
  let b := embed (interval one m Q)
  let d := embed (interval (N*m) (L*one) Q)
  have hL := top_positive m N hm hN
  have hQ := GammaEulerConstantName.mesh_positive (Γ := Γ) p
  have sum : Γ ⊢[PRAAx] qsub a b ≐ qadd a (embed (interval m one Q)) :=
    GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (reversed_interval one m Q (le_refl one) hm)
  have product := RationalHarmonicIntervalProduct.finite_product_error N L m one Q hN hL hm (le_refl one) hQ
  have product' : Γ ⊢[PRAAx] distanceBounded (qsub a b) d two (unit p) :=
    distance_radius_mono _ _ _ _ _ _ hQ (unit_positive p)
      (le_of_eq_add (d := (num 6)*unit p)
        (by dsimp [Q,GammaEulerConstantName.mesh,GammaEulerConstantName.unit,unit]; ipra_ring))
      (distance_congr sum.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
        (distance_symmetric _ _ _ _ hQ product))
  have combined := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _
    (unit_positive p) hN product' (integer_interval_bound m N p hm hN)
  have total : Γ ⊢[PRAAx] distanceBounded (qsub a b) qzero (one*unit p+two*N) (N*unit p) :=
    distance_congr (.eqRefl _) (.eqRefl _) (add_comm _ _) (mul_comm _ _) combined
  exact (GaussianReconstructionRoots.distance_zero_iff _ _ _ (RationalAlgebra.positive_product hN (unit_positive p))).andE₁.impE total

theorem ratio_log_diagonal (m N p : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (sample p N (top m N)) (sample p one m)
      (diagonalNumerator one N (num 18) p) (diagonalDenominator N p) := by
  let L := top m N
  let P := unit p
  let D := N*P
  have hP := unit_positive (Γ := Γ) p
  have hD : Γ ⊢[PRAAx] le one D := RationalAlgebra.positive_product hN hP
  have left := GaussianPositiveRationalLogarithmProperness.sample_interval_error p N L (.andI hN (top_positive m N hm hN))
  have right := GaussianPositiveRationalLogarithmProperness.sample_interval_error p one m (.andI (le_refl one) hm)
  have left' := distance_radius_mono _ _ _ _ (num 8*N) D hP hD (le_of_eq_add (d := zero) (by dsimp [D,P]; ipra_ring)) left
  have right' := distance_radius_mono _ _ _ _ (num 8*N) D hP hD (le_of_eq_add (d := zero) (by dsimp [D,P]; ipra_ring))
    (distance_symmetric _ _ _ _ hP right)
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp [diagonalNumerator]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hD
      (distance_triangle_same _ _ _ _ _ _ hD left' (finite_ratio_distance m N p hm hN)) right')

theorem ratio_log_envelope (m N : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    diagonalEnvelope logF logF (data N (top m N)) (data one m) one N (num 18) := by
  refine .allI ?_
  have hm' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by simpa [Fm.shift,Syn.shift] using hm.shift
  have hN' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
  simpa [diagonalEnvelope,sample,Syn.shift] using
    ratio_log_diagonal (Syn.shift m) (Syn.shift N) (var 0) hm' hN'

/-- The original positive rational logarithms differ by at most (1/N),
with the standard dyadic error at each requested observation. -/
theorem ratio_log_independent_rate (m N : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    independentRate logF logF (data N (top m N)) (data one m) one N :=
  GaussianNamedLipschitzRate.independent_rate _ _ _ _ one N (num 18) hN
    (name_regular N (top m N) (.andI hN (top_positive m N hm hN)))
    (name_regular one m (.andI (le_refl one) hm))
    (ratio_log_envelope m N hm hN)

theorem actual_gauss_multiplication_log_ratio_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((le one (var 1) ⋏ le one (var 0)) ⟶
      independentRate logF logF (data (var 0) (top (var 1) (var 0))) (data one (var 1)) one (var 0)) :=
  closeUniv 2 (.impI (ratio_log_independent_rate _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationLogRatio
