import IPRADerivations.Analysis.Stirling.Binet.WeightedIntegrals.GaussianBinetWeightedExponentialGrid

/-!
# The zero-rate weighted exponential integral

At zero decay rate the literal weighted left sum is exactly `1/(2*N)`.
The left-mesh bias therefore has a dyadic cutoff independent of the
observation clock, and the integral is zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBinetWeightedExponentialZero

open_ipra
open ComplexLogarithmRemainder (scale oneCode)
open GaussianBinetWeightedExponentialAlgebra (tagWeight)
open GaussianBinetWeightedExponentialGrid (value rowValue evaluatorF)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (sampleBody sampleData)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalFiniteSum (sum sum_congr_bounded termsEqual)
open GaussianRationalHorner
  (represents qmul ofGaussian_represents ofGaussian_canonical canonical_unique represents_congr positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub qsub_represents qsub_canonical)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr rescale_to)
open GaussianRootAlgebra
  (sub equal_refl equal_of_values re_sub im_sub re_scale im_scale re_one im_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def antiderivative (j N : PTm n) : PTm n :=
  qsub (fraction (j*succ N) (two*N)) (fraction (j*j) (two*N))
def body : PTm 2 := antiderivative (var 0) (var 1)

ipra_subst antiderivative [two]

private theorem represented (j N : PTm n) (h : Γ ⊢[PRAAx] le one (two*N)) :
    Γ ⊢[PRAAx] represents (antiderivative j N)
      (sub (scale (j*succ N) oneCode) (scale (j*j) oneCode)) (two*N) :=
  qsub_represents _ _ _ _ _ h (ofGaussian_represents _ _ h) (ofGaussian_represents _ _ h)

private theorem step_at (j N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] qsub (antiderivative (succ j) N) (antiderivative j N) ≐ tagWeight j N := by
  have h : Γ ⊢[PRAAx] le one (two*N) := positive_product _ _ (le_succ_self _) hN
  have l : Γ ⊢[PRAAx] represents (fraction one two) (scale N oneCode) (two*N) :=
    represents_congr (.eqRefl _) (by
      apply equal_of_values <;> simp only [re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring) (.eqRefl _)
      (rescale_to _ _ two N (two*N) (ofGaussian_represents _ _ (le_succ_self _)) (.eqRefl _))
  have r : Γ ⊢[PRAAx] represents (fraction j N) (scale (two*j) oneCode) (two*N) :=
    represents_congr (.eqRefl _) (by
      apply equal_of_values <;> simp only [re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring)
      (mul_comm N two) (rescale_to _ _ N two (N*two) (ofGaussian_represents _ _ hN) (.eqRefl _))
  apply canonical_unique _ _ _ _ (qsub_canonical _ _) (qsub_canonical _ _) h
    (hrv := qsub_represents _ _ _ _ _ h l r)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _)
    (h := qsub_represents _ _ _ _ _ h (represented (succ j) N h) (represented j N h))
  apply equal_of_values <;> simp only [re_sub,im_sub,re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring

private theorem endpoint (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] qsub (antiderivative N N) (antiderivative zero N) ≐ fraction one two := by
  have h : Γ ⊢[PRAAx] le one (two*N) := positive_product _ _ (le_succ_self _) hN
  have rhs : Γ ⊢[PRAAx] represents (fraction one two) (scale N oneCode) (two*N) :=
    represents_congr (.eqRefl _) (by
      apply equal_of_values <;> simp only [re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring) (.eqRefl _)
      (rescale_to _ _ two N (two*N) (ofGaussian_represents _ _ (le_succ_self _)) (.eqRefl _))
  apply canonical_unique _ _ _ _ (qsub_canonical _ _) (ofGaussian_canonical _ _ (le_succ_self _)) h (hrv := rhs)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _)
    (h := qsub_represents _ _ _ _ _ h (represented N N h) (represented zero N h))
  apply equal_of_values <;> simp only [re_sub,im_sub,re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring

private theorem row_at (p b j N : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] rowValue p zero b j N ≐ tagWeight j N :=
  (qmul_congr (.eqRefl _) ((GaussianEulerDecayMesh.observation_numerator_congr (zero*j) zero (b*N) p
    (by ipra_ring)).eqTrans (GaussianBinetWeightedExponentialGrid.zero_observation (b*N) p
      (positive_product _ _ hb hN)))).eqTrans (GaussianReciprocalHorner.qmul_one_right _ (qsub_canonical _ _))

private theorem body_at (j N : PTm n) :
    inst2 body j N = antiderivative j N := by
  simp only [body,inst2,subst_antiderivative,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]

theorem finite_exact (p b N : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] value p N zero b ≐ fraction one (two*N) := by
  let f := sampleBody evaluatorF
  let d := sampleData p N one one one (pairT zero b)
  let g := GaussianRationalParameterTelescope.forward body
  have rows : Γ ⊢[PRAAx] termsEqual f g N d N := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s N) :: Γ.map Fm.shift
    have bn : Δ ⊢[PRAAx] le one (s b) := (Order.shift_one_le hb).wk
    have nn : Δ ⊢[PRAAx] le one (s N) := (Order.shift_one_le hN).wk
    have vr := (GaussianBinetWeightedExponentialGrid.cell_at (Γ := Δ) (var 0) (s p) (s N) zero (s b)).eqTrans
      (row_at (s p) (s b) (var 0) (s N) bn nn)
    simpa only [termsEqual,Syn.shift,s,Δ,d,g,f,GaussianCompactRiemannName.subst_sampleData,
      subst_pairT,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,
      GaussianRationalParameterTelescope.forward_at,body_at] using
      vr.eqTrans (step_at (var 0) (s N) nn).eqSymm
  have ser : Γ ⊢[PRAAx] sum f N d ≐ fraction one two :=
    (GaussianRationalFiniteSum.sum_congr_bounded f g N d N rows).eqTrans
      ((GaussianRationalParameterTelescope.forward_sum body N N).eqTrans
        (by simpa only [body_at] using endpoint N hN))
  have ew : Γ ⊢[PRAAx] GaussianRationalRiemannRefinement.weight one one N ≐ fraction one N :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (one_mul N)
  exact (qmul_congr ew ser).eqTrans ((GaussianEulerDampedTimeRate.fraction_product one N one two hN (le_succ_self _)).eqTrans
    (GaussianCompactRiemannName.fraction_congr _ _ _ _ (one_mul one) (mul_comm N two)))

theorem cofinal_zero (p q b N : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le (unit q) N) :
    Γ ⊢[PRAAx] distanceBounded (value p N zero b) GaussianRationalHorner.qzero one (unit q) := by
  have hp := unit_positive (Γ := Γ) q
  have hN' := le_trans hp hN
  have h : Γ ⊢[PRAAx] le one (two*N) := positive_product _ _ (le_succ_self _) hN'
  have frac := GaussianEulerDecayFactorBounds.fraction_is_radius_point (Γ := Γ) one (two*N) h
  have vb := GaussianRationalReciprocal.bound_congr frac.eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianDominantPairAlgebra.radius_bounded one (two*N) h)
  have grow : Γ ⊢[PRAAx] le (unit q) (two*N) := le_trans hN
    (le_congr (one_mul N) (.eqRefl _) (mul_le_mul_right N (le_succ_self one)))
  have bound : Γ ⊢[PRAAx] bounded (fraction one (two*N)) one (unit q) :=
    GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ h hp
      (le_congr (by ipra_ring) (by ipra_ring) grow) vb
  exact GaussianRationalDistanceOrder.distance_congr (finite_exact p b N hb hN').eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    ((GaussianReconstructionRoots.distance_zero_iff _ _ _ hp).iffMpr bound)

end LeanProofs.IPRA.Analysis.GaussianBinetWeightedExponentialZero
