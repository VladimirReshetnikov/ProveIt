import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.FiniteRows.GaussianBinetLaplaceMomentCompact
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianCompactScalarMajorant

/-!
# Width bound for the actual weighted Binet quadrature

The compact horizon bounds the exact time power. The original Binet
observation has norm at most one, so the weighted panel has norm at
most its physical width times the horizon to the natural power.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentWidth

open_ipra
open GaussianBinetLaplaceIntegrand (cofinalF cofinalData input cofinal_bound)
open GaussianBinetLaplaceMomentCompact (data weight_bound)
open GaussianBinetLaplaceMomentFloor (weight clock observation gain fixedData evaluatorF evaluator_at nameF)
open GaussianBinetLaplaceStrip (source tagNumerator tag_inside)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianCompactRiemannName (grid grid_inside inside sampleBody sampleData sample_body_at quadrature precision mesh)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalRiemannRefinement (constantBody leftSum termsDistance)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReconstructionRoots (distance_zero_iff)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem observation_bound (p j X D R T A B : PTm n) (h : Γ ⊢[PRAAx] input X zero D zero R T A B) :
    Γ ⊢[PRAAx] bounded (observation p j X D R T A B) (pw T j) one := by
  have b := cofinal_bound (clock p j T) X zero D zero R T A B h
  have u := bounded_radius_mono _ one two one one (le_succ_self one) (le_refl one) (by ipra_le 1) b
  exact bound_congr (.eqRefl _) (one_mul _) (one_mul _)
    (bounded_product _ _ one one _ one (le_refl one) (le_refl one) u (weight_bound j A B T h.andE₂.andE₁ h.andE₂.andE₂))

theorem quadrature_bound (p M j X D R T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] bounded (quadrature evaluatorF p M (E+A) C E (fixedData j X D R T)) (C*pw T j) E := by
  let f := sampleBody evaluatorF
  let x := sampleData p M (E+A) C E (fixedData j X D R T)
  have rows : Γ ⊢[PRAAx] termsDistance f constantBody M x qzero (pw T j) one := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s M)::Γ.map Fm.shift
    let t := grid (var 0) (s M) (s E+s A) (s C) (s E)
    have hs : Δ ⊢[PRAAx] source (s X) zero (s D) zero (s R) (s T) (s A) (s C) (s E) := by
      simpa only [Δ,s,Fm.shift,Syn.shift,GaussianBinetLaplaceStrip.subst_source,ConciseIPRA.PTm.subst_zero] using h.shift.wk
    have ms : Δ ⊢[PRAAx] le one (s M) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hM.shift.wk
    have e := hs.andE₂.andE₁
    have ht : Δ ⊢[PRAAx] inside (s E+s A) (s C) (s E) t :=
      grid_inside _ _ _ _ _ (le_trans e (le_add_right _ _)) e ms (le_of_lt Prf.hyp0)
    have time := tag_inside t (s A) (s C) (s E) (s T) e hs.andE₂.andE₂ ht
    have b := observation_bound (s p) (s j) (s X) (s D) (s R) (s T) (tagNumerator t) (sndT t)
      (.andI hs.andE₁ (.andI ht.andE₂.andE₁ time.andE₂))
    have read := (sample_body_at (Γ := Δ) evaluatorF (var 0) (s p) (s M) (s E+s A) (s C) (s E)
      (fixedData (s j) (s X) (s D) (s R) (s T))).eqTrans
        (evaluator_at (s p) t (s j) (s X) (s D) (s R) (s T))
    rw [GaussianRationalRiemannRefinement.constant_entry]
    simpa only [f,x,Δ,s,Syn.shift,GaussianCompactRiemannName.subst_sampleData,GaussianBinetLaplaceMomentFloor.subst_fixedData,
      GaussianRationalHorner.subst_qzero,PTm.subst_add,subst_ap2,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      (distance_zero_iff _ _ _ (le_refl one)).iffMpr (bound_congr read.eqSymm (.eqRefl _) (.eqRefl _) b)
  have zeroSum : Γ ⊢[PRAAx] GaussianRationalFiniteSum.sum constantBody M qzero ≐ qzero :=
    (GaussianRationalRiemannRefinement.constant_sum qzero M).eqTrans (GaussianRationalFactorialEulerSums.scale_zero_value M)
  have zeroInt : Γ ⊢[PRAAx] leftSum constantBody M qzero C E ≐ qzero :=
    (qmul_congr (.eqRefl _) zeroSum).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_right _)
  have norm := GaussianCompactScalarMajorant.common_mesh_distance f constantBody M x qzero C E (pw T j) one
    hM h.andE₂.andE₁ (le_refl one) rows
  exact (distance_zero_iff _ _ _ h.andE₂.andE₁).iffMp
    (distance_congr (.eqRefl _) zeroInt (.eqRefl _) (by ipra_ring) norm)

theorem width_bound (p j X D R T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (data j X D R T A C E)) (C*pw T j) E :=
  bound_congr (GaussianCompactRiemannName.name_at evaluatorF p (E+A) C E (gain j R T) T
    (fixedData j X D R T)).eqSymm (.eqRefl _) (.eqRefl _)
    (quadrature_bound (precision p T) (mesh p (gain j R T) T) j X D R T A C E h
      (GaussianCompactRiemannName.mesh_positive p (gain j R T) T))

theorem small_origin_bound (p j X D R C E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R one zero C E) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (data j X D R one zero C E)) C E := by
  have e : Γ ⊢[PRAAx] C*pw one j ≐ C :=
    (congrMul (.eqRefl C) (GaussianPolynomialPerturbation.one_power j)).eqTrans (by ipra_ring)
  exact bound_congr (.eqRefl _) e (.eqRefl _) (width_bound p j X D R one zero C E h)

theorem actual_weighted_Binet_small_origin_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 2) zero (var 3) zero (var 4) one zero (var 5) (var 6) ⟶
      bounded (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4) one zero (var 5) (var 6)))
        (var 5) (var 6)) :=
  closeUniv 7 (.impI (small_origin_bound _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentWidth
