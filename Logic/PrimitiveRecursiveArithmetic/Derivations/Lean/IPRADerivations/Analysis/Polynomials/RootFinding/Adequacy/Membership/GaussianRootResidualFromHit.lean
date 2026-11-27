import IPRADerivations.Analysis.Polynomials.RootFinding.Reconstruction.RootSupport.GaussianRootFiniteEvaluation
import IPRADerivations.Analysis.Polynomials.Horner.Perturbation.GaussianRationalHornerLipschitz
import IPRADerivations.Analysis.RationalArithmetic.Covers.GaussianRationalCover

/-!
# Actual sampled residuals from original finite root-list hits

Source04 adequacy, the converse finite estimate. Actual listed zeros and
common radii are derived from the original coefficient name and the checked
factorizer. The sampled polynomial's actual Euclidean coefficient bounds
supply its exact weighted-sum Lipschitz constant. Intuitionistic existential
elimination removes the original hit index. No residual, evaluation-gap,
coefficient-error, or desired radius law is supplied.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRootResidualFromHit

open_ipra
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (CN A R unit unit_positive bounded_radius_mono_one)
open LeanProofs.IPRA.Analysis.GaussianFactorParameters (monicRD)
open LeanProofs.IPRA.Analysis.GaussianRootRadius (roots product)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (bound_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open LeanProofs.IPRA.Analysis.GaussianRootFiniteEvaluation (coefficientNumerator coefficientDenominator)
open LeanProofs.IPRA.Analysis.GaussianRationalCover (hit)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def numerator (a : PR 3) (N U t s x p q : PTm n) : PTm n :=
  GaussianRationalHornerLipschitz.constant N U (A a N x)*p*coefficientDenominator a N t s x+
    GaussianRootSchedule.coefficientConstant N (R a N x)*coefficientNumerator a N t s x*q
def denominator (a : PR 3) (N t s x q : PTm n) : PTm n := q*coefficientDenominator a N t s x

ipra_subst numerator
ipra_subst denominator

theorem radius_positive (a : PR 3) (N x : PTm n) : Γ ⊢[PRAAx] le one (R a N x) :=
  le_trans (GaussianRootRadius.A_positive a N x) (le_add_right _ two)

/-- A genuine original CN sample coefficient has norm at most A. The
leading coefficient is literal one and is handled separately. -/
theorem sample_coefficient_bound (a : PR 3) (N s x i : PTm n)
    (hCN : Γ ⊢[PRAAx] CN a N x) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    bounded (entry (GaussianRootSamples.sample a N s x) i) (A a N x) one := by
  refine .orE (zero_or_succ i) ?_ ?_
  · have leading : ((i ≐ zero) :: Γ) ⊢[PRAAx]
        entry (GaussianRootSamples.sample a N s x) i ≐ GaussianRationalSyntheticDivision.qone :=
      (entry_congr (.eqRefl _) Prf.hyp0).eqTrans (GaussianRootSamples.sample_leading a N s x)
    have oneBound : ((i ≐ zero) :: Γ) ⊢[PRAAx]
        bounded GaussianRationalSyntheticDivision.qone (A a N x) one :=
      bounded_radius_mono_one (GaussianRootRadius.A_positive a N x) GaussianRationalReciprocal.qone_bounded
    exact bound_congr leading.eqSymm (.eqRefl _) (.eqRefl _) oneBound
  · have inside : ((i ≐ succ (PTm.pred i)) :: Γ) ⊢[PRAAx] lt (PTm.pred i) N :=
      le_congr Prf.hyp0 (.eqRefl _) hi.wk
    have original := GaussianCoefficientNameBounds.sample_bound a N x (PTm.monus N (succ (PTm.pred i))) s hCN.wk
      (GaussianApproximateFactorization.remaining_active N (PTm.pred i) inside)
    have bigger := bounded_radius_mono_one (GaussianMonicResidualRadius.monus_le_left (A a N x) one) original
    exact bound_congr ((entry_congr (.eqRefl _) Prf.hyp0).eqTrans
      (GaussianRootSamples.sample_coefficient a N s x (PTm.pred i) inside)).eqSymm (.eqRefl _) (.eqRefl _) bigger

/-- All stored sample coefficients inherit their original Euclidean A bound;
no coefficient-bound contract is an input. -/
theorem sample_coefficients (a : PR 3) (N s x : PTm n) (hCN : Γ ⊢[PRAAx] CN a N x) : Γ ⊢[PRAAx]
    GaussianEuclideanResidualRadius.coefficientBounds (GaussianRootSamples.sample a N s x) (A a N x) := by
  refine .allI (.impI ?_)
  have cnShift : Γ.map Fm.shift ⊢[PRAAx] CN a (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianCoefficientNameBounds.subst_CN,Syn.shift] using hCN.shift
  have inside : (lt (var 0) (length (Syn.shift (GaussianRootSamples.sample a N s x))) :: Γ.map Fm.shift) ⊢[PRAAx]
      le (var 0) (Syn.shift N) :=
    (succ_monus_succ _ _).eqSymm.eqTrans
      (lt_congr (.eqRefl _) (GaussianRootSamples.sample_length a (Syn.shift N) (Syn.shift s) (Syn.shift x))
        (by simpa only [Syn.shift,GaussianRootSamples.subst_sample] using Prf.hyp0))
  simpa only [Syn.shift,GaussianRootSamples.subst_sample,GaussianCoefficientNameBounds.subst_A] using
    sample_coefficient_bound a (Syn.shift N) (Syn.shift s) (Syn.shift x) (var 0) cnShift.wk inside

/-- The actual listed product root has a small actual sample-polynomial
residual at radius R, obtained from actual AF and CN discrepancies. -/
theorem sample_at_listed_root (step a : PR 3) (N t s x i : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    bounded (evaluate (GaussianRootSamples.sample a N s x) (entry (roots step a N t x) i))
      (GaussianRootSchedule.coefficientConstant N (R a N x)*coefficientNumerator a N t s x)
      (coefficientDenominator a N t s x) := by
  have positive := GaussianRootFiniteEvaluation.coefficient_denominator_positive (Γ := Γ) a N t s x
  have difference := GaussianRootFiniteEvaluation.evaluation_distance step a N (R a N x) t s x
    (entry (roots step a N t x) i) hRD hCN hN (radius_positive a N x)
    (GaussianRootRadius.root_radius step a N t x i hRD hCN hN hi)
  have reverse := distance_symmetric _ _ _ _ positive difference
  have zeroDistance := distance_congr (.eqRefl _) (GaussianRootRadius.listed_zero step a N t x i hi)
    (.eqRefl _) (.eqRefl _) reverse
  exact (GaussianReconstructionRoots.distance_zero_iff _ _ _ positive).iffMp zeroDistance

/-- The estimate at an actual supplied finite hit index. All radius and
residual facts about that listed point are derived from RD and CN. -/
theorem point_residual_bound (step a : PR 3) (N U t s x z p q i : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hRU : Γ ⊢[PRAAx] le (R a N x) U)
    (hz : Γ ⊢[PRAAx] bounded z U one) (hq : Γ ⊢[PRAAx] le one q)
    (hi : Γ ⊢[PRAAx] lt i N) (hHit : Γ ⊢[PRAAx] distanceBounded z (entry (roots step a N t x) i) p q) : Γ ⊢[PRAAx]
    bounded (evaluate (GaussianRootSamples.sample a N s x) z)
      (numerator a N U t s x p q) (denominator a N t s x q) := by
  have rootBound := GaussianRootRadius.root_radius step a N t x i hRD hCN hN hi
  have rootAtU := bounded_radius_mono_one hRU rootBound
  have variation := GaussianRationalHornerLipschitz.evaluation_bound (GaussianRootSamples.sample a N s x) z
    (entry (roots step a N t x) i) N U (A a N x) p q
    (GaussianRootSamples.sample_length a N s x) (sample_coefficients a N s x hCN) hz rootAtU hq hHit
  exact GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ hq
    (GaussianRootFiniteEvaluation.coefficient_denominator_positive a N t s x) variation
    (sample_at_listed_root step a N t s x i hRD hCN hN hi)


/-- Intuitionistic elimination of an original finite hit yields the
actual sampled residual. No minimizing index or residual bound is supplied. -/
theorem residual_from_hit (step a : PR 3) (N U t s x z p q : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hRU : Γ ⊢[PRAAx] le (R a N x) U)
    (hz : Γ ⊢[PRAAx] bounded z U one) (hq : Γ ⊢[PRAAx] le one q)
    (hHit : Γ ⊢[PRAAx] hit z (roots step a N t x) p q) : Γ ⊢[PRAAx]
    bounded (evaluate (GaussianRootSamples.sample a N s x) z)
      (numerator a N U t s x p q) (denominator a N t s x q) := by
  refine .exE hHit ?_
  let E : Fm PTm (n+1) := lt (var 0) (length (Syn.shift (roots step a N t x))) ⋏
    distanceBounded (Syn.shift z) (entry (Syn.shift (roots step a N t x)) (var 0)) (Syn.shift p) (Syn.shift q)
  have rdShift : Γ.map Fm.shift ⊢[PRAAx] monicRD step := by
    simpa only [Fm.shift,GaussianFactorParameters.subst_monicRD] using hRD.shift
  have cnShift : Γ.map Fm.shift ⊢[PRAAx] CN a (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianCoefficientNameBounds.subst_CN,Syn.shift] using hCN.shift
  have nShift : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hN.shift
  have ruShift : Γ.map Fm.shift ⊢[PRAAx] le (R a (Syn.shift N) (Syn.shift x)) (Syn.shift U) := by
    simpa only [Fm.shift,subst_le,GaussianCoefficientNameBounds.subst_R,Syn.shift] using hRU.shift
  have zShift : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift z) (Syn.shift U) one := by
    simpa only [Fm.shift,GaussianRationalMetric.subst_bounded,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hz.shift
  have qShift : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift q) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hq.shift
  have inside : E :: Γ.map Fm.shift ⊢[PRAAx] lt (var 0) (Syn.shift N) :=
    lt_congr (.eqRefl _) (GaussianRootRadius.roots_length (Γ := Γ.map Fm.shift) step a (Syn.shift N) (Syn.shift t) (Syn.shift x)).wk
      (by simpa only [E,Syn.shift,GaussianRootRadius.subst_roots] using Prf.andE₁ Prf.hyp0)
  have near : E :: Γ.map Fm.shift ⊢[PRAAx] distanceBounded (Syn.shift z)
      (entry (roots step a (Syn.shift N) (Syn.shift t) (Syn.shift x)) (var 0)) (Syn.shift p) (Syn.shift q) := by
    simpa only [E,Syn.shift,GaussianRootRadius.subst_roots] using Prf.andE₂ Prf.hyp0
  have result := point_residual_bound step a (Syn.shift N) (Syn.shift U) (Syn.shift t) (Syn.shift s) (Syn.shift x)
    (Syn.shift z) (Syn.shift p) (Syn.shift q) (var 0) rdShift.wk cnShift.wk nShift.wk ruShift.wk zShift.wk qShift.wk inside near
  simpa only [E,Fm.shift,GaussianRationalMetric.subst_bounded,GaussianRationalHorner.subst_evaluate,
    GaussianRootSamples.subst_sample,subst_numerator,subst_denominator,Syn.shift] using result

theorem denominator_positive (a : PR 3) (N t s x q : PTm n) (hq : Γ ⊢[PRAAx] le one q) :
    Γ ⊢[PRAAx] le one (denominator a N t s x q) :=
  GaussianRationalHorner.positive_product _ _ hq (GaussianRootFiniteEvaluation.coefficient_denominator_positive a N t s x)


/-- The actual residual and its exact computed radius are returned together. -/
def output (a : PR 3) (N U t s x z p q : PTm n) : PTm n :=
  pairT (evaluate (GaussianRootSamples.sample a N s x) z)
    (pairT (numerator a N U t s x p q) (denominator a N t s x q))
def outputF (a : PR 3) : PR 8 := PTm.toPR
  (output a (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
def run (a : PR 3) (N U t s x z p q : PTm n) : PTm n := PTm.app (outputF a) ![N,U,t,s,x,z,p,q]

ipra_subst output
ipra_subst run

theorem program_at (a : PR 3) (N U t s x z p q : PTm n) : Γ ⊢[PRAAx]
    run a N U t s x z p q ≐ output a N U t s x z p q := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output a (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) : PTm 8) ![N,U,t,s,x,z,p,q]

theorem output_value (a : PR 3) (N U t s x z p q : PTm n) : Γ ⊢[PRAAx]
    fstT (run a N U t s x z p q) ≐ evaluate (GaussianRootSamples.sample a N s x) z :=
  (program_at a N U t s x z p q).fstE
theorem output_numerator (a : PR 3) (N U t s x z p q : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run a N U t s x z p q)) ≐ numerator a N U t s x p q :=
  (program_at a N U t s x z p q).sndE.fstE
theorem output_denominator (a : PR 3) (N U t s x z p q : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run a N U t s x z p q)) ≐ denominator a N t s x q :=
  (program_at a N U t s x z p q).sndE.sndE

theorem program_certificate (step a : PR 3) (N U t s x z p q : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hRU : Γ ⊢[PRAAx] le (R a N x) U)
    (hz : Γ ⊢[PRAAx] bounded z U one) (hq : Γ ⊢[PRAAx] le one q)
    (hHit : Γ ⊢[PRAAx] hit z (roots step a N t x) p q) : Γ ⊢[PRAAx]
    le one (sndT (sndT (run a N U t s x z p q))) ⋏
      bounded (fstT (run a N U t s x z p q))
        (fstT (sndT (run a N U t s x z p q))) (sndT (sndT (run a N U t s x z p q))) :=
  .andI (le_congr (.eqRefl _) (output_denominator a N U t s x z p q).eqSymm (denominator_positive a N t s x q hq))
    (bound_congr (output_value a N U t s x z p q).eqSymm (output_numerator a N U t s x z p q).eqSymm
      (output_denominator a N U t s x z p q).eqSymm
      (residual_from_hit step a N U t s x z p q hRD hCN hN hRU hz hq hHit))

theorem sampled_euclidean_coefficients_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (CN a (var 0) (var 2) ⟶ GaussianEuclideanResidualRadius.coefficientBounds
      (GaussianRootSamples.sample a (var 0) (var 1) (var 2)) (A a (var 0) (var 2))) :=
  closeUniv 3 (.impI (sample_coefficients _ _ _ _ Prf.hyp0))

theorem sampled_listed_root_residual_closed (step a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (monicRD step ⟶ CN a (var 0) (var 3) ⟶ le one (var 0) ⟶ lt (var 4) (var 0) ⟶
      bounded (evaluate (GaussianRootSamples.sample a (var 0) (var 2) (var 3))
        (entry (roots step a (var 0) (var 1) (var 3)) (var 4)))
        (GaussianRootSchedule.coefficientConstant (var 0) (R a (var 0) (var 3))*
          coefficientNumerator a (var 0) (var 1) (var 2) (var 3))
        (coefficientDenominator a (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (sample_at_listed_root _ _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem finite_residual_from_hit_closed (step a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (monicRD step ⟶ CN a (var 0) (var 4) ⟶ le one (var 0) ⟶ le (R a (var 0) (var 4)) (var 1) ⟶
      bounded (var 5) (var 1) one ⟶ le one (var 7) ⟶ hit (var 5) (roots step a (var 0) (var 2) (var 4)) (var 6) (var 7) ⟶
      bounded (evaluate (GaussianRootSamples.sample a (var 0) (var 3) (var 4)) (var 5))
        (numerator a (var 0) (var 1) (var 2) (var 3) (var 4) (var 6) (var 7))
        (denominator a (var 0) (var 2) (var 3) (var 4) (var 7))) := by
  apply closeUniv 8
  refine .impI (.impI (.impI (.impI (.impI (.impI (.impI ?_))))))
  exact residual_from_hit _ _ _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem residual_from_hit_program_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (run a (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ≐
      output a (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) :=
  closeUniv 8 (program_at _ _ _ _ _ _ _ _ _)

theorem residual_from_hit_certificate_closed (step a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (monicRD step ⟶ CN a (var 0) (var 4) ⟶ le one (var 0) ⟶ le (R a (var 0) (var 4)) (var 1) ⟶
      bounded (var 5) (var 1) one ⟶ le one (var 7) ⟶ hit (var 5) (roots step a (var 0) (var 2) (var 4)) (var 6) (var 7) ⟶
      (le one (sndT (sndT (run a (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))) ⋏
        bounded (fstT (run a (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))
          (fstT (sndT (run a (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))))
          (sndT (sndT (run a (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))))) := by
  apply closeUniv 8
  refine .impI (.impI (.impI (.impI (.impI (.impI (.impI ?_))))))
  exact program_certificate _ _ _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

end LeanProofs.IPRA.Analysis.GaussianRootResidualFromHit
