import IPRADerivations.Analysis.Polynomials.RootFinding.FundamentalTheorem.GaussianGeneralFTARootName
import IPRADerivations.Analysis.Polynomials.RootFinding.Adequacy.GaussianRootApproximationWitness

/-!
# The constructed general FTA program is a fast Gaussian point name

The ordered source Cauchy estimate implies the repository's actual
two-precision pointCN predicate, without a supplied name-validity premise.
The same returned program lies in the computed source disk at every
precision. All degrees, apartness witnesses, persistent data and query
precisions remain numerical inputs of ordinary iPRA derivations.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGeneralFTAName

open_ipra
open LeanProofs.IPRA.Analysis.GaussianGeneralPolynomialSamples (sourceInput)
open LeanProofs.IPRA.Analysis.GaussianGeneralFTATrajectory (alpha nameF nameData)
open LeanProofs.IPRA.Analysis.GaussianGeneralFTAConstants (R)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (unit unit_positive)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalDistanceOrder
  (distance_congr distance_symmetric distance_radius_mono)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem pair_budget (t u : PTm n) : Γ ⊢[PRAAx]
    le (unit u*unit t) ((unit u+unit t)*unit (t+two)) := by
  have growth := GaussianFactorBudget.power_monotone_length (Γ := Γ) two t (t+two)
    (le_succ_self one) (le_add_right _ _)
  have first : Γ ⊢[PRAAx] le (unit u*unit t) (unit u*unit (t+two)) :=
    le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right (unit u) growth)
  exact le_trans first (le_of_eq_add (d := unit t*unit (t+two)) (by ipra_ring))

theorem ordered_coherence (a : PR 3) (N k h x t u : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) (htu : Γ ⊢[PRAAx] le t u) : Γ ⊢[PRAAx]
    distanceBounded (alpha a N h x u) (alpha a N h x t)
      (unit u+unit t) (unit u*unit t) :=
  distance_radius_mono _ _ _ _ _ _ (unit_positive _)
    (GaussianRationalHorner.positive_product _ _ (unit_positive _) (unit_positive _))
    (le_congr (one_mul _).eqSymm (.eqRefl _) (pair_budget t u))
    (GaussianGeneralFTARootName.actual_alpha_cauchy a N k h x t u hSource htu)

theorem coherence (a : PR 3) (N k h x t u : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    distanceBounded (alpha a N h x t) (alpha a N h x u)
      (unit t+unit u) (unit t*unit u) := by
  refine .orE (le_total t u) ?_ (ordered_coherence a N k h x u t hSource.wk Prf.hyp0)
  exact distance_congr (.eqRefl _) (.eqRefl _) (add_comm _ _) (mul_comm _ _)
    (distance_symmetric _ _ _ _
      (GaussianRationalHorner.positive_product _ _ (unit_positive _) (unit_positive _))
      (ordered_coherence a N k h x t u hSource.wk Prf.hyp0))

theorem named_coherence (a : PR 3) (N k h x t u : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF a) t (nameData N h x)) (ap2 (nameF a) u (nameData N h x))
      (unit t+unit u) (unit t*unit u) :=
  distance_congr (GaussianGeneralFTATrajectory.name_at a N h x t).eqSymm
    (GaussianGeneralFTATrajectory.name_at a N h x u).eqSymm (.eqRefl _) (.eqRefl _)
    (coherence a N k h x t u hSource)

theorem name_fast (a : PR 3) (N k h x : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    pointCN (nameF a) (nameData N h x) := by
  refine .allI (.allI ?_)
  have input : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      sourceInput a (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift k))
        (Syn.shift (Syn.shift h)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,GaussianGeneralPolynomialSamples.subst_sourceInput,Syn.shift] using hSource.shift.shift
  simpa only [Syn.shift,GaussianGeneralFTATrajectory.subst_nameData,
    GaussianEuclideanPointDistance.unit,GaussianCoefficientNameBounds.unit] using
    named_coherence a (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift k))
      (Syn.shift (Syn.shift h)) (Syn.shift (Syn.shift x)) (var 1) (var 0) input

theorem named_disk (a : PR 3) (N k h x t : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    bounded (ap2 (nameF a) t (nameData N h x)) (R a N h x) one :=
  GaussianRationalReciprocal.bound_congr (GaussianGeneralFTATrajectory.name_at a N h x t).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianGeneralFTARootName.alpha_disk a N k h x t hSource)

theorem name_bounds (a : PR 3) (N k h x : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    GaussianRootApproximationWitness.pointBounds (nameF a) (R a N h x) (nameData N h x) := by
  refine .allI ?_
  have input : Γ.map Fm.shift ⊢[PRAAx] sourceInput a (Syn.shift N) (Syn.shift k) (Syn.shift h) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianGeneralPolynomialSamples.subst_sourceInput,Syn.shift] using hSource.shift
  simpa only [Syn.shift,GaussianGeneralFTATrajectory.subst_nameData,GaussianGeneralFTAConstants.subst_R,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    named_disk a (Syn.shift N) (Syn.shift k) (Syn.shift h) (Syn.shift x) (var 0) input

theorem constructed_general_root_name_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶
      (pointCN (nameF a) (nameData (var 0) (var 2) (var 3)) ⋏
       GaussianRootApproximationWitness.pointBounds (nameF a) (R a (var 0) (var 2) (var 3))
         (nameData (var 0) (var 2) (var 3)))) :=
  closeUniv 4 (.impI (.andI (name_fast _ _ _ _ _ Prf.hyp0) (name_bounds _ _ _ _ _ Prf.hyp0)))

theorem constructed_general_root_pair_coherence_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶
      distanceBounded (ap2 (nameF a) (var 4) (nameData (var 0) (var 2) (var 3)))
        (ap2 (nameF a) (var 5) (nameData (var 0) (var 2) (var 3)))
        (unit (var 4)+unit (var 5)) (unit (var 4)*unit (var 5))) :=
  closeUniv 6 (.impI (named_coherence _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGeneralFTAName
