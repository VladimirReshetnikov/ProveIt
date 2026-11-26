import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianGeneralFTATelescope
import IPRADerivations.Analysis.Polynomials.GaussianRationalAllCoefficientPerturbation
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianGeneralFTACoefficientDrift

/-!
# The computed general FTA root name and its original sample residuals

The actual root-name schedule is J(t)=K(t+H+2), M(t)=J(t)+L.
All constants, coefficient samples, trajectory values and precisions are
numerical object-theory inputs. The finite decay and precision budgets
are derived from the computed constants, without incoming root bounds.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGeneralFTARootName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianGeneralFTAConstants (B R C K H L QNum QDen rhoNum)
open LeanProofs.IPRA.Analysis.GaussianGeneralFTATrajectory (trajectory polynomial J M alpha nameF nameData)
open LeanProofs.IPRA.Analysis.GaussianGeneralPolynomialSamples (sourceInput sample)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (unit unit_positive)
open LeanProofs.IPRA.Analysis.GaussianDescentClockArithmetic (positive_product)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def beta (a : PR 3) (N h x t : PTm n) : PTm n := evaluate (sample a N (M a N h x t) x) (alpha a N h x t)
@[simp] theorem subst_beta {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x t : PTm n) :
    Syn.subst σ (beta a N h x t) = beta a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) (Syn.subst σ t) := by simp [beta]

theorem J_monotone (a : PR 3) (N h x t u : PTm n) (htu : Γ ⊢[PRAAx] le t u) : Γ ⊢[PRAAx]
    le (J a N h x t) (J a N h x u) :=
  le_congr (mul_comm _ _) (mul_comm _ _)
    (mul_le_mul_right (K N) (add_le_add_right two (add_le_add_right (H a N h x) htu)))

/-- The same source bit-length budget pays for every smaller natural
amplitude. The finite dyadic theorem is used at the actual scheduled J. -/
theorem scheduled_decay (a : PR 3) (N h x t V : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hV : Γ ⊢[PRAAx] le V (unit (H a N h x))) : Γ ⊢[PRAAx]
    le (V*pw (rhoNum N) (J a N h x t)*unit (t+two)) (pw (K N) (J a N h x t)) := by
  have raw := GaussianDescentClockArithmetic.dyadic_decay (Γ := Γ) (K N) (t+H a N h x+two)
    (GaussianGeneralFTAConstants.K_positive N hN)
  have amp : Γ ⊢[PRAAx] le (V*unit (t+two)) (unit (t+H a N h x+two)) := by
    refine le_congr (.eqRefl _) ?_ (mul_le_mul_right (unit (t+two)) hV)
    exact ((pw_add two (H a N h x) (t+two)).eqSymm.eqTrans
      (congrAp2 powF (by ipra_ring) (.eqRefl _)))
  exact le_trans (b := unit (t+H a N h x+two)*pw (rhoNum N) (J a N h x t))
    (le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right _ amp)) raw

theorem tail_schedule_budget (a : PR 3) (N h x t : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    le (GaussianGeneralFTATelescope.tailNumerator a N h x (J a N h x t)*unit (t+two))
      (GaussianGeneralFTATelescope.tailDenominator N (J a N h x t)) :=
  scheduled_decay a N h x t _ hN (GaussianGeneralFTAConstants.H_budget a N h x)

theorem initial_amplitude_budget (a : PR 3) (N h x : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    le (B a x) (unit (H a N h x)) := by
  have c : Γ ⊢[PRAAx] le (C a N h x) (R a N h x*C a N h x*K N) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (le_mul_mono (le_refl (C a N h x))
        (positive_product _ _ (GaussianGeneralFTAConstants.R_positive a N h x)
          (GaussianGeneralFTAConstants.K_positive N hN)))
  exact le_trans (GaussianGeneralFTAConstants.C_ge_B a N h x hN)
    (le_trans c (GaussianGeneralFTAConstants.H_budget a N h x))

theorem residual_schedule_budget (a : PR 3) (N h x t : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    le ((B a x*pw (QNum N) (J a N h x t))*unit (t+two)) (pw (QDen N) (J a N h x t)) := by
  have hK := GaussianGeneralFTAConstants.K_positive (Γ := Γ) N hN
  have hD := GaussianGeneralFTAConstants.QDen_positive (Γ := Γ) N
  have raised := RationalNonnegativePowerOrder.power_order_preserve _ _ _ _ (J a N h x t) hD hK
    (GaussianGeneralFTARates.Q_le_rho N hN)
  have rate := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (RationalNonnegativePowers.power_represents _ _ (J a N h x t) hD)
    (RationalNonnegativePowers.power_represents _ _ (J a N h x t) hK) raised
  have first := mul_le_mul_right (B a x*unit (t+two)) rate
  have second := mul_le_mul_right (pw (QDen N) (J a N h x t))
    (scheduled_decay a N h x t (B a x) hN (initial_amplitude_budget a N h x hN))
  apply RationalValueBounds.positive_cancel
    (GaussianPolynomialPerturbation.power_positive (K N) (J a N h x t) hK)
  exact le_trans (b := B a x*pw (rhoNum N) (J a N h x t)*unit (t+two)*pw (QDen N) (J a N h x t))
    (le_congr (by ipra_ring) (by ipra_ring) first)
    second

theorem later_coherence_cross (s m : PTm n) (hms : Γ ⊢[PRAAx] le m s) : Γ ⊢[PRAAx]
    le ((unit s+unit m)*unit m) (two*(unit s*unit m)) := by
  have unitOrder : Γ ⊢[PRAAx] le (unit m) (unit s) :=
    GaussianFactorBudget.power_monotone_length two m s (le_succ_self one) hms
  exact le_congr (.eqRefl _) (by ipra_ring)
    (mul_le_mul_right (unit m) (add_le_add₂ (le_refl (unit s)) unitOrder))

theorem later_sample_gap (a : PR 3) (N h x t s : PTm n)
    (hCN : Γ ⊢[PRAAx] GaussianGeneralCoefficientNames.generalCN a N x)
    (hs : Γ ⊢[PRAAx] le (M a N h x t) s)
    (hz : Γ ⊢[PRAAx] bounded (alpha a N h x t) (R a N h x) one) : Γ ⊢[PRAAx]
    distanceBounded (evaluate (sample a N s x) (alpha a N h x t)) (beta a N h x t)
      (two*(succ N*pw (R a N h x) N)) (unit (M a N h x t)) := by
  have actual := GaussianRationalAllCoefficientPerturbation.evaluation_bound _ _ _ N (R a N h x)
    (unit s+unit (M a N h x t)) (unit s*unit (M a N h x t))
    (GaussianGeneralPolynomialSamples.sample_length a N s x)
    (GaussianGeneralPolynomialSamples.sample_length a N (M a N h x t) x)
    (GaussianGeneralFTAConstants.R_positive a N h x) (positive_product _ _ (unit_positive _) (unit_positive _))
    (GaussianGeneralPolynomialSamples.all_coefficient_coherence a N s (M a N h x t) x hCN) hz
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (unit_positive _) (unit_positive _)) (unit_positive _)
    (le_congr (by ipra_ring) (by ipra_ring)
      (mul_le_mul_right (succ N*pw (R a N h x) N) (later_coherence_cross _ _ hs))) actual

theorem later_precision_budget (a : PR 3) (N h x t : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    le ((two*(succ N*pw (R a N h x) N))*unit (t+two+one)) (unit (M a N h x t)) := by
  have twoDen := mul_le_mul_right (two*(succ N*pw (R a N h x) N))
    (GaussianGeneralFTAConstants.QDen_lower (Γ := Γ) N)
  have precision := GaussianGeneralFTACoefficientDrift.computed_precision_budget (Γ := Γ) a N h x
  have fourS : Γ ⊢[PRAAx] le ((two*two)*(succ N*pw (R a N h x) N)) (unit (L a N h x)) :=
    le_trans (le_congr (by ipra_ring) (by unfold GaussianGeneralFTACoefficientDrift.degreeCost; ipra_ring) twoDen) precision
  have exponent := GaussianFactorBudget.power_monotone_length two (t+two) (J a N h x t)
    (le_succ_self one) (GaussianGeneralFTATrajectory.J_lower a N h x t hN)
  have raw := le_mul_mono fourS exponent
  refine le_congr ?_ ?_ raw
  · have step : Γ ⊢[PRAAx] pw two (t+two+one) ≐ pw two (t+two)*two :=
      (congrAp2 powF (succ_eq_add_one (t+two)).eqSymm (.eqRefl two)).eqTrans (pw_succ two (t+two))
    refine withEq step fun e => ?_
    simp only [unit]
    apply deriveNat; ipra_simps; rw [e]; ring
  · exact ((mul_comm _ _).eqTrans (pw_add two (J a N h x t) (L a N h x)).eqSymm)

theorem source_degree (a : PR 3) (N k h x : PTm n) (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    le one N := GaussianGeneralFTARadiusStep.source_degree a N k h x hSource

/-- This is the exact Cauchy margin of the source construction, at the
actual scheduled trajectory points. -/
theorem actual_alpha_cauchy (a : PR 3) (N k h x t u : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) (htu : Γ ⊢[PRAAx] le t u) : Γ ⊢[PRAAx]
    distanceBounded (alpha a N h x u) (alpha a N h x t) one (unit (t+two)) := by
  have hN := source_degree a N k h x hSource
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
    (GaussianPolynomialPerturbation.power_positive _ _ (GaussianGeneralFTAConstants.K_positive N hN)) (unit_positive _)
    (le_congr (.eqRefl _) (one_mul _).eqSymm (tail_schedule_budget a N h x t hN))
    (GaussianGeneralFTATelescope.source_tail a N k h x (J a N h x t) (J a N h x u) hSource (J_monotone a N h x t u htu))

theorem alpha_disk (a : PR 3) (N k h x t : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    bounded (alpha a N h x t) (R a N h x) one :=
  GaussianGeneralFTAInvariant.point_disk a N k h x (J a N h x t) hSource

theorem actual_beta_zero_bound (a : PR 3) (N k h x t : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    bounded (beta a N h x t) one (unit (t+two)) := by
  have hN := source_degree a N k h x hSource
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (GaussianPolynomialPerturbation.power_positive _ _ (GaussianGeneralFTAConstants.QDen_positive N)) (unit_positive _)
    (le_congr (.eqRefl _) (one_mul _).eqSymm (residual_schedule_budget a N h x t hN))
    (GaussianGeneralFTAInvariant.residual_bound a N k h x (J a N h x t) hSource)

theorem actual_later_sample_gap (a : PR 3) (N k h x t s : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) (hs : Γ ⊢[PRAAx] le (M a N h x t) s) : Γ ⊢[PRAAx]
    distanceBounded (evaluate (sample a N s x) (alpha a N h x t)) (beta a N h x t)
      one (unit (t+two+one)) :=
  GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _ (unit_positive _) (unit_positive _)
    (le_congr (.eqRefl _) (one_mul _).eqSymm
      (later_precision_budget a N h x t (source_degree a N k h x hSource)))
    (later_sample_gap a N h x t s (Prf.andE₁ hSource) hs (alpha_disk a N k h x t hSource))

theorem two_unit_margin (t : PTm n) : Γ ⊢[PRAAx] le (two*unit t) (unit (t+two)) :=
  le_congr ((pw_succ two t).eqTrans (mul_comm _ _)) (.eqRefl _)
    (GaussianFactorBudget.power_monotone_length two (succ t) (t+two) (le_succ_self one)
      (le_of_eq_add (d := one) (by ipra_ring)))

/-- Every original later coefficient sample has a small actual Horner
value at the constructed root observation. No represented-value law is
assumed, and the leading coefficient is the original observation. -/
theorem actual_later_sample_root (a : PR 3) (N k h x t s : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) (hs : Γ ⊢[PRAAx] le (M a N h x t) s) : Γ ⊢[PRAAx]
    bounded (evaluate (sample a N s x) (alpha a N h x t)) one (unit t) := by
  have gap := actual_later_sample_gap a N k h x t s hSource hs
  have lower : Γ ⊢[PRAAx] le (unit (t+two)) (unit (t+two+one)) :=
    GaussianFactorBudget.power_monotone_length two (t+two) (t+two+one) (le_succ_self one) (le_add_right _ _)
  have common := GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _ (unit_positive _) (unit_positive _)
    (le_congr (one_mul _).eqSymm (one_mul _).eqSymm lower) gap
  have sum := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ (unit_positive _) (unit_positive _)
    common (actual_beta_zero_bound a N k h x t hSource)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (unit_positive _) (unit_positive _)) (unit_positive _)
    (le_congr (by ipra_ring) (one_mul _).eqSymm
      (mul_le_mul_right (unit (t+two)) (two_unit_margin t))) sum

theorem named_alpha_cauchy (a : PR 3) (N k h x t u : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) (htu : Γ ⊢[PRAAx] le t u) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF a) u (nameData N h x)) (ap2 (nameF a) t (nameData N h x)) one (unit (t+two)) :=
  GaussianRationalDistanceOrder.distance_congr (GaussianGeneralFTATrajectory.name_at a N h x u).eqSymm
    (GaussianGeneralFTATrajectory.name_at a N h x t).eqSymm (.eqRefl _) (.eqRefl _)
    (actual_alpha_cauchy a N k h x t u hSource htu)

theorem named_later_sample_root (a : PR 3) (N k h x t s : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) (hs : Γ ⊢[PRAAx] le (M a N h x t) s) : Γ ⊢[PRAAx]
    bounded (evaluate (sample a N s x) (ap2 (nameF a) t (nameData N h x))) one (unit t) :=
  GaussianRationalReciprocal.bound_congr
    (GaussianRationalTranslation.evaluate_congr (.eqRefl _) (GaussianGeneralFTATrajectory.name_at a N h x t).eqSymm)
    (.eqRefl _) (.eqRefl _) (actual_later_sample_root a N k h x t s hSource hs)

theorem source_alpha_cauchy_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶ le (var 4) (var 5) ⟶
      distanceBounded (alpha a (var 0) (var 2) (var 3) (var 5)) (alpha a (var 0) (var 2) (var 3) (var 4))
        one (unit (var 4+two))) :=
  closeUniv 6 (.impI (.impI (actual_alpha_cauchy _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem source_beta_zero_bound_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶ bounded (beta a (var 0) (var 2) (var 3) (var 4))
      one (unit (var 4+two))) :=
  closeUniv 5 (.impI (actual_beta_zero_bound _ _ _ _ _ _ Prf.hyp0))

theorem source_later_sample_root_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶ le (M a (var 0) (var 2) (var 3) (var 4)) (var 5) ⟶
      bounded (evaluate (sample a (var 0) (var 5) (var 3)) (alpha a (var 0) (var 2) (var 3) (var 4)))
        one (unit (var 4))) :=
  closeUniv 6 (.impI (.impI (actual_later_sample_root _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

/-- The two original main inequalities, uniformly in every numerical
input degree, apartness witness, query precision and later sample. -/
theorem original_general_fta_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶ le (var 4) (var 5) ⟶
      le (M a (var 0) (var 2) (var 3) (var 4)) (var 6) ⟶
      (distanceBounded (alpha a (var 0) (var 2) (var 3) (var 5)) (alpha a (var 0) (var 2) (var 3) (var 4))
        one (unit (var 4+two)) ⋏
       bounded (evaluate (sample a (var 0) (var 6) (var 3)) (alpha a (var 0) (var 2) (var 3) (var 4)))
        one (unit (var 4)))) :=
  closeUniv 7 (.impI (.impI (.impI (.andI
    (actual_alpha_cauchy _ _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1)
    (actual_later_sample_root _ _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp0)))))

theorem actual_root_name_program_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((ap2 (nameF a) (var 3) (nameData (var 0) (var 1) (var 2)) ≐ alpha a (var 0) (var 1) (var 2) (var 3)) ⋏
      GaussianRationalHorner.canonical (ap2 (nameF a) (var 3) (nameData (var 0) (var 1) (var 2)))) :=
  closeUniv 4 (.andI (GaussianGeneralFTATrajectory.name_at _ _ _ _ _) (GaussianGeneralFTATrajectory.returned_canonical _ _ _ _ _))

theorem actual_named_general_fta_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶ le (var 4) (var 5) ⟶
      le (M a (var 0) (var 2) (var 3) (var 4)) (var 6) ⟶
      (distanceBounded (ap2 (nameF a) (var 5) (nameData (var 0) (var 2) (var 3)))
        (ap2 (nameF a) (var 4) (nameData (var 0) (var 2) (var 3))) one (unit (var 4+two)) ⋏
       bounded (evaluate (sample a (var 0) (var 6) (var 3))
        (ap2 (nameF a) (var 4) (nameData (var 0) (var 2) (var 3)))) one (unit (var 4)))) :=
  closeUniv 7 (.impI (.impI (.impI (.andI
    (named_alpha_cauchy _ _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1)
    (named_later_sample_root _ _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianGeneralFTARootName
