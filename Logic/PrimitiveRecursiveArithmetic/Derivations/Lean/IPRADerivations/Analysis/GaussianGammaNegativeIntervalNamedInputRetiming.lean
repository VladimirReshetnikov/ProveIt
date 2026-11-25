import IPRADerivations.Analysis.GaussianGammaNegativeIntervalNamedInput
import IPRADerivations.Analysis.GaussianNamedPositiveLateLogSource
import IPRADerivations.Analysis.RationalCompactObservationTightening

/-!
# Late real observations inside a negative Gamma interval

Two named order bounds place the real offset in a pole-separated
interval. Halving the certified margin makes every sufficiently late
observation an admissible input to the rational evaluation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedInputRetiming

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedEulerUnitTime (source)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at)
open GaussianNamedPositiveLateLogSource (retimedF retimedData sample_at)
open GaussianNamedRealOrderTransport (remove_upper_slack precision)
open GaussianNamedRightHalfPlane (threshold threshold_budget)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product)
open GaussianSignedNameExponentialOrder (realSamples real_sample_at)
open GaussianStirlingMultiplicativeBoundsOrder (fraction_real_part)
open GaussianUnitIntervalInputDecoding (lowerPoint upperPoint)
open RationalCompactObservationTightening (lower_guard upper_guard)
open RationalGaussianEmbedding (axis_congr)
open RationalValueBounds (upper upper_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def orderedWindow (f : PR 2) (x E : PTm n) : Fm PTm n :=
  pointCN f x ⋏ (realSamples f x ⋏ (le one E ⋏
    (realOrder constantF f (fraction one E) x ⋏ realOrder f constantF x (fraction (monus E one) E))))

@[simp] theorem subst_orderedWindow {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x E : PTm n) :
    (orderedWindow f x E).subst σ = orderedWindow f (Syn.subst σ x) (Syn.subst σ E) := by
  simp [orderedWindow,one]

private theorem left_observation (f : PR 2) (p x E : PTm n) (hs : Γ ⊢[PRAAx] orderedWindow f x E) :
    Γ ⊢[PRAAx] upper (lowerPoint E) (fstT (ap2 f p x)) one (unit p) := by
  let a := fraction one E
  let t := precision (lowerPoint E) (fstT (ap2 f p x)) (unit p) one
  have h := real_order_at constantF f a x t p hs.andE₂.andE₂.andE₂.andE₁
  apply remove_upper_slack _ _ _ _ one
  exact upper_congr ((congrFst (constant_at t a)).eqTrans (fraction_real_part one E hs.andE₂.andE₂.andE₁))
    (.eqRefl _) (by ipra_ring) (by ipra_ring) h

private theorem right_observation (f : PR 2) (p x E : PTm n) (hs : Γ ⊢[PRAAx] orderedWindow f x E) :
    Γ ⊢[PRAAx] upper (fstT (ap2 f p x)) (upperPoint E) one (unit p) := by
  let a := fraction (monus E one) E
  let t := precision (fstT (ap2 f p x)) (upperPoint E) (unit p) one
  have h := real_order_at f constantF x a p t hs.andE₂.andE₂.andE₂.andE₂
  apply remove_upper_slack _ _ _ _ one
  exact upper_congr (.eqRefl _) ((congrFst (constant_at t a)).eqTrans (fraction_real_part (monus E one) E hs.andE₂.andE₂.andE₁))
    (by ipra_ring) (by ipra_ring) h

theorem late_observation (f : PR 2) (p x E : PTm n) (hs : Γ ⊢[PRAAx] orderedWindow f x E)
    (hp : Γ ⊢[PRAAx] le (threshold E) p) :
    Γ ⊢[PRAAx] GaussianUnitIntervalInputDecoding.source (ap2 f p x) (two*E) := by
  let a := ap2 f p x
  have hE := hs.andE₂.andE₂.andE₁
  have budget := threshold_budget p E hp
  have lo := lower_guard (fstT a) E (two*E) (unit p) hE (le_refl _) budget (left_observation f p x E hs)
  have hi := upper_guard (fstT a) E (two*E) (unit p) hE (le_refl _) budget (right_observation f p x E hs)
  exact .andI (real_sample_at f x p hs.andE₂.andE₁).andE₂
    (.andI (positive_product _ _ (le_succ_self one) hE) (.andI lo hi))

theorem retimed_observation (f : PR 2) (p x E : PTm n) (hs : Γ ⊢[PRAAx] orderedWindow f x E) :
    Γ ⊢[PRAAx] GaussianUnitIntervalInputDecoding.source (ap2 (retimedF f) p (retimedData x E)) (two*E) := by
  have raw := late_observation f (p+threshold E) x E hs (le_add_left _ _)
  simpa using Prf.eqSubst1 (Ax := PRAAx) (Γ := Γ)
    (GaussianUnitIntervalInputDecoding.source (var 0) (Syn.shift (two*E)))
    (sample_at f p x E).eqSymm (by simpa using raw)

theorem retimed_source (f : PR 2) (x E : PTm n) (hs : Γ ⊢[PRAAx] orderedWindow f x E) :
    Γ ⊢[PRAAx] source (retimedF f) (retimedData x E) (two*E) := by
  refine .andI (GaussianNamedPositiveLateLogSource.name_regular f x E hs.andE₁) (.allI ?_)
  have hw : Γ.map Fm.shift ⊢[PRAAx] orderedWindow f (Syn.shift x) (Syn.shift E) :=
    by simpa only [Fm.shift, subst_orderedWindow,Syn.shift] using hs.shift
  simpa only [GaussianNamedEulerUnitKernel.admissibleSamples,Syn.shift,
    GaussianNamedPositiveLateLogSource.subst_retimedData,PTm.subst_mul,two,one,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    retimed_observation f (var 0) (Syn.shift x) (Syn.shift E) hw

theorem actual_original_negative_Gamma_named_input_retiming_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (orderedWindow f (var 0) (var 1) ⟶
        (source (retimedF f) (retimedData (var 0) (var 1)) (two*var 1) ⋏
         crossEquivalent f (retimedF f) (var 0) (retimedData (var 0) (var 1)))) :=
  closeUniv 2 (.impI (.andI (retimed_source _ _ _ Prf.hyp0)
    (GaussianNamedPositiveLateLogSource.original_cross _ _ _ Prf.hyp0.andE₁)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedInputRetiming
