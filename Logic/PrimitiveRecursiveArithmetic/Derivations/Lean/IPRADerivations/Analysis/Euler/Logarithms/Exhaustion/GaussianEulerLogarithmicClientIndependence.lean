import IPRADerivations.Analysis.Euler.Logarithms.Exhaustion.GaussianEulerLogarithmicClientRate
import IPRADerivations.Analysis.Euler.Logarithms.Exhaustion.GaussianEulerLogarithmicClientIntervalName
import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicIntervalAdditivity
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactClientIndependence

/-!
# Source-only independence of original logarithmic compact clients

Both actual compact inputs and the local evaluator agreement are
derived from original numerical sources. The generic common-grid
comparison then identifies the independently retimed original names.
Combining it with actual interval rescaling gives canonical client
alignment at a new denominator, radius certificate and top guard.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicClientIndependence

open_ipra
open GaussianEulerLogarithmicClientIntervalName (nameF data compact_input canonical_source rescaled_source)
open GaussianEulerLogarithmicCompactName (evaluatorF fixedData)
open GaussianEulerLogarithmicMultiplier (lipschitz)
open GaussianNameEquivalence (crossEquivalent cross_at cross_trans)
open GaussianCoefficientNameBounds (unit)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R S B a C G E T F U : PTm n) : Fm PTm n :=
  GaussianEulerLogarithmicClientIntervalName.source z R B a C G E T ⋏
    GaussianEulerLogarithmicClientIntervalName.source z S B a C G F U
ipra_subst source

theorem agreement_at (t j z R S B a C G E T F U : PTm n)
    (h : Γ ⊢[PRAAx] source z R S B a C G E T F U)
    (ht : Γ ⊢[PRAAx] GaussianCompactRiemannName.inside a C G t) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianCompactRiemannName.evaluatorName evaluatorF) (GaussianCompactRiemannName.evaluatorName evaluatorF)
      (GaussianCompactRiemannName.nameData t (fixedData j R E T z B))
      (GaussianCompactRiemannName.nameData t (fixedData j S F U z B)) :=
  GaussianEulerLogarithmicClientRate.wrapped_client_cross t j z R S B E T F U
    (.andI (.andI h.andE₁.andE₁ (GaussianEulerLogarithmicClientIntervalName.domain_of_inside z R B a C G E T t h.andE₁ ht))
      (.andI h.andE₂.andE₁ (GaussianEulerLogarithmicClientIntervalName.domain_of_inside z S B a C G F U t h.andE₂ ht)))

theorem local_agreement (j z R S B a C G E T F U : PTm n)
    (h : Γ ⊢[PRAAx] source z R S B a C G E T F U) : Γ ⊢[PRAAx]
    GaussianCompactClientIndependence.localAgreement evaluatorF evaluatorF a C G
      (fixedData j R E T z B) (fixedData j S F U z B) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift S) (Syn.shift B)
      (Syn.shift a) (Syn.shift C) (Syn.shift G) (Syn.shift E) (Syn.shift T) (Syn.shift F) (Syn.shift U) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  simpa only [GaussianCompactClientIndependence.localAgreement,GaussianEulerLogarithmicCompactName.subst_fixedData,Syn.shift] using
    agreement_at (var 0) (Syn.shift j) (Syn.shift z) (Syn.shift R) (Syn.shift S) (Syn.shift B)
      (Syn.shift a) (Syn.shift C) (Syn.shift G) (Syn.shift E) (Syn.shift T) (Syn.shift F) (Syn.shift U) hs.wk Prf.hyp0

theorem comparison_input (j z R S B a C G E T F U : PTm n)
    (h : Γ ⊢[PRAAx] source z R S B a C G E T F U) : Γ ⊢[PRAAx]
    GaussianCompactClientIndependence.input evaluatorF evaluatorF a C G (lipschitz j R E T) T
      (lipschitz j S F U) U (fixedData j R E T z B) (fixedData j S F U z B) :=
  .andI (compact_input j z R B a C G E T h.andE₁)
    (.andI (compact_input j z S B a C G F U h.andE₂) (local_agreement j z R S B a C G E T F U h))

theorem original_independence (j z R S B a C G E T F U : PTm n)
    (h : Γ ⊢[PRAAx] source z R S B a C G E T F U) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (data j z R B a C G E T) (data j z S B a C G F U) :=
  GaussianCompactClientIndependence.name_independence evaluatorF evaluatorF a C G (lipschitz j R E T) T
    (lipschitz j S F U) U (fixedData j R E T z B) (fixedData j S F U z B)
    (comparison_input j z R S B a C G E T F U h)

theorem original_observations (p q j z R S B a C G E T F U : PTm n)
    (h : Γ ⊢[PRAAx] source z R S B a C G E T F U) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data j z R B a C G E T)) (ap2 nameF q (data j z S B a C G F U))
      (unit p+unit q) (unit p*unit q) := cross_at _ _ _ _ p q (original_independence j z R S B a C G E T F U h)

/-- This aligns the actual canonical names after interval denominator
rescaling while allowing a different legitimate radius and top guard. -/
theorem original_rescaled_client (k j z R S B a C E T U : PTm n)
    (hLeft : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.intervalSource z R B a C E T)
    (hRight : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.intervalSource z S B (k*a) (k*C) (k*E) U)
    (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (GaussianEulerLogarithmicIntervalName.data j z R B a C E T)
      (GaussianEulerLogarithmicIntervalName.data j z S B (k*a) (k*C) (k*E) U) :=
  cross_trans nameF nameF nameF _ (GaussianEulerLogarithmicIntervalAdditivity.rescaledData k j z R B a C E T) _
    (GaussianEulerLogarithmicIntervalAdditivity.original_rescaling k j z R B a C E T hLeft hk)
    (original_independence j z R S B (k*a) (k*C) (k*E) E T (k*E) U
      (.andI (rescaled_source k z R B a C E E T (canonical_source z R B a C E T hLeft) hk)
        (canonical_source z S B (k*a) (k*C) (k*E) U hRight)))

theorem actual_logarithmic_original_client_name_independence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) ⟶
      crossEquivalent nameF nameF (data (var 0) (var 1) (var 2) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9))
        (data (var 0) (var 1) (var 3) (var 4) (var 5) (var 6) (var 7) (var 10) (var 11))) :=
  closeUniv 12 (.impI (original_independence _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicClientIndependence
