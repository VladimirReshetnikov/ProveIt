import IPRADerivations.Analysis.GaussianGammaMinimumFreeze
import IPRADerivations.Analysis.GaussianNamedPositiveLogarithmExponential
import IPRADerivations.Analysis.GaussianStirlingMultiplicativeBoundsStrictOrder

/-!
# Transfer order on the named log Gamma back to the original Gamma

Exponentiation recovers the real-axis projection used to construct the
named logarithm. The projection preserves the literal real coordinate of
every original Gamma observation, so both weak and strict real order
return to the original Gamma names.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaMinimumFreezeOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerVerticalProjection (projected_coordinate)
open GaussianGammaFiniteApproximantName (exponential_input exponentialInputData)
open GaussianGammaMinimumFreeze (nameF data realF retimeF retimeData log_input name_regular)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNamedGammaPositiveLower (source)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at)
open GaussianRationalHorner (canonical canonical_congr)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianStirlingGammaLogarithm (gammaMargin gammaLogMargin)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_transport)
open RationalValueBounds (upper_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => GaussianNamedGamma.nameF
local notation "gd" => GaussianNamedGamma.data
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "expData" => exponentialInputData

private theorem canonical_log_at (f : PR 2) (p x A : PTm n) :
    Γ ⊢[PRAAx] canonical (ap2 (nameF f) p (data x A)) := by
  let h := retimeF f
  let v := retimeData x A
  let r := GaussianNamedPositiveLogarithm.clock p gammaLogMargin
  exact canonical_congr (GaussianNamedPositiveLogarithm.sample_at h p v gammaLogMargin)
    (GaussianPositiveRationalLogarithm.sample_canonical (succ p)
      (GaussianNamedPositiveLogarithm.numerator h r v) (GaussianNamedPositiveLogarithm.denominator h r v))

theorem log_real_samples (f : PR 2) (x A : PTm n) :
    Γ ⊢[PRAAx] realSamples (nameF f) (data x A) := by
  refine .allI ?_
  let X := Syn.shift x
  let B := Syn.shift A
  let p : PTm (n+1) := var 0
  have c := canonical_log_at (Γ := Γ.map Fm.shift) f p X B
  have r : Γ.map Fm.shift ⊢[PRAAx] RationalGaussianEmbedding.axis (ap2 (nameF f) p (data X B)) :=
    GaussianNamedPositiveLogarithm.sample_real (retimeF f) p (retimeData X B) gammaLogMargin
  simpa only [realSamples, GaussianGammaMinimumFreeze.subst_data, Syn.shift, X, B, p] using Prf.andI c r

theorem original_exponential_recovers_projection (f : PR 2) (x A : PTm n) (hs : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] crossEquivalent (E (nameF f)) (realF f) (expData (nameF f) (data x A)) (gd x A) := by
  let T := U (realF f) (gd x A)
  let X := data x A
  let F := nameF f
  let R := GaussianCompactLogarithmBounds.radius gammaLogMargin T
  have h := log_input f x A hs
  have compare := GaussianExponentialRadiusIndependence.same_input_cross F (U F X) R X
    (exponential_input F X (name_regular f x A hs))
    (GaussianNamedPositiveLogarithm.exponential_input (retimeF f) (retimeData x A) gammaLogMargin T h)
  have recover := GaussianNamedPositiveLogarithmExponential.original_recovery (retimeF f) (retimeData x A) gammaLogMargin T h
  have retime := GaussianNamedPositiveLateLogSource.original_cross (realF f) (gd x A) gammaMargin
    (GaussianGammaRealValues.axis_regular _ _ (GaussianNamedGamma.name_regular f x A hs.andE₁))
  exact cross_trans _ _ _ _ _ _ compare
    (cross_trans _ _ _ _ _ _ recover (cross_symm _ _ _ _ retime))

private theorem original_canonical (f : PR 2) (p x A : PTm n) :
    Γ ⊢[PRAAx] canonical (ap2 (G f) p (gd x A)) := by
  let r := GaussianNamedGamma.clock f p x A
  let z := GaussianNamedRightHalfPlane.numerator f r x
  let B := GaussianNamedRightHalfPlane.denominator f r x
  let R := GaussianNamedRightHalfPlane.radius f x
  exact canonical_congr (GaussianNamedGamma.name_at f p x A)
    (GaussianNameReciprocal.name_canonical GaussianGammaC7Name.nameF
      (GaussianGammaReciprocalInverse.gammaHeight z R B (two*A)) (GaussianGammaC7Name.data z R B) (succ p))

private theorem coordinate_at (f : PR 2) (p x A : PTm n) : Γ ⊢[PRAAx]
    fstT (ap2 (realF f) p (gd x A)) ≐ fstT (ap2 (G f) p (gd x A)) :=
  (projected_coordinate (G f) p (gd x A)).eqTrans
    (RationalNormalForm.normalize_fixed_point _ (original_canonical f p x A).andE₂.andE₁)

private theorem axis_from_order (f g : PR 2) (x y A B : PTm n)
    (h : Γ ⊢[PRAAx] realOrder (G f) (G g) (gd x A) (gd y B)) :
    Γ ⊢[PRAAx] realOrder (realF f) (realF g) (gd x A) (gd y B) := by
  refine .allI (.allI ?_)
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] realOrder (G f) (G g) (gd (sh x) (sh A)) (gd (sh y) (sh B)) := by
    simpa only [Fm.shift, Syn.shift, GaussianNamedPositiveExponentialOrder.subst_realOrder, GaussianNamedGamma.subst_data,
      Δ, sh] using h.shift.shift
  have d := real_order_at _ _ _ _ (var 1) (var 0) hs
  have e := upper_congr (coordinate_at f (var 1) (sh x) (sh A)).eqSymm
    (coordinate_at g (var 0) (sh y) (sh B)).eqSymm (.eqRefl _) (.eqRefl _) d
  simpa only [realOrder, GaussianNamedGamma.subst_data, Syn.shift, sh] using e

private theorem order_from_axis (f g : PR 2) (x y A B : PTm n)
    (h : Γ ⊢[PRAAx] realOrder (realF f) (realF g) (gd x A) (gd y B)) :
    Γ ⊢[PRAAx] realOrder (G f) (G g) (gd x A) (gd y B) := by
  refine .allI (.allI ?_)
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] realOrder (realF f) (realF g) (gd (sh x) (sh A)) (gd (sh y) (sh B)) := by
    simpa only [Fm.shift, Syn.shift, GaussianNamedPositiveExponentialOrder.subst_realOrder, GaussianNamedGamma.subst_data,
      Δ, sh] using h.shift.shift
  have d := real_order_at _ _ _ _ (var 1) (var 0) hs
  have e := upper_congr (coordinate_at f (var 1) (sh x) (sh A))
    (coordinate_at g (var 0) (sh y) (sh B)) (.eqRefl _) (.eqRefl _) d
  simpa only [realOrder, GaussianNamedGamma.subst_data, Syn.shift, sh] using e

theorem order_from_log (f g : PR 2) (x y A B : PTm n) (hs : Γ ⊢[PRAAx] source f x A)
    (ht : Γ ⊢[PRAAx] source g y B) (h : Γ ⊢[PRAAx] realOrder (nameF f) (nameF g) (data x A) (data y B)) :
    Γ ⊢[PRAAx] realOrder (G f) (G g) (gd x A) (gd y B) := by
  have exp := GaussianStirlingMultiplicativeBoundsOrder.exponential_order _ _ _ _
    (name_regular f x A hs) (name_regular g y B ht) (log_real_samples f x A) (log_real_samples g y B) h
  have axis := GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (cross_symm _ _ _ _ (original_exponential_recovers_projection f x A hs))
    (original_exponential_recovers_projection g y B ht) exp
  exact order_from_axis f g x y A B axis

theorem strict_order_from_log (f g : PR 2) (x y A B : PTm n) (hs : Γ ⊢[PRAAx] source f x A)
    (ht : Γ ⊢[PRAAx] source g y B) (h : Γ ⊢[PRAAx] strictOrder (nameF f) (nameF g) (data x A) (data y B)) :
    Γ ⊢[PRAAx] strictOrder (G f) (G g) (gd x A) (gd y B) := by
  have exp := GaussianStirlingMultiplicativeBoundsStrictOrder.strict_exponential_order _ _ _ _
    (name_regular f x A hs) (name_regular g y B ht) (log_real_samples f x A) (log_real_samples g y B) h
  have axis := strict_transport _ _ _ _ _ _ _ _
    (cross_symm _ _ _ _ (original_exponential_recovers_projection f x A hs))
    (original_exponential_recovers_projection g y B ht) exp
  exact .andI (order_from_axis f g x y A B axis.andE₁)
    (.impI (axis.andE₂.wk.impE (axis_from_order g f y x B A Prf.hyp0)))

theorem actual_named_log_Gamma_order_reflection_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((source f (var 0) (var 2) ⋏ source g (var 1) (var 3)) ⟶
       ((realOrder (nameF f) (nameF g) (data (var 0) (var 2)) (data (var 1) (var 3)) ⟶
           realOrder (G f) (G g) (gd (var 0) (var 2)) (gd (var 1) (var 3))) ⋏
        (strictOrder (nameF f) (nameF g) (data (var 0) (var 2)) (data (var 1) (var 3)) ⟶
           strictOrder (G f) (G g) (gd (var 0) (var 2)) (gd (var 1) (var 3))))) :=
  closeUniv 4 (.impI (.andI
    (.impI (order_from_log f g _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0))
    (.impI (strict_order_from_log f g _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaMinimumFreezeOrder
