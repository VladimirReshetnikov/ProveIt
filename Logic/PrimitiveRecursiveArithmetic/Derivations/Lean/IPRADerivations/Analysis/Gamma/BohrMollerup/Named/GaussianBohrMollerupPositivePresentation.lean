import IPRADerivations.Analysis.Gamma.BohrMollerup.GaussianBohrMollerupUniqueness
import IPRADerivations.Analysis.Stirling.Duplication.GaussianStirlingLogDuplication

/-!
# Positive fixed presentations of Gamma

A certified positive name contributes its actual named logarithm.
The logarithmic uniqueness theorem identifies the logarithms, and
recovery under the original exponential identifies the positive names.
-/

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace LeanProofs.IPRA.Analysis.GaussianBohrMollerupPositivePresentation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBohrMollerupPresentation (Presentation argument laws native)
open GaussianExponentialRadiusIndependence (independent_radii_proper)
open GaussianGammaFiniteApproximantName (exponential_input)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianStirlingGammaLogarithm (source logGammaF logGammaData log_gamma_regular gammaData)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def logarithmPresentation (f : PR 2) (x e : PTm 2) : Presentation :=
  ⟨GaussianNamedPositiveLogarithm.nameF f, GaussianNamedPositiveLogarithm.data x e⟩

@[simp] theorem logarithm_program (f : PR 2) (x e : PTm 2) :
    (logarithmPresentation f x e).nameF = GaussianNamedPositiveLogarithm.nameF f := rfl

@[simp] theorem logarithm_argument (f : PR 2) (x e : PTm 2) (a b : PTm n) :
    argument (logarithmPresentation f x e) a b =
      GaussianNamedPositiveLogarithm.data (inst2 x a b) (inst2 e a b) := by
  simp [argument,logarithmPresentation,inst2]

theorem positive_uniqueness (f : PR 2) (x e : PTm 2) (a b T : PTm n)
    (law : Γ ⊢[PRAAx] laws (logarithmPresentation f x e)) (s : Γ ⊢[PRAAx] source a b)
    (p : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source f (inst2 x a b) (inst2 e a b) T) :
    Γ ⊢[PRAAx] crossEquivalent f gammaF (inst2 x a b) (gammaData a b) := by
  let text := inst2 x a b
  let margin := inst2 e a b
  let F := GaussianNamedPositiveLogarithm.nameF f
  let X := GaussianNamedPositiveLogarithm.data text margin
  let Y := logGammaData a b
  let R := GaussianCompactLogarithmBounds.radius margin T
  let S := U logGammaF Y
  have eq := GaussianBohrMollerupUniqueness.uniqueness (logarithmPresentation f x e) native a b law
    GaussianBohrMollerupNativeNormalization.native_laws s
  have eq' : Γ ⊢[PRAAx] crossEquivalent F logGammaF X Y := by
    simpa only [logarithm_argument,GaussianBohrMollerupPresentation.native_program,
      GaussianBohrMollerupPresentation.native_argument,logarithm_program,F,X,Y,text,margin] using eq
  have hi : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input F R X :=
    GaussianNamedPositiveLogarithm.exponential_input f text margin T p
  have hj := exponential_input logGammaF Y (log_gamma_regular a b s)
  have equalExp := independent_radii_proper F logGammaF R S X Y hi hj eq'
  have l : Γ ⊢[PRAAx] crossEquivalent (GaussianRadiusExponentialName.nameF F) f
      (GaussianRadiusExponentialName.data R X) text :=
    GaussianNamedPositiveLogarithmExponential.original_recovery f text margin T p
  have r : Γ ⊢[PRAAx] crossEquivalent (GaussianRadiusExponentialName.nameF logGammaF) gammaF
      (GaussianRadiusExponentialName.data S Y) (gammaData a b) :=
    GaussianStirlingLogDuplication.exponential_gamma a b s
  exact cross_trans f (GaussianRadiusExponentialName.nameF F) gammaF
    text (GaussianRadiusExponentialName.data R X) (gammaData a b)
    (cross_symm _ _ _ _ l) (cross_trans _ _ _ _ _ _ equalExp r)

theorem actual_positive_fixed_presentation_Gamma_uniqueness_closed (f : PR 2) (x e : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (laws (logarithmPresentation f x e) ⟶
        source (var 0) (var 1) ⋏
          GaussianNamedPositiveLogarithm.source f (inst2 x (var 0) (var 1)) (inst2 e (var 0) (var 1)) (var 2) ⟶
        crossEquivalent f gammaF (inst2 x (var 0) (var 1)) (gammaData (var 0) (var 1))) :=
  closeUniv 3 (.impI (.impI (positive_uniqueness f x e _ _ _ Prf.hyp1 Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBohrMollerupPositivePresentation
