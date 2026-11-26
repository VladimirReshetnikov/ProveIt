import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalDerivativeFractionProperness
import IPRADerivations.Analysis.Barnes.TailControl.GaussianBarnesCanonicalTailContinuity
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalTailExponentialDerivative

/-!
# Equivalent fractions in the original Barnes tail derivative

At a fixed certified disk, the original tail exponential takes the
same value on equivalent Gaussian fractions by its uniform continuity
estimate. Multiply by the exactly matched derivative series to obtain
the same result for the actual tail derivative name.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTailDerivativeFractionProperness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalTailContinuity (inputClock)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedInverseRate (rate_at rateNumerator rateDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalSlackRemoval (slack slack_removal_at)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "T" => GaussianBarnesCanonicalTailExponential.nameF
local notation "td" => GaussianBarnesCanonicalTailExponential.data
local notation "L" => GaussianBarnesCanonicalDerivativeCofinal.nameF
local notation "ld" => GaussianBarnesCanonicalLogCofinal.data
local notation "D" => GaussianBarnesCanonicalTailExponentialDerivative.derivativeF
local notation "dd" => GaussianBarnesCanonicalTailExponentialDerivative.derivativeData

private theorem comparison_slack (z w R B C p q m : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source w R C)
    (eq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w C) : Γ ⊢[PRAAx]
    slack (qsub (ap2 T p (td z R B)) (ap2 T q (td w R C))) (unit p+unit q) (unit p*unit q) one m := by
  let J := unit (inputClock R m)
  have hJ : Γ ⊢[PRAAx] le one J := unit_positive _
  have near := distance_radius_mono _ _ zero J one J hJ hJ (le_of_eq_add (d := J) (by ipra_ring))
    (GaussianNameConjugation.equal_distance _ _ J hJ eq)
  have rt := GaussianBarnesCanonicalTailContinuity.uniform_input z w R B C m hz hw near
  have obs := rate_at T T (td z R B) (td w R C) one (unit m) p q rt
  change Γ ⊢[PRAAx] distanceBounded (ap2 T p (td z R B)) (ap2 T q (td w R C))
    ((unit p+unit q)*unit m+one*(unit p*unit q)) ((unit p*unit q)*unit m)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold rateNumerator; ipra_ring) (by unfold rateDenominator; ipra_ring) obs

theorem exponential_proper (z w R B C : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source w R C)
    (eq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w C) : Γ ⊢[PRAAx]
    crossEquivalent T T (td z R B) (td w R C) := by
  refine .allI (.allI ?_)
  let sh (u : PTm n) := Syn.shift (Syn.shift u)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  let x := ap2 T p (td (sh z) (sh R) (sh B))
  let y := ap2 T q (td (sh w) (sh R) (sh C))
  let A := unit p+unit q
  let B' := unit p*unit q
  let m := GaussianRationalSlackRemoval.precision (qsub x y) A B' one
  have h₁ : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [sh,Δ,Syn.shift,Fm.shift] using hz.shift.shift
  have h₀ : Δ ⊢[PRAAx] source (sh w) (sh R) (sh C) := by simpa [sh,Δ,Syn.shift,Fm.shift] using hw.shift.shift
  have e : Δ ⊢[PRAAx] ofGaussian (sh z) (sh B) ≐ ofGaussian (sh w) (sh C) :=
    by simpa [sh,Δ,Syn.shift,Fm.shift] using eq.shift.shift
  have hB' : Δ ⊢[PRAAx] le one B' := positive_product _ _ (unit_positive p) (unit_positive q)
  have same := slack_removal_at (qsub x y) A B' one hB'
    (comparison_slack (sh z) (sh w) (sh R) (sh B) (sh C) p q m h₁ h₀ e)
  simpa only [crossEquivalent,Syn.shift,sh,Δ,GaussianBarnesCanonicalTailExponential.subst_data,x,y,p,q,A,B',
    distanceBounded,GaussianEuclideanPointDistance.unit,GaussianCoefficientNameBounds.unit] using same

theorem derivative_proper (z w R B C : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source w R C)
    (eq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w C) : Γ ⊢[PRAAx]
    crossEquivalent D D (dd z R B) (dd w R C) :=
  GaussianGammaAdjacentCutoff.multiply_cross T T L L _ _ _ _
    (GaussianBarnesCanonicalTailExponential.regular z R B hz) (GaussianBarnesCanonicalTailExponential.regular w R C hw)
    (GaussianBarnesCanonicalDerivativeCofinal.regular z R B hz) (GaussianBarnesCanonicalDerivativeCofinal.regular w R C hw)
    (exponential_proper z w R B C hz hw eq) (GaussianBarnesCanonicalDerivativeFractionProperness.proper z w R B C hz hw eq)

theorem actual_Barnes_tail_exponential_derivative_fraction_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let z := var 0
     let w := var 1
     let R := var 2
     let B := var 3
     let C := var 4
     (source z R B ⋏ (source w R C ⋏ (ofGaussian z B ≐ ofGaussian w C))) ⟶
       crossEquivalent D D (dd z R B) (dd w R C)) :=
  closeUniv 5 (.impI (derivative_proper _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTailDerivativeFractionProperness
