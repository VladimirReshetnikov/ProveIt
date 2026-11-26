import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalValueDerivativeProperness
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotientProperness

/-!
# Independence of the certified Barnes derivative disk

At a point inside two disks, choose one sufficiently small native
step admitted in both. The original Barnes value is already independent
of its disk, so the two actual quotients agree. Removing the common
dyadic error identifies the derivative names at independent precisions.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDerivativeDiskIndependence

open_ipra
open ComplexLogarithmRemainder (add scale oneCode normSq bounded_mono)
open GaussianBarnesCanonicalDerivativeStep (refinement at_refinement)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial_positive)
open GaussianBarnesCanonicalValueDerivative (input nameF data quotientF quotientData numerator denominator regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianNamedRateComposition (symmetric same_denominator_at)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalSlackRemoval (slack slack_removal_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B : PTm n) :
    Syn.subst σ (data z R B) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [data,GaussianBarnesCanonicalValueDerivativeJoin.derivativeData,
    GaussianNamedNativeProductDerivativeRate.derivativeData]

private theorem widened (z R B : PTm n) (hs : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] source z (succ R) B :=
  .andI hs.andE₁ (bounded_mono hs.andE₂ (mul_le_mul_right B (le_succ_self R)))

private theorem step_rate (z R B m A : PTm n) (hs : Γ ⊢[PRAAx] source z R B)
    (ht : Γ ⊢[PRAAx] GaussianBarnesCanonicalDerivativeStep.certificateAt z R B m A) :
    Γ ⊢[PRAAx] independentRate quotientF nameF (quotientData (scale A z) oneCode (succ R) (A*B))
      (data z (succ R) B) one (unit m) := by
  let s := succ R
  have hp := ht.andE₂.andE₂.andE₁
  have rate := GaussianBarnesCanonicalValueDerivativeProperness.fixed_reference_rate (scale A z) z oneCode s (A*B) B
    hp (widened z R B hs) ht.andE₁.eqSymm
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _
    (positive_product _ _ hp.andE₂.andE₁.andE₁ (initial_positive s)) (unit_positive m)
    (le_congr (.eqRefl _) (one_mul _).eqSymm ht.andE₂.andE₂.andE₂) rate

private theorem quotient_cross (z h R S B : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source z S B)
    (hu : Γ ⊢[PRAAx] source (add z h) R B) (hv : Γ ⊢[PRAAx] source (add z h) S B) :
    Γ ⊢[PRAAx] crossEquivalent quotientF quotientF (quotientData z h R B) (quotientData z h S B) :=
  GaussianNamedDifferenceQuotientProperness.proper V V V V (vd (add z h) R B) (vd (add z h) S B)
    (vd z R B) (vd z S B) h B (GaussianBarnesCanonicalValue.regular (add z h) R B hu)
    (GaussianBarnesCanonicalValue.regular (add z h) S B hv) (GaussianBarnesCanonicalValue.regular z R B hz)
    (GaussianBarnesCanonicalValue.regular z S B hw) (GaussianBarnesCanonicalProperness.independent_radii (add z h) R S B hu hv)
    (GaussianBarnesCanonicalProperness.independent_radii z R S B hz hw)

private theorem comparison_slack (z R S B p q m : PTm n) (hr : Γ ⊢[PRAAx] source z R B)
    (hs : Γ ⊢[PRAAx] source z S B) : Γ ⊢[PRAAx]
    slack (qsub (ap2 nameF p (data z (succ R) B)) (ap2 nameF q (data z (succ S) B)))
      (unit p+unit q) (unit p*unit q) two m := by
  let A := refinement R m+refinement S m
  let w := scale A z
  let E := A*B
  let r := succ R
  let s := succ S
  let x := quotientData w oneCode r E
  let y := quotientData w oneCode s E
  let d := data z r B
  let e := data z s B
  let U := unit m
  have pr := at_refinement z R B m A hr (le_add_right _ _)
  have ps := at_refinement z S B m A hs (le_add_left _ _)
  have ir : Γ ⊢[PRAAx] input w oneCode r E := pr.andE₂.andE₂.andE₁
  have is : Γ ⊢[PRAAx] input w oneCode s E := ps.andE₂.andE₂.andE₁
  have same := quotient_cross w oneCode r s E ir.andE₂.andE₁ is.andE₂.andE₁ ir.andE₂.andE₂.andE₁ is.andE₂.andE₂.andE₁
  have hU := unit_positive (Γ := Γ) m
  have rt := symmetric quotientF nameF x d one U hU (step_rate z R B m A hr pr)
  have st := GaussianNamedRateTransport.transport quotientF nameF quotientF nameF y e x e one U hU
    (step_rate z S B m A hs ps) same (cross_refl _ _ (regular z s B (widened z S B hs)))
  have obs := same_denominator_at nameF quotientF nameF d x e one U one p q hU rt st
  change Γ ⊢[PRAAx] distanceBounded (ap2 nameF p d) (ap2 nameF q e)
    ((unit p+unit q)*U+two*(unit p*unit q)) ((unit p*unit q)*U)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold rateNumerator; ipra_ring)
    (by unfold rateDenominator; ipra_ring) obs

theorem independent_radii (z R S B : PTm n) (hr : Γ ⊢[PRAAx] source z R B)
    (hs : Γ ⊢[PRAAx] source z S B) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (data z (succ R) B) (data z (succ S) B) := by
  refine .allI (.allI ?_)
  let sh (u : PTm n) := Syn.shift (Syn.shift u)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  let x := ap2 nameF p (data (sh z) (succ (sh R)) (sh B))
  let y := ap2 nameF q (data (sh z) (succ (sh S)) (sh B))
  let A := unit p+unit q
  let E := unit p*unit q
  let m := GaussianRationalSlackRemoval.precision (qsub x y) A E two
  have h₁ : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [sh,Δ,Syn.shift,Fm.shift] using hr.shift.shift
  have h₂ : Δ ⊢[PRAAx] source (sh z) (sh S) (sh B) := by simpa [sh,Δ,Syn.shift,Fm.shift] using hs.shift.shift
  have he : Δ ⊢[PRAAx] le one E := positive_product _ _ (unit_positive p) (unit_positive q)
  have same := slack_removal_at (qsub x y) A E two he
    (comparison_slack (sh z) (sh R) (sh S) (sh B) p q m h₁ h₂)
  simpa only [crossEquivalent,Syn.shift,sh,Δ,subst_data,ConciseIPRA.PTm.subst_succ,p,q,x,y,A,E,
    distanceBounded,GaussianEuclideanPointDistance.unit,GaussianCoefficientNameBounds.unit] using same

theorem actual_Barnes_derivative_independent_interior_disks_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let z := var 0
     let R := var 1
     let S := var 2
     let B := var 3
     (source z R B ⋏ source z S B) ⟶ crossEquivalent nameF nameF (data z (succ R) B) (data z (succ S) B)) :=
  closeUniv 4 (.impI (independent_radii _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDerivativeDiskIndependence
