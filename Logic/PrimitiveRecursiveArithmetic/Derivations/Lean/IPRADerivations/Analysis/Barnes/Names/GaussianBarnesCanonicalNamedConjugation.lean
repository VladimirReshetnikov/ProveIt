import IPRADerivations.Analysis.Barnes.Names.GaussianBarnesCanonicalNamedFrozen
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalValueConjugation

/-!
# Conjugation of Barnes values on regular Gaussian names

Freeze the actual input and its conjugate at a common late clock. The
frozen rational codes conjugate exactly. The two original Barnes
evaluators retain their own precision demands and certified radii.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedConjugation

open_ipra
open GaussianBarnesCanonicalNamed (nameF clock name_regular)
open GaussianBarnesCanonicalNamedDemand (source data frozenData native_source)
open GaussianBarnesCanonicalNamedFrozen (frozen_rate)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianNamedRateComposition (symmetric same_denominator_at)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalReciprocal (conjugate)
open GaussianRationalSlackRemoval (slack slack_removal_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Conj" => GaussianNameConjugation.nameF
local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "valueData" => GaussianBarnesCanonicalValue.data

theorem conjugate_source (f : PR 2) (x R : PTm n) (h : Γ ⊢[PRAAx] source f x R) : Γ ⊢[PRAAx] source (Conj f) x R :=
  GaussianNameConjugation.exponential_input f R x h

theorem frozen_argument (f : PR 2) (k x : PTm n) : Γ ⊢[PRAAx]
    ofGaussian (conjugate (rawGaussian (ap2 f k x))) (rawDen (ap2 f k x)) ≐
      ofGaussian (rawGaussian (ap2 (Conj f) k x)) (rawDen (ap2 (Conj f) k x)) := by
  let q := ap2 f k x
  let r := ap2 (Conj f) k x
  have e := GaussianRationalConjugation.of_gaussian (Γ := Γ) (rawGaussian q) (rawDen q) (raw_den_positive q)
  have read := GaussianNameConjugation.sample_at (Γ := Γ) f k x
  have fixed := GaussianExponentialReference.recode_fixed (Γ := Γ) r (GaussianNameConjugation.sample_canonical f k x)
  exact e.eqSymm.eqTrans ((GaussianNameConjugation.point_recode q).eqTrans (fixed.eqTrans read).eqSymm)

theorem frozen_cross (f : PR 2) (k x R S : PTm n)
    (h : Γ ⊢[PRAAx] source f x R) (h' : Γ ⊢[PRAAx] source (Conj f) x S) : Γ ⊢[PRAAx]
    crossEquivalent (Conj V) V (frozenData f k x R) (frozenData (Conj f) k x S) := by
  let q := ap2 f k x
  let r := ap2 (Conj f) k x
  let z := rawGaussian q
  let w := rawGaussian r
  let B := rawDen q
  let D := rawDen r
  have a := native_source f k x R h
  have b := native_source (Conj f) k x S h'
  exact cross_trans (Conj V) V V (frozenData f k x R) (valueData (conjugate z) R B) (frozenData (Conj f) k x S)
    (GaussianBarnesCanonicalValueConjugation.value_cross z R B a)
    (GaussianBarnesCanonicalProperness.proper (conjugate z) w R S B D
      (GaussianBarnesCanonicalHeadConjugation.conjugate_source z R B a) b (frozen_argument f k x))

private theorem comparison_slack (f : PR 2) (x R S p q m : PTm n)
    (h : Γ ⊢[PRAAx] source f x R) (h' : Γ ⊢[PRAAx] source (Conj f) x S) : Γ ⊢[PRAAx]
    slack (qsub (ap2 (Conj (nameF f)) p (data x R)) (ap2 (nameF (Conj f)) q (data x S)))
      (unit p+unit q) (unit p*unit q) two m := by
  let k := clock m R+clock m S
  let F := nameF f
  let G := nameF (Conj f)
  let a := frozenData f k x R
  let b := frozenData (Conj f) k x S
  let X := data x R
  let Y := data x S
  have hz := frozen_rate f m k x R h (le_add_right (clock m R) (clock m S))
  have hw := frozen_rate (Conj f) m k x S h' (le_add_left (clock m S) (clock m R))
  have hU := unit_positive (Γ := Γ) m
  have left := GaussianNamedRateConjugation.transport F V X a one (unit m) hU hz
  have right := GaussianNamedRateTransport.transport G V G (Conj V) Y b Y a one (unit m) hU hw
    (cross_refl G Y (name_regular (Conj f) x S h')) (frozen_cross f k x R S h h')
  have observed := same_denominator_at (Conj F) (Conj V) G X a Y one (unit m) one p q hU left
    (symmetric G (Conj V) Y a one (unit m) hU right)
  change Γ ⊢[PRAAx] distanceBounded (ap2 (Conj F) p X) (ap2 G q Y)
    ((unit p+unit q)*unit m+two*(unit p*unit q)) ((unit p*unit q)*unit m)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold rateNumerator; ipra_ring)
    (by unfold rateDenominator; ipra_ring) observed

theorem comparison_at (f : PR 2) (x R S p q : PTm n)
    (h : Γ ⊢[PRAAx] source f x R) (h' : Γ ⊢[PRAAx] source (Conj f) x S) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (Conj (nameF f)) p (data x R)) (ap2 (nameF (Conj f)) q (data x S))
      (unit p+unit q) (unit p*unit q) :=
  slack_removal_at _ _ _ two (positive_product _ _ (unit_positive p) (unit_positive q))
    (comparison_slack f x R S p q _ h h')

theorem named_cross (f : PR 2) (x R S : PTm n)
    (h : Γ ⊢[PRAAx] source f x R) (h' : Γ ⊢[PRAAx] source (Conj f) x S) : Γ ⊢[PRAAx]
    crossEquivalent (Conj (nameF f)) (nameF (Conj f)) (data x R) (data x S) := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have left : Δ ⊢[PRAAx] source f (sh x) (sh R) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.shift
  have right : Δ ⊢[PRAAx] source (Conj f) (sh x) (sh S) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using h'.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,Syn.shift,GaussianBarnesCanonicalNamedDemand.subst_data,sh,Δ] using
    comparison_at f (sh x) (sh R) (sh S) (var 1) (var 0) left right

theorem proper (f g : PR 2) (x y R S : PTm n) (h : Γ ⊢[PRAAx] source f x R) (h' : Γ ⊢[PRAAx] source g y S)
    (e : Γ ⊢[PRAAx] crossEquivalent (Conj f) g x y) : Γ ⊢[PRAAx]
    crossEquivalent (Conj (nameF f)) (nameF g) (data x R) (data y S) := by
  have c := conjugate_source f x R h
  exact cross_trans _ _ _ _ _ _ (named_cross f x R R h c)
    (GaussianBarnesCanonicalNamedFrozen.proper (Conj f) g x y R S c h' e)

theorem actual_Barnes_named_conjugation_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source f (var 0) (var 1) ⟶
      crossEquivalent (Conj (nameF f)) (nameF (Conj f)) (data (var 0) (var 1)) (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (named_cross f _ _ _ Prf.hyp0 (conjugate_source f _ _ Prf.hyp0)))

theorem actual_Barnes_named_conjugation_proper_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source f (var 0) (var 2) ⟶ source g (var 1) (var 3) ⟶ crossEquivalent (Conj f) g (var 0) (var 1) ⟶
      crossEquivalent (Conj (nameF f)) (nameF g) (data (var 0) (var 2)) (data (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (proper f g _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedConjugation
