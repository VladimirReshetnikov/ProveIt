import IPRADerivations.Analysis.Barnes.CanonicalProducts.GaussianBarnesCanonicalProduct
import IPRADerivations.Analysis.Barnes.CanonicalProducts.GaussianBarnesCanonicalFiniteProperness
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateComposition

/-!
# Independence of the rational chart for the Barnes canonical product

Two encodings of the same rational point may give different denominators,
head lengths, clipping bounds, and observation clocks. Compare both names with the literal
product at one common cutoff and remove its two leading dyadic errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalProperness

open_ipra
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalProduct (cutoff cutoff_rate_of_le literalData)
open GaussianBarnesCanonicalValue (prefixF nameF data regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianNamedRateComposition (symmetric same_denominator_at)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalSlackRemoval (slack slack_removal_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def commonCutoff (m z w R S B D : PTm n) : PTm n := cutoff m z R B+cutoff m w S D

theorem comparison_slack (z w R S B D p q m : PTm n)
    (hR : Γ ⊢[PRAAx] source z R B) (hS : Γ ⊢[PRAAx] source w S D)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) : Γ ⊢[PRAAx]
    slack (qsub (ap2 nameF p (data z R B)) (ap2 nameF q (data w S D)))
      (unit p+unit q) (unit p*unit q) two m := by
  let N := commonCutoff m z w R S B D
  let a := literalData z R B N
  let b := literalData w S D N
  have kthR : Γ ⊢[PRAAx] le (cutoff m z R B) N := le_add_right _ _
  have kthS : Γ ⊢[PRAAx] le (cutoff m w S D) N :=
    le_congr (.eqRefl _) (add_comm _ _) (le_add_right _ _)
  have hr := cutoff_rate_of_le m z R B N hR kthR
  have hs := cutoff_rate_of_le m w S D N hS kthS
  have equivalent : Γ ⊢[PRAAx] crossEquivalent prefixF prefixF a b :=
    GaussianBarnesCanonicalFiniteProperness.prefix_cross z w R S B D N hR hS he
  have right := GaussianNamedRateTransport.transport prefixF nameF prefixF nameF b (data w S D) a (data w S D)
    one (unit m) (unit_positive m) hs equivalent (cross_refl nameF _ (regular w S D hS))
  have left := symmetric prefixF nameF a (data z R B) one (unit m) (unit_positive m) hr
  have observed := same_denominator_at nameF prefixF nameF (data z R B) a (data w S D)
    one (unit m) one p q (unit_positive m) left right
  change Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z R B)) (ap2 nameF q (data w S D))
    ((unit p+unit q)*unit m+two*(unit p*unit q)) ((unit p*unit q)*unit m)
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by unfold rateNumerator; ipra_ring) (by unfold rateDenominator; ipra_ring) observed

theorem comparison_at (z w R S B D p q : PTm n)
    (hR : Γ ⊢[PRAAx] source z R B) (hS : Γ ⊢[PRAAx] source w S D)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z R B)) (ap2 nameF q (data w S D)) (unit p+unit q) (unit p*unit q) :=
  slack_removal_at _ _ _ two (positive_product _ _ (unit_positive p) (unit_positive q))
    (comparison_slack z w R S B D p q _ hR hS he)


theorem proper (z w R S B D : PTm n)
    (hR : Γ ⊢[PRAAx] source z R B) (hS : Γ ⊢[PRAAx] source w S D)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (data z R B) (data w S D) := by
  let sh (x : PTm n) := Syn.shift (Syn.shift x)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have sr : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hR.shift.shift
  have ss : Δ ⊢[PRAAx] source (sh w) (sh S) (sh D) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hS.shift.shift
  have ee : Δ ⊢[PRAAx] ofGaussian (sh z) (sh B) ≐ ofGaussian (sh w) (sh D) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using he.shift.shift
  unfold crossEquivalent
  refine .allI (.allI ?_)
  simpa only [Syn.shift,GaussianBarnesCanonicalValue.subst_data,sh,Δ] using
    comparison_at (Γ := Δ) (sh z) (sh w) (sh R) (sh S) (sh B) (sh D) (var 1) (var 0) sr ss ee

theorem independent_radii (z R S B : PTm n)
    (hR : Γ ⊢[PRAAx] source z R B) (hS : Γ ⊢[PRAAx] source z S B) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (data z R B) (data z S B) :=
  proper z z R S B B hR hS (.eqRefl (ofGaussian z B))

theorem actual_Barnes_canonical_product_rational_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let z := var 0
     let w := var 1
     let R := var 2
     let S := var 3
     let B := var 4
     let D := var 5
     source z R B ⟶ source w S D ⟶ (ofGaussian z B ≐ ofGaussian w D) ⟶
       crossEquivalent nameF nameF (data z R B) (data w S D)) :=
  closeUniv 6 (.impI (.impI (.impI (proper _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalProperness
