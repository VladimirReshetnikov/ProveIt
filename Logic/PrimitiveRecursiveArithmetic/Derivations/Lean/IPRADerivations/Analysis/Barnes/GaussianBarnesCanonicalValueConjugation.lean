import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalPrefixConjugation
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalUniformCutoff
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateConjugation
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateComposition

/-!
# Conjugation of the original cofinal Barnes value

A common literal truncation gives exact finite conjugation. Both
cofinal names compare with it at an arbitrary dyadic rate. Removing
the two truncation errors yields equivalence at independent clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalValueConjugation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalProduct (literalData)
open GaussianBarnesCanonicalUniformCutoff (cutoff uniform_rate)
open GaussianBarnesCanonicalValue (prefixF nameF data regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianNamedRateComposition (symmetric same_denominator_at)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalReciprocal (conjugate subst_conjugate)
open GaussianRationalSlackRemoval (slack slack_removal_at)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Conj" => GaussianNameConjugation.nameF

theorem comparison_slack (z R B p q m : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    slack (qsub (ap2 (Conj nameF) p (data z R B)) (ap2 nameF q (data (conjugate z) R B)))
      (unit p+unit q) (unit p*unit q) two m := by
  let w := conjugate z
  let N := cutoff R m
  let a := literalData z R B N
  let b := literalData w R B N
  let X := data z R B
  let Y := data w R B
  have hw := GaussianBarnesCanonicalHeadConjugation.conjugate_source z R B h
  have hz := uniform_rate z R B m N h (le_refl N)
  have ht := uniform_rate w R B m N hw (le_refl N)
  have e := GaussianBarnesCanonicalPrefixConjugation.prefix_cross z R B N h
  have conjugated := GaussianNamedRateConjugation.transport prefixF nameF a X one (unit m) (unit_positive m) hz
  have left := symmetric (Conj prefixF) (Conj nameF) a X one (unit m) (unit_positive m) conjugated
  have right := GaussianNamedRateTransport.transport prefixF nameF (Conj prefixF) nameF b Y a Y
    one (unit m) (unit_positive m) ht e (cross_refl nameF Y (regular w R B hw))
  have observed := same_denominator_at (Conj nameF) (Conj prefixF) nameF X a Y
    one (unit m) one p q (unit_positive m) left right
  change Γ ⊢[PRAAx] distanceBounded (ap2 (Conj nameF) p X) (ap2 nameF q Y)
    ((unit p+unit q)*unit m+two*(unit p*unit q)) ((unit p*unit q)*unit m)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold rateNumerator; ipra_ring)
    (by unfold rateDenominator; ipra_ring) observed

theorem comparison_at (z R B p q : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (Conj nameF) p (data z R B)) (ap2 nameF q (data (conjugate z) R B))
      (unit p+unit q) (unit p*unit q) :=
  slack_removal_at _ _ _ two (positive_product _ _ (unit_positive p) (unit_positive q))
    (comparison_slack z R B p q _ h)

theorem value_cross (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    crossEquivalent (Conj nameF) nameF (data z R B) (data (conjugate z) R B) := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,Syn.shift,GaussianBarnesCanonicalValue.subst_data,subst_conjugate,sh,Δ] using
    comparison_at (sh z) (sh R) (sh B) (var 1) (var 0) hs

theorem actual_Barnes_canonical_value_conjugation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (let z := var 0
     let R := var 1
     let B := var 2
     source z R B ⟶ crossEquivalent (Conj nameF) nameF (data z R B) (data (conjugate z) R B)) :=
  closeUniv 3 (.impI (value_cross _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalValueConjugation
