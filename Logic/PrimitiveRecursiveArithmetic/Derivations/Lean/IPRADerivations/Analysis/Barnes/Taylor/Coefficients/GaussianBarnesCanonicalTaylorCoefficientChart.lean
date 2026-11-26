import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.ProductCoefficients.GaussianBarnesCanonicalTaylorProductChart
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.FixedCoefficients.GaussianBarnesCanonicalFixedTaylorCoefficientName

/-!
# Chart independence of the original Barnes Taylor coefficient names

The observations on two equivalent charts may have different clocks.
A shared later clock, and a shared later cutoff for the cofinal names,
give exactly equal raw coefficients. The two original ready estimates
bound the distances to the separately requested observations.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorCoefficientChart

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalExponentTaylorRetainedCoefficient (cutoff precision)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalTaylorProductChart (coefficient_proper)
open GaussianBarnesCanonicalTaylorProductCoefficientCauchy (productCoefficient)
open GaussianBarnesCanonicalTaylorProductCoefficientName (clock)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalMetric (distanceBounded)
open GaussianReconstructionRoots (distance_triangle)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalFixedTaylorCoefficientName.nameF
local notation "fd" => GaussianBarnesCanonicalFixedTaylorCoefficientName.data
local notation "G" => GaussianBarnesCanonicalTaylorProductCoefficientName.nameF
local notation "gd" => GaussianBarnesCanonicalTaylorProductCoefficientName.data

private theorem join_samples (x y u v p t : PTm n)
    (hx : Γ ⊢[PRAAx] distanceBounded x u one (unit p))
    (hy : Γ ⊢[PRAAx] distanceBounded y v one (unit t)) (huv : Γ ⊢[PRAAx] u ≐ v) :
    Γ ⊢[PRAAx] distanceBounded x y (unit p+unit t) (unit p*unit t) :=
  distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle _ _ _ _ _ _ _ (unit_positive p) (unit_positive t) hx
      (distance_congr huv.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
        (distance_symmetric _ _ _ _ (unit_positive t) hy)))

theorem fixed_at (p t z w R B D r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source w R D) (he : Γ ⊢[PRAAx] le e (previous M))
    (hq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F p (fd z R B r M e)) (ap2 F t (fd w R D r M e))
      (unit p+unit t) (unit p*unit t) := by
  let a := precision (clock p z R B M e) R
  let b := precision (clock t w R D M e) R
  let q := a+b
  have ha := GaussianBarnesCanonicalFixedTaylorCoefficientName.sample_ready (Γ := Γ) p z R B M e
  have hb := GaussianBarnesCanonicalFixedTaylorCoefficientName.sample_ready (Γ := Γ) t w R D M e
  have za : Γ ⊢[PRAAx] GaussianBarnesCanonicalFixedTaylorCoefficientName.ready p z R B M e q :=
    le_trans ha (unit_monotone (le_add_right a b))
  have wb : Γ ⊢[PRAAx] GaussianBarnesCanonicalFixedTaylorCoefficientName.ready t w R D M e q :=
    le_trans hb (unit_monotone (le_add_left b a))
  have left := GaussianBarnesCanonicalFixedTaylorCoefficientName.ready_gap p a q z R B r M e hz he ha za
  have right := GaussianBarnesCanonicalFixedTaylorCoefficientName.ready_gap t b q w R D r M e hw he hb wb
  exact join_samples _ _ _ _ p t
    (distance_congr (GaussianBarnesCanonicalFixedTaylorCoefficientName.sample_at p z R B r M e).eqSymm
      (.eqRefl _) (.eqRefl _) (.eqRefl _) left)
    (distance_congr (GaussianBarnesCanonicalFixedTaylorCoefficientName.sample_at t w R D r M e).eqSymm
      (.eqRefl _) (.eqRefl _) (.eqRefl _) right)
    (coefficient_proper q z w R B D r M e hz.andE₁ hw.andE₁ hq)

theorem cofinal_at (p t z w R B D M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source w R D) (he : Γ ⊢[PRAAx] le e (previous M))
    (hq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 G p (gd z R B M e)) (ap2 G t (gd w R D M e))
      (unit p+unit t) (unit p*unit t) := by
  let a := precision (clock p z R B M e) R
  let b := precision (clock t w R D M e) R
  let r := cutoff (clock p z R B M e) R M
  let s := cutoff (clock t w R D M e) R M
  let q := a+b
  let u := r+s
  have ha := GaussianBarnesCanonicalTaylorProductCoefficientName.sample_ready (Γ := Γ) p z R B M e
  have hb := GaussianBarnesCanonicalTaylorProductCoefficientName.sample_ready (Γ := Γ) t w R D M e
  have za : Γ ⊢[PRAAx] GaussianBarnesCanonicalTaylorProductCoefficientName.ready p z R B M e q u :=
    .andI (le_trans ha.andE₁ (unit_monotone (le_add_right a b))) (le_add_right r s)
  have wb : Γ ⊢[PRAAx] GaussianBarnesCanonicalTaylorProductCoefficientName.ready t w R D M e q u :=
    .andI (le_trans hb.andE₁ (unit_monotone (le_add_left b a))) (le_add_left s r)
  have left := GaussianBarnesCanonicalTaylorProductCoefficientName.ready_gap p a q z R B r u M e hz he ha za
  have right := GaussianBarnesCanonicalTaylorProductCoefficientName.ready_gap t b q w R D s u M e hw he hb wb
  exact join_samples _ _ _ _ p t
    (distance_congr (GaussianBarnesCanonicalTaylorProductCoefficientName.sample_at p z R B M e).eqSymm
      (.eqRefl _) (.eqRefl _) (.eqRefl _) left)
    (distance_congr (GaussianBarnesCanonicalTaylorProductCoefficientName.sample_at t w R D M e).eqSymm
      (.eqRefl _) (.eqRefl _) (.eqRefl _) right)
    (coefficient_proper q z w R B D u M e hz.andE₁ hw.andE₁ hq)

theorem fixed_cross (z w R B D r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source w R D) (he : Γ ⊢[PRAAx] le e (previous M))
    (hq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] crossEquivalent F F (fd z R B r M e) (fd w R D r M e) := by
  refine .allI (.allI ?_)
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hz' : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hz.shift.shift
  have hw' : Δ ⊢[PRAAx] source (sh w) (sh R) (sh D) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hw.shift.shift
  have he' : Δ ⊢[PRAAx] le (sh e) (previous (sh M)) := by simpa [Δ,sh,Fm.shift,Syn.shift] using he.shift.shift
  have hq' : Δ ⊢[PRAAx] ofGaussian (sh z) (sh B) ≐ ofGaussian (sh w) (sh D) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hq.shift.shift
  simpa [Δ,sh,Syn.shift] using fixed_at (var 1) (var 0) (sh z) (sh w) (sh R) (sh B) (sh D) (sh r) (sh M)
    (sh e) hz' hw' he' hq'

theorem cofinal_cross (z w R B D M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source w R D) (he : Γ ⊢[PRAAx] le e (previous M))
    (hq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] crossEquivalent G G (gd z R B M e) (gd w R D M e) := by
  refine .allI (.allI ?_)
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hz' : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hz.shift.shift
  have hw' : Δ ⊢[PRAAx] source (sh w) (sh R) (sh D) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hw.shift.shift
  have he' : Δ ⊢[PRAAx] le (sh e) (previous (sh M)) := by simpa [Δ,sh,Fm.shift,Syn.shift] using he.shift.shift
  have hq' : Δ ⊢[PRAAx] ofGaussian (sh z) (sh B) ≐ ofGaussian (sh w) (sh D) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hq.shift.shift
  simpa [Δ,sh,Syn.shift] using cofinal_at (var 1) (var 0) (sh z) (sh w) (sh R) (sh B) (sh D) (sh M)
    (sh e) hz' hw' he' hq'

theorem actual_Barnes_fixed_Taylor_coefficient_chart_independent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let z := var 0
     let w := var 1
     let R := var 2
     let B := var 3
     let D := var 4
     let r := var 5
     let M := var 6
     let e := var 7
     (source z R B ⋏ source w R D ⋏ le e (previous M) ⋏ ofGaussian z B ≐ ofGaussian w D) ⟶
       crossEquivalent F F (fd z R B r M e) (fd w R D r M e)) :=
  closeUniv 8 (.impI (fixed_cross (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

theorem actual_Barnes_cofinal_Taylor_coefficient_chart_independent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let z := var 0
     let w := var 1
     let R := var 2
     let B := var 3
     let D := var 4
     let M := var 5
     let e := var 6
     (source z R B ⋏ source w R D ⋏ le e (previous M) ⋏ ofGaussian z B ≐ ofGaussian w D) ⟶
       crossEquivalent G G (gd z R B M e) (gd w R D M e)) :=
  closeUniv 7 (.impI (cofinal_cross (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorCoefficientChart
