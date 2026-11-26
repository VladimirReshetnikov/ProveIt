import IPRADerivations.Analysis.Barnes.CanonicalProducts.GaussianBarnesCanonicalProperness
import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalCofinalTaylorGridObservations

/-!
# Radius comparison on the original cofinal Barnes grid

The value at each grid node is independent of the admitted radius.
Use the actual forward difference and its normalization to pay for
the finite amplification of the observation errors.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCofinalGridRadiusComparison

open_ipra
open ComplexLogarithmRemainder (add bounded normSq scale)
open GaussianBarnesCanonicalCofinalTaylorGridObservations
  (amplification cofinalGrid cofinal_at deadline node_source)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianFastValueCut (query_budget)
open GaussianPolynomialForwardDifferenceGridError (rowBound)
open GaussianPolynomialForwardDifferenceNormalization (normalized normalized_error)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (distanceBounded)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem row_bound (t z h R S B H e : PTm n) (hR : Γ ⊢[PRAAx] source z R B)
    (hS : Γ ⊢[PRAAx] source z S B) (hh : Γ ⊢[PRAAx] bounded h H) (hs : Γ ⊢[PRAAx] le (e*H) B) :
    Γ ⊢[PRAAx] rowBound (cofinalGrid t z h R B e) (cofinalGrid t z h S B e) (succ e) two (unit t) := by
  refine .allI (.impI ?_)
  let sh (x : PTm n) := Syn.shift x
  let j : PTm (n+1) := var 0
  let Δ := lt j (succ (sh e)) :: Γ.map Fm.shift
  have hr : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hR.shift.wk
  have hk : Δ ⊢[PRAAx] source (sh z) (sh S) (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hS.shift.wk
  have hd : Δ ⊢[PRAAx] bounded (sh h) (sh H) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hh.shift.wk
  have hm : Δ ⊢[PRAAx] le (sh e*sh H) (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hs.shift.wk
  have hj : Δ ⊢[PRAAx] lt j (succ (sh e)) := Prf.hyp0
  have hj' := Common.le_of_lt_succ hj
  let w := add (sh z) (scale j (sh h))
  have rp := node_source (sh z) (sh h) (sh R) (sh B) (sh H) (sh e) j hr hd hm hj'
  have sp := node_source (sh z) (sh h) (sh S) (sh B) (sh H) (sh e) j hk hd hm hj'
  have value := GaussianBarnesCanonicalProperness.comparison_at w w (sh R+one) (sh S+one) (sh B) (sh B)
    (sh t) (sh t) rp sp (.eqRefl _)
  have actual := distance_congr (cofinal_at (sh t) (sh z) (sh h) (sh R) (sh B) (sh e) j hj).eqSymm
    (cofinal_at (sh t) (sh z) (sh h) (sh S) (sh B) (sh e) j hj).eqSymm (.eqRefl _) (.eqRefl _) value
  have ht := unit_positive (Γ := Δ) (sh t)
  have collapsed : Δ ⊢[PRAAx] distanceBounded (entry (cofinalGrid (sh t) (sh z) (sh h) (sh R) (sh B) (sh e)) j)
      (entry (cofinalGrid (sh t) (sh z) (sh h) (sh S) (sh B) (sh e)) j) two (unit (sh t)) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ ht ht) ht (le_of_eq_add (d := zero) (by ipra_ring)) actual
  simpa [rowBound,Δ,sh,j,Syn.shift,one,two] using collapsed

theorem scheduled_bound (p t z h R S B H e : PTm n) (hR : Γ ⊢[PRAAx] source z R B)
    (hS : Γ ⊢[PRAAx] source z S B) (hh : Γ ⊢[PRAAx] bounded h H) (hs : Γ ⊢[PRAAx] le (e*H) B)
    (hn : Γ ⊢[PRAAx] le one (normSq h)) (ht : Γ ⊢[PRAAx] le (deadline p B e) t) :
    Γ ⊢[PRAAx] distanceBounded
      (normalized (cofinalGrid t z h R B e) e (ofGaussian h B))
      (normalized (cofinalGrid t z h S B e) e (ofGaussian h B)) one (unit p) := by
  let A := amplification B e
  have raw := normalized_error _ _ e _ B _ _ hR.andE₁
    (GaussianNamedDifferenceQuotient.parameter_lower h B (.andI hR.andE₁ hn)) (unit_positive t)
    (row_bound t z h R S B H e hR hS hh hs)
  have pay : Γ ⊢[PRAAx] le (num 3*A*unit p) (unit t) :=
    le_trans (query_budget _ _) (unit_monotone ht)
  have fit : Γ ⊢[PRAAx] le ((pw B e*(pw two e*two))*unit p) (num 3*A*unit p) := by
    apply le_of_eq_add (d := A*unit p)
    dsimp only [A,amplification]
    ipra_ring
  exact distance_radius_mono _ _ _ _ _ _ (unit_positive t) (unit_positive p)
    (le_congr (.eqRefl _) (one_mul _).eqSymm (le_trans fit pay)) raw

theorem actual_Barnes_original_cofinal_grid_radius_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (let p := var 0
     let t := var 1
     let z := var 2
     let h := var 3
     let R := var 4
     let S := var 5
     let B := var 6
     let H := var 7
     let e := var 8
     (source z R B ⋏ source z S B ⋏ bounded h H ⋏ le (e*H) B ⋏ le one (normSq h) ⋏ le (deadline p B e) t) ⟶
       distanceBounded (normalized (cofinalGrid t z h R B e) e (ofGaussian h B))
         (normalized (cofinalGrid t z h S B e) e (ofGaussian h B)) one (unit p)) :=
  closeUniv 9 (.impI (scheduled_bound _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCofinalGridRadiusComparison
