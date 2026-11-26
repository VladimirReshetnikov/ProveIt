import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.GaussianBinetLaplaceMomentImproperBound
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.GaussianBinetLaplaceMomentTaylorGrid

/-!
# Right Taylor remainder for the actual improper Binet moment names

All four original moments are read on one common refinement of a
cofinal prefix. The fixed unit prefix bounds the higher moment
independently of that common horizon. The aligned-grid slack is paid
at a late observation clock before comparing with the original
improper samples.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentImproperTaylor

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetLaplaceMomentImproper (nameF data cutoff)
open GaussianBinetLaplaceMomentImproperBound (momentBound prefixGrid prefix_source cofinal_refinement_error)
open GaussianBinetLaplaceMomentFloor (gain)
open GaussianBinetLaplaceMomentTaylorMajorant (errorCost)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianCompactRiemannName (mesh precision mesh_positive)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (qsub bounded distanceBounded)
open GaussianReconstructionRoots (norm_from_distance)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (LeanProofs.IPRA.Q.mk _ t)
local notation "realSource" => GaussianLogGammaEulerResidualDomain.source

def higherBound (j D : PTm n) : PTm n := momentBound (succ (succ j)) D+num 3
def leading (j D H : PTm n) : PTm n := num 3*(H*H)*higherBound j D
def linearSample (p j X D R H Q : PTm n) : PTm n :=
  qsub (ap2 nameF p (data j X D R)) (qmul (radiusPoint H Q) (ap2 nameF p (data (succ j) X D R)))

@[simp] theorem subst_higherBound {m : ℕ} (σ : Fin n → PTm m) (j D : PTm n) :
    Syn.subst σ (higherBound j D) = higherBound (Syn.subst σ j) (Syn.subst σ D) := by simp [higherBound]
@[simp] theorem subst_leading {m : ℕ} (σ : Fin n → PTm m) (j D H : PTm n) :
    Syn.subst σ (leading j D H) = leading (Syn.subst σ j) (Syn.subst σ D) (Syn.subst σ H) := by simp [leading]
@[simp] theorem subst_linearSample {m : ℕ} (σ : Fin n → PTm m) (p j X D R H Q : PTm n) :
    Syn.subst σ (linearSample p j X D R H Q) =
      linearSample (Syn.subst σ p) (Syn.subst σ j) (Syn.subst σ X) (Syn.subst σ D)
        (Syn.subst σ R) (Syn.subst σ H) (Syn.subst σ Q) := by simp [linearSample]

private theorem dyadic_scale (a b C E p : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (h : Γ ⊢[PRAAx] distanceBounded a b C (unit p)) :
    Γ ⊢[PRAAx] distanceBounded a b (C*E) (E*unit p) := by
  have hP := unit_positive (Γ := Γ) p
  exact distance_radius_mono _ _ _ _ _ _ hP (positive_product _ _ hE hP)
    (le_of_eq_add (d := zero) (by ipra_ring)) h

private theorem higher_grid_bound (p q M K j X D R T C : PTm n)
    (h : Γ ⊢[PRAAx] realSource X zero D zero R) (hK : Γ ⊢[PRAAx] le one K)
    (hM : Γ ⊢[PRAAx] M ≐ K*mesh p (gain (succ (succ j)) R T) T)
    (hq : Γ ⊢[PRAAx] le (precision p T) q) (hT : Γ ⊢[PRAAx] le (cutoff p (succ (succ j)) D) T)
    (b : Γ ⊢[PRAAx] bounded (ap2 nameF p (data (succ (succ j)) X D R)) C one) :
    Γ ⊢[PRAAx] bounded (prefixGrid q M (succ (succ j)) X D R T) (C+num 3) one := by
  have hp := unit_positive (Γ := Γ) p
  have d := cofinal_refinement_error p q M K (succ (succ j)) X D R T h hK hM hq hT
  have raw := norm_from_distance _ _ (num 3) (unit p) C one hp (le_refl one)
    (distance_symmetric _ _ _ _ hp d) b
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hp (le_refl one)) (le_refl one)
    (by ipra_le 3*sl hp) raw

/-- A cap at the actual higher-moment observation controls the same aligned
Taylor grid, so the coefficient can depend on a fixed positive margin. -/
theorem observation_taylor_with_cap (p j X D R S H Q C : PTm n)
    (h : Γ ⊢[PRAAx] realSource X zero D zero R)
    (h' : Γ ⊢[PRAAx] realSource (X*Q+H*D) zero (D*Q) zero S)
    (hQ : Γ ⊢[PRAAx] le one Q) (hH : Γ ⊢[PRAAx] le H Q)
    (hCap : Γ ⊢[PRAAx] bounded (ap2 nameF p (data (succ (succ j)) X D R)) C one) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data j (X*Q+H*D) (D*Q) S))
      (linearSample p j X D R H Q)
      (num 3*(H*H)*(C+num 3)*unit p+num 10*(Q*Q)) ((Q*Q)*unit p) := by
  let a := X*Q+H*D
  let b := D*Q
  let k := succ j
  let l := succ (succ j)
  let T₀ := cutoff p j D
  let T₁ := cutoff p j b
  let T₂ := cutoff p k D
  let T₃ := cutoff p l D
  let T := T₀+T₁+T₂+T₃
  let N₀ := mesh p (gain j R T) T
  let N₁ := mesh p (gain j S T) T
  let N₂ := mesh p (gain k R T) T
  let N₃ := mesh p (gain l R T) T
  let M := N₀*N₁*N₂*N₃
  let q := GaussianFastValueCut.exponent (T*errorCost j T) (precision p T)
  let U := unit p
  let E := Q*Q
  have hp := unit_positive (Γ := Γ) p
  have hE := positive_product _ _ hQ hQ
  have V := positive_product _ _ hE hp
  have m₀ : Γ ⊢[PRAAx] le one N₀ := mesh_positive _ _ _
  have m₁ : Γ ⊢[PRAAx] le one N₁ := mesh_positive _ _ _
  have m₂ : Γ ⊢[PRAAx] le one N₂ := mesh_positive _ _ _
  have m₃ : Γ ⊢[PRAAx] le one N₃ := mesh_positive _ _ _
  have hM : Γ ⊢[PRAAx] le one M := positive_product _ _ (positive_product _ _ (positive_product _ _ m₀ m₁) m₂) m₃
  have hq : Γ ⊢[PRAAx] le (precision p T) q := le_add_right _ _
  have early : Γ ⊢[PRAAx] le T₀ T := le_trans (le_add_right _ _) (le_trans (le_add_right _ _) (le_add_right _ _))
  have later : Γ ⊢[PRAAx] le T₁ T := le_trans (le_add_left _ _) (le_trans (le_add_right _ _) (le_add_right _ _))
  have next : Γ ⊢[PRAAx] le T₂ T := le_trans (le_add_left _ _) (le_add_right _ _)
  have final : Γ ⊢[PRAAx] le T₃ T := le_add_left _ _
  have old := cofinal_refinement_error p q M (N₁*N₂*N₃) j X D R T h
    (positive_product _ _ (positive_product _ _ m₁ m₂) m₃) (by dsimp only [M]; ipra_ring) hq early
  have moved := cofinal_refinement_error p q M (N₀*N₂*N₃) j a b S T h'
    (positive_product _ _ (positive_product _ _ m₀ m₂) m₃) (by dsimp only [M]; ipra_ring) hq later
  have successor := cofinal_refinement_error p q M (N₀*N₁*N₃) k X D R T h
    (positive_product _ _ (positive_product _ _ m₀ m₁) m₃) (by dsimp only [M]; ipra_ring) hq next
  have cap := higher_grid_bound p q M (N₀*N₁*N₂) j X D R T C h
    (positive_product _ _ (positive_product _ _ m₀ m₁) m₂) (by dsimp only [M]; ipra_ring) hq final hCap
  have finite := GaussianBinetLaplaceMomentTaylorGrid.aligned_taylor_bound q M j X D R S T H Q zero T one
    (C+num 3) one (prefix_source X D R T h) (prefix_source a b S T h') hM hQ hH (le_refl one) cap
  have hpq : Γ ⊢[PRAAx] le p (precision p T) := le_trans (le_add_right p T) (le_add_right _ _)
  have pad : Γ ⊢[PRAAx] le ((T*errorCost j T)*unit p) (unit q) :=
    le_trans (le_mul_mono (le_refl (T*errorCost j T)) (GaussianExponentialReference.unit_monotone hpq))
      (GaussianFastValueCut.query_budget _ _)
  have scaledFinite : Γ ⊢[PRAAx] distanceBounded (prefixGrid q M j a b S T)
      (qsub (prefixGrid q M j X D R T) (qmul (radiusPoint H Q) (prefixGrid q M k X D R T)))
      (num 3*(H*H)*(C+num 3)*unit p+E) (E*unit p) := by
    have den : Γ ⊢[PRAAx] le one ((one*unit q)*((Q*Q)*one)) :=
      positive_product _ _ (positive_product _ _ (le_refl one) (unit_positive q)) (positive_product _ _ hE (le_refl one))
    apply distance_radius_mono _ _ _ _ _ _ den V ?_ finite
    dsimp only [E]
    ipra_le 𝔞(Q)*𝔞(Q)*𝔞(Q)*𝔞(Q)*sl pad
  have step : Γ ⊢[PRAAx] bounded (radiusPoint H Q) one one :=
    bounded_radius_mono _ H Q one one hQ (le_refl one) (le_congr (by ipra_ring) (by ipra_ring) hH) (radius_bounded H Q hQ)
  have scaled := GaussianApproximateInverseDistance.multiply_distance (radiusPoint H Q) _ _ one (num 3) U hp step successor
  have near := GaussianNamedDifference.difference_distance _ _ _ _ _ _ U hp old
    (distance_congr (.eqRefl _) (.eqRefl _) (one_mul _) (.eqRefl _) scaled)
  have before := dyadic_scale _ _ (num 3) E p hE moved
  have after := dyadic_scale _ _ _ E p hE (distance_symmetric _ _ _ _ hp near)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [E]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ V (distance_triangle_same _ _ _ _ _ _ V before scaledFinite) after)

theorem observation_taylor (p j X D R S H Q : PTm n)
    (h : Γ ⊢[PRAAx] realSource X zero D zero R)
    (h' : Γ ⊢[PRAAx] realSource (X*Q+H*D) zero (D*Q) zero S)
    (hQ : Γ ⊢[PRAAx] le one Q) (hH : Γ ⊢[PRAAx] le H Q) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data j (X*Q+H*D) (D*Q) S))
      (linearSample p j X D R H Q)
      (leading j D H*unit p+num 10*(Q*Q)) ((Q*Q)*unit p) :=
  observation_taylor_with_cap p j X D R S H Q (momentBound (succ (succ j)) D) h h' hQ hH
    (GaussianBinetLaplaceMomentImproperBound.observation_bound p (succ (succ j)) X D R h)

theorem actual_improper_Binet_moment_right_Taylor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let p := var 0
     let j := var 1
     let X := var 2
     let D := var 3
     let R := var 4
     let S := var 5
     let H := var 6
     let Q := var 7
     (realSource X zero D zero R ⋏ realSource (X*Q+H*D) zero (D*Q) zero S) ⟶
       (le one Q ⋏ le H Q) ⟶
        distanceBounded (ap2 nameF p (data j (X*Q+H*D) (D*Q) S))
          (linearSample p j X D R H Q)
          (leading j D H*unit p+num 10*(Q*Q)) ((Q*Q)*unit p)) :=
  closeUniv 8 (.impI (.impI (observation_taylor _ _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentImproperTaylor
