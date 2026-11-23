import IPRADerivations.Analysis.GaussianEulerIntegrationByPartsEndpointRescale
import IPRADerivations.Analysis.GaussianEulerLowerCofinalQuadrature

/-!
# Cofinal endpoint budget for the original affine grid

The original numerical cutoff is chosen late enough for the upper
factorial bound and the lower root bound. A separate primitive-recursive
observation precision controls both sampling errors and the affine
encoding comparison. The resulting estimate holds for every positive
grid size and every later cutoff and observation precision.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsEndpointBudget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegrationByPartsLinear (primitive)
open GaussianBetaPrimitiveLowerEndpoint (rootDen)
open GaussianGammaIntegralCutoffs (etaDen height top tailCoefficient top_positive)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_sum bounded_negative)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianExponentialReference (unit_monotone)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def cutoff (t R : PTm n) : PTm n := succ t+two*fact (succ (succ R))*unit (succ t)
def rightCost (R T : PTm n) : PTm n := num 4*pw T (succ R)+num 6*T
def minimumObservation (t k A R : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (num 9+rightCost R (top k A R)) (succ t)

theorem cutoff_later (t R : PTm n) : Γ ⊢[PRAAx] le (succ t) (cutoff t R) :=
  le_add_right _ _

private theorem endpoint_observation {x y : PTm n} (A C D K U : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hU : Γ ⊢[PRAAx] le one U)
    (hnear : Γ ⊢[PRAAx] distanceBounded x y K U)
    (hbound : Γ ⊢[PRAAx] bounded y (A*U+C*D) (D*U)) : Γ ⊢[PRAAx]
    bounded x (A*U+(C+K)*D) (D*U) := by
  have hd := positive_product _ _ hD hU
  have h := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ hU hd hnear hbound
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hU hd) hd
    (le_congr (by ipra_ring) (.eqRefl _) (le_refl _)) h

private theorem two_budgets (A C D p t : PTm n)
    (hA : Γ ⊢[PRAAx] le (A*unit (succ t)) D)
    (hC : Γ ⊢[PRAAx] le (C*unit (succ t)) (unit p)) : Γ ⊢[PRAAx]
    le ((A*unit p+C*D)*unit t) (D*unit p) := by
  have e : Γ ⊢[PRAAx] unit (succ t) ≐ two*unit t := (pw_succ two t).eqTrans (mul_comm _ _)
  have left := le_congr (congrMul (.eqRefl A) e) (.eqRefl _) hA
  have right := le_congr (congrMul (.eqRefl C) e) (.eqRefl _) hC
  apply RationalValueBounds.positive_cancel (le_succ_self one)
  ipra_le 𝔞(unit p)*sl left+𝔞(D)*sl right

theorem original_encoded_endpoints_small (t p z R B k A N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A)
    (hN : Γ ⊢[PRAAx] le one N) (hk : Γ ⊢[PRAAx] le (cutoff t R) k)
    (hp : Γ ⊢[PRAAx] le (minimumObservation t k A R) p) : Γ ⊢[PRAAx]
    bounded (primitive p z B (one*N) (etaDen k A R*N)) one (unit t) ⋏
    bounded (primitive p z B (one*N+width k A R*N) (etaDen k A R*N)) one (unit t) := by
  let D := rootDen k A R
  let T := top k A R
  let U := unit p
  let J := succ (succ R)
  let F := two*fact J
  let hB := h.andE₂.andE₁.andE₁
  have hT : Γ ⊢[PRAAx] le one T := top_positive k A R
  have hD : Γ ⊢[PRAAx] le one D := unit_positive _
  have hU : Γ ⊢[PRAAx] le one U := unit_positive p
  have root : Γ ⊢[PRAAx] le (num 3*unit (succ t)) D := by
    have later : Γ ⊢[PRAAx] le (succ t+num 6) (k+num 6) :=
      add_le_add_right _ (le_trans (cutoff_later t R) hk)
    have omitted := le_of_lt (GaussianGammaIntegralCutoffs.omitted_tail_budget (Γ := Γ) k A R)
    have onePart : Γ ⊢[PRAAx] le (unit (k+num 6)) ((A+tailCoefficient R)*unit (k+num 6)) :=
      le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right _ (le_trans h.andE₁ (le_add_right _ _)))
    exact le_trans (GaussianEulerLowerCofinalQuadrature.three_slack (succ t))
      (le_trans (unit_monotone later) (le_trans onePart omitted))
  have topBudget : Γ ⊢[PRAAx] le (F*unit (succ t)) T := by
    have ht : Γ ⊢[PRAAx] le k (height k A R) := le_of_eq_add (d := A+tailCoefficient R+num 10) (by unfold height; ipra_ring)
    have topBound : Γ ⊢[PRAAx] le (height k A R) T := by
      change Γ ⊢[PRAAx] le (height k A R) (two*height k A R)
      exact le_of_eq_add (d := height k A R) (by ipra_ring)
    exact le_trans (le_add_left (F*unit (succ t)) (succ t)) (le_trans hk (le_trans ht topBound))
  have clock := le_trans (GaussianFastValueCut.query_budget (num 9+rightCost R T) (succ t)) (unit_monotone hp)
  have leftObs : Γ ⊢[PRAAx] le (num 9*unit (succ t)) U :=
    le_trans (mul_le_mul_right _ (le_add_right (num 9) (rightCost R T))) clock
  have rightObs : Γ ⊢[PRAAx] le (rightCost R T*unit (succ t)) U :=
    le_trans (mul_le_mul_right _ (le_add_left (rightCost R T) (num 9))) clock
  have near := GaussianEulerIntegrationByPartsEndpointRescale.original_affine_cutoff_endpoints p z R B k A N hB hN
  have lo := GaussianEulerIntegrationByPartsEndpoints.lower_endpoint p z R B A k h
  have low := endpoint_observation (num 3) (num 3) D (num 6) U hD hU near.andE₁ lo
  have low' := bound_congr (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] num 3*U+(num 3+num 6)*D ≐ num 3*U+num 9*D)
    (.eqRefl _) low
  have high := GaussianEulerIntegrationByPartsEndpoints.upper_endpoint p z R B T h.andE₂.andE₁ hT
  have power := natEq (pw_succ (Γ := Γ) T (succ R))
  have high' : Γ ⊢[PRAAx] bounded (primitive p z B T one) (F*U+num 4*pw T (succ R)*T) (T*U) :=
    bound_congr (.eqRefl _) (by
      apply deriveNat
      dsimp only [F,U,J]
      ipra_simps
      rw [power]
      ring) (.eqRefl _) high
  have big := endpoint_observation F (num 4*pw T (succ R)) T (num 6*T) U hT hU near.andE₂ high'
  exact .andI
    (bounded_radius_mono _ _ _ _ _ (positive_product _ _ hD hU) (unit_positive t)
      (le_congr (.eqRefl _) (by ipra_ring) (two_budgets _ _ _ _ _ root leftObs)) low')
    (bounded_radius_mono _ _ _ _ _ (positive_product _ _ hT hU) (unit_positive t)
      (le_congr (.eqRefl _) (by ipra_ring) (two_budgets F (rightCost R T) T p t topBudget rightObs)) big)

theorem original_affine_boundary_difference_small (t p z R B k A N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A)
    (hN : Γ ⊢[PRAAx] le one N) (hk : Γ ⊢[PRAAx] le (cutoff t R) k)
    (hp : Γ ⊢[PRAAx] le (minimumObservation t k A R) p) : Γ ⊢[PRAAx]
    bounded (GaussianRationalMetric.qsub (primitive p z B (one*N+width k A R*N) (etaDen k A R*N))
      (primitive p z B (one*N) (etaDen k A R*N))) two (unit t) := by
  let U := unit t
  have hU := unit_positive (Γ := Γ) t
  have ends := original_encoded_endpoints_small t p z R B k A N h hN hk hp
  have raw := bounded_sum _ _ one U one U hU hU ends.andE₂ (bounded_negative _ _ _ hU ends.andE₁)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hU hU) hU
    (le_congr (by ipra_ring) (.eqRefl _) (le_refl _)) raw

theorem actual_integration_by_parts_cofinal_boundary_small_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((GaussianEulerLowerPowerCoefficients.source (var 2) (var 3) (var 4) (var 6) ⋏ le one (var 7) ⋏
      le (cutoff (var 0) (var 3)) (var 5) ⋏ le (minimumObservation (var 0) (var 5) (var 6) (var 3)) (var 1)) ⟶
      bounded (GaussianRationalMetric.qsub (primitive (var 1) (var 2) (var 4)
        (one*var 7+width (var 5) (var 6) (var 3)*var 7) (etaDen (var 5) (var 6) (var 3)*var 7))
        (primitive (var 1) (var 2) (var 4) (one*var 7) (etaDen (var 5) (var 6) (var 3)*var 7))) two (unit (var 0))) :=
  closeUniv 8 (.impI (original_affine_boundary_difference_small _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsEndpointBudget
