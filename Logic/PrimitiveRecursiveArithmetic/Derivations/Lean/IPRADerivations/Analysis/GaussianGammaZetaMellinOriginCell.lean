import IPRADerivations.Analysis.GaussianGammaZetaMellinOriginBound
import IPRADerivations.Analysis.GaussianEulerLowerTailPowerPanel

/-!
# Weighted right cells of the Gamma–zeta Mellin origin grid

A cell between x/b and y/b in the root coordinate uses the physical
width (y/b)^(k+1) - (x/b)^(k+1). At the original right tag this width
cancels the singular part of the Mellin point bound. The resulting
majorant is proportional to the root-coordinate width.
-/

set_option autoImplicit false
set_option maxHeartbeats 680000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinOriginCell

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEulerLowerTailPowerPanel (width width_bound)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaZetaMellinOriginBound (origin_bound)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.PTm (monus num)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Mellin" => GaussianGammaZetaMellinIntegrand.nameF
local notation "mellinData" => GaussianGammaZetaMellinIntegrand.data

def value (p z D k x y b : PTm n) : PTm n :=
  qmul (fraction (width x y k) (pw b (succ k)))
    (ap2 Mellin p (mellinData (shifted z D) D (pw y (succ k)) (pw b (succ k))))

@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (p z D k x y b : PTm n) :
    Syn.subst σ (value p z D k x y b) =
      value (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ D) (Syn.subst σ k) (Syn.subst σ x)
        (Syn.subst σ y) (Syn.subst σ b) := by
  simp [value,GaussianGammaEulerHeadShift.subst_shifted]

theorem right_cell_bound (p z R D k x y b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerOrder.source z R D (succ k) y b)
    (hxy : Γ ⊢[PRAAx] le x y) :
    Γ ⊢[PRAAx] bounded (value p z D k x y b)
      ((succ k*monus y x)*(unit p+num 3)) (b*unit p) := by
  let V := pw y k
  let W := pw b k
  let B := pw b (succ k)
  let G := succ k*monus y x
  let U := unit p
  let H := width x y k
  have hb : Γ ⊢[PRAAx] le one b := h.andE₂.andE₁.andE₂
  have hv : Γ ⊢[PRAAx] le one V := GaussianPolynomialPerturbation.power_positive _ _ h.andE₂.andE₁.andE₁
  have hB : Γ ⊢[PRAAx] le one B := GaussianPolynomialPerturbation.power_positive _ _ hb
  have hu := unit_positive (Γ := Γ) p
  have hvu := positive_product _ _ hv hu
  have vp := congrAp2 powF (pred_succ (Γ := Γ) k) (.eqRefl y)
  have wp := congrAp2 powF (pred_succ (Γ := Γ) k) (.eqRefl b)
  have point : Γ ⊢[PRAAx] bounded
      (ap2 Mellin p (mellinData (shifted z D) D (pw y (succ k)) (pw b (succ k))))
      (W*U+num 3*V) (V*U) :=
    bound_congr (.eqRefl _) (congrAdd (congrMul wp (.eqRefl U)) (congrMul (.eqRefl _) vp))
      (congrMul vp (.eqRefl U)) (origin_bound p z R D (succ k) y b h)
  have weight : Γ ⊢[PRAAx] bounded (fraction H B) H B :=
    bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point H B hB).eqSymm
      (.eqRefl H) (.eqRefl B) (GaussianDominantPairAlgebra.radius_bounded H B hB)
  have raw := bounded_product _ _ H B (W*U+num 3*V) (V*U) hB hvu weight point
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ hB hvu) (positive_product _ _ hb hu) ?_ raw
  change Γ ⊢[PRAAx] le ((H*(W*U+num 3*V))*(b*U)) ((G*(U+num 3))*(B*(V*U)))
  have widthCap : Γ ⊢[PRAAx] le H (G*V) :=
    le_congr (.eqRefl H) (by dsimp only [G,V]; ipra_ring) (width_bound x y k hxy)
  have pointCap : Γ ⊢[PRAAx] le (W*U+num 3*V) (W*(U+num 3)) := by
    have small : Γ ⊢[PRAAx] le V W := pw_le_pw k h.andE₂.andE₂
    ipra_le 3*sl small
  have out : Γ ⊢[PRAAx] ((G*V)*(W*(U+num 3)))*(b*U) ≐ (G*(U+num 3))*(B*(V*U)) :=
    (by ipra_ring : Γ ⊢[PRAAx] ((G*V)*(W*(U+num 3)))*(b*U) ≐ (G*(U+num 3))*((W*b)*(V*U))).eqTrans
      (congrMul (.eqRefl _) (congrMul (pw_succ b k).eqSymm (.eqRefl _)))
  exact le_congr (.eqRefl _) out (mul_le_mul_right (b*U) (le_mul_mono widthCap pointCap))

theorem actual_gamma_zeta_mellin_origin_cell_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let p := var 0
     let z := var 1
     let R := var 2
     let D := var 3
     let k := var 4
     let x := var 5
     let y := var 6
     let b := var 7
     GaussianEulerLowerPowerOrder.source z R D (succ k) y b ⋏ le x y ⟶
       bounded (value p z D k x y b) ((succ k*monus y x)*(unit p+num 3)) (b*unit p)) :=
  closeUniv 8 (.impI (right_cell_bound _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinOriginCell
