import IPRADerivations.Analysis.Stirling.GaussianGammaHalfWallisRate

/-!
# Quantitative uniqueness for the positive golden-ratio equation

For two nonnegative rational inputs, a lower bound of 3/2 on the
second input bounds the modulus of the difference of their quadratic
residuals from below by half the input difference.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianGoldenRatioRationalUniqueness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalMetric (distanceBounded)
open GaussianGammaHalfWallisRate (fraction_distance)
open GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def residual (a b K U : PTm n) : Fm PTm n :=
  le (U*(a*a)) (U*(a*b+b*b)+K*(b*b)) ⋏
    le (U*(a*b+b*b)) (U*(a*a)+K*(b*b))

private theorem scaled_cancel (x y S T U K : PTm n)
    (hT : Γ ⊢[PRAAx] le one T) (hS : Γ ⊢[PRAAx] le T (two*S))
    (h : Γ ⊢[PRAAx] le (U*x*S) (U*y*S+K*(T*T))) :
    Γ ⊢[PRAAx] le (U*x) (U*y+two*K*T) := by
  refine .orE (le_total x y) ?_ ?_
  · exact le_trans (le_mul_mono (le_refl U) Prf.hyp0) (le_add_right _ _)
  · let Δ := le y x :: Γ
    let r := monus x y
    have eq : Δ ⊢[PRAAx] x ≐ y+r := eq_add_of_le Prf.hyp0
    have scaled : Δ ⊢[PRAAx] le (U*(y+r)*S) (U*y*S+K*(T*T)) :=
      le_congr (congrMul (congrMul (.eqRefl U) eq) (.eqRefl S)) (.eqRefl _) h.wk
    have reduced : Δ ⊢[PRAAx] le (U*r*S) (K*(T*T)) :=
      le_of_add_le_add_right (c := U*y*S) (le_congr (by ipra_ring) (by ipra_ring) scaled)
    have more : Δ ⊢[PRAAx] le (T*(U*r)) (T*(two*K*T)) := by
      ipra_le (Groth.ι (Q.mk Δ (U*r)))*sl hS.wk+2*sl reduced
    have small := RationalValueBounds.positive_cancel hT.wk more
    exact le_congr (congrMul (.eqRefl U) eq.eqSymm) (.eqRefl _) (by ipra_le sl small)

theorem residual_distance (a b c d K J U : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (hU : Γ ⊢[PRAAx] le one U) (lower : Γ ⊢[PRAAx] le (num 3*d) (two*c))
    (left : Γ ⊢[PRAAx] residual a b K U) (right : Γ ⊢[PRAAx] residual c d J U) :
    Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) (two*(K+J)) U := by
  let x := a*d
  let y := c*b
  let T := b*d
  let S := monus (x+y) T
  have hT : Γ ⊢[PRAAx] le one T := positive_product _ _ hb hd
  have leC : Γ ⊢[PRAAx] le d c := by
    apply mul_le_cancel (d' := one)
    ipra_le sl lower+𝔞 d
  have low : Γ ⊢[PRAAx] le T (x+y) :=
    le_trans (le_mul_mono (le_refl b) leC) (le_congr (mul_comm c b) (.eqRefl _) (le_add_left y x))
  have eq : Γ ⊢[PRAAx] x+y ≐ T+S := eq_add_of_le low
  have hi : Γ ⊢[PRAAx] le (T+two*T) (two*(x+y)) := by
    dsimp only [T,x,y]
    ipra_le 𝔞 b*sl lower+2*𝔞(a*d)
  have hs : Γ ⊢[PRAAx] le T (two*S) := by
    apply le_of_add_le_add_right (c := two*T)
    exact le_congr (.eqRefl _) ((congrMul (.eqRefl two) eq).eqTrans (by ipra_ring)) hi
  have l : Γ ⊢[PRAAx] le (U*x*(x+y)+U*y*T) (U*y*(x+y)+U*x*T+(K+J)*(T*T)) := by
    dsimp only [x,y,T]
    ipra_le 𝔞(d*d)*sl left.andE₁+𝔞(b*b)*sl right.andE₂
  have r : Γ ⊢[PRAAx] le (U*y*(x+y)+U*x*T) (U*x*(x+y)+U*y*T+(K+J)*(T*T)) := by
    dsimp only [x,y,T]
    ipra_le 𝔞(b*b)*sl right.andE₁+𝔞(d*d)*sl left.andE₂
  have f (u v : PTm n)
      (h : Γ ⊢[PRAAx] le (U*u*(x+y)+U*v*T) (U*v*(x+y)+U*u*T+(K+J)*(T*T))) :
      Γ ⊢[PRAAx] le (U*u*S) (U*v*S+(K+J)*(T*T)) := by
    have a := congrAdd (congrMul (.eqRefl (U*u)) eq) (.eqRefl (U*v*T))
    have b := congrAdd (congrAdd (congrMul (.eqRefl (U*v)) eq) (.eqRefl (U*u*T))) (.eqRefl ((K+J)*(T*T)))
    apply le_of_add_le_add_right (c := U*u*T+U*v*T)
    exact le_congr (a.eqTrans (by ipra_ring)) (b.eqTrans (by ipra_ring)) h
  have forward := scaled_cancel x y S T U (K+J) hT hs (f x y l)
  have backward := scaled_cancel y x S T U (K+J) hT hs (f y x r)
  exact fraction_distance _ _ _ _ _ _ hb hd hU
    (le_congr (.eqRefl _) (by dsimp only [T,y]; ipra_ring) forward)
    (le_congr (.eqRefl _) (by dsimp only [T,x]; ipra_ring) backward)

theorem actual_positive_quadratic_residual_distance_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      ((((le one (var 1) ⋏ le one (var 3)) ⋏ le one (var 6)) ⋏ le (num 3*var 3) (two*var 2)) ⋏
        (residual (var 0) (var 1) (var 4) (var 6) ⋏ residual (var 2) (var 3) (var 5) (var 6)) ⟶
        distanceBounded (fraction (var 0) (var 1)) (fraction (var 2) (var 3)) (two*(var 4+var 5)) (var 6)) :=
  closeUniv 7 (.impI (residual_distance _ _ _ _ _ _ _ Prf.hyp0.andE₁.andE₁.andE₁.andE₁
    Prf.hyp0.andE₁.andE₁.andE₁.andE₂ Prf.hyp0.andE₁.andE₁.andE₂ Prf.hyp0.andE₁.andE₂
    Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGoldenRatioRationalUniqueness
