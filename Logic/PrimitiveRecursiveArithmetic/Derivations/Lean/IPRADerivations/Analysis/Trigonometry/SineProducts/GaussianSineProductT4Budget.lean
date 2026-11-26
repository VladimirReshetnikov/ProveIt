import IPRADerivations.Analysis.Trigonometry.SineProducts.GaussianSineProductName

/-!
# The explicit sine-product schedule and error budget

This is the natural-arithmetic part of Gamma (T4). The paper's odd
multiple and the bound (2^{74R^2}(R+1)^2/K) are literal PR terms.
The last bridge allows either the paper's tail coefficient 16 or the
coefficient 32 from a twice-tail finite product estimate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSineProductT4Budget

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianBalancedRadiusArithmetic (unit_monotone)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def halfIndex (R K : PTm n) : PTm n := num 4*((K*K)*(R*R))
def multiple (R K : PTm n) : PTm n := succ (num 8*((K*K)*(R*R)))
def squareDenominator (R K : PTm n) : PTm n := multiple R K*multiple R K

def headError (R K : PTm n) : PTm n := num 96*(R*R)*(two*(R*R)+K)
def prefactorError (R : PTm n) : PTm n := unit (num 64*(R*R))*(num 8*(R*R))
def productError (R K T : PTm n) : PTm n :=
  unit (num 68*(R*R))*(T*(R*R)*squareDenominator R K+K*headError R K)
def rate (R : PTm n) : PTm n := unit (num 74*(R*R))*(succ R*succ R)
def cutoff (R p : PTm n) : PTm n := rate R*unit p

ipra_subst halfIndex
ipra_subst multiple
ipra_subst squareDenominator
ipra_subst headError
ipra_subst prefactorError
ipra_subst productError
ipra_subst rate
ipra_subst cutoff

theorem odd_multiple (R K : PTm n) :
    Γ ⊢[PRAAx] multiple R K ≐ two*halfIndex R K+one := by unfold multiple halfIndex; ipra_ring

theorem multiple_positive (R K : PTm n) : Γ ⊢[PRAAx] le one (multiple R K) := zero_lt_succ _

theorem denominator_positive (R K : PTm n) : Γ ⊢[PRAAx] le one (squareDenominator R K) :=
  positive_product _ _ (multiple_positive R K) (multiple_positive R K)

private theorem square_factor_bounds (R K : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] le K ((K*K)*(R*R)) ⋏ le R ((K*K)*(R*R)) := by
  have hRR := positive_product R R hR hR
  have hKK := positive_product K K hK hK
  exact .andI
    (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_mul_mono (le_refl K) hK) hRR))
    (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono hKK (le_mul_mono (le_refl R) hR)))

theorem cutoff_le_half_index (R K : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] le K (halfIndex R K) := by
  unfold halfIndex
  ipra_le sl (square_factor_bounds R K hR hK).andE₁+3*𝔞 ((K*K)*(R*R))

theorem argument_disk (R K : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] le (num 4*R) (multiple R K) := by
  unfold multiple
  ipra_le 4*sl (square_factor_bounds R K hR hK).andE₂+4*𝔞 ((K*K)*(R*R))+1

theorem root_disk (R K k : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K)
    (hk : Γ ⊢[PRAAx] le k K) : Γ ⊢[PRAAx] le (num 4*k) (multiple R K) := by
  unfold multiple
  ipra_le 4*sl hk+4*sl (square_factor_bounds R K hR hK).andE₁+4*𝔞 ((K*K)*(R*R))+1

private theorem square_residual (R K : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] le (K*(num 96*(two*(R*R)+K)+num 8)) (num 8*squareDenominator R K) := by
  let H := R*R
  let L := (K*K)*H
  have hL : Γ ⊢[PRAAx] le one L := le_trans hK (square_factor_bounds R K hR hK).andE₁
  have pK : Γ ⊢[PRAAx] le K L := (square_factor_bounds R K hR hK).andE₁
  have pH : Γ ⊢[PRAAx] le H L :=
    le_congr (one_mul H) (.eqRefl _) (le_mul_mono (positive_product K K hK hK) (le_refl H))
  have first : Γ ⊢[PRAAx] le (K*H) (L*L) := le_mul_mono pK pH
  have second : Γ ⊢[PRAAx] le (K*K) (L*L) := le_mul_mono pK pK
  have third : Γ ⊢[PRAAx] le K (L*L) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono pK hL)
  change Γ ⊢[PRAAx] le (K*(num 96*(two*H+K)+num 8)) (num 8*(succ (num 8*L)*succ (num 8*L)))
  ipra_le 192*sl first+96*sl second+8*sl third+216*𝔞 L*𝔞 L+128*𝔞 L+8

private theorem unit_six : Γ ⊢[PRAAx] (unit (num 6) : PTm n) ≐ num 64 := by
  have square : Γ ⊢[PRAAx] pw two two ≐ num 4 :=
    (pw_succ two one).eqTrans ((congrMul (pw_one two) (.eqRefl _)).eqTrans (by ipra_ring))
  have fourth : Γ ⊢[PRAAx] pw two (two+two) ≐ num 16 :=
    (pw_add two two two).eqTrans ((congrMul square square).eqTrans (by ipra_ring))
  exact (congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] num 6 ≐ (two+two)+two) (.eqRefl two)).eqTrans
    ((pw_add two (two+two) two).eqTrans ((congrMul fourth square).eqTrans (by ipra_ring)))

private theorem decay_exponent (R : PTm n) (hR : Γ ⊢[PRAAx] le one R) :
    Γ ⊢[PRAAx] le (num 64*unit (num 68*(R*R))) (unit (num 74*(R*R))) := by
  let H := R*R
  have hH : Γ ⊢[PRAAx] le one H := positive_product R R hR hR
  have h6 : Γ ⊢[PRAAx] le (num 6) (num 6*H) := by ipra_le 6*sl hH
  have split : Γ ⊢[PRAAx] unit (num 68*H)*unit (num 6*H) ≐ unit (num 74*H) :=
    (pw_add two (num 68*H) (num 6*H)).eqSymm.eqTrans (congrAp2 powF (by ipra_ring) (.eqRefl two))
  exact le_congr ((congrMul (.eqRefl _) unit_six).eqTrans (mul_comm _ _)) split
    (le_mul_mono (le_refl (unit (num 68*H))) (unit_monotone _ _ h6))

theorem budget (R K T : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K)
    (hT : Γ ⊢[PRAAx] le T (num 32)) :
    Γ ⊢[PRAAx] le (K*prefactorError R+productError R K T) (rate R*squareDenominator R K) := by
  let H := R*R
  let D := squareDenominator R K
  let W := unit (num 68*H)
  have large : Γ ⊢[PRAAx] le (unit (num 64*H)) W := unit_monotone _ _ (by ipra_le 4*𝔞 H)
  have first : Γ ⊢[PRAAx] le (K*prefactorError R+productError R K T)
      (W*(T*H*D+H*(K*(num 96*(two*H+K)+num 8)))) := by
    apply le_congr ?_ ?_ (add_le_add₂ (le_mul_mono (le_refl (K*(num 8*H))) large)
      (le_refl (productError R K T)))
    · unfold prefactorError
      dsimp only [H]
      ipra_ring
    · unfold productError
      dsimp only [W,H,D]
      unfold headError
      ipra_ring
  have residual : Γ ⊢[PRAAx] le (T*H*D+H*(K*(num 96*(two*H+K)+num 8))) (num 40*H*D) := by
    have step : Γ ⊢[PRAAx] le (H*(K*(num 96*(two*H+K)+num 8))) (H*(num 8*D)) :=
      le_mul_mono (le_refl H) (square_residual R K hR hK)
    ipra_le sl step+𝔞 H*𝔞 D*sl hT
  have margin : Γ ⊢[PRAAx] le (num 40*W) (unit (num 74*H)) :=
    le_trans (by ipra_le 24*𝔞 W : Γ ⊢[PRAAx] le (num 40*W) (num 64*W)) (decay_exponent R hR)
  have radius : Γ ⊢[PRAAx] le H (succ R*succ R) := by dsimp only [H]; ipra_le 2*𝔞 R+1
  exact le_trans (le_trans first (le_mul_mono (le_refl W) residual))
    (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_mul_mono margin radius) (le_refl D)))

theorem absorb_errors (a b c R K T : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K)
    (hT : Γ ⊢[PRAAx] le T (num 32))
    (h₁ : Γ ⊢[PRAAx] distanceBounded a b (prefactorError R) (squareDenominator R K))
    (h₂ : Γ ⊢[PRAAx] distanceBounded b c (productError R K T) (K*squareDenominator R K)) :
    Γ ⊢[PRAAx] distanceBounded a c (rate R) K := by
  let D := squareDenominator R K
  have hD := denominator_positive (Γ := Γ) R K
  have hKD := positive_product K D hK hD
  have left := distance_radius_mono a b _ _ (K*prefactorError R) (K*D) hD hKD
    (le_of_eq_add (d := zero) (by ipra_ring)) h₁
  have total := distance_triangle_same _ _ _ _ _ _ hKD left h₂
  exact distance_radius_mono a c _ _ _ _ hKD hK
    (le_congr (.eqRefl _) (by unfold D; ipra_ring)
      (le_mul_mono (budget R K T hR hK hT) (le_refl K))) total

theorem precision_bound (a b R K p : PTm n)
    (hK : Γ ⊢[PRAAx] le one K) (hp : Γ ⊢[PRAAx] le (cutoff R p) K)
    (h : Γ ⊢[PRAAx] distanceBounded a b (rate R) K) :
    Γ ⊢[PRAAx] distanceBounded a b one (unit p) :=
  distance_radius_mono a b _ _ _ _ hK (unit_positive p)
    (le_congr (.eqRefl _) (one_mul K).eqSymm hp) h

theorem actual_t4_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((le one (var 2) ⋏ le one (var 1)) ⟶ le (var 0) (num 32) ⟶
      le (var 1*prefactorError (var 2)+productError (var 2) (var 1) (var 0))
        (rate (var 2)*squareDenominator (var 2) (var 1))) :=
  closeUniv 3 (.impI (.impI (budget _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianSineProductT4Budget
