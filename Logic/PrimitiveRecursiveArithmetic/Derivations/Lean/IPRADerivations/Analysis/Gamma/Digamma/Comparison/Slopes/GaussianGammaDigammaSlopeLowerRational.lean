import IPRADerivations.Analysis.Gamma.Digamma.Comparison.Slopes.GaussianGammaDigammaSlopeLower
import IPRADerivations.Analysis.Gamma.Digamma.Series.GaussianGammaDigammaRescaling
import IPRADerivations.Analysis.Gamma.Integrals.CompactQuadrature.GaussianGammaCompactCutoffAlignment
import IPRADerivations.Analysis.Names.Rates.Order.GaussianNamedRealOrderTransport

/-!
# Lower digamma slope for separately encoded positive rationals

The native names at a/b and c/d retain their own input encodings.
Rescaling to the common denominator d*b transfers the exact lower
slope with margin (c*b−a*d)/(4*d*b).
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaSlopeLowerRational

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (fraction_congr)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaDigammaNative (data nameF name_regular)
open GaussianGammaDigammaRescaling (original_rescaling)
open GaussianGammaDigammaSlopeLower (lowerF lower_slope)
open GaussianGammaDigammaSlopeLowerFinite (margin)
open GaussianNameArithmetic (addData add_equivalent)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_to_diagonal)
open GaussianNameRingLaws (add_sample_error three)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at scalar_coordinate_distance)
open GaussianNamedRealOrderTransport (transport)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalSyntheticDivision (qadd_congr)
open RationalValueBounds (upper upper_congr upper_of_radius upper_triangle upper_mono)
open GaussianStirlingGammaLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def domain (a b c d : PTm n) : Fm PTm n :=
  le one b ⋏ (le b a ⋏ (le one d ⋏ (le d c ⋏ (le (d*a) (b*c) ⋏ le c (two*d)))))

ipra_subst domain [two]

def quarterGap (a b c d : PTm n) : PTm n := fraction (monus (c*b) (a*d)) (num 4*b*d)

ipra_subst quarterGap

def lowerData (a b c d : PTm n) : PTm n :=
  addData (data a b) (margin (d*a) (b*c) (d*b))

ipra_subst lowerData

theorem lower_slope_rational (a b c d : PTm n) (h : Γ ⊢[PRAAx] domain a b c d) :
    Γ ⊢[PRAAx] realOrder lowerF nameF (lowerData a b c d) (data c d) := by
  let B := d*b
  let A := d*a
  let C := b*c
  let g := margin A C B
  have hb : Γ ⊢[PRAAx] le one b := h.andE₁
  have hba : Γ ⊢[PRAAx] le b a := h.andE₂.andE₁
  have hd : Γ ⊢[PRAAx] le one d := h.andE₂.andE₂.andE₁
  have hdc : Γ ⊢[PRAAx] le d c := h.andE₂.andE₂.andE₂.andE₁
  have hAC : Γ ⊢[PRAAx] le A C := h.andE₂.andE₂.andE₂.andE₂.andE₁
  have hcu : Γ ⊢[PRAAx] le c (two*d) := h.andE₂.andE₂.andE₂.andE₂.andE₂
  have hB := positive_product d b hd hb
  have hBA : Γ ⊢[PRAAx] le B A := le_congr (mul_comm b d) (mul_comm a d) (mul_le_mul_right d hba)
  have hCU : Γ ⊢[PRAAx] le C (two*B) := by
    unfold C B
    ipra_le 𝔞 b * sl hcu
  have common : Γ ⊢[PRAAx] GaussianGammaDigammaSlopeLowerFinite.domain A C B :=
    .andI hB (.andI hBA (.andI hAC hCU))
  have leftSource : Γ ⊢[PRAAx] source a b := .andI (le_trans hb hba) hb
  have rightSource : Γ ⊢[PRAAx] source c d := .andI (le_trans hd hdc) hd
  have eqLeft := original_rescaling a b d leftSource hd
  have eB : Γ ⊢[PRAAx] b*d ≐ B := mul_comm b d
  have eqRight := GaussianGammaDigammaRescaling.original_rescaling c d b rightSource hb
  have recode : Γ ⊢[PRAAx] data C (b*d) ≐ data C B := by
    simpa only [GaussianGammaDigammaNative.subst_data,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
      Prf.eqCongr (data (var 0) (var 1) : PTm 2) (σ := ![C,b*d]) (σ' := ![C,B])
        (fun i => by fin_cases i; exact .eqRefl _; exact eB)
  have crossRight : Γ ⊢[PRAAx] crossEquivalent nameF nameF (data C B) (data c d) :=
    GaussianGammaCompactCutoffAlignment.cross_data_congr _ _ _ _ _ _ recode (.eqRefl _) eqRight
  have r := constant_regular (Γ := Γ) g
  have eqAdded := add_equivalent nameF nameF constantF constantF (data a b) (data A B) g g
    (name_regular a b leftSource) (name_regular A B (.andI (le_trans hB hBA) hB))
    r r (cross_to_diagonal _ _ _ _ (cross_symm _ _ _ _ eqLeft))
    (cross_to_diagonal _ _ _ _ (cross_refl _ _ r))
  exact transport lowerF lowerF nameF nameF (lowerData a b c d)
    (GaussianGammaDigammaSlopeLower.lowerData A C B) (data C B) (data c d) eqAdded crossRight
    (lower_slope A C B common)

private theorem gap_recode (a b c d : PTm n) :
    Γ ⊢[PRAAx] margin (d*a) (b*c) (d*b) ≐ quarterGap a b c d :=
  fraction_congr _ _ _ _ (congrMonus (mul_comm b c) (mul_comm d a)) (by ipra_ring)

/-- Original observations at two independent clocks. Normalized addition
costs 3/2^p, so the exact error is 4/2^p+1/2^q. -/
theorem lower_slope_rational_at_exact (a b c d p q : PTm n) (h : Γ ⊢[PRAAx] domain a b c d) :
    Γ ⊢[PRAAx] upper
      (RationalArithmetic.add (fstT (ap2 nameF p (data a b))) (fstT (quarterGap a b c d)))
      (fstT (ap2 nameF q (data c d))) (num 4*unit q+unit p) (unit p*unit q) := by
  let g := margin (d*a) (b*c) (d*b)
  let X := ap2 nameF p (data a b)
  let Y := ap2 lowerF p (lowerData a b c d)
  let Z := ap2 nameF q (data c d)
  let P := unit p
  let Q := unit q
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have src : Γ ⊢[PRAAx] source a b := .andI (le_trans h.andE₁ h.andE₂.andE₁) h.andE₁
  have err : Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded Y (qadd X g) three P :=
    distance_congr (.eqRefl _) (qadd_congr (.eqRefl _) (constant_at p g)) (.eqRefl _) (.eqRefl _)
      (add_sample_error nameF constantF (data a b) g p (name_regular a b src) (constant_regular g))
  have raw := upper_of_radius _ _ _ _
    (scalar_coordinate_distance _ _ _ _ hp (distance_symmetric _ _ _ _ hp err))
  have obs : Γ ⊢[PRAAx] upper (fstT Y) (fstT Z) (P+Q) (P*Q) :=
    real_order_at lowerF nameF (lowerData a b c d) (data c d) p q (lower_slope_rational a b c d h)
  have joined := upper_triangle _ _ _ _ _ _ _ raw obs
  have exactRadius : Γ ⊢[PRAAx] upper (fstT (qadd X g)) (fstT Z) (num 4*Q+P) (P*Q) :=
    upper_mono _ _ _ _ _ _ (positive_product _ _ hp (positive_product _ _ hp hq)) joined
      (le_of_eq_add (d := zero) (by unfold three; ipra_ring))
  have e := (RationalGaussianRealPart.real_add (Γ := Γ) X g).eqTrans
    (RationalAlgebra.add_congr (.eqRefl _) (congrFst (gap_recode a b c d)))
  exact upper_congr e (.eqRefl _) (.eqRefl _) (.eqRefl _) exactRadius

theorem lower_slope_rational_at (a b c d p q : PTm n) (h : Γ ⊢[PRAAx] domain a b c d) :
    Γ ⊢[PRAAx] upper
      (RationalArithmetic.add (fstT (ap2 nameF p (data a b))) (fstT (quarterGap a b c d)))
      (fstT (ap2 nameF q (data c d))) (num 4*(unit p+unit q)) (unit p*unit q) := by
  apply upper_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive q))
    (lower_slope_rational_at_exact a b c d p q h)
  ipra_le 3*𝔞 (unit p)*𝔞 (unit p*unit q)

theorem actual_original_digamma_lower_slope_rational_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (domain (var 0) (var 1) (var 2) (var 3) ⟶
        realOrder lowerF nameF (lowerData (var 0) (var 1) (var 2) (var 3)) (data (var 2) (var 3))) :=
  closeUniv 4 (.impI (lower_slope_rational _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaSlopeLowerRational
