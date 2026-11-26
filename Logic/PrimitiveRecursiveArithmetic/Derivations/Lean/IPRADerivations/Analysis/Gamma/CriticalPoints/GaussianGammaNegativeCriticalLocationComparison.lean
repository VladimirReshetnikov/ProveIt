import IPRADerivations.Analysis.Gamma.CriticalPoints.GaussianGammaNegativeCriticalLowerSlope
import IPRADerivations.Analysis.Gamma.CriticalPoints.GaussianGammaNegativeCriticalRescale

/-!
# Lower slope between independently encoded negative digamma arguments

The two original named values are transported from their common positive
denominator. The added lower-slope displacement is the actual rational
((c/d-a/b)/4), and the original observation allowances are preserved.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalLocationComparison

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeCriticalCorrectionSlope (ordered)
open GaussianGammaNegativeCriticalEndpoints (nameF nameData name_regular)
open GaussianGammaNegativeCriticalLowerSlope (lowerF lower_slope)
open GaussianGammaNegativeCriticalRescale (scaled_guard original_rescale)
open GaussianNameArithmetic (addData add_equivalent)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_refl cross_to_diagonal)
open GaussianNameRingLaws (add_sample_error three)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at)
open GaussianNamedRealOrderTransport (transport)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianStirlingGammaFractionalIncrementObservations (scalar_upper)
open RationalValueBounds (upper upper_congr upper_triangle upper_mono)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def domain (a b c d : PTm n) : Fm PTm n :=
  guard a b ⋏ (guard c d ⋏ le (d*a) (b*c))
def margin (a b c d : PTm n) : PTm n := GaussianGammaNegativeCriticalLowerSlope.margin (d*a) (b*c) (d*b)
def lowerData (a b c d N : PTm n) : PTm n := addData (nameData a b N) (margin a b c d)

theorem datum_congr {a a' b b' N : PTm n}
    (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] nameData a b N ≐ nameData a' b' N := by
  simpa only [GaussianGammaNegativeCriticalEndpoints.subst_nameData,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (nameData (var 0) (var 1) (var 2) : PTm 3) (σ := ![a,b,N]) (σ' := ![a',b',N])
      (fun j => by fin_cases j; exacts [ha,hb,.eqRefl _])

theorem mixed_lower_slope (a b c d N : PTm n) (h : Γ ⊢[PRAAx] domain a b c d) :
    Γ ⊢[PRAAx] realOrder lowerF nameF (lowerData a b c d N) (nameData c d N) := by
  let A := d*a
  let C := b*c
  let B := d*b
  let m := margin a b c d
  have h1 := h.andE₁
  have h2 := h.andE₂.andE₁
  have ob := le_trans h1.andE₁ (le_of_lt h1.andE₂)
  have od := le_trans h2.andE₁ (le_of_lt h2.andE₂)
  have s1 := scaled_guard a b d h1 od
  have s2 := scaled_guard c d b h2 ob
  have hc : Γ ⊢[PRAAx] lt C B := lt_congr (.eqRefl _) (mul_comm b d) s2.andE₂
  have hp : Γ ⊢[PRAAx] ordered A C B := .andI s1.andE₁ (.andI h.andE₂.andE₂ hc)
  have right : Γ ⊢[PRAAx] crossEquivalent nameF nameF (nameData C B N) (nameData c d N) :=
    GaussianGammaCompactCutoffAlignment.cross_data_congr _ _ _ _ _ _
      (datum_congr (.eqRefl _) (mul_comm b d)) (.eqRefl _) (original_rescale c d N b h2 ob)
  have left := add_equivalent nameF nameF constantF constantF (nameData a b N) (nameData A B N) m m
    (name_regular _ _ _ h1) (name_regular _ _ _ s1) (constant_regular m) (constant_regular m)
    (cross_to_diagonal _ _ _ _ (cross_symm _ _ _ _ (original_rescale a b N d h1 od)))
    (cross_to_diagonal _ _ _ _ (cross_refl _ _ (constant_regular m)))
  exact transport _ _ _ _ _ _ _ _ left right (lower_slope A C B N hp)

theorem mixed_lower_at (p q a b c d N : PTm n) (h : Γ ⊢[PRAAx] domain a b c d) :
    Γ ⊢[PRAAx] upper
      (RationalArithmetic.add (fstT (ap2 nameF p (nameData a b N))) (fstT (margin a b c d)))
      (fstT (ap2 nameF q (nameData c d N))) (num 4*unit q+unit p) (unit p*unit q) := by
  let x := nameData a b N
  let y := nameData c d N
  let m := margin a b c d
  let v := ap2 nameF p x
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have err : Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded
      (ap2 lowerF p (lowerData a b c d N)) (qadd v m) three (unit p) :=
    distance_congr (.eqRefl _) (qadd_congr (.eqRefl _) (constant_at p m)) (.eqRefl _) (.eqRefl _)
      (add_sample_error nameF constantF x m p (name_regular a b N h.andE₁) (constant_regular m))
  have raw := scalar_upper _ _ _ _ hp (distance_symmetric _ _ _ _ hp err)
  have observed := real_order_at lowerF nameF (lowerData a b c d N) y p q (mixed_lower_slope a b c d N h)
  have joined := upper_triangle _ _ _ _ _ _ _ raw observed
  have scale := upper_mono _ _ _ _ (num 4*unit q+unit p) (unit p*unit q)
    (positive_product _ _ hp (positive_product _ _ hp hq)) joined (by unfold three; ipra_le 0)
  exact upper_congr (RationalGaussianRealPart.real_add v m) (.eqRefl _) (.eqRefl _) (.eqRefl _) scale

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalLocationComparison
