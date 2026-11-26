import IPRADerivations.Analysis.Gamma.NegativeAxis.GaussianGammaNegativeIntervalChordInverse
import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUnitCompactTimeBounds
import IPRADerivations.Analysis.Beta.GaussianEulerBetaProductPascal

/-!
# The inverse shift-product derivative at two rational offsets

The original inverse multipliers are kept at their own encodings. A
common denominator computes a finite coefficient whose error against
the original derivative is linear in the displacement. Multiplying
this error by the displacement bounds the first-order remainder.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalInverseRationalEnvelope

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeIntervalChordInverse (poleMargin inverse_bound)
open GaussianGammaNegativeIntervalInverseBound (literal_inverse)
open GaussianGammaNegativeIntervalInverseRecurrence (inverse correctionFactor)
open GaussianGammaNegativeIntervalNative (product)
open GaussianGammaNegativeIntervalRescale (guard_rescale original_product_rescale)
open GaussianGammaNegativeProductDerivative (dividedDifference original_product_gap)
open GaussianGammaNegativeProductDerivativeInverse (inverseCoefficient inverse_coefficient_difference)
open GaussianGammaNegativeProductDerivativeInverseRate (inverseGapCost inverseRateCost original_inverse_gap_bound original_inverse_coefficient_rate)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (positive_product qmul qmul_canonical)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr qone)
open GaussianStirlingGammaLogarithm (arg)
open GaussianStirlingRationalTelescopers (fraction_same)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev window (a b E : PTm n) : Fm PTm n := GaussianEulerUnitCompactTimeBounds.source a b E

def productCoefficient (a b c d N : PTm n) : PTm n :=
  dividedDifference (arg (d*a)) (arg (b*c)) (d*b) (succ N)

def finiteCoefficient (a b c d N : PTm n) : PTm n :=
  inverseCoefficient (inverse c d N) (inverse a b N) (productCoefficient a b c d N)

@[simp] theorem subst_productCoefficient {m : ℕ} (σ : Fin n → PTm m) (a b c d N : PTm n) :
    Syn.subst σ (productCoefficient a b c d N) =
      productCoefficient (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) (Syn.subst σ d) (Syn.subst σ N) := by
  simp [productCoefficient]

@[simp] theorem subst_finiteCoefficient {m : ℕ} (σ : Fin n → PTm m) (a b c d N : PTm n) :
    Syn.subst σ (finiteCoefficient a b c d N) =
      finiteCoefficient (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) (Syn.subst σ d) (Syn.subst σ N) := by
  simp [finiteCoefficient]

private theorem denominator_positive {a b : PTm n} (h : Γ ⊢[PRAAx] guard a b) : Γ ⊢[PRAAx] le one b :=
  le_trans h.andE₁ (le_of_lt h.andE₂)

private theorem denominator_product_congr {a b d N : PTm n} (e : Γ ⊢[PRAAx] b ≐ d) :
    Γ ⊢[PRAAx] product a b N ≐ product a d N := by
  simpa [product, GaussianGammaNegativeIntervalNative.argument] using
    Prf.eqCongr (product (var 0) (var 1) (var 2) : PTm 3) (σ := ![a,b,N]) (σ' := ![a,d,N])
      (fun k => by fin_cases k; exact .eqRefl a; exact e; exact .eqRefl N)

theorem inverse_rescale (a b N s : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hs : Γ ⊢[PRAAx] le one s) :
    Γ ⊢[PRAAx] inverse (s*a) (s*b) N ≐ inverse a b N :=
  GaussianEulerBetaProductPascal.inverse_unique (product a b N) _ _ (qmul_canonical _ _) (qmul_canonical _ _)
    ((qmul_congr (original_product_rescale a b s N h hs).eqSymm (.eqRefl _)).eqTrans
      (literal_inverse (s*a) (s*b) N (guard_rescale a b s h hs)))
    (literal_inverse a b N h)

theorem correction_factor_rescale (a b N s : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hs : Γ ⊢[PRAAx] le one s) :
    Γ ⊢[PRAAx] correctionFactor (s*a) (s*b) N ≐ correctionFactor a b N :=
  qmul_congr (inverse_rescale a b N s h hs) (GaussianGammaNegativeCriticalRescale.correction_rescale a b N s h hs)

private theorem aligned_guard_right (b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hc : Γ ⊢[PRAAx] guard c d) :
    Γ ⊢[PRAAx] guard (b*c) (d*b) := by
  have h := guard_rescale c d b hc hb
  exact .andI h.andE₁ (le_congr (.eqRefl _) (mul_comm _ _) h.andE₂)

private theorem aligned_product_right (b c d N : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hc : Γ ⊢[PRAAx] guard c d) :
    Γ ⊢[PRAAx] product (b*c) (d*b) N ≐ product c d N :=
  (denominator_product_congr (mul_comm d b)).eqTrans (original_product_rescale c d b N hc hb)

private theorem aligned_fraction_left (a b d : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] fraction (d*a) (d*b) ≐ fraction a b :=
  fraction_same _ _ _ _ (positive_product _ _ hd hb) hb (by ipra_ring)

private theorem aligned_fraction_right (b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] fraction (b*c) (d*b) ≐ fraction c d :=
  fraction_same _ _ _ _ (positive_product _ _ hd hb) hd (by ipra_ring)

theorem exact_difference (a b c d N : PTm n) (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c d) :
    Γ ⊢[PRAAx] qsub (inverse c d N) (inverse a b N) ≐
      qmul (qsub (fraction c d) (fraction a b)) (finiteCoefficient a b c d N) := by
  have hb := denominator_positive ha
  have hd := denominator_positive hc
  have hB := positive_product (Γ := Γ) _ _ hd hb
  have gap : Γ ⊢[PRAAx] qsub (product c d N) (product a b N) ≐
      qmul (qsub (fraction c d) (fraction a b)) (productCoefficient a b c d N) :=
    (qsub_congr (aligned_product_right b c d N hb hc).eqSymm
        (original_product_rescale a b d N ha hd).eqSymm).eqTrans
      ((original_product_gap (arg (d*a)) (arg (b*c)) (d*b) (succ N) hB).eqTrans
        (qmul_congr (qsub_congr (aligned_fraction_right b c d hb hd) (aligned_fraction_left a b d hb hd)) (.eqRefl _)))
  exact inverse_coefficient_difference _ _ _ _ _ _ (qmul_canonical _ _) (qmul_canonical _ _)
    (literal_inverse c d N hc) (literal_inverse a b N ha) gap

theorem envelope (a b c d E N A D : PTm n) (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c d)
    (hma : Γ ⊢[PRAAx] poleMargin a b E) (hmc : Γ ⊢[PRAAx] poleMargin c d E) (hD : Γ ⊢[PRAAx] le one D)
    (hStep : Γ ⊢[PRAAx] distanceBounded (fraction c d) (fraction a b) A D) : Γ ⊢[PRAAx]
    distanceBounded (inverse c d N) (inverse a b N) (inverseGapCost (succ N) (E*E)*A) D ⋏
    distanceBounded (finiteCoefficient a b c d N) (correctionFactor a b N) (inverseRateCost (succ N) (E*E)*A) D := by
  let u := d*a
  let v := b*c
  let B := d*b
  let i₀ := inverse a b N
  let i₁ := inverse c d N
  have hb := denominator_positive ha
  have hd := denominator_positive hc
  have hBase := guard_rescale a b d ha hd
  have hTarget := aligned_guard_right b c d hb hc
  have hi₀ : Γ ⊢[PRAAx] qmul (product u B N) i₀ ≐ qone :=
    (qmul_congr (original_product_rescale a b d N ha hd) (.eqRefl _)).eqTrans (literal_inverse a b N ha)
  have hi₁ : Γ ⊢[PRAAx] qmul (product v B N) i₁ ≐ qone :=
    (qmul_congr (aligned_product_right b c d N hb hc) (.eqRefl _)).eqTrans (literal_inverse c d N hc)
  have bound₀ := inverse_bound a b E N ha hma
  have bound₁ := inverse_bound c d E N hc hmc
  have step := distance_congr (aligned_fraction_right b c d hb hd).eqSymm
    (aligned_fraction_left a b d hb hd).eqSymm (.eqRefl _) (.eqRefl _) hStep
  have variation := original_inverse_gap_bound u v B N i₁ i₀ (E*E) A D hBase hTarget
    (qmul_canonical _ _) (qmul_canonical _ _) hi₁ hi₀ bound₁ bound₀ hD step
  have rate := original_inverse_coefficient_rate u v B N i₁ i₀ (E*E) A D hBase hTarget
    (qmul_canonical _ _) (qmul_canonical _ _) hi₁ hi₀ bound₁ bound₀ hD step
  have correction := GaussianGammaNegativeCriticalRescale.correction_rescale a b N d ha hd
  exact .andI variation (distance_congr (.eqRefl _) (qmul_congr (.eqRefl _) correction) (.eqRefl _) (.eqRefl _) rate)

private theorem window_margin (a b E : PTm n) (h : Γ ⊢[PRAAx] window a b E) : Γ ⊢[PRAAx] poleMargin a b E :=
  .andI h.andE₂.andE₂.andE₁ (GaussianEulerUnitCompactTimeBounds.gap_margin a b E h)

theorem inverse_bound_on_window (a b E N : PTm n) (h : Γ ⊢[PRAAx] window a b E) :
    Γ ⊢[PRAAx] bounded (inverse a b N) (E*E) one :=
  inverse_bound a b E N h.andE₁ (window_margin a b E h)

theorem window_envelope (a b c d E N A D : PTm n) (ha : Γ ⊢[PRAAx] window a b E) (hc : Γ ⊢[PRAAx] window c d E)
    (hD : Γ ⊢[PRAAx] le one D) (hStep : Γ ⊢[PRAAx] distanceBounded (fraction c d) (fraction a b) A D) : Γ ⊢[PRAAx]
    distanceBounded (inverse c d N) (inverse a b N) (inverseGapCost (succ N) (E*E)*A) D ⋏
    distanceBounded (finiteCoefficient a b c d N) (correctionFactor a b N) (inverseRateCost (succ N) (E*E)*A) D :=
  envelope a b c d E N A D ha.andE₁ hc.andE₁ (window_margin a b E ha) (window_margin c d E hc) hD hStep

theorem window_quadratic_remainder (a b c d E N A D : PTm n)
    (ha : Γ ⊢[PRAAx] window a b E) (hc : Γ ⊢[PRAAx] window c d E) (hD : Γ ⊢[PRAAx] le one D)
    (hStep : Γ ⊢[PRAAx] distanceBounded (fraction c d) (fraction a b) A D) : Γ ⊢[PRAAx]
    distanceBounded (qsub (inverse c d N) (inverse a b N))
      (qmul (qsub (fraction c d) (fraction a b)) (correctionFactor a b N)) (inverseRateCost (succ N) (E*E)*A*A) (D*D) := by
  let s := qsub (fraction c d) (fraction a b)
  let u := finiteCoefficient a b c d N
  let v := correctionFactor a b N
  let R := inverseRateCost (succ N) (E*E)
  have rate := (window_envelope a b c d E N A D ha hc hD hStep).andE₂
  have weighted := bounded_product s (qsub u v) A D (R*A) D hD hD hStep rate
  have gap := exact_difference a b c d N ha.andE₁ hc.andE₁
  exact bound_congr ((GaussianRationalRoundedPower.multiplication_difference s u v).eqSymm.eqTrans
    (qsub_congr gap.eqSymm (.eqRefl _))) (by ipra_ring) (.eqRefl _) weighted

theorem actual_negative_Gamma_inverse_shift_rescale_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((guard (var 0) (var 1) ⋏ le one (var 3)) ⟶
        (inverse (var 3*var 0) (var 3*var 1) (var 2) ≐ inverse (var 0) (var 1) (var 2)) ⋏
        (correctionFactor (var 3*var 0) (var 3*var 1) (var 2) ≐ correctionFactor (var 0) (var 1) (var 2))) :=
  closeUniv 4 (.impI (.andI
    (inverse_rescale _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)
    (correction_factor_rescale _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

theorem actual_negative_Gamma_inverse_shift_rational_envelope_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (let a : PTm 8 := var 0; let b : PTm 8 := var 1; let c : PTm 8 := var 2; let d : PTm 8 := var 3;
       let E : PTm 8 := var 4; let N : PTm 8 := var 5; let A : PTm 8 := var 6; let D : PTm 8 := var 7;
       (window a b E ⋏ (window c d E ⋏ (le one D ⋏ distanceBounded (fraction c d) (fraction a b) A D))) ⟶
         (qsub (inverse c d N) (inverse a b N) ≐ qmul (qsub (fraction c d) (fraction a b)) (finiteCoefficient a b c d N)) ⋏
           (distanceBounded (inverse c d N) (inverse a b N) (inverseGapCost (succ N) (E*E)*A) D ⋏
             (distanceBounded (finiteCoefficient a b c d N) (correctionFactor a b N) (inverseRateCost (succ N) (E*E)*A) D ⋏
               distanceBounded (qsub (inverse c d N) (inverse a b N))
                 (qmul (qsub (fraction c d) (fraction a b)) (correctionFactor a b N)) (inverseRateCost (succ N) (E*E)*A*A) (D*D)))) := by
  apply closeUniv 8
  refine .impI ?_
  have h := window_envelope (Γ := [_]) (var 0 : PTm 8) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂
  exact .andI (exact_difference _ _ _ _ _ Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₂.andE₁.andE₁)
    (.andI h.andE₁ (.andI h.andE₂ (window_quadratic_remainder _ _ _ _ _ _ _ _
      Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalInverseRationalEnvelope
