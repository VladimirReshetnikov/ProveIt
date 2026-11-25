import IPRADerivations.Analysis.GaussianLogGammaEulerReciprocalSlopeCofinal
import IPRADerivations.Analysis.GaussianLogGammaEulerLinearSlope
import IPRADerivations.Analysis.GaussianRationalLowerBounds
import IPRADerivations.Analysis.GaussianBetaUpperPowerCancellation

/-!
# Uniform magnitude of the original cofinal Euler slope

On a fixed disk with a positive real margin, compare every original
cofinal reciprocal-slope observation to the cutoff-one read.
The bound depends on the disk and margin and is uniform in the
denominator of the signed rational input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerReciprocalSlopeBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerLinearSlope (shifted_point)
open GaussianLogGammaEulerReciprocalSlope (reciprocalSum rowBody row_at shiftedPoint shifted_lower)
open GaussianLogGammaEulerReciprocalSlopeCofinal (canonicalData cutoff nameF sample_at)
open GaussianLogGammaEulerReciprocalSlopeGap (gapDenominator gapNumerator observed ordered_gap subst_observed)
open GaussianLogGammaEulerResidualDomain (native source)
open GaussianLogGammaEulerResidualRadius (native_norm radius)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (ofGaussian_represents positive_product qadd qzero)
open GaussianRationalMetric (bounded distanceBounded qnegative qnegative_canonical)
open GaussianRationalReciprocal
  (bound_congr bounded_negative bounded_sum inverse_bound reciprocal reciprocal_canonical)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr qzero_add)
open GaussianReconstructionRoots (norm_from_distance)
open ConciseIPRA.PTm (succ zero)
open LeanProofs.IPRA.PTm (monus num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def bound (R K : PTm n) : PTm n := R + K + num 4

@[simp] theorem subst_bound {m : ℕ} (σ : Fin n → PTm m) (R K : PTm n) :
    Syn.subst σ (bound R K) = bound (Syn.subst σ R) (Syn.subst σ K) := by simp [bound]

private theorem argument_lower (A B D neg K : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D neg)
    (hK : Γ ⊢[PRAAx] le one K) (hm : Γ ⊢[PRAAx] le D (K*A)) :
    Γ ⊢[PRAAx] GaussianRationalLowerBounds.lower (argument A B D neg) one K := by
  have component : Γ ⊢[PRAAx] le (A*A) (ComplexLogarithmRemainder.normSq (native A B neg)) :=
    le_congr (.eqRefl _) (native_norm A B neg h.andE₁.andE₂).eqSymm (le_add_right _ _)
  have squared := le_mul_mono hm hm
  have scaled := le_mul_mono (le_refl (K*K)) component
  have clear := le_trans squared (le_congr (by ipra_ring) (.eqRefl _) scaled)
  exact GaussianRationalLowerBounds.lower_from_representation _ (native A B neg) D one K h.andE₂ hK
    (ofGaussian_represents _ _ h.andE₂) (le_congr (by ipra_ring) (.eqRefl _) clear)

private theorem at_zero (A B D neg K : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D neg)
    (hK : Γ ⊢[PRAAx] le one K) (hm : Γ ⊢[PRAAx] le D (K*A)) :
    Γ ⊢[PRAAx] bounded (reciprocal (shiftedPoint (argument A B D neg) zero)) K one := by
  let a := A + zero * D
  have margin := le_trans hm (le_mul_mono (le_refl K) (le_add_right A (zero * D)))
  have hs := GaussianLogGammaEulerHead.shifted_source zero A D neg h
  have lower := argument_lower a B D neg K hs hK margin
  exact bound_congr (GaussianNameReciprocal.reciprocal_congr (shifted_point A B D neg zero h.andE₂)).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianRationalLowerBounds.inverse_bound _ one K (le_refl one) hK lower)

private theorem cutoff_one_bound (A B D neg K : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D neg)
    (hK : Γ ⊢[PRAAx] le one K) (hm : Γ ⊢[PRAAx] le D (K*A)) :
    Γ ⊢[PRAAx] bounded (observed zero A B D neg one) (K + one) one := by
  let z := argument A B D neg
  let u := reciprocal (shiftedPoint z zero)
  let v := reciprocal (shiftedPoint z one)
  let s := reciprocalSum A B D neg (succ one)
  have first := at_zero A B D neg K h hK hm
  have second := inverse_bound (shiftedPoint z one) one (le_refl one) (shifted_lower A B D neg one h)
  have built := GaussianRationalFiniteSum.sum_succ (Γ := Γ) rowBody zero z
  have term : Γ ⊢[PRAAx] inst2 rowBody zero z ≐ u := row_at z zero
  have replaced := qadd_congr (GaussianRationalFiniteSum.sum_zero rowBody z) term
  have oneRow := built.eqTrans (replaced.eqTrans (qzero_add u (reciprocal_canonical _)))
  have rows : Γ ⊢[PRAAx] s ≐ qadd u v :=
    (GaussianRationalFiniteSum.sum_succ rowBody one z).eqTrans (qadd_congr oneRow (row_at z one))
  have hSum : Γ ⊢[PRAAx] bounded s (K+one) one :=
    bound_congr rows.eqSymm (by ipra_ring) (by ipra_ring)
      (bounded_sum u v K one one one (le_refl one) (le_refl one) first second)
  have logarithm := (GaussianBetaUpperPowerCancellation.rational_log_integer_at (Γ := Γ) zero one).eqTrans
    (GaussianBetaUpperPowerCancellation.integer_log_at_one (GaussianBetaUpperPowerCancellation.logClock zero))
  have read : Γ ⊢[PRAAx] observed zero A B D neg one ≐ qnegative s :=
    (qsub_congr logarithm (.eqRefl s)).eqTrans (qzero_add _ (qnegative_canonical s))
  exact bound_congr read.eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_negative s (K+one) one (le_refl one) hSum)

private theorem index_five {α : Type} (a b c d e f : α) : ![a, b, c, d, e, f] (5 : Fin 6) = f := rfl

private theorem observed_congr (p A B D neg N M : PTm n) (h : Γ ⊢[PRAAx] N ≐ M) :
    Γ ⊢[PRAAx] observed p A B D neg N ≐ observed p A B D neg M := by
  simpa only [subst_observed, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, index_five, Matrix.head_cons, Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (observed (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
      (σ := ![p,A,B,D,neg,N]) (σ' := ![p,A,B,D,neg,M]) (fun i => by
        fin_cases i
        any_goals exact h
        all_goals exact .eqRefl _)

theorem canonical_at (p A B D neg R K : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R)
    (hK : Γ ⊢[PRAAx] le one K) (hm : Γ ⊢[PRAAx] le D (K*A)) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (canonicalData A B D neg)) (bound R K) one := by
  let R₀ := radius A B
  let N := cutoff R₀ p
  let U := unit (succ p)
  let V : PTm n := unit zero
  let x := ap2 nameF p (canonicalData A B D neg)
  let y := observed zero A B D neg one
  have hN : Γ ⊢[PRAAx] le one N := positive_product _ _ (le_add_left one R₀) (unit_positive (succ p))
  have hU := unit_positive (Γ := Γ) (succ p)
  have hV := unit_positive (Γ := Γ) zero
  have raw := ordered_gap (succ p) zero A B D neg R one (monus N one) h (le_refl one)
  have bind := (observed_congr (succ p) A B D neg _ _ (eq_add_of_le hN).eqSymm).eqTrans
    (sample_at p A B D neg R₀).eqSymm
  have comparison : Γ ⊢[PRAAx] distanceBounded x y (R + num 3) one :=
    distance_congr bind (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (distance_radius_mono _ _ _ _ (R + num 3) one
        (positive_product _ _ (le_refl one) (positive_product U V hU hV)) (le_refl one)
        (by dsimp only [gapNumerator, gapDenominator, U, V]; ipra_le 𝔞(V)*sl hU+𝔞(U)*sl hV) raw)
  exact bound_congr (.eqRefl _) (by unfold bound; ipra_ring) (by ipra_ring)
    (norm_from_distance x y (R+num 3) one (K+one) one (le_refl one) (le_refl one)
      comparison (cutoff_one_bound A B D neg K h.andE₁ hK hm))

theorem actual_cofinal_Euler_slope_uniform_magnitude_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (source (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ le one (var 6) ⟶ le (var 3) (var 6 * var 1) ⟶
        bounded (ap2 nameF (var 0) (canonicalData (var 1) (var 2) (var 3) (var 4)))
          (bound (var 5) (var 6)) one) :=
  closeUniv 7 (.impI (.impI (.impI (canonical_at _ _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerReciprocalSlopeBound
