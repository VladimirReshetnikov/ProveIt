import IPRADerivations.Analysis.GaussianLogGammaEulerCofinal
import IPRADerivations.Analysis.GaussianLogGammaEulerRecurrenceFinite
import IPRADerivations.Analysis.GaussianLogGammaEulerTerminalShiftError

/-!
# The canonical log-Gamma unit recurrence

A common cutoff pays both original Euler tails and the terminal correction.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerRecurrence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianLogGammaEulerCofinal (canonicalData canonical_regular cost)
open GaussianLogGammaEulerRecurrenceFinite (correctedF correctedData shift_source)
open GaussianLogGammaEulerResidualRadius (radius)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianNameRingLaws (equivalent_of_envelope additive_inverse_value)
open GaussianNamedDifference (name_regular sample_error difference_distance)
open GaussianPositiveRationalLogarithm (logF)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same reversed_difference)
open GaussianRationalHorner (qadd qzero canonical positive_product)
open GaussianRationalMetric (qnegative qsub distanceBounded)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianReciprocalHorner (qadd_commutative qadd_zero_right)
open GaussianRightHalfPlaneLogarithm (source)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianNamedDifference.nameF
local notation "X" => GaussianNamedDifference.data
local notation "C" => GaussianLogGammaEulerCofinal.nameF
local notation "H" => GaussianLogGammaEulerHead.nameF
local notation "Y" => GaussianLogGammaEulerHead.data
local notation "G" => GaussianRightHalfPlaneLogarithm.nameF
local notation "P" => GaussianRightHalfPlaneLogarithm.data
local notation "L" => GaussianPositiveRationalLogarithm.data
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

private theorem double_subtract (a c : PTm n) (hc : Γ ⊢[PRAAx] canonical c) :
    Γ ⊢[PRAAx] qsub a (qsub a c) ≐ c := by
  have opposite : Γ ⊢[PRAAx] qsub qzero a ≐ qnegative a :=
    (qadd_commutative _ _).eqTrans (qadd_zero_right _ (GaussianRationalMetric.qnegative_canonical a))
  have cancel := (qadd_congr (.eqRefl a) opposite.eqSymm).eqTrans (additive_inverse_value a)
  change Γ ⊢[PRAAx] qadd a (qnegative (qsub a c)) ≐ c
  have reorder : Γ ⊢[PRAAx] qadd a (qadd c (qnegative a)) ≐ qadd c (qadd a (qnegative a)) :=
    (GaussianRationalSumAlgebra.qadd_associative _ _ _).eqSymm.eqTrans
      ((qadd_congr (qadd_commutative a c) (.eqRefl (qnegative a))).eqTrans
        (GaussianRationalSumAlgebra.qadd_associative _ _ _))
  exact (qadd_congr (.eqRefl a) (reversed_difference a c)).eqTrans
    (reorder.eqTrans ((qadd_congr (.eqRefl c) cancel).eqTrans (qadd_zero_right c hc)))

private theorem correction_from_terminal (p A B D neg N : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (hN : Γ ⊢[PRAAx] le one N)
    (term : Γ ⊢[PRAAx] distanceBounded (ap2 G p (P (A+succ N*D) B D neg))
      (ap2 logF p (L N one)) (num 9) (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 correctedF p (correctedData A B D neg N))
      (ap2 G p (P A B D neg)) (num 21) (unit p) := by
  let x := L N one
  let y := P (A+succ N*D) B D neg
  let z := P A B D neg
  let a := ap2 logF p x
  let b := ap2 G p y
  let c := ap2 G p z
  let d := ap2 (F G G) p (X y z)
  let U := unit p
  let sample := ap2 correctedF p (correctedData A B D neg N)
  have hU := unit_positive (Γ := Γ) p
  have hx := GaussianPositiveRationalLogarithm.name_regular (Γ := Γ) N one (.andI hN (le_refl one))
  have hy := GaussianRightHalfPlaneLogarithm.regular (A+succ N*D) B D neg
    (GaussianLogGammaEulerHead.shifted_source (succ N) A D neg h)
  have hz := GaussianRightHalfPlaneLogarithm.regular A B D neg h
  have first : Γ ⊢[PRAAx] distanceBounded sample (qsub a d) (num 6) U :=
    sample_error logF (F G G) x (X y z) p hx (name_regular G G y z hy hz)
  have second := difference_distance a a d (qsub b c) zero (num 6) U hU
    (distance_refl_zero a U hU) (sample_error G G y z p hy hz)
  have middle := distance_triangle_same sample (qsub a d) (qsub a (qsub b c)) (num 6) (zero+num 6) U hU first second
  have inner := difference_distance b a c c (num 9) zero U hU term (distance_refl_zero c U hU)
  have last := difference_distance a a (qsub b c) (qsub a c) zero (num 9+zero) U hU
    (distance_refl_zero a U hU) inner
  have hc : Γ ⊢[PRAAx] canonical c := GaussianNameArithmetic.add_canonical _ _ _ _ p
  exact distance_congr (.eqRefl _) (double_subtract a c hc) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same sample (qsub a (qsub b c)) (qsub a (qsub a c)) _ _ U hU middle last)

private theorem finite_rate (p A B D neg N : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (hN : Γ ⊢[PRAAx] le one N)
    (hlarge : Γ ⊢[PRAAx] le (num 8*radius A B) N)
    (hpaid : Γ ⊢[PRAAx] le (cost (radius A B)*unit p) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 C p (canonicalData A B D neg)) (ap2 H p (Y A B D neg N))
      (num 3) (unit p) := by
  let U := unit p
  have hu := unit_positive (Γ := Γ) p
  have den := positive_product _ _ (positive_product _ _ hN hu) hu
  exact distance_radius_mono _ _ _ _ (num 3) U den hu
    (by ipra_le 𝔞(U)^2*sl hpaid)
    (GaussianLogGammaEulerCofinal.canonical_original_cutoff_distance p p A B D neg N h hN hlarge)

private theorem recurrence_at (p A B D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 (F C C) p (X (canonicalData (A+D) B D neg) (canonicalData A B D neg)))
      (ap2 G p (P A B D neg)) (num 41) (unit p) := by
  let r := radius A B
  let s := radius (A+D) B
  let U := unit p
  let N := num 8*(r+s)+one+(cost r+cost s+two*s)*U
  let x := canonicalData (A+D) B D neg
  let y := canonicalData A B D neg
  let x' := Y (A+D) B D neg N
  let y' := Y A B D neg N
  let c := ap2 (F C C) p (X x y)
  let f := ap2 (F H H) p (X x' y')
  let w := qsub (ap2 C p x) (ap2 C p y)
  let w' := qsub (ap2 H p x') (ap2 H p y')
  let d := ap2 correctedF p (correctedData A B D neg N)
  have hU := unit_positive (Γ := Γ) p
  have hs := shift_source A D neg h
  have hN : Γ ⊢[PRAAx] le one N := by unfold N; ipra_le 8*(𝔞(r)+𝔞(s))+(𝔞(cost r)+𝔞(cost s)+2*𝔞(s))*𝔞(U)
  have hr : Γ ⊢[PRAAx] le (num 8*r) N := by unfold N; ipra_le 8*𝔞(s)+1+(𝔞(cost r)+𝔞(cost s)+2*𝔞(s))*𝔞(U)
  have hlarge : Γ ⊢[PRAAx] le (num 8*s) N := by unfold N; ipra_le 8*𝔞(r)+1+(𝔞(cost r)+𝔞(cost s)+2*𝔞(s))*𝔞(U)
  have hpayR : Γ ⊢[PRAAx] le (cost r*U) N := by unfold N; ipra_le 8*(𝔞(r)+𝔞(s))+1+(𝔞(cost s)+2*𝔞(s))*𝔞(U)
  have hpayS : Γ ⊢[PRAAx] le (cost s*U) N := by unfold N; ipra_le 8*(𝔞(r)+𝔞(s))+1+(𝔞(cost r)+2*𝔞(s))*𝔞(U)
  have hpayTerm : Γ ⊢[PRAAx] le (two*s*U) N := by unfold N; ipra_le 8*(𝔞(r)+𝔞(s))+1+(𝔞(cost r)+𝔞(cost s))*𝔞(U)
  have e₁ : Γ ⊢[PRAAx] distanceBounded c w (num 6) U :=
    sample_error C C x y p (canonical_regular (A+D) B D neg hs) (canonical_regular A B D neg h)
  have e₂ : Γ ⊢[PRAAx] distanceBounded w w' (num 3+num 3) U :=
    difference_distance _ _ _ _ _ _ U hU
      (finite_rate p (A+D) B D neg N hs hN hlarge hpayS) (finite_rate p A B D neg N h hN hr hpayR)
  have e₃ : Γ ⊢[PRAAx] distanceBounded w' f (num 6) U :=
    distance_symmetric _ _ _ _ hU (sample_error H H x' y' p
      (GaussianLogGammaEulerHead.regular (A+D) B D neg N hs hN) (GaussianLogGammaEulerHead.regular A B D neg N h hN))
  have e₄ : Γ ⊢[PRAAx] distanceBounded f d two U :=
    distance_radius_mono f d (U+U) (U*U) two U (positive_product _ _ hU hU) hU
      (le_of_eq_add (d := zero) (by ipra_ring))
      (cross_at (F H H) correctedF (X x' y') (correctedData A B D neg N) p p
        (GaussianLogGammaEulerRecurrenceFinite.difference A B D neg N h hN))
  have e₅ := GaussianLogGammaEulerTerminalShiftError.terminal_sample_error p A B D neg N h hlarge
  have term := distance_radius_mono _ _ (num 2*s*U+num 8*N) (N*U) (num 9) U
    (positive_product _ _ hN hU) hU (by ipra_le 𝔞(U)*sl hpayTerm) e₅
  have e₆ := correction_from_terminal p A B D neg N h hN term
  have c₂ := distance_triangle_same c w w' _ _ U hU e₁ e₂
  have c₃ := distance_triangle_same c w' f _ _ U hU c₂ e₃
  have c₄ := distance_triangle_same c f d _ _ U hU c₃ e₄
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same c d _ _ _ U hU c₄ e₆)

theorem recurrence (A B D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] crossEquivalent (F C C) G
      (X (canonicalData (A+D) B D neg) (canonicalData A B D neg)) (P A B D neg) := by
  apply equivalent_of_envelope _ _ _ _ (num 41)
    (name_regular C C _ _ (canonical_regular _ _ _ _ (shift_source A D neg h)) (canonical_regular A B D neg h))
    (GaussianRightHalfPlaneLogarithm.regular A B D neg h)
  refine .allI ?_
  let s (a : PTm n) := Syn.shift a
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (s A) (s D) (s neg) := by
    simpa [Fm.shift,Syn.shift,s,source,GaussianRightHalfPlaneArgument.source] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,s,PTm.subst_add,
    GaussianNamedDifference.subst_data,GaussianLogGammaEulerCofinal.subst_canonicalData,
    GaussianRightHalfPlaneLogarithm.subst_data,LeanProofs.IPRA.PTm.subst_num] using
    recurrence_at (var 0) (s A) (s B) (s D) (s neg) hs

theorem actual_canonical_log_Gamma_unit_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 2) (var 3) ⟶ crossEquivalent (F C C) G
      (X (canonicalData (var 0+var 2) (var 1) (var 2) (var 3))
        (canonicalData (var 0) (var 1) (var 2) (var 3))) (P (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (recurrence _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerRecurrence
