import IPRADerivations.Analysis.GaussianLogGammaEulerReciprocalSlopeGap
import IPRADerivations.Analysis.GaussianNamedLipschitzRate

/-!
# Cofinal complex Euler slope

At precision `p`, read the literal Euler slope at clock `p+1` and
cutoff `(R+1)·2^(p+1)`. The explicit cutoff pays for the analytic tail,
and the faster clock pays for the original logarithm observation.
The resulting name has rate `(R+1)/N` to the original finite slope.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerReciprocalSlopeCofinal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerRepresentation (subst_argument)
open GaussianLogGammaEulerResidualDomain (source subst_source)
open GaussianLogGammaEulerResidualRadius (radius source_of_right_half_plane)
open GaussianLogGammaEulerReciprocalSlope (rowBody reciprocalSum)
open GaussianLogGammaEulerReciprocalSlopeGap (gapNumerator gapDenominator ordered_gap subst_observed)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator independent_rate)
open GaussianPositiveRationalLogarithm (logF sample name_regular)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalSyntheticDivision (qsub_congr)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "slopeF" => GaussianLogGammaEulerReciprocalSlope.nameF
local notation "slopeData" => GaussianLogGammaEulerReciprocalSlope.data
local notation "finiteRead" => GaussianLogGammaEulerReciprocalSlopeGap.observed

def cutoff (R p : PTm n) : PTm n := (R + one) * unit (succ p)

private def readAt (p z R : PTm n) : PTm n :=
  qsub (sample (succ p) (cutoff R p) one) (GaussianRationalFiniteSum.sum rowBody (succ (cutoff R p)) z)

def data (A B D neg R : PTm n) : PTm n := pairT (argument A B D neg) R

def canonicalData (A B D neg : PTm n) : PTm n := data A B D neg (radius A B)

private def body : PTm 2 := readAt (var 0) (fstT (var 1)) (sndT (var 1))
def nameF : PR 2 := PTm.toPR body

@[simp] theorem subst_cutoff {m : ℕ} (σ : Fin n → PTm m) (R p : PTm n) :
    Syn.subst σ (cutoff R p) = cutoff (Syn.subst σ R) (Syn.subst σ p) := by simp [cutoff, one]

@[simp] private theorem subst_readAt {m : ℕ} (σ : Fin n → PTm m) (p z R : PTm n) :
    Syn.subst σ (readAt p z R) = readAt (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) := by
  simp [readAt, sample, one]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (A B D neg R : PTm n) :
    Syn.subst σ (data A B D neg R) = data (Syn.subst σ A) (Syn.subst σ B)
      (Syn.subst σ D) (Syn.subst σ neg) (Syn.subst σ R) := by simp [data]

theorem sample_at (p A B D neg R : PTm n) :
    Γ ⊢[PRAAx] ap2 nameF p (data A B D neg R) ≐ finiteRead (succ p) A B D neg (cutoff R p) := by
  let z := argument A B D neg
  let x := data A B D neg R
  have read : Γ ⊢[PRAAx] ap2 nameF p x ≐ readAt p (fstT x) (sndT x) := by
    simpa only [nameF, body, ap2, subst_readAt, subst_fstT, subst_sndT, Syn.subst_var,
      Matrix.cons_val_zero, Matrix.cons_val_one] using toPR_eq (Γ := Γ) body ![p, x]
  have align : Γ ⊢[PRAAx] readAt p (fstT x) (sndT x) ≐ readAt p z R := by
    simpa only [subst_readAt, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (readAt (var 0) (var 1) (var 2) : PTm 3)
        (σ := ![p, fstT x, sndT x]) (σ' := ![p, z, R]) (fun i => by
          fin_cases i
          · exact .eqRefl p
          · exact fst_pair z R
          · exact snd_pair z R)
  exact read.eqTrans align

private theorem cutoff_positive (R p : PTm n) : Γ ⊢[PRAAx] le one (cutoff R p) :=
  positive_product _ _ (le_add_left one R) (unit_positive _)

private theorem index_five {α : Type} (a b c d e f : α) : ![a, b, c, d, e, f] (5 : Fin 6) = f := rfl

private theorem index_congr (p A B D neg N M : PTm n) (h : Γ ⊢[PRAAx] N ≐ M) :
    Γ ⊢[PRAAx] finiteRead p A B D neg N ≐ finiteRead p A B D neg M := by
  simpa only [subst_observed, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, index_five, Matrix.head_cons, Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (finiteRead (var 1) (var 2) (var 3) (var 4) (var 5) (var 0) : PTm 6)
      (σ := ![N, p, A, B, D, neg]) (σ' := ![M, p, A, B, D, neg]) (fun i => by
        fin_cases i
        · exact h
        all_goals exact .eqRefl _)

private theorem ordered (p q A B D neg R N M : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R)
    (hN : Γ ⊢[PRAAx] le one N) (hNM : Γ ⊢[PRAAx] le N M) :
    Γ ⊢[PRAAx] distanceBounded (finiteRead p A B D neg M) (finiteRead q A B D neg N)
      (gapNumerator p q R N) (gapDenominator p q N) :=
  distance_congr (index_congr p A B D neg _ _ (eq_add_of_le hNM).eqSymm) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (ordered_gap p q A B D neg R N (monus M N) h hN)

private theorem denominator_positive (p q N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le one (gapDenominator p q N) :=
  positive_product _ _ hN (positive_product _ _ (unit_positive p) (unit_positive q))

private theorem unit_successor (p : PTm n) : Γ ⊢[PRAAx] unit (succ p) ≐ two * unit p := by
  exact (pw_succ two p).eqTrans (mul_comm _ _)

/-- The cofinal read and any later raw cutoff differ by their two sampling errors. -/
theorem late_read_distance (p q A B D neg R N : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R)
    (hle : Γ ⊢[PRAAx] le (cutoff R p) N) :
    Γ ⊢[PRAAx] distanceBounded (finiteRead (succ p) A B D neg (cutoff R p)) (finiteRead q A B D neg N)
      (unit p + unit q) (unit p * unit q) := by
  let C := cutoff R p
  have hC := cutoff_positive (Γ := Γ) R p
  have hz := denominator_positive q (succ p) C hC
  have raw := distance_symmetric _ _ _ _ hz (ordered q (succ p) A B D neg R C N h hC hle)
  apply distance_radius_mono _ _ _ _ _ _ hz (positive_product _ _ (unit_positive p) (unit_positive q)) ?_ raw
  refine le_of_eq_add (d := zero) ?_
  have ep := natEq (unit_successor (Γ := Γ) p)
  apply deriveNat
  dsimp only [C, cutoff, gapNumerator, gapDenominator]
  ipra_simps
  rw [ep]
  ring

private theorem lower_second_error (x y p q : PTm n)
    (h : Γ ⊢[PRAAx] distanceBounded x y (unit p + unit (succ q)) (unit p * unit (succ q))) :
    Γ ⊢[PRAAx] distanceBounded x y (unit p + unit q) (unit p * unit q) := by
  have hp := unit_positive (Γ := Γ) p
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp (unit_positive (succ q)))
    (positive_product _ _ hp (unit_positive q)) ?_ h
  refine le_of_eq_add (d := unit p * unit p * unit q) ?_
  have eq := natEq (unit_successor (Γ := Γ) q)
  apply deriveNat
  ipra_simps
  rw [eq]
  ring

theorem observed_distance (p q A B D neg R : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R) :
    Γ ⊢[PRAAx] distanceBounded (finiteRead (succ p) A B D neg (cutoff R p))
      (finiteRead (succ q) A B D neg (cutoff R q)) (unit p + unit q) (unit p * unit q) := by
  refine (le_total (cutoff R p) (cutoff R q)).orE ?_ ?_
  · exact lower_second_error _ _ p q (late_read_distance p (succ q) A B D neg R _ h.wk Prf.hyp0)
  · have rev := lower_second_error _ _ q p
      (late_read_distance q (succ p) A B D neg R (cutoff R p) h.wk Prf.hyp0)
    exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive q) (unit_positive p)) rev)

theorem regular (A B D neg R : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R) :
    Γ ⊢[PRAAx] pointCN nameF (data A B D neg R) := by
  refine .allI (.allI ?_)
  let s (a : PTm n) := Syn.shift (Syn.shift a)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] source (s A) (s B) (s D) (s neg) (s R) := by
    simpa only [Δ, s, Fm.shift, Syn.shift, subst_source] using h.shift.shift
  have atClock (p : PTm (n + 1 + 1)) := sample_at (Γ := Δ) p (s A) (s B) (s D) (s neg) (s R)
  simpa only [Syn.shift, s, subst_data, GaussianEuclideanPointDistance.unit, unit] using
    distance_congr (atClock (var 1)).eqSymm (atClock (var 0)).eqSymm (.eqRefl _) (.eqRefl _)
      (observed_distance (var 1) (var 0) (s A) (s B) (s D) (s neg) (s R) hs)

private theorem arbitrary_read_distance (p q A B D neg R N : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (finiteRead (succ p) A B D neg (cutoff R p)) (finiteRead q A B D neg N)
      (gapNumerator p q R N) (gapDenominator p q N) := by
  refine (le_total (cutoff R p) N).orE ?_ ?_
  · have late := late_read_distance p q A B D neg R N h.wk Prf.hyp0
    exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive q))
      (denominator_positive p q N hN.wk)
      (le_of_eq_add (d := (R + one) * (unit p * unit q) * (unit p * unit q))
        (by unfold gapNumerator gapDenominator; ipra_ring)) late
  · have raw := ordered (succ p) q A B D neg R N (cutoff R p) h.wk hN.wk Prf.hyp0
    apply distance_radius_mono _ _ _ _ _ _ (denominator_positive (succ p) q N hN.wk)
      (denominator_positive p q N hN.wk) ?_ raw
    refine le_of_eq_add (d := N * N * unit p * unit q * unit q) ?_
    have eq := natEq (unit_successor (Γ := (le N (cutoff R p)) :: Γ) p)
    apply deriveNat
    unfold gapNumerator gapDenominator
    ipra_simps
    rw [eq]
    ring

private theorem slope_readback (p A B D neg N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 slopeF p (slopeData A B D neg N)) (finiteRead p A B D neg N)
      (num 6) (unit p) := by
  let z := reciprocalSum A B D neg (succ N)
  let x := GaussianPositiveRationalLogarithm.data N one
  exact distance_congr (.eqRefl _) (qsub_congr (.eqRefl _) (constant_at p z)) (.eqRefl _) (.eqRefl _)
    (GaussianNamedDifference.sample_error logF constantF x z p (name_regular N one (.andI hN (le_refl one)))
      (constant_regular z))

private theorem diagonal_bound (p A B D neg R N : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A B D neg R)) (ap2 slopeF p (slopeData A B D neg N))
      (diagonalNumerator (R + one) N (num 8) p) (diagonalDenominator N p) := by
  let x := ap2 nameF p (data A B D neg R)
  let y := finiteRead p A B D neg N
  let z := ap2 slopeF p (slopeData A B D neg N)
  let Q := N * unit p
  let M := (R + one) * unit p + two * N
  have hp := unit_positive (Γ := Γ) p
  have hQ := positive_product _ _ hN hp
  have a : Γ ⊢[PRAAx] distanceBounded x y M Q :=
    distance_radius_mono x y _ _ M Q (denominator_positive p p N hN) hQ
      (le_of_eq_add (d := zero) (by dsimp only [M, Q, gapNumerator, gapDenominator]; ipra_ring))
      (distance_congr (sample_at p A B D neg R).eqSymm (.eqRefl y) (.eqRefl _) (.eqRefl _)
        (arbitrary_read_distance p p A B D neg R N h hN))
  have b : Γ ⊢[PRAAx] distanceBounded y z (num 6 * N) Q :=
    distance_radius_mono y z _ _ _ _ hp hQ (le_of_eq_add (d := zero) (by dsimp only [Q]; ipra_ring))
      (distance_symmetric _ _ _ _ hp (slope_readback p A B D neg N hN))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [M, diagonalNumerator]; ipra_ring) (.eqRefl _)
    (distance_triangle_same x y z M (num 6 * N) Q hQ a b)

theorem original_cutoff_rate (A B D neg R N : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] independentRate nameF slopeF (data A B D neg R) (slopeData A B D neg N) (R + one) N := by
  apply independent_rate nameF slopeF (data A B D neg R) (slopeData A B D neg N) (R + one) N (num 8)
    hN (regular A B D neg R h)
    (GaussianLogGammaEulerReciprocalSlope.regular A B D neg N hN)
  refine .allI ?_
  let s (a : PTm n) := Syn.shift a
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (s A) (s B) (s D) (s neg) (s R) := by
    simpa only [s, Fm.shift, Syn.shift, subst_source] using h.shift
  have hNs : Γ.map Fm.shift ⊢[PRAAx] le one (s N) := by simpa [Fm.shift, s, Syn.shift] using hN.shift
  simpa only [diagonalEnvelope, subst_data, Syn.shift, s, PTm.subst_add, one,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, PTm.subst_num,
    GaussianNamedDifference.subst_data, GaussianPositiveRationalLogarithm.subst_data,
    GaussianLogGammaEulerReciprocalSlope.data, reciprocalSum, GaussianRationalFiniteSum.subst_sum,
    subst_argument] using diagonal_bound (var 0) (s A) (s B) (s D) (s neg) (s R) (s N) hs hNs

theorem canonical_regular (A B D neg : PTm n) (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D neg) :
    Γ ⊢[PRAAx] pointCN nameF (canonicalData A B D neg) :=
  regular A B D neg (radius A B) (source_of_right_half_plane A B D neg h)

theorem canonical_cutoff_rate (A B D neg N : PTm n) (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D neg)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] independentRate nameF slopeF (canonicalData A B D neg) (slopeData A B D neg N)
      (radius A B + one) N :=
  original_cutoff_rate A B D neg (radius A B) N (source_of_right_half_plane A B D neg h) hN

theorem actual_canonical_complex_Euler_slope_cutoff_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (GaussianRightHalfPlaneLogarithm.source (var 0) (var 2) (var 3) ⟶ le one (var 4) ⟶
        independentRate nameF slopeF (canonicalData (var 0) (var 1) (var 2) (var 3))
          (slopeData (var 0) (var 1) (var 2) (var 3) (var 4)) (radius (var 0) (var 1) + one) (var 4)) :=
  closeUniv 5 (.impI (.impI (canonical_cutoff_rate _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerReciprocalSlopeCofinal
