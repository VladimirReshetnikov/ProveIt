import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianLogGammaEulerHeadGap
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianLogGammaEulerResidualRadius

/-!
# Cofinal Euler logarithm observations

One additional bit of precision pays for the finite head observation
and its tail at the selected cutoff. The resulting primitive recursive
sampler is a regular Gaussian name. The comparison with arbitrary
admissible finite heads works on either side of the selected cutoff.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerCofinal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianLogGammaEulerHead (rowData)
open GaussianLogGammaEulerResidualDomain (source subst_source)
open GaussianLogGammaEulerResidualRadius (radius source_of_right_half_plane)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm)
open GaussianNameRingLaws (equivalent_of_envelope)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalSlackRemoval (precision slack_removal_at)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianLogGammaEulerNormalizedHead.nameF
local notation "headData" => GaussianLogGammaEulerNormalizedHead.data
local notation "G" => GaussianLogGammaEulerHead.nameF
local notation "originalData" => GaussianLogGammaEulerHead.data

def cost (R : PTm n) : PTm n := R*R+R

def cutoff (R p : PTm n) : PTm n := (num 8*R+one)+cost R*unit (succ p)

def observed (p A B D neg R : PTm n) : PTm n :=
  ap2 F (succ p) (headData A B D neg (cutoff R p))

def data (A B D neg R : PTm n) : PTm n := pairT R (rowData A B D neg)

def canonicalData (A B D neg : PTm n) : PTm n := data A B D neg (radius A B)

private def body : PTm 2 :=
  observed (var 0) (fstT (sndT (var 1))) (fstT (sndT (sndT (var 1))))
    (fstT (sndT (sndT (sndT (var 1))))) (sndT (sndT (sndT (sndT (var 1))))) (fstT (var 1))

def nameF : PR 2 := PTm.toPR body

@[simp] theorem subst_cutoff {m : ℕ} (σ : Fin n → PTm m) (R p : PTm n) :
    Syn.subst σ (cutoff R p) = cutoff (Syn.subst σ R) (Syn.subst σ p) := by simp [cutoff,cost,one]

@[simp] theorem subst_observed {m : ℕ} (σ : Fin n → PTm m) (p A B D neg R : PTm n) :
    Syn.subst σ (observed p A B D neg R) = observed (Syn.subst σ p) (Syn.subst σ A)
      (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ neg) (Syn.subst σ R) := by simp [observed]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (A B D neg R : PTm n) :
    Syn.subst σ (data A B D neg R) =
      data (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ neg) (Syn.subst σ R) := by
  simp [data]

@[simp] theorem subst_canonicalData {m : ℕ} (σ : Fin n → PTm m) (A B D neg : PTm n) :
    Syn.subst σ (canonicalData A B D neg) =
      canonicalData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ neg) := by
  simp [canonicalData]

private theorem index_five {α : Type} (a b c d e f : α) : ![a,b,c,d,e,f] (5 : Fin 6) = f := rfl

theorem sample_at (p A B D neg R : PTm n) :
    Γ ⊢[PRAAx] ap2 nameF p (data A B D neg R) ≐ observed p A B D neg R := by
  let x := data A B D neg R
  let a := fstT (sndT x)
  let b := fstT (sndT (sndT x))
  let d := fstT (sndT (sndT (sndT x)))
  let s := sndT (sndT (sndT (sndT x)))
  have read : Γ ⊢[PRAAx] ap2 nameF p x ≐ observed p a b d s (fstT x) := by
    simpa [nameF,body,ap2,a,b,d,s] using toPR_eq (Γ := Γ) body ![p,x]
  have rows : Γ ⊢[PRAAx] sndT x ≐ rowData A B D neg := snd_pair _ _
  have firstTail := (congrSnd rows).eqTrans (snd_pair A _)
  have lastTail := (congrSnd firstTail).eqTrans (snd_pair B _)
  have eA : Γ ⊢[PRAAx] a ≐ A := (congrFst rows).eqTrans (fst_pair A _)
  have eB : Γ ⊢[PRAAx] b ≐ B := (congrFst firstTail).eqTrans (fst_pair B _)
  have eD : Γ ⊢[PRAAx] d ≐ D := (congrFst lastTail).eqTrans (fst_pair D neg)
  have eS : Γ ⊢[PRAAx] s ≐ neg := (congrSnd lastTail).eqTrans (snd_pair D neg)
  have eR : Γ ⊢[PRAAx] fstT x ≐ R := fst_pair _ _
  refine read.eqTrans ?_
  simpa only [subst_observed,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,index_five,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
      (observed (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
      (σ := ![p,a,b,d,s,fstT x]) (σ' := ![p,A,B,D,neg,R])
      (fun i => by fin_cases i; exact .eqRefl _; exact eA; exact eB; exact eD; exact eS; exact eR)

theorem cutoff_positive (R p : PTm n) : Γ ⊢[PRAAx] le one (cutoff R p) :=
  le_trans (le_add_left one _) (le_add_right _ _)

theorem cutoff_large (R p : PTm n) : Γ ⊢[PRAAx] le (num 8*R) (cutoff R p) :=
  le_trans (le_add_right _ one) (le_add_right _ _)

theorem cutoff_budget (R p : PTm n) : Γ ⊢[PRAAx] le (cost R*unit (succ p)) (cutoff R p) :=
  le_add_left _ _

private def radiusNumerator (C N p q : PTm n) : PTm n := C*unit p*unit q+N*(unit p+unit q)
private def radiusDenominator (N p q : PTm n) : PTm n := N*unit p*unit q

private theorem radius_positive (N p q : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le one (radiusDenominator N p q) :=
  positive_product _ _ (positive_product _ _ hN (unit_positive p)) (unit_positive q)

private theorem swap_radius (x y C N p q : PTm n)
    (h : Γ ⊢[PRAAx] distanceBounded x y (radiusNumerator C N p q) (radiusDenominator N p q)) :
    Γ ⊢[PRAAx] distanceBounded x y (radiusNumerator C N q p) (radiusDenominator N q p) :=
  distance_congr (.eqRefl _) (.eqRefl _) (by unfold radiusNumerator; ipra_ring)
    (by unfold radiusDenominator; ipra_ring) h

private theorem head_congr (q A B D neg : PTm n) {N M : PTm n}
    (e : Γ ⊢[PRAAx] N ≐ M) :
    Γ ⊢[PRAAx] ap2 F q (headData A B D neg N) ≐ ap2 F q (headData A B D neg M) := by
  simpa only [subst_ap2,GaussianLogGammaEulerNormalizedHead.subst_data,Syn.subst_var,
      Syn.inst_zero,Syn.subst_inst_shift] using
    Prf.eqCongr1 (Ax := PRAAx)
      (ap2 F (Syn.shift q) (headData (Syn.shift A) (Syn.shift B) (Syn.shift D) (Syn.shift neg) (var 0))) e

private theorem ordered_distance (p q A B D neg R N M : PTm n)
    (h : Γ ⊢[PRAAx] source A B D neg R) (hN : Γ ⊢[PRAAx] le one N)
    (hlarge : Γ ⊢[PRAAx] le (two*R) N) (hle : Γ ⊢[PRAAx] le N M) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F p (headData A B D neg M)) (ap2 F q (headData A B D neg N))
      (radiusNumerator (cost R) N p q) (radiusDenominator N p q) := by
  have e : Γ ⊢[PRAAx] N+monus M N ≐ M := (eq_add_of_le hle).eqSymm
  have gap := GaussianLogGammaEulerHeadGap.sharp_normalized_ordered_gap p q A B D neg R N (monus M N) h hN hlarge
  exact distance_congr (head_congr p A B D neg e) (.eqRefl _) (.eqRefl _) (.eqRefl _) gap

private theorem lower_precision (x y C N p q : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] distanceBounded x y (radiusNumerator C N (succ p) q) (radiusDenominator N (succ p) q)) :
    Γ ⊢[PRAAx] distanceBounded x y (radiusNumerator C N p q) (radiusDenominator N p q) := by
  apply distance_radius_mono _ _ _ _ _ _ (radius_positive N (succ p) q hN) (radius_positive N p q hN) ?_ h
  have e := natEq (pw_succ (Γ := Γ) two p)
  refine le_of_eq_add (d := N*N*unit p*unit q*unit q) ?_
  apply deriveNat
  dsimp only [radiusNumerator,radiusDenominator,unit]
  ipra_simps
  rw [e]
  ring

private theorem absorb_tail (x y C N p q : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hbudget : Γ ⊢[PRAAx] le (C*unit (succ p)) N)
    (h : Γ ⊢[PRAAx] distanceBounded x y (radiusNumerator C N (succ p) q) (radiusDenominator N (succ p) q)) :
    Γ ⊢[PRAAx] distanceBounded x y (unit p+unit q) (unit p*unit q) := by
  have paid : Γ ⊢[PRAAx] le (radiusNumerator C N (succ p) q) (N*(unit (succ p)+two*unit q)) :=
    le_congr (.eqRefl _) (by ipra_ring)
      (add_le_add_right (N*(unit (succ p)+unit q)) (mul_le_mul_right (unit q) hbudget))
  apply distance_radius_mono _ _ _ _ _ _ (radius_positive N (succ p) q hN)
    (positive_product _ _ (unit_positive p) (unit_positive q)) ?_ h
  apply le_trans (mul_le_mul_right (unit p*unit q) paid)
  apply le_congr (.eqRefl _) ?_ (le_refl _)
  have e := natEq (pw_succ (Γ := Γ) two p)
  apply deriveNat
  dsimp only [radiusDenominator,unit]
  ipra_simps
  rw [e]
  ring

private theorem halve_second_error (x y p q : PTm n)
    (h : Γ ⊢[PRAAx] distanceBounded x y (unit p+unit (succ q)) (unit p*unit (succ q))) :
    Γ ⊢[PRAAx] distanceBounded x y (unit p+unit q) (unit p*unit q) := by
  have hp := unit_positive (Γ := Γ) p
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp (unit_positive (succ q)))
    (positive_product _ _ hp (unit_positive q)) ?_ h
  have e := natEq (pw_succ (Γ := Γ) two q)
  refine le_of_eq_add (d := unit p*unit p*unit q) ?_
  apply deriveNat
  dsimp only [unit]
  ipra_simps
  rw [e]
  ring

theorem late_cutoff_distance (p q A B D neg R N : PTm n)
    (h : Γ ⊢[PRAAx] source A B D neg R) (hle : Γ ⊢[PRAAx] le (cutoff R p) N) :
    Γ ⊢[PRAAx] distanceBounded (observed p A B D neg R) (ap2 F q (headData A B D neg N))
      (unit p+unit q) (unit p*unit q) := by
  let M := cutoff R p
  have hM := cutoff_positive (Γ := Γ) R p
  have sharp : Γ ⊢[PRAAx] le (two*R) M :=
    le_trans (AnalyticNumberTheory.PhiLower.le_mul_mono (by ipra_le 6) (le_refl R)) (cutoff_large R p)
  have raw := ordered_distance q (succ p) A B D neg R M N h hM sharp hle
  have forward := distance_symmetric _ _ _ _ (radius_positive M (succ p) q hM)
    (swap_radius _ _ _ _ _ _ raw)
  exact absorb_tail _ _ (cost R) M p q hM (cutoff_budget R p) forward

theorem observed_distance (p q A B D neg R : PTm n)
    (h : Γ ⊢[PRAAx] source A B D neg R) :
    Γ ⊢[PRAAx] distanceBounded (observed p A B D neg R) (observed q A B D neg R)
      (unit p+unit q) (unit p*unit q) := by
  refine (le_total (cutoff R p) (cutoff R q)).orE ?_ ?_
  · exact halve_second_error _ _ p q (late_cutoff_distance p (succ q) A B D neg R _ h.wk Prf.hyp0)
  · have rev := halve_second_error _ _ q p
      (late_cutoff_distance q (succ p) A B D neg R (cutoff R p) h.wk Prf.hyp0)
    have fwd := distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive q) (unit_positive p)) rev
    exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring) fwd

theorem regular (A B D neg R : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R) :
    Γ ⊢[PRAAx] pointCN nameF (data A B D neg R) := by
  refine .allI (.allI ?_)
  let sh (a : PTm n) := Syn.shift (Syn.shift a)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] source (sh A) (sh B) (sh D) (sh neg) (sh R) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,subst_source] using h.shift.shift
  have e (p : PTm (n+1+1)) := sample_at (Γ := Δ) p (sh A) (sh B) (sh D) (sh neg) (sh R)
  simpa only [Syn.shift,sh,subst_data,GaussianEuclideanPointDistance.unit,unit] using
    distance_congr (e (var 1)).eqSymm (e (var 0)).eqSymm (.eqRefl _) (.eqRefl _)
      (observed_distance (var 1) (var 0) (sh A) (sh B) (sh D) (sh neg) (sh R) hs)

theorem sharp_cutoff_distance (p q A B D neg R N : PTm n)
    (h : Γ ⊢[PRAAx] source A B D neg R) (hN : Γ ⊢[PRAAx] le one N)
    (hlarge : Γ ⊢[PRAAx] le (two*R) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A B D neg R)) (ap2 F q (headData A B D neg N))
      (cost R*unit p*unit q+N*(unit p+unit q)) (N*unit p*unit q) := by
  apply distance_congr (sample_at p A B D neg R).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
  refine (le_total N (cutoff R p)).orE ?_ ?_
  · exact lower_precision _ _ (cost R) N p q hN.wk
      (ordered_distance (succ p) q A B D neg R N _ h.wk hN.wk hlarge.wk Prf.hyp0)
  · have late := late_cutoff_distance p q A B D neg R N h.wk Prf.hyp0
    apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive q))
      (radius_positive N p q hN.wk) ?_ late
    exact le_of_eq_add (d := cost R*unit p*unit q*(unit p*unit q)) (by unfold radiusDenominator; ipra_ring)

private theorem radius_diagonal (p A B D neg R S : PTm n)
    (hR : Γ ⊢[PRAAx] source A B D neg R) (hS : Γ ⊢[PRAAx] source A B D neg S) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A B D neg R)) (ap2 nameF p (data A B D neg S))
      (num 4) (unit p) := by
  let N := cutoff R p+cutoff S p
  let x := observed p A B D neg R
  let y := observed p A B D neg S
  let z := ap2 F p (headData A B D neg N)
  let u := unit p
  have hu := unit_positive (Γ := Γ) p
  have hD := positive_product (Γ := Γ) u u hu hu
  have left := late_cutoff_distance p p A B D neg R N hR (le_add_right _ _)
  have right := late_cutoff_distance p p A B D neg S N hS (le_add_left _ _)
  have gap := distance_triangle_same x z y (u+u) (u+u) (u*u) hD left
    (distance_symmetric _ _ _ _ hD right)
  have reduced := distance_radius_mono x y _ _ (num 4) u hD hu
    (le_of_eq_add (d := zero) (by dsimp only [u]; ipra_ring)) gap
  exact distance_congr (sample_at p A B D neg R).eqSymm (sample_at p A B D neg S).eqSymm
    (.eqRefl _) (.eqRefl _) reduced

theorem radius_independent (A B D neg R S : PTm n)
    (hR : Γ ⊢[PRAAx] source A B D neg R) (hS : Γ ⊢[PRAAx] source A B D neg S) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (data A B D neg R) (data A B D neg S) := by
  refine equivalent_of_envelope _ _ _ _ (num 4) (regular _ _ _ _ _ hR) (regular _ _ _ _ _ hS) (.allI ?_)
  let Δ := Γ.map Fm.shift
  let sh (a : PTm n) := Syn.shift a
  have hr : Δ ⊢[PRAAx] source (sh A) (sh B) (sh D) (sh neg) (sh R) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,subst_source] using hR.shift
  have hs : Δ ⊢[PRAAx] source (sh A) (sh B) (sh D) (sh neg) (sh S) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,subst_source] using hS.shift
  simpa only [Syn.shift,sh,subst_data,PTm.subst_num] using
    radius_diagonal (var 0) (sh A) (sh B) (sh D) (sh neg) (sh R) (sh S) hr hs

theorem sharp_original_cutoff_distance (p q A B D neg R N : PTm n)
    (h : Γ ⊢[PRAAx] source A B D neg R) (hN : Γ ⊢[PRAAx] le one N)
    (hlarge : Γ ⊢[PRAAx] le (two*R) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A B D neg R)) (ap2 G q (originalData A B D neg N))
      (cost R*unit p*unit q+N*(unit p+unit q)) (N*unit p*unit q) := by
  let x := ap2 nameF p (data A B D neg R)
  let y := ap2 G q (originalData A B D neg N)
  let a := radiusNumerator (cost R) N p q
  let b := radiusDenominator N p q
  let t := precision (qsub x y) a b two
  let z := ap2 F t (headData A B D neg N)
  have hb := radius_positive N p q hN
  have ht := unit_positive (Γ := Γ) t
  have left := sharp_cutoff_distance p t A B D neg R N h hN hlarge
  have eq := GaussianLogGammaEulerNormalizedHead.equivalent A B D neg N h.andE₁ hN
  have right := cross_at F G _ _ t q (cross_symm G F _ _ eq)
  have hLeft := radius_positive N p t hN
  have hRight := positive_product _ _ ht (unit_positive q)
  have joined := GaussianRationalPanelTailDistance.triangle x z y _ _ _ _ hLeft hRight left right
  apply slack_removal_at (qsub x y) a b two hb
  exact distance_radius_mono x y _ _ (a*unit t+two*b) (b*unit t)
    (positive_product _ _ hLeft hRight) (positive_product _ _ hb ht)
    (le_of_eq_add (d := zero) (by dsimp only [a,b,radiusNumerator,radiusDenominator]; ipra_ring)) joined

theorem canonical_regular (A B D neg : PTm n) (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D neg) :
    Γ ⊢[PRAAx] pointCN nameF (canonicalData A B D neg) :=
  regular A B D neg (radius A B) (source_of_right_half_plane A B D neg h)

theorem canonical_sharp_original_cutoff_distance (p q A B D neg N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D neg) (hN : Γ ⊢[PRAAx] le one N)
    (hlarge : Γ ⊢[PRAAx] le (two*radius A B) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (canonicalData A B D neg)) (ap2 G q (originalData A B D neg N))
      (cost (radius A B)*unit p*unit q+N*(unit p+unit q)) (N*unit p*unit q) :=
  sharp_original_cutoff_distance p q A B D neg (radius A B) N (source_of_right_half_plane A B D neg h) hN hlarge

theorem cutoff_distance (p q A B D neg R N : PTm n)
    (h : Γ ⊢[PRAAx] source A B D neg R) (hN : Γ ⊢[PRAAx] le one N)
    (hlarge : Γ ⊢[PRAAx] le (num 8*R) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A B D neg R)) (ap2 F q (headData A B D neg N))
      (cost R*unit p*unit q+N*(unit p+unit q)) (N*unit p*unit q) :=
  sharp_cutoff_distance p q A B D neg R N h hN
    (le_trans (AnalyticNumberTheory.PhiLower.le_mul_mono (by ipra_le 6) (le_refl R)) hlarge)

theorem original_cutoff_distance (p q A B D neg R N : PTm n)
    (h : Γ ⊢[PRAAx] source A B D neg R) (hN : Γ ⊢[PRAAx] le one N)
    (hlarge : Γ ⊢[PRAAx] le (num 8*R) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A B D neg R)) (ap2 G q (originalData A B D neg N))
      (cost R*unit p*unit q+N*(unit p+unit q)) (N*unit p*unit q) :=
  sharp_original_cutoff_distance p q A B D neg R N h hN
    (le_trans (AnalyticNumberTheory.PhiLower.le_mul_mono (by ipra_le 6) (le_refl R)) hlarge)

theorem canonical_original_cutoff_distance (p q A B D neg N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D neg) (hN : Γ ⊢[PRAAx] le one N)
    (hlarge : Γ ⊢[PRAAx] le (num 8*radius A B) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (canonicalData A B D neg)) (ap2 G q (originalData A B D neg N))
      (cost (radius A B)*unit p*unit q+N*(unit p+unit q)) (N*unit p*unit q) :=
  canonical_sharp_original_cutoff_distance p q A B D neg N h hN
    (le_trans (AnalyticNumberTheory.PhiLower.le_mul_mono (by ipra_le 6) (le_refl (radius A B))) hlarge)

theorem actual_Euler_log_Gamma_cofinal_regular_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
        pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (regular _ _ _ _ _ Prf.hyp0))

theorem actual_Euler_log_Gamma_cofinal_cutoff_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
        (le one (var 5) ⋏ le (num 8*var 4) (var 5)) ⟶
        distanceBounded (ap2 nameF (var 6) (data (var 0) (var 1) (var 2) (var 3) (var 4)))
          (ap2 F (var 7) (headData (var 0) (var 1) (var 2) (var 3) (var 5)))
          (cost (var 4)*unit (var 6)*unit (var 7)+var 5*(unit (var 6)+unit (var 7)))
          (var 5*unit (var 6)*unit (var 7))) :=
  closeUniv 8 (.impI (.impI (cutoff_distance _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

theorem actual_Euler_log_Gamma_cofinal_radius_independence_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((source (var 0) (var 1) (var 2) (var 3) (var 4) ⋏ source (var 0) (var 1) (var 2) (var 3) (var 5)) ⟶
        crossEquivalent nameF nameF (data (var 0) (var 1) (var 2) (var 3) (var 4))
          (data (var 0) (var 1) (var 2) (var 3) (var 5))) :=
  closeUniv 6 (.impI (radius_independent _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_canonical_Euler_log_Gamma_regular_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (GaussianRightHalfPlaneLogarithm.source (var 0) (var 2) (var 3) ⟶
        pointCN nameF (canonicalData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (canonical_regular _ _ _ _ Prf.hyp0))

theorem actual_canonical_Euler_log_Gamma_original_cutoff_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (GaussianRightHalfPlaneLogarithm.source (var 0) (var 2) (var 3) ⟶
        (le one (var 4) ⋏ le (num 8*radius (var 0) (var 1)) (var 4)) ⟶
        distanceBounded (ap2 nameF (var 5) (canonicalData (var 0) (var 1) (var 2) (var 3)))
          (ap2 G (var 6) (originalData (var 0) (var 1) (var 2) (var 3) (var 4)))
          (cost (radius (var 0) (var 1))*unit (var 5)*unit (var 6)+var 4*(unit (var 5)+unit (var 6)))
          (var 4*unit (var 5)*unit (var 6))) :=
  closeUniv 7 (.impI (.impI (canonical_original_cutoff_distance _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

theorem actual_canonical_Euler_log_Gamma_sharp_original_cutoff_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (GaussianRightHalfPlaneLogarithm.source (var 0) (var 2) (var 3) ⟶
        (le one (var 4) ⋏ le (two*radius (var 0) (var 1)) (var 4)) ⟶
        distanceBounded (ap2 nameF (var 5) (canonicalData (var 0) (var 1) (var 2) (var 3)))
          (ap2 G (var 6) (originalData (var 0) (var 1) (var 2) (var 3) (var 4)))
          (cost (radius (var 0) (var 1))*unit (var 5)*unit (var 6)+var 4*(unit (var 5)+unit (var 6)))
          (var 4*unit (var 5)*unit (var 6))) :=
  closeUniv 7 (.impI (.impI (canonical_sharp_original_cutoff_distance _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerCofinal
