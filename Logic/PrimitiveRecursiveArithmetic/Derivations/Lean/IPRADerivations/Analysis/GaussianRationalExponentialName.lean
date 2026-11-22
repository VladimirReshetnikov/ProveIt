import IPRADerivations.Analysis.GaussianRationalExponentialTail
import IPRADerivations.Analysis.GaussianEuclideanDistanceName
import IPRADerivations.Analysis.GaussianRationalDistanceOrder

/-!
# An actual finite-series exponential name at an original rational input

The PR2 sample at p is the SAME original scalarSum at the computed
last included index Nt(B,p)-1. The original rational query and numerical
disk radius are packed as persistent data. The actual finite tail proves
ordered-precision comparison; a genuine order split derives pointCN.
Only the original Euclidean query disk is assumed. Exponentiation of
arbitrary regular input names and its properness remain separate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalExponentialName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (canonical)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPolynomialExponential (scalarSum scalarBody)
open GaussianRationalExponentialTail (cutoff lastIndex precisionDenominator)
open GaussianCoefficientNameBounds (unit unit_positive subst_unit)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (q B : PTm n) : PTm n := pairT B q
def input (x : PTm n) : Fm PTm n := bounded (sndT x) (fstT x) one
def value (p x : PTm n) : PTm n := scalarSum (sndT x) (lastIndex (fstT x) p)
def nameF : PR 2 := PTm.toPR (value (var 0) (var 1))
def sample (p x : PTm n) : PTm n := ap2 nameF p x
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (q B : PTm n) :
    Syn.subst σ (data q B) = data (Syn.subst σ q) (Syn.subst σ B) := by simp [data]
@[simp] theorem subst_input {l : ℕ} (σ : Fin n → PTm l) (x : PTm n) :
    (input x).subst σ = input (Syn.subst σ x) := by simp [input]
@[simp] theorem subst_value {l : ℕ} (σ : Fin n → PTm l) (p x : PTm n) :
    Syn.subst σ (value p x) = value (Syn.subst σ p) (Syn.subst σ x) := by simp [value]
@[simp] theorem subst_sample {l : ℕ} (σ : Fin n → PTm l) (p x : PTm n) :
    Syn.subst σ (sample p x) = sample (Syn.subst σ p) (Syn.subst σ x) := by simp [sample]

theorem sample_at (p x : PTm n) : Γ ⊢[PRAAx] sample p x ≐ value p x := by
  simpa [sample,nameF,ap2] using toPR_eq (Γ := Γ) (value (var 0) (var 1) : PTm 2) ![p,x]
theorem sample_canonical (p x : PTm n) : Γ ⊢[PRAAx] canonical (sample p x) :=
  GaussianRationalHorner.canonical_congr (sample_at p x) (GaussianRationalFiniteSum.sum_canonical _ _ _)

theorem cutoff_add (B p k : PTm n) : Γ ⊢[PRAAx] cutoff B (p+k) ≐ cutoff B p+k := by
  unfold cutoff ExponentialTail.Nt
  ipra_ring

theorem last_index_add (B p k : PTm n) : Γ ⊢[PRAAx] lastIndex B (p+k) ≐ lastIndex B p+k := by
  have e : Γ ⊢[PRAAx] succ (lastIndex B (p+k)) ≐ succ (lastIndex B p+k) :=
    (GaussianRationalExponentialTail.last_successor B (p+k)).eqTrans
      ((cutoff_add B p k).eqTrans
        ((congrAdd (GaussianRationalExponentialTail.last_successor B p).eqSymm (.eqRefl k)).eqTrans (by ipra_ring)))
  exact (pred_succ _).eqSymm.eqTrans ((congrPred e).eqTrans (pred_succ _))

theorem value_later (x p k : PTm n) : Γ ⊢[PRAAx] value (p+k) x ≐
    scalarSum (sndT x) (lastIndex (fstT x) p+k) :=
  GaussianRationalFiniteSum.sum_index_congr scalarBody (congrSucc (last_index_add (fstT x) p k)) (.eqRefl _)

/-- The SAME original finite scalarSum tail supplies the ordered
comparison; no sample-regularity or exponential-value law is assumed. -/
theorem ordered_error (x p k : PTm n) (hx : Γ ⊢[PRAAx] input x) : Γ ⊢[PRAAx]
    distanceBounded (sample (p+k) x) (sample p x) one (precisionDenominator p) :=
  distance_congr ((sample_at (p+k) x).eqTrans (value_later x p k)).eqSymm
    (sample_at p x).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalExponentialTail.scalar_cutoff_distance (sndT x) (fstT x) p k hx)

theorem ordered_unit_error (x p k : PTm n) (hx : Γ ⊢[PRAAx] input x) : Γ ⊢[PRAAx]
    distanceBounded (sample (p+k) x) (sample p x) one (unit p) :=
  distance_radius_mono _ _ _ _ _ _ (GaussianRationalExponentialTail.precision_positive p) (unit_positive p)
    (le_congr (one_mul _).eqSymm (one_mul _).eqSymm
      (GaussianFactorBudget.power_monotone_length two p (p+num 3) (le_succ_self one) (le_add_right _ _)))
    (ordered_error x p k hx)

theorem later_comparison (x s t : PTm n) (hx : Γ ⊢[PRAAx] input x) (hst : Γ ⊢[PRAAx] le s t) : Γ ⊢[PRAAx]
    distanceBounded (sample t x) (sample s x) one (unit s) :=
  distance_congr (congrAp2 nameF (eq_add_of_le hst).eqSymm (.eqRefl _)) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (ordered_unit_error x s (monus t s) hx)

/-- Independent numerical precisions use a genuine native order split.
The resulting comparison is the original Euclidean pointCN inequality. -/
theorem sample_regularity (x s t : PTm n) (hx : Γ ⊢[PRAAx] input x) : Γ ⊢[PRAAx]
    distanceBounded (sample s x) (sample t x) (unit s+unit t) (unit s*unit t) := by
  refine .orE (lt_or_le s t) ?_ ?_
  · exact distance_radius_mono _ _ _ _ _ _ (unit_positive s) (GaussianRationalHorner.positive_product _ _ (unit_positive s) (unit_positive t))
      (le_of_eq_add (d := unit s*unit s) (by ipra_ring))
      (distance_symmetric _ _ _ _ (unit_positive s) (later_comparison x s t hx.wk (le_of_lt Prf.hyp0)))
  · exact distance_radius_mono _ _ _ _ _ _ (unit_positive t) (GaussianRationalHorner.positive_product _ _ (unit_positive s) (unit_positive t))
      (le_of_eq_add (d := unit t*unit t) (by ipra_ring)) (later_comparison x t s hx.wk Prf.hyp0)

theorem name_regular (x : PTm n) (hx : Γ ⊢[PRAAx] input x) : Γ ⊢[PRAAx] pointCN nameF x := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] input (Syn.shift (Syn.shift x)) := by
    simpa [Fm.shift,Syn.shift] using hx.shift.shift
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,sample,unit,Syn.shift] using
    sample_regularity (Syn.shift (Syn.shift x)) (var 1) (var 0) hs

theorem input_data (q B : PTm n) (hq : Γ ⊢[PRAAx] bounded q B one) : Γ ⊢[PRAAx] input (data q B) :=
  GaussianRationalReciprocal.bound_congr (snd_pair B q).eqSymm (fst_pair B q).eqSymm (.eqRefl _) hq

theorem original_rational_name (q B : PTm n) (hq : Γ ⊢[PRAAx] bounded q B one) : Γ ⊢[PRAAx]
    pointCN nameF (data q B) := name_regular _ (input_data q B hq)

/-- Actual packed source data decode back to the ORIGINAL rational input
and the computed original finite scalarSum, without raw code eta. -/
theorem source_sample (p q B : PTm n) : Γ ⊢[PRAAx] sample p (data q B) ≐ scalarSum q (lastIndex B p) := by
  have idx : Γ ⊢[PRAAx] lastIndex (fstT (data q B)) p ≐ lastIndex B p := by
    simpa only [GaussianRationalExponentialTail.subst_lastIndex,Syn.subst_var,Matrix.cons_val_zero,
      Matrix.cons_val_one] using Prf.eqCongr (lastIndex (var 0) (var 1) : PTm 2)
        (σ := ![fstT (data q B),p]) (σ' := ![B,p])
        (fun i => by fin_cases i; exact fst_pair B q; exact .eqRefl _)
  exact (sample_at p (data q B)).eqTrans
    (GaussianRationalFiniteSum.sum_index_congr scalarBody (congrSucc idx) (snd_pair B q))

theorem original_ordered_error (q B p k : PTm n) (hq : Γ ⊢[PRAAx] bounded q B one) : Γ ⊢[PRAAx]
    distanceBounded (sample (p+k) (data q B)) (sample p (data q B)) one (precisionDenominator p) :=
  ordered_error _ p k (input_data q B hq)

def output (p q B : PTm n) : PTm n := pairT (sample p (data q B))
  (pairT (scalarSum q (lastIndex B p)) (pairT (lastIndex B p) q))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (p q B : PTm n) : PTm n := ap3 outputF p q B
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (p q B : PTm n) :
    Syn.subst σ (output p q B) = output (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ B) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (p q B : PTm n) :
    Syn.subst σ (run p q B) = run (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ B) := by simp [run]

theorem program_at (p q B : PTm n) : Γ ⊢[PRAAx] run p q B ≐ output p q B := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![p,q,B]
theorem returned_sample (p q B : PTm n) : Γ ⊢[PRAAx] fstT (run p q B) ≐ sample p (data q B) :=
  (congrFst (program_at _ _ _)).eqTrans (fst_pair _ _)
theorem returned_tail (p q B : PTm n) : Γ ⊢[PRAAx] sndT (run p q B) ≐ pairT (scalarSum q (lastIndex B p)) (pairT (lastIndex B p) q) :=
  (congrSnd (program_at _ _ _)).eqTrans (snd_pair _ _)
theorem returned_original (p q B : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run p q B)) ≐ scalarSum q (lastIndex B p) :=
  (congrFst (returned_tail _ _ _)).eqTrans (fst_pair _ _)
theorem returned_pair (p q B : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run p q B)) ≐ pairT (lastIndex B p) q :=
  (congrSnd (returned_tail _ _ _)).eqTrans (snd_pair _ _)
theorem returned_index (p q B : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run p q B))) ≐ lastIndex B p :=
  (congrFst (returned_pair _ _ _)).eqTrans (fst_pair _ _)
theorem returned_query (p q B : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run p q B))) ≐ q :=
  (congrSnd (returned_pair _ _ _)).eqTrans (snd_pair _ _)
theorem returned_equal (p q B : PTm n) : Γ ⊢[PRAAx] fstT (run p q B) ≐ fstT (sndT (run p q B)) :=
  (returned_sample _ _ _).eqTrans ((source_sample p q B).eqTrans (returned_original _ _ _).eqSymm)

theorem actual_rational_exponential_sample_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (sample (var 0) (var 1) ≐ value (var 0) (var 1)) := closeUniv 2 (sample_at _ _)
theorem actual_rational_exponential_sample_canonical_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (canonical (sample (var 0) (var 1))) := closeUniv 2 (sample_canonical _ _)
theorem actual_rational_exponential_cutoff_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lastIndex (var 0) (var 1+var 2) ≐ lastIndex (var 0) (var 1)+var 2) := closeUniv 3 (last_index_add _ _ _)
theorem original_rational_exponential_ordered_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input (var 0) ⟶ distanceBounded (sample (var 1+var 2) (var 0)) (sample (var 1) (var 0))
      one (precisionDenominator (var 1))) := closeUniv 3 (.impI (ordered_error _ _ _ Prf.hyp0))
theorem original_rational_exponential_regular_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (input (var 0) ⟶ pointCN nameF (var 0)) := closeUniv 1 (.impI (name_regular _ Prf.hyp0))
theorem original_rational_disk_exponential_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (bounded (var 0) (var 1) one ⟶ pointCN nameF (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (original_rational_name _ _ Prf.hyp0))
theorem original_rational_exponential_value_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (sample (var 0) (data (var 1) (var 2)) ≐ scalarSum (var 1) (lastIndex (var 2) (var 0))) :=
  closeUniv 3 (source_sample _ _ _)
theorem actual_rational_exponential_source_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_rational_exponential_returned_value_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (fstT (run (var 0) (var 1) (var 2)) ≐ fstT (sndT (run (var 0) (var 1) (var 2)))) := closeUniv 3 (returned_equal _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalExponentialName
