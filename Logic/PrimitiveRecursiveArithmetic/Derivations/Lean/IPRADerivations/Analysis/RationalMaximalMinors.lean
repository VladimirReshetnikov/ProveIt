import IPRADerivations.Analysis.RationalSelectedMinors
import IPRADerivations.Probability.UnionUtility
import IPRADerivations.AnalyticNumberTheory.Multiplicative
import IPRADerivations.DiophantineNumberTheory.FLTMultiples
import IPRADerivations.Foundations.RuntimeWordAppend
import IPRADerivations.Core.CongruenceTactic

/-!
# A maximum nonzero minor selected by an actual bounded scan

Each address decodes to one pair of source row and column masks. Square
nonzero candidates receive their size plus one. The standard numerical
argmax therefore returns a valid maximum minor even for rank zero,
where the empty minor has determinant one.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalMaximalMinors

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open RationalSelectedMinors (count subst_count original normalized)
open RationalSubtupleSpan (bit bitBody bit_body_at)
open RationalScalarDeterminantGaussianEmbedding (determinant)
open RationalGaussianEmbedding (embed)
open RationalPolynomialGaussianEmbedding (embed_congr)
open GaussianRationalHorner (qzero)
open LeanProofs.IPRA.Foundations.SequenceComposition (length add_lt_left)
open LeanProofs.IPRA.Foundations.BoundedReflection (eq_of_eqb)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rowSize (P R : PTm n) : PTm n := count (length P) R
def columnSize (d C : PTm n) : PTm n := count d C
def value (P d R C : PTm n) : PTm n := embed (determinant (original P d R C) (rowSize P R))
def clearedValue (P d R C : PTm n) : PTm n := embed (determinant (normalized P d R C) (rowSize P R))
def valid (P d R C : PTm n) : Fm PTm n := rowSize P R ≐ columnSize d C ⋏ neg (value P d R C ≐ qzero)
def score (P d R C : PTm n) : PTm n :=
  RationalArithmetic.select (eqb (rowSize P R) (columnSize d C)) zero
    (RationalArithmetic.select (eqb (value P d R C) qzero) (succ (rowSize P R)) zero)

@[simp] theorem subst_rowSize {k : ℕ} (σ : Fin n → PTm k) (P R : PTm n) :
    Syn.subst σ (rowSize P R) = rowSize (Syn.subst σ P) (Syn.subst σ R) := by simp [rowSize]
@[simp] theorem subst_columnSize {k : ℕ} (σ : Fin n → PTm k) (d C : PTm n) :
    Syn.subst σ (columnSize d C) = columnSize (Syn.subst σ d) (Syn.subst σ C) := by simp [columnSize]
@[simp] theorem subst_value {k : ℕ} (σ : Fin n → PTm k) (P d R C : PTm n) :
    Syn.subst σ (value P d R C) = value (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ R) (Syn.subst σ C) := by
  simp [value]
@[simp] theorem subst_score {k : ℕ} (σ : Fin n → PTm k) (P d R C : PTm n) :
    Syn.subst σ (score P d R C) = score (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ R) (Syn.subst σ C) := by
  simp [score]

theorem score_valid (P d R C : PTm n) (h : Γ ⊢[PRAAx] valid P d R C) :
    Γ ⊢[PRAAx] score P d R C ≐ succ (rowSize P R) :=
  (RationalArithmetic.select_one _ _ _ (eqb_of_eq (.andE₁ h))).eqTrans
    (RationalArithmetic.select_zero _ _ _ (eqb_of_ne (.andE₂ h)))

theorem score_cases (P d R C : PTm n) : Γ ⊢[PRAAx]
    (score P d R C ≐ zero) ⋎ (valid P d R C ⋏ score P d R C ≐ succ (rowSize P R)) := by
  refine .orE (eq_or_ne (rowSize P R) (columnSize d C)) ?_ ?_
  · refine .orE (eq_or_ne (value P d R C) qzero) ?_ ?_
    · exact .orI₁ ((RationalArithmetic.select_one _ _ _ (eqb_of_eq Prf.hyp1)).eqTrans
        (RationalArithmetic.select_one _ _ _ (eqb_of_eq Prf.hyp0)))
    · have good : neg (value P d R C ≐ qzero) :: (rowSize P R ≐ columnSize d C) :: Γ ⊢[PRAAx] valid P d R C :=
        .andI Prf.hyp1 Prf.hyp0
      exact .orI₂ (.andI good (score_valid _ _ _ _ good))
  · exact .orI₁ (RationalArithmetic.select_zero _ _ _ (eqb_of_ne Prf.hyp0))

theorem positive_score_valid (P d R C : PTm n) (hp : Γ ⊢[PRAAx] le one (score P d R C)) :
    Γ ⊢[PRAAx] valid P d R C :=
  .orE (score_cases P d R C)
    (le_lt_absurd _ (le_congr (.eqRefl _) Prf.hyp0 hp.wk) (zero_lt_succ zero)) (.andE₁ Prf.hyp0)

theorem zero_mask_count (N : PTm n) : Γ ⊢[PRAAx] count N zero ≐ zero := by
  have all : Γ ⊢[PRAAx] .all (count (var 0) zero ≐ zero) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,subst_count,Syn.subst_var,Syn.inst_zero,ConciseIPRA.PTm.subst_zero]
      exact Foundations.FilteredEnumeration.rank_zero bitBody zero
    · simp only [Fm.subst_eq,subst_count,Syn.subst_var,Syn.repl_zero,ConciseIPRA.PTm.subst_zero]
      let Δ := (count (var 0) zero ≐ zero) :: Γ.map Fm.shift
      have b : Δ ⊢[PRAAx] bit zero (var 0) ≐ zero :=
        (congrAp2 remF (quo_zero _) (.eqRefl two)).eqTrans (rem_zero two)
      have be : Δ ⊢[PRAAx] inst2 bitBody (var 0) zero ≐ zero := by rw [bit_body_at]; exact b
      have s : Δ ⊢[PRAAx] Signum.sg (inst2 bitBody (var 0) zero) ≐ zero :=
        (congrMonus (.eqRefl one) (congrMonus (.eqRefl one) be)).eqTrans Signum.sg_zero
      exact (Foundations.FilteredEnumeration.rank_succ bitBody (var 0) zero).eqTrans
        ((congrAdd Prf.hyp0 s).eqTrans (add_zero zero))
  simpa only [Fm.subst_eq,subst_count,Syn.subst_var,Syn.inst_zero,ConciseIPRA.PTm.subst_zero] using all.allE N

theorem empty_valid (P d : PTm n) : Γ ⊢[PRAAx] valid P d zero zero := by
  have hk := zero_mask_count (Γ := Γ) (length P)
  refine .andI (hk.eqTrans (zero_mask_count d).eqSymm) (.impI ?_)
  have ev : (value P d zero zero ≐ qzero) :: Γ ⊢[PRAAx] value P d zero zero ≐ GaussianRationalSyntheticDivision.qone := by
    let A := original P d zero zero
    have h : (value P d zero zero ≐ qzero) :: Γ ⊢[PRAAx] determinant A (rowSize P zero) ≐ determinant A zero :=
      (RationalScalarDeterminantGaussianEmbedding.determinant_at A (rowSize P zero)).eqSymm.eqTrans
      ((congrAp2 RationalScalarDeterminantGaussianEmbedding.determinantF (.eqRefl A) hk.wk).eqTrans
        (RationalScalarDeterminantGaussianEmbedding.determinant_at A zero))
    exact (embed_congr h).eqTrans ((RationalGaussianEmbedding.embed_equal _ _
      (RationalScalarDeterminantGaussianEmbedding.empty_determinant A)).eqTrans RationalGaussianEmbedding.embed_one)
  exact .impE GaussianRationalCurveFibers.gaussian_one_nonzero (ev.eqSymm.eqTrans Prf.hyp0)

def maskLimit (d : PTm n) : PTm n := pw two d
def address (d R C : PTm n) : PTm n := maskLimit d*R+C
def rowMask (d z : PTm n) : PTm n := quo z (maskLimit d)
def columnMask (d z : PTm n) : PTm n := rem z (maskLimit d)
def horizon (P d : PTm n) : PTm n := maskLimit d*maskLimit (length P)
def candidateScore (P d z : PTm n) : PTm n := score P d (rowMask d z) (columnMask d z)
def scoreBody : PTm 2 := candidateScore (fstT (var 1)) (sndT (var 1)) (var 0)
def bestAddress (P d : PTm n) : PTm n := Probability.UnionUtility.Ag scoreBody (succ (pred (horizon P d))) (pairT P d)
def bestRow (P d : PTm n) : PTm n := rowMask d (bestAddress P d)
def bestColumn (P d : PTm n) : PTm n := columnMask d (bestAddress P d)
def rank (P d : PTm n) : PTm n := rowSize P (bestRow P d)

theorem limit_positive (d : PTm n) : Γ ⊢[PRAAx] maskLimit d ≐ succ (pred (maskLimit d)) := by
  simpa [maskLimit,two] using (DiophantineNumberTheory.FLTMultiples.pw_pos (Γ := Γ) one d)

theorem horizon_positive (P d : PTm n) : Γ ⊢[PRAAx] horizon P d ≐ succ (pred (horizon P d)) :=
  pos_mul' (limit_positive d) (limit_positive (length P))

theorem limit_one_le (d : PTm n) : Γ ⊢[PRAAx] le one (maskLimit d) :=
  le_congr (.eqRefl _) (limit_positive d).eqSymm ((succ_monus_succ zero _).eqTrans (zero_le _))

theorem address_bound (P d R C : PTm n) (hr : Γ ⊢[PRAAx] lt R (maskLimit (length P)))
    (hc : Γ ⊢[PRAAx] lt C (maskLimit d)) : Γ ⊢[PRAAx] lt (address d R C) (horizon P d) := by
  have first := add_lt_left (maskLimit d*R) hc
  refine lt_of_lt_of_le first (le_congr ?_ (.eqRefl _) (le_mul_mono (le_refl (maskLimit d)) hr))
  ipra_ring

theorem address_decode (d R C : PTm n) (hc : Γ ⊢[PRAAx] lt C (maskLimit d)) : Γ ⊢[PRAAx]
    rowMask d (address d R C) ≐ R ⋏ columnMask d (address d R C) ≐ C :=
  Foundations.RuntimeWordAppend.divide_unique _ _ _ _ (limit_one_le d) (.eqRefl _) hc

@[simp] theorem subst_maskLimit {k : ℕ} (σ : Fin n → PTm k) (d : PTm n) :
    Syn.subst σ (maskLimit d) = maskLimit (Syn.subst σ d) := by simp [maskLimit,two,one]
@[simp] theorem subst_rowMask {k : ℕ} (σ : Fin n → PTm k) (d z : PTm n) :
    Syn.subst σ (rowMask d z) = rowMask (Syn.subst σ d) (Syn.subst σ z) := by simp [rowMask,quo]
@[simp] theorem subst_columnMask {k : ℕ} (σ : Fin n → PTm k) (d z : PTm n) :
    Syn.subst σ (columnMask d z) = columnMask (Syn.subst σ d) (Syn.subst σ z) := by simp [columnMask,rem]
@[simp] theorem subst_candidateScore {k : ℕ} (σ : Fin n → PTm k) (P d z : PTm n) :
    Syn.subst σ (candidateScore P d z) = candidateScore (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ z) := by
  simp [candidateScore]

theorem score_congr (P d : PTm n) {R R' C C' : PTm n} (hR : Γ ⊢[PRAAx] R ≐ R') (hC : Γ ⊢[PRAAx] C ≐ C') :
    Γ ⊢[PRAAx] score P d R C ≐ score P d R' C' := by
  ipra_congr (score (var 0) (var 1) (var 2) (var 3) : PTm 4) with [.eqRefl P, .eqRefl d, hR, hC]

theorem candidate_score_at (P d z : PTm n) : Γ ⊢[PRAAx] inst2 scoreBody z (pairT P d) ≐ candidateScore P d z := by
  ipra_congr (candidateScore (var 0) (var 1) (var 2) : PTm 3) with
    [fst_pair _ _, snd_pair _ _, .eqRefl z] using [scoreBody, inst2]

theorem candidate_address_score (P d R C : PTm n) (hc : Γ ⊢[PRAAx] lt C (maskLimit d)) :
    Γ ⊢[PRAAx] candidateScore P d (address d R C) ≐ score P d R C := by
  have h := address_decode d R C hc
  exact score_congr P d (.andE₁ h) (.andE₂ h)

theorem best_address_bound (P d : PTm n) : Γ ⊢[PRAAx] lt (bestAddress P d) (horizon P d) :=
  lt_congr (.eqRefl _) (horizon_positive P d).eqSymm
    (.andE₁ (Probability.UnionUtility.ag_attains scoreBody (pred (horizon P d)) (pairT P d)))

theorem best_mask_bounds (P d : PTm n) : Γ ⊢[PRAAx]
    lt (bestRow P d) (maskLimit (length P)) ⋏ lt (bestColumn P d) (maskLimit d) :=
  .andI (AnalyticNumberTheory.Multiplicative.quo_lt (limit_positive d) (best_address_bound P d))
    (AnalyticNumberTheory.Multiplicative.rem_lt' (limit_positive d) (bestAddress P d))

theorem best_score (P d z : PTm n) (hz : Γ ⊢[PRAAx] lt z (horizon P d)) :
    Γ ⊢[PRAAx] le (candidateScore P d z) (candidateScore P d (bestAddress P d)) := by
  have h := Probability.UnionUtility.argmax scoreBody (x := pairT P d)
    (lt_congr (.eqRefl _) (horizon_positive P d) hz)
  exact le_congr (candidate_score_at _ _ _) (candidate_score_at _ _ _) (.andE₂ h)

theorem best_valid (P d : PTm n) : Γ ⊢[PRAAx] valid P d (bestRow P d) (bestColumn P d) := by
  have hb := candidate_address_score (Γ := Γ) P d zero zero (limit_one_le d)
  have hz := address_bound (Γ := Γ) P d zero zero (limit_one_le (length P)) (limit_one_le d)
  have hs := best_score P d (address d zero zero) hz
  have scoreOne := (hb.eqTrans (score_valid P d zero zero (empty_valid P d))).eqTrans
    (congrSucc (zero_mask_count (length P)))
  exact positive_score_valid _ _ _ _ (le_congr scoreOne (.eqRefl _) hs)

theorem rank_maximal (P d R C : PTm n) (hR : Γ ⊢[PRAAx] lt R (maskLimit (length P)))
    (hC : Γ ⊢[PRAAx] lt C (maskLimit d)) (h : Γ ⊢[PRAAx] valid P d R C) :
    Γ ⊢[PRAAx] le (rowSize P R) (rank P d) := by
  have l := (candidate_address_score P d R C hC).eqTrans (score_valid P d R C h)
  have r := score_valid (Γ := Γ) P d (bestRow P d) (bestColumn P d) (best_valid P d)
  have bounds := best_score P d (address d R C) (address_bound P d R C hR hC)
  exact (succ_monus_succ _ _).eqSymm.eqTrans (le_congr l r bounds)

theorem larger_minor_zero (P d R C : PTm n) (hR : Γ ⊢[PRAAx] lt R (maskLimit (length P)))
    (hC : Γ ⊢[PRAAx] lt C (maskLimit d)) (h : Γ ⊢[PRAAx] rowSize P R ≐ columnSize d C)
    (hk : Γ ⊢[PRAAx] lt (rank P d) (rowSize P R)) : Γ ⊢[PRAAx] clearedValue P d R C ≐ qzero := by
  have hv : Γ ⊢[PRAAx] value P d R C ≐ qzero := .orE (eq_or_ne _ _) Prf.hyp0
    (le_lt_absurd _ (rank_maximal P d R C hR.wk hC.wk (.andI h.wk Prf.hyp0)) hk.wk)
  exact (RationalSelectedMinors.normalized_determinant_zero_iff P d R C (rowSize P R) (.eqRefl _) h).iffMpr hv

theorem horizon_exact (P d : PTm n) : Γ ⊢[PRAAx] horizon P d ≐ pw two (length P+d) :=
  (mul_comm (maskLimit d) (maskLimit (length P))).eqTrans (pw_add two (length P) d).eqSymm

theorem best_cleared_nonzero (P d : PTm n) : Γ ⊢[PRAAx] neg (clearedValue P d (bestRow P d) (bestColumn P d) ≐ qzero) := by
  have h := best_valid (Γ := Γ) P d
  have e := RationalSelectedMinors.normalized_determinant_zero_iff P d (bestRow P d) (bestColumn P d)
    (rank P d) (.eqRefl _) (.andE₁ h)
  exact .impI (.impE (Prf.andE₂ h).wk (e.wk.iffMp Prf.hyp0))

theorem rank_le_columns (P d : PTm n) : Γ ⊢[PRAAx] le (rank P d) d :=
  le_congr (Prf.andE₁ (best_valid P d)).eqSymm (.eqRefl _) (RationalSelectedMinors.count_bound d (bestColumn P d))

def output (P d : PTm n) : PTm n := pairT (bestRow P d) (pairT (bestColumn P d) (rank P d))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (P d : PTm n) : PTm n := ap2 outputF P d

@[simp] theorem subst_horizon {k : ℕ} (σ : Fin n → PTm k) (P d : PTm n) :
    Syn.subst σ (horizon P d) = horizon (Syn.subst σ P) (Syn.subst σ d) := by simp [horizon]
@[simp] theorem subst_bestAddress {k : ℕ} (σ : Fin n → PTm k) (P d : PTm n) :
    Syn.subst σ (bestAddress P d) = bestAddress (Syn.subst σ P) (Syn.subst σ d) := by
  simp [bestAddress,Probability.UnionUtility.Ag]
@[simp] theorem subst_bestRow {k : ℕ} (σ : Fin n → PTm k) (P d : PTm n) :
    Syn.subst σ (bestRow P d) = bestRow (Syn.subst σ P) (Syn.subst σ d) := by simp [bestRow]
@[simp] theorem subst_bestColumn {k : ℕ} (σ : Fin n → PTm k) (P d : PTm n) :
    Syn.subst σ (bestColumn P d) = bestColumn (Syn.subst σ P) (Syn.subst σ d) := by simp [bestColumn]
@[simp] theorem subst_rank {k : ℕ} (σ : Fin n → PTm k) (P d : PTm n) :
    Syn.subst σ (rank P d) = rank (Syn.subst σ P) (Syn.subst σ d) := by simp [rank]
@[simp] theorem subst_valid {k : ℕ} (σ : Fin n → PTm k) (P d R C : PTm n) :
    (valid P d R C).subst σ = valid (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ R) (Syn.subst σ C) := by simp [valid]
@[simp] theorem subst_clearedValue {k : ℕ} (σ : Fin n → PTm k) (P d R C : PTm n) :
    Syn.subst σ (clearedValue P d R C) = clearedValue (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ R) (Syn.subst σ C) := by
  simp [clearedValue]

theorem program_at (P d : PTm n) : Γ ⊢[PRAAx] run P d ≐ output P d := by
  simpa [run,outputF,output,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![P,d]

theorem actual_minor_scan_horizon_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (horizon (var 0) (var 1) ≐ pw two (length (var 0)+var 1)) := closeUniv 2 (horizon_exact _ _)

theorem actual_selected_maximum_minor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((lt (bestRow (var 0) (var 1)) (maskLimit (length (var 0))) ⋏ lt (bestColumn (var 0) (var 1)) (maskLimit (var 1))) ⋏
      (valid (var 0) (var 1) (bestRow (var 0) (var 1)) (bestColumn (var 0) (var 1)) ⋏
        neg (clearedValue (var 0) (var 1) (bestRow (var 0) (var 1)) (bestColumn (var 0) (var 1)) ≐ qzero))) :=
  closeUniv 2 (.andI (best_mask_bounds _ _) (.andI (best_valid _ _) (best_cleared_nonzero _ _)))

theorem actual_larger_cleared_minor_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 2) (maskLimit (length (var 0))) ⟶ lt (var 3) (maskLimit (var 1)) ⟶
      rowSize (var 0) (var 2) ≐ columnSize (var 1) (var 3) ⟶ lt (rank (var 0) (var 1)) (rowSize (var 0) (var 2)) ⟶
      clearedValue (var 0) (var 1) (var 2) (var 3) ≐ qzero) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (larger_minor_zero (var 0) (var 1) (var 2) (var 3)
    (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0)))))

theorem actual_maximal_minor_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)

end LeanProofs.IPRA.Analysis.RationalMaximalMinors
