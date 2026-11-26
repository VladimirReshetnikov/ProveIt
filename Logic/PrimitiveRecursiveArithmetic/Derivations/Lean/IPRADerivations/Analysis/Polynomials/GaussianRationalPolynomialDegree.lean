import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRationalFiniteRoots
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRationalMonicReduction

/-!
# Actual nonzero-coefficient scan, canonical trimming and computed degree

All original lists, degree bounds and search/prefix indices are numerical.
The least nonzero FIELD coefficient is found by an actual bounded test of
its canonical recoding. The all-zero branch explicitly returns the canonical
zero polynomial; its reported natural degree zero is a sentinel. No semantic
function-zero converse or equality of arbitrary outer list codes is claimed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalPolynomialDegree

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qadd qmul canonical horner hornerF evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qone qadd_congr qmul_congr qzero_canonical qmul_zero_left canonicalCoefficients)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant
  (recode recode_congr recode_canonical recode_eq zeroPrefix zero_prefix_at zero_prefix_horner)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def zeroBit : PTm 2 := eqb (recode (entry (var 1) (var 0))) qzero
def first (C N : PTm n) : PTm n := Search.mu zeroBit (succ N) C
def flag (C N : PTm n) : PTm n := Signum.sg (monus (succ N) (first C N))
def degree (C N : PTm n) : PTm n := monus N (first C N)
def nonzeroCoefficients (C N : PTm n) : Fm PTm n := .ex
  (lt (var 0) (succ (Syn.shift N)) ⋏ neg (recode (entry (Syn.shift C) (var 0)) ≐ qzero))
def allZero (C N : PTm n) : Fm PTm n := zeroPrefix C (succ N)
def tailData (C e : PTm n) : PTm n := pairT C e
def tailBody : PTm 2 := recode (entry (fstT (var 1)) (sndT (var 1)+var 0))
def canonicalTail (C e L : PTm n) : PTm n := sequence tailBody L (tailData C e)
def zeroPolynomial : PTm n := GaussianRationalPolynomialBuffers.zeros one
def trimmed (C N : PTm n) : PTm n := RationalArithmetic.select (flag C N) zeroPolynomial
  (canonicalTail C (first C N) (succ (degree C N)))

@[simp] theorem subst_first {l : ℕ} (σ : Fin n → PTm l) (C N : PTm n) :
    Syn.subst σ (first C N) = first (Syn.subst σ C) (Syn.subst σ N) := by simp [first,Search.mu]
@[simp] theorem subst_flag {l : ℕ} (σ : Fin n → PTm l) (C N : PTm n) :
    Syn.subst σ (flag C N) = flag (Syn.subst σ C) (Syn.subst σ N) := by simp [flag,Signum.sg]
@[simp] theorem subst_degree {l : ℕ} (σ : Fin n → PTm l) (C N : PTm n) :
    Syn.subst σ (degree C N) = degree (Syn.subst σ C) (Syn.subst σ N) := by simp [degree]
@[simp] theorem subst_nonzeroCoefficients {l : ℕ} (σ : Fin n → PTm l) (C N : PTm n) :
    (nonzeroCoefficients C N).subst σ = nonzeroCoefficients (Syn.subst σ C) (Syn.subst σ N) := by
  simp [nonzeroCoefficients,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_allZero {l : ℕ} (σ : Fin n → PTm l) (C N : PTm n) :
    (allZero C N).subst σ = allZero (Syn.subst σ C) (Syn.subst σ N) := by simp [allZero]
@[simp] theorem subst_tailData {l : ℕ} (σ : Fin n → PTm l) (C e : PTm n) :
    Syn.subst σ (tailData C e) = tailData (Syn.subst σ C) (Syn.subst σ e) := by simp [tailData]
@[simp] theorem subst_canonicalTail {l : ℕ} (σ : Fin n → PTm l) (C e L : PTm n) :
    Syn.subst σ (canonicalTail C e L) = canonicalTail (Syn.subst σ C) (Syn.subst σ e) (Syn.subst σ L) := by simp [canonicalTail]
@[simp] theorem subst_zeroPolynomial {l : ℕ} (σ : Fin n → PTm l) : Syn.subst σ (zeroPolynomial : PTm n) = (zeroPolynomial : PTm l) := by simp [zeroPolynomial]
@[simp] theorem subst_trimmed {l : ℕ} (σ : Fin n → PTm l) (C N : PTm n) :
    Syn.subst σ (trimmed C N) = trimmed (Syn.subst σ C) (Syn.subst σ N) := by simp [trimmed]

theorem zero_bit_at (C i : PTm n) : inst2 zeroBit i C = eqb (recode (entry C i)) qzero := by simp [zeroBit,inst2]
theorem first_bound (C N : PTm n) : Γ ⊢[PRAAx] le (first C N) (succ N) :=
  .andE₁ (Search.search_spec (f := zeroBit) (succ N) zero C)
theorem first_zero_prefix (C N : PTm n) : Γ ⊢[PRAAx] zeroPrefix C (first C N) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift (first C N)) :: Γ.map Fm.shift
  have range : Δ ⊢[PRAAx] lt (var 0) (first (Syn.shift C) (Syn.shift N)) := by
    simpa only [Δ,Syn.shift,subst_first] using (Prf.hyp0 (Ax := PRAAx) (Γ := Γ.map Fm.shift)
      (φ := lt (var 0) (Syn.shift (first C N))))
  have minimal : Δ ⊢[PRAAx] neg (eqb (recode (entry (Syn.shift C) (var 0))) qzero ≐ zero) := by
    simpa only [zero_bit_at] using Search.search_minimal (f := zeroBit) range

  exact AnalyticNumberTheory.Valuation.eq_of_eqb_ne minimal

theorem first_nonzero (C N : PTm n) (h : Γ ⊢[PRAAx] lt (first C N) (succ N)) : Γ ⊢[PRAAx]
    neg (recode (entry C (first C N)) ≐ qzero) := by
  have hit : Γ ⊢[PRAAx] eqb (recode (entry C (first C N))) qzero ≐ zero := by
    simpa only [zero_bit_at,first] using Prf.impE (.andE₁ (.andE₂ (Search.search_spec (f := zeroBit) (succ N) zero C))) h
  exact .impI (succ_ne_zero ((eqb_of_eq Prf.hyp0).eqSymm.eqTrans hit.wk))

theorem flag_one_of_found (C N : PTm n) (h : Γ ⊢[PRAAx] lt (first C N) (succ N)) : Γ ⊢[PRAAx]
    flag C N ≐ one := AnalyticNumberTheory.Totatives.sg_lt h
theorem flag_zero_of_default (C N : PTm n) (h : Γ ⊢[PRAAx] first C N ≐ succ N) : Γ ⊢[PRAAx]
    flag C N ≐ zero := AnalyticNumberTheory.Totatives.sg_le (le_congr (.eqRefl _) h.eqSymm (le_refl (succ N)))

theorem found_of_flag_one (C N : PTm n) (h : Γ ⊢[PRAAx] flag C N ≐ one) : Γ ⊢[PRAAx]
    lt (first C N) (succ N) := by
  refine .orE (lt_or_eq_of_le (first_bound C N)) Prf.hyp0 ?_
  exact .botE _ (succ_ne_zero (h.wk.eqSymm.eqTrans (flag_zero_of_default C N Prf.hyp0)))
theorem default_of_flag_zero (C N : PTm n) (h : Γ ⊢[PRAAx] flag C N ≐ zero) : Γ ⊢[PRAAx]
    first C N ≐ succ N := by
  refine .orE (lt_or_eq_of_le (first_bound C N)) ?_ Prf.hyp0
  exact .botE _ (succ_ne_zero ((flag_one_of_found C N Prf.hyp0).eqSymm.eqTrans h.wk))
theorem flag_cases (C N : PTm n) : Γ ⊢[PRAAx] (flag C N ≐ zero) ⋎ (flag C N ≐ one) :=
  .orE (lt_or_eq_of_le (first_bound C N)) (.orI₂ (flag_one_of_found C N Prf.hyp0)) (.orI₁ (flag_zero_of_default C N Prf.hyp0))

theorem first_from_witness (C N i : PTm n) (hi : Γ ⊢[PRAAx] lt i (succ N))
    (hne : Γ ⊢[PRAAx] neg (recode (entry C i) ≐ qzero)) : Γ ⊢[PRAAx]
    lt (first C N) (succ N) ⋏ le (first C N) i := by
  have hit : Γ ⊢[PRAAx] inst2 zeroBit i C ≐ zero := by simpa only [zero_bit_at] using eqb_of_ne hne
  have found := Search.search_found (f := zeroBit) hit hi
  exact .andI (.andE₁ found) (.andE₂ (.andE₂ found))

theorem flag_one_of_nonzero (C N : PTm n) (h : Γ ⊢[PRAAx] nonzeroCoefficients C N) : Γ ⊢[PRAAx] flag C N ≐ one := by
  refine .exE h ?_
  have source : (lt (var 0) (succ (Syn.shift N)) ⋏ neg (recode (entry (Syn.shift C) (var 0)) ≐ qzero)) :: Γ.map Fm.shift ⊢[PRAAx]
      lt (first (Syn.shift C) (Syn.shift N)) (succ (Syn.shift N)) :=
    .andE₁ (first_from_witness _ _ _ (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0))
  simpa only [Fm.shift,Fm.subst_eq,subst_flag,Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using flag_one_of_found _ _ source

theorem nonzero_of_flag_one (C N : PTm n) (h : Γ ⊢[PRAAx] flag C N ≐ one) : Γ ⊢[PRAAx] nonzeroCoefficients C N := by
  refine .exI (first C N) ?_
  simpa only [Fm.subst_and,Fm.subst_imp,Fm.subst_bot,Fm.subst_eq,subst_lt,subst_entry,
    GaussianTranslatedNonconstant.subst_recode,GaussianRationalHorner.subst_qzero,ConciseIPRA.PTm.subst_succ,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,neg] using
      Prf.andI (found_of_flag_one C N h) (first_nonzero C N (found_of_flag_one C N h))

theorem success_iff_nonzero (C N : PTm n) : Γ ⊢[PRAAx] Fm.iff (flag C N ≐ one) (nonzeroCoefficients C N) :=
  .andI (.impI (nonzero_of_flag_one C N Prf.hyp0)) (.impI (flag_one_of_nonzero C N Prf.hyp0))

theorem all_zero_of_flag_zero (C N : PTm n) (h : Γ ⊢[PRAAx] flag C N ≐ zero) : Γ ⊢[PRAAx] allZero C N := by
  refine .allI (.impI ?_)
  have ds : Γ.map Fm.shift ⊢[PRAAx] first (Syn.shift C) (Syn.shift N) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_first,ConciseIPRA.PTm.subst_succ,Syn.shift] using (default_of_flag_zero C N h).shift
  exact zero_prefix_at _ _ _ (first_zero_prefix _ _) (lt_congr (.eqRefl _) ds.wk.eqSymm Prf.hyp0)

theorem flag_zero_of_all_zero (C N : PTm n) (h : Γ ⊢[PRAAx] allZero C N) : Γ ⊢[PRAAx] flag C N ≐ zero := by
  refine .orE (lt_or_eq_of_le (first_bound C N)) ?_ (flag_zero_of_default C N Prf.hyp0)
  exact .botE _ (.impE (first_nonzero C N Prf.hyp0) (zero_prefix_at C (succ N) (first C N) h.wk Prf.hyp0))
theorem failure_iff_all_zero (C N : PTm n) : Γ ⊢[PRAAx] Fm.iff (flag C N ≐ zero) (allZero C N) :=
  .andI (.impI (all_zero_of_flag_zero C N Prf.hyp0)) (.impI (flag_zero_of_all_zero C N Prf.hyp0))

theorem tail_body_at (C e i : PTm n) : Γ ⊢[PRAAx]
    inst2 tailBody i (tailData C e) ≐ recode (entry C (e+i)) := by
  simp only [tailBody,inst2,GaussianTranslatedNonconstant.subst_recode,subst_entry,subst_fstT,subst_sndT,PTm.subst_add,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact recode_congr (entry_congr (fst_pair _ _) (congrAdd (snd_pair _ _) (.eqRefl _)))
theorem tail_length (C e L : PTm n) : Γ ⊢[PRAAx] length (canonicalTail C e L) ≐ L := sequence_length _ _ _
theorem tail_lookup (C e L i : PTm n) (hi : Γ ⊢[PRAAx] lt i L) : Γ ⊢[PRAAx]
    entry (canonicalTail C e L) i ≐ recode (entry C (e+i)) :=
  (sequence_decode tailBody hi).eqTrans (tail_body_at C e i)
theorem tail_canonical (C e L : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (canonicalTail C e L) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift (canonicalTail C e L))) :: Γ.map Fm.shift
  have range : Δ ⊢[PRAAx] lt (var 0) (Syn.shift L) :=
    lt_congr (.eqRefl _) (tail_length (Syn.shift C) (Syn.shift e) (Syn.shift L))
      (by simpa only [Δ,Syn.shift,subst_canonicalTail] using
        (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift (canonicalTail C e L)))))
  simpa only [Δ,Syn.shift,subst_canonicalTail] using
    GaussianRationalHorner.canonical_congr (tail_lookup _ _ _ _ range) (recode_canonical _)

theorem trim_success (C N : PTm n) (h : Γ ⊢[PRAAx] flag C N ≐ one) : Γ ⊢[PRAAx]
    trimmed C N ≐ canonicalTail C (first C N) (succ (degree C N)) := RationalArithmetic.select_one _ _ _ h
theorem trim_failure (C N : PTm n) (h : Γ ⊢[PRAAx] flag C N ≐ zero) : Γ ⊢[PRAAx]
    trimmed C N ≐ zeroPolynomial := RationalArithmetic.select_zero _ _ _ h

theorem degree_le (C N : PTm n) : Γ ⊢[PRAAx] le (degree C N) N := by
  refine .orE (lt_or_le N (first C N)) ?_ ?_
  · exact le_congr (le_of_lt Prf.hyp0 : _ ⊢[PRAAx] degree C N ≐ zero).eqSymm (.eqRefl _) (zero_le N)
  · exact le_of_eq_add (d := first C N) ((eq_add_of_le Prf.hyp0).eqTrans (add_comm _ _))
theorem degree_zero_of_failure (C N : PTm n) (h : Γ ⊢[PRAAx] flag C N ≐ zero) : Γ ⊢[PRAAx] degree C N ≐ zero :=
  (congrMonus (.eqRefl _) (default_of_flag_zero C N h)).eqTrans (le_succ_self N)
theorem success_index (C N : PTm n) (h : Γ ⊢[PRAAx] flag C N ≐ one) : Γ ⊢[PRAAx] le (first C N) N :=
  (succ_monus_succ _ _).eqSymm.eqTrans (found_of_flag_one C N h)
theorem degree_balance (C N : PTm n) (h : Γ ⊢[PRAAx] flag C N ≐ one) : Γ ⊢[PRAAx]
    first C N+succ (degree C N) ≐ succ N :=
  (by unfold degree; ipra_ring : Γ ⊢[PRAAx] first C N+succ (degree C N) ≐ succ (first C N+degree C N)).eqTrans
    (congrSucc (eq_add_of_le (success_index C N h)).eqSymm)

theorem trimmed_length (C N : PTm n) : Γ ⊢[PRAAx] length (trimmed C N) ≐ succ (degree C N) := by
  refine .orE (flag_cases C N) ?_ ?_
  · exact (congrFst (trim_failure C N Prf.hyp0)).eqTrans
      ((GaussianRationalPolynomialBuffers.zeros_length one).eqTrans (congrSucc (degree_zero_of_failure C N Prf.hyp0)).eqSymm)
  · exact (congrFst (trim_success C N Prf.hyp0)).eqTrans (tail_length _ _ _)
theorem trimmed_canonical (C N : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (trimmed C N) := by
  refine .orE (flag_cases C N) ?_ ?_
  · exact GaussianRationalMonicReduction.canonical_coefficients_congr (trim_failure C N Prf.hyp0)
      (GaussianRationalMonicReduction.zeros_canonical one)
  · exact GaussianRationalMonicReduction.canonical_coefficients_congr (trim_success C N Prf.hyp0) (tail_canonical _ _ _)

theorem trimmed_head (C N : PTm n) (h : Γ ⊢[PRAAx] flag C N ≐ one) : Γ ⊢[PRAAx]
    entry (trimmed C N) zero ≐ recode (entry C (first C N)) :=
  (entry_congr (trim_success C N h) (.eqRefl _)).eqTrans
    ((tail_lookup _ _ _ _ (zero_lt_succ _)).eqTrans (recode_congr (entry_congr (.eqRefl _) (add_zero _))))
theorem trimmed_nonzero_head (C N : PTm n) (h : Γ ⊢[PRAAx] flag C N ≐ one) : Γ ⊢[PRAAx]
    GaussianRationalFiniteRoots.nonzeroHead (trimmed C N) := by
  have headCode : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.head (trimmed C N) ≐ recode (entry C (first C N)) :=
    (recode_congr (trimmed_head C N h)).eqTrans (recode_eq _ (recode_canonical _))
  exact .impI (.impE (first_nonzero C N (found_of_flag_one C N h)).wk (headCode.wk.eqSymm.eqTrans Prf.hyp0))

def tailLaw (C e L z r : PTm n) : Fm PTm n := le r L ⟶ horner (canonicalTail C e L) z r ≐ horner C z (e+r)
@[simp] theorem subst_tailLaw {l : ℕ} (σ : Fin n → PTm l) (C e L z r : PTm n) :
    (tailLaw C e L z r).subst σ = tailLaw (Syn.subst σ C) (Syn.subst σ e) (Syn.subst σ L) (Syn.subst σ z) (Syn.subst σ r) := by simp [tailLaw]

/-- Genuine guarded QF leading-zero removal preserves raw original values;
the canonical tail coefficient is simplified only inside normalized qadd. -/
theorem tail_prefix (C e L z r : PTm n) (hZero : Γ ⊢[PRAAx] zeroPrefix C e)
    (hr : Γ ⊢[PRAAx] le r L) : Γ ⊢[PRAAx] horner (canonicalTail C e L) z r ≐ horner C z (e+r) := by
  have all : Γ ⊢[PRAAx] .all (tailLaw (Syn.shift C) (Syn.shift e) (Syn.shift L) (Syn.shift z) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_tailLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI ((GaussianRationalHorner.horner_zero _ _).eqTrans
        (((congrAp3 hornerF (add_zero e) (.eqRefl C) (.eqRefl z)).eqTrans
          (zero_prefix_horner C z e e hZero (le_refl _))).eqSymm)).wk
    · simp only [subst_tailLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let Δ := le (succ (var 0)) (Syn.shift L) :: tailLaw (Syn.shift C) (Syn.shift e) (Syn.shift L) (Syn.shift z) (var 0) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] horner (canonicalTail (Syn.shift C) (Syn.shift e) (Syn.shift L)) (Syn.shift z) (var 0) ≐
          horner (Syn.shift C) (Syn.shift z) (Syn.shift e+var 0) := .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      exact (GaussianRationalHorner.horner_succ _ _ _).eqTrans
        ((qadd_congr (qmul_congr ih (.eqRefl _)) (tail_lookup _ _ _ _ Prf.hyp0)).eqTrans
          ((GaussianRationalSyntheticCoefficientValues.qadd_recode_right _ _).eqTrans
            ((GaussianRationalHorner.horner_succ _ _ _).eqSymm.eqTrans
              (congrAp3 hornerF (by ipra_ring) (.eqRefl _) (.eqRefl _)))))
  have rule : Γ ⊢[PRAAx] tailLaw C e L z r := by
    simpa only [subst_tailLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r
  exact .impE rule hr

theorem tail_evaluation (C e L z : PTm n) (hZero : Γ ⊢[PRAAx] zeroPrefix C e) : Γ ⊢[PRAAx]
    evaluate (canonicalTail C e L) z ≐ horner C z (e+L) :=
  (congrAp3 hornerF (tail_length _ _ _) (.eqRefl _) (.eqRefl _)).eqTrans (tail_prefix C e L z L hZero (le_refl _))

theorem trimmed_evaluation (C N z : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    evaluate (trimmed C N) z ≐ evaluate C z := by
  refine .orE (flag_cases C N) ?_ ?_
  · have oldZero : (flag C N ≐ zero) :: Γ ⊢[PRAAx] evaluate C z ≐ qzero :=
      (congrAp3 hornerF hC.wk (.eqRefl _) (.eqRefl _)).eqTrans
        (zero_prefix_horner C z (succ N) (succ N) (all_zero_of_flag_zero C N Prf.hyp0) (le_refl _))
    exact (GaussianRationalFiniteRoots.evaluate_congr (trim_failure C N Prf.hyp0) (.eqRefl _)).eqTrans
      ((GaussianRationalPolynomialBuffers.zeros_evaluation one z).eqTrans oldZero.eqSymm)
  · exact (GaussianRationalFiniteRoots.evaluate_congr (trim_success C N Prf.hyp0) (.eqRefl _)).eqTrans
      ((tail_evaluation C (first C N) (succ (degree C N)) z (first_zero_prefix C N)).eqTrans
        ((congrAp3 hornerF (degree_balance C N Prf.hyp0) (.eqRefl _) (.eqRefl _)).eqTrans
          (congrAp3 hornerF hC.wk.eqSymm (.eqRefl _) (.eqRefl _))))

theorem trimmed_roots (C N R : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hRoots : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.roots C R) : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.roots (trimmed C N) R := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hC.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] GaussianRationalFiniteRoots.roots (Syn.shift C) (Syn.shift R) := by
    simpa only [Fm.shift,GaussianRationalFiniteRoots.subst_roots,Syn.shift] using hRoots.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_trimmed] using
    (trimmed_evaluation (Syn.shift C) (Syn.shift N) (entry (Syn.shift R) (var 0)) cs.wk).eqTrans
      (GaussianRationalFiniteRoots.roots_at _ _ _ rs.wk Prf.hyp0)

/-- The same computed trim and degree discharge the nonzero-head root
bound from the original nonzero-coefficient and original root-list data. -/
theorem computed_root_bound (C N R : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hNonzero : Γ ⊢[PRAAx] nonzeroCoefficients C N) (hRoots : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.roots C R)
    (hDistinct : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R) : Γ ⊢[PRAAx]
    le (length R) (degree C N) ⋏ le (degree C N) N :=
  .andI (GaussianRationalFiniteRoots.finite_root_bound (trimmed C N) (degree C N) R (trimmed_length C N)
    (trimmed_nonzero_head C N (flag_one_of_nonzero C N hNonzero)) (trimmed_roots C N R hC hRoots) hDistinct) (degree_le C N)

/-! The tagged PR2 output retains the actual success bit, least original
index, computed degree and canonical polynomial. All four fields are decoded
from this one program rather than substituted as independent certificates. -/
def output (C N : PTm n) : PTm n := pairT (flag C N) (pairT (first C N) (pairT (degree C N) (trimmed C N)))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (C N : PTm n) : PTm n := ap2 outputF C N
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (C N : PTm n) :
    Syn.subst σ (output C N) = output (Syn.subst σ C) (Syn.subst σ N) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (C N : PTm n) :
    Syn.subst σ (run C N) = run (Syn.subst σ C) (Syn.subst σ N) := by simp [run]
theorem program_at (C N : PTm n) : Γ ⊢[PRAAx] run C N ≐ output C N := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![C,N]
theorem returned_flag (C N : PTm n) : Γ ⊢[PRAAx] fstT (run C N) ≐ flag C N :=
  (congrFst (program_at _ _)).eqTrans (fst_pair _ _)
theorem returned_first (C N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run C N)) ≐ first C N :=
  (congrFst ((congrSnd (program_at _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_degree (C N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run C N))) ≐ degree C N :=
  (congrFst ((congrSnd ((congrSnd (program_at _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_trim (C N : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run C N))) ≐ trimmed C N :=
  (congrSnd ((congrSnd ((congrSnd (program_at _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_degree_bound (C N : PTm n) : Γ ⊢[PRAAx] le (fstT (sndT (sndT (run C N)))) N :=
  le_congr (returned_degree _ _).eqSymm (.eqRefl _) (degree_le _ _)
theorem returned_length (C N : PTm n) : Γ ⊢[PRAAx]
    length (sndT (sndT (sndT (run C N)))) ≐ succ (fstT (sndT (sndT (run C N)))) :=
  (congrFst (returned_trim _ _)).eqTrans ((trimmed_length _ _).eqTrans (congrSucc (returned_degree _ _)).eqSymm)
theorem returned_canonical (C N : PTm n) : Γ ⊢[PRAAx]
    canonicalCoefficients (sndT (sndT (sndT (run C N)))) :=
  GaussianRationalMonicReduction.canonical_coefficients_congr (returned_trim _ _) (trimmed_canonical _ _)
theorem returned_evaluation (C N z : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    evaluate (sndT (sndT (sndT (run C N)))) z ≐ evaluate C z :=
  (GaussianRationalFiniteRoots.evaluate_congr (returned_trim _ _) (.eqRefl _)).eqTrans (trimmed_evaluation _ _ _ hC)
theorem returned_root_bound (C N R : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hNonzero : Γ ⊢[PRAAx] nonzeroCoefficients C N) (hRoots : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.roots C R)
    (hDistinct : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R) : Γ ⊢[PRAAx]
    le (length R) (fstT (sndT (sndT (run C N)))) ⋏ le (fstT (sndT (sndT (run C N)))) N :=
  .andI (le_congr (.eqRefl _) (returned_degree _ _).eqSymm (.andE₁ (computed_root_bound _ _ _ hC hNonzero hRoots hDistinct)))
    (returned_degree_bound _ _)

/-! Genuine ordinary closed statements bind every original numerical list,
degree, scan index, query point and root list within the object language. -/
theorem tagged_degree_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)
theorem scan_success_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (Fm.iff (flag (var 0) (var 1) ≐ one) (nonzeroCoefficients (var 0) (var 1))) :=
  closeUniv 2 (success_iff_nonzero _ _)
theorem scan_failure_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (Fm.iff (flag (var 0) (var 1) ≐ zero) (allZero (var 0) (var 1))) :=
  closeUniv 2 (failure_iff_all_zero _ _)
theorem scan_least_witness_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (succ (var 1)) ⟶ neg (recode (entry (var 0) (var 2)) ≐ qzero) ⟶
      (lt (first (var 0) (var 1)) (succ (var 1)) ⋏ le (first (var 0) (var 1)) (var 2))) :=
  closeUniv 3 (.impI (.impI (first_from_witness _ _ _ Prf.hyp1 Prf.hyp0)))
theorem canonical_trim_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((length (trimmed (var 0) (var 1)) ≐ succ (degree (var 0) (var 1))) ⋏
      (canonicalCoefficients (trimmed (var 0) (var 1)) ⋏ le (degree (var 0) (var 1)) (var 1))) :=
  closeUniv 2 (.andI (trimmed_length _ _) (.andI (trimmed_canonical _ _) (degree_le _ _)))
theorem original_evaluation_preserved_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 0) ≐ succ (var 1) ⟶ evaluate (trimmed (var 0) (var 1)) (var 2) ≐ evaluate (var 0) (var 2)) :=
  closeUniv 3 (.impI (trimmed_evaluation _ _ _ Prf.hyp0))
theorem computed_nonzero_head_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (nonzeroCoefficients (var 0) (var 1) ⟶ GaussianRationalFiniteRoots.nonzeroHead (trimmed (var 0) (var 1))) :=
  closeUniv 2 (.impI (trimmed_nonzero_head _ _ (flag_one_of_nonzero _ _ Prf.hyp0)))
theorem computed_runtime_root_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 0) ≐ succ (var 1) ⟶ nonzeroCoefficients (var 0) (var 1) ⟶
      GaussianRationalFiniteRoots.roots (var 0) (var 2) ⟶ GaussianRationalFiniteRoots.distinct (var 2) ⟶
        (le (length (var 2)) (degree (var 0) (var 1)) ⋏ le (degree (var 0) (var 1)) (var 1))) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (computed_root_bound _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))
theorem returned_trim_correct_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 0) ≐ succ (var 1) ⟶
      ((length (sndT (sndT (sndT (run (var 0) (var 1))))) ≐ succ (fstT (sndT (sndT (run (var 0) (var 1)))))) ⋏
        (canonicalCoefficients (sndT (sndT (sndT (run (var 0) (var 1))))) ⋏
          evaluate (sndT (sndT (sndT (run (var 0) (var 1))))) (var 2) ≐ evaluate (var 0) (var 2)))) :=
  closeUniv 3 (.impI (.andI (returned_length _ _) (.andI (returned_canonical _ _) (returned_evaluation _ _ _ Prf.hyp0))))
theorem returned_runtime_root_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 0) ≐ succ (var 1) ⟶ nonzeroCoefficients (var 0) (var 1) ⟶
      GaussianRationalFiniteRoots.roots (var 0) (var 2) ⟶ GaussianRationalFiniteRoots.distinct (var 2) ⟶
        (le (length (var 2)) (fstT (sndT (sndT (run (var 0) (var 1))))) ⋏
          le (fstT (sndT (sndT (run (var 0) (var 1))))) (var 1))) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (returned_root_bound _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianRationalPolynomialDegree
