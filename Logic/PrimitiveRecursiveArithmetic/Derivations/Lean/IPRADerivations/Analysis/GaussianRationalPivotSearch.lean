import IPRADerivations.Analysis.GaussianRationalRowElimination
import IPRADerivations.Foundations.BoundedReflection

/-!
# Actual least available Gaussian-rational pivot

The numerical history stores zero for a skipped column and succ(row) for
an earlier selected row. A genuine bounded all-test marks availability;
the actual least-witness scan finds the first available nonzero FIELD
entry. Success and failure are derived from these original tests. No
valid history, rank, pivot-search contract or null invariant is input.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalPivotSearch

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero)
open LeanProofs.IPRA.Analysis.GaussianRationalRowElimination (shape pivot eliminate nullRows)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open LeanProofs.IPRA.Foundations.BoundedReflection (allB all_cases all_elim all_intro exB wit ex_cases ex_intro ex_elim ex_none ex_least)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero)
open LeanProofs.IPRA.PTm (monus)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def markData (H r : PTm n) : PTm n := pairT H r
def differentBody : PTm 2 := monus one (eqb (entry (fstT (var 1)) (var 0)) (succ (sndT (var 1))))
def available (H c r : PTm n) : PTm n := allB differentBody c (markData H r)
def unmarked (H c r : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift c) ⟶ neg (entry (Syn.shift H) (var 0) ≐ succ (Syn.shift r)))
def candidate (A H c p r : PTm n) : PTm n := available H c r * monus one (eqb (pivot A r p) qzero)
def data (A H c p : PTm n) : PTm n := pairT A (pairT H (pairT c p))
def fields (q : PTm n) : Fin 4 → PTm n := ![fstT q,fstT (sndT q),fstT (sndT (sndT q)),sndT (sndT (sndT q))]
def candidateBody : PTm 2 := candidate (fields (var 1) 0) (fields (var 1) 1) (fields (var 1) 2) (fields (var 1) 3) (var 0)
def selected (A R H c p : PTm n) : PTm n := wit candidateBody R (data A H c p)
def flag (A R H c p : PTm n) : PTm n := exB candidateBody R (data A H c p)
def eligible (A H c p r : PTm n) : Fm PTm n := unmarked H c r ⋏ neg (pivot A r p ≐ qzero)

@[simp] theorem subst_markData {k : ℕ} (σ : Fin n → PTm k) (H r : PTm n) :
    Syn.subst σ (markData H r) = markData (Syn.subst σ H) (Syn.subst σ r) := by simp [markData]
@[simp] theorem subst_available {k : ℕ} (σ : Fin n → PTm k) (H c r : PTm n) :
    Syn.subst σ (available H c r) = available (Syn.subst σ H) (Syn.subst σ c) (Syn.subst σ r) := by simp [available]
@[simp] theorem subst_unmarked {k : ℕ} (σ : Fin n → PTm k) (H c r : PTm n) :
    (unmarked H c r).subst σ = unmarked (Syn.subst σ H) (Syn.subst σ c) (Syn.subst σ r) := by
  simp [unmarked,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_candidate {k : ℕ} (σ : Fin n → PTm k) (A H c p r : PTm n) :
    Syn.subst σ (candidate A H c p r) = candidate (Syn.subst σ A) (Syn.subst σ H) (Syn.subst σ c) (Syn.subst σ p) (Syn.subst σ r) := by simp [candidate]
@[simp] theorem subst_data {k : ℕ} (σ : Fin n → PTm k) (A H c p : PTm n) :
    Syn.subst σ (data A H c p) = data (Syn.subst σ A) (Syn.subst σ H) (Syn.subst σ c) (Syn.subst σ p) := by simp [data]
@[simp] theorem subst_fields {k : ℕ} (σ : Fin n → PTm k) (q : PTm n) (i : Fin 4) :
    Syn.subst σ (fields q i) = fields (Syn.subst σ q) i := by fin_cases i <;> simp [fields]
@[simp] theorem subst_selected {k : ℕ} (σ : Fin n → PTm k) (A R H c p : PTm n) :
    Syn.subst σ (selected A R H c p) = selected (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ H) (Syn.subst σ c) (Syn.subst σ p) := by simp [selected]
@[simp] theorem subst_flag {k : ℕ} (σ : Fin n → PTm k) (A R H c p : PTm n) :
    Syn.subst σ (flag A R H c p) = flag (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ H) (Syn.subst σ c) (Syn.subst σ p) := by simp [flag,exB]
@[simp] theorem subst_eligible {k : ℕ} (σ : Fin n → PTm k) (A H c p r : PTm n) :
    (eligible A H c p r).subst σ = eligible (Syn.subst σ A) (Syn.subst σ H) (Syn.subst σ c) (Syn.subst σ p) (Syn.subst σ r) := by simp [eligible]

theorem different_body_at (H r k : PTm n) : Γ ⊢[PRAAx]
    inst2 differentBody k (markData H r) ≐ monus one (eqb (entry H k) (succ r)) := by
  simp only [differentBody,inst2,PTm.subst_monus,subst_eqb,subst_entry,subst_fstT,subst_sndT,
    ConciseIPRA.PTm.subst_succ,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact congrMonus (.eqRefl _) (AnalyticNumberTheory.Euler.congrEqb (Foundations.SequenceComposition.entry_congr (fst_pair _ _) (.eqRefl _)) (congrSucc (snd_pair _ _)))
theorem available_cases (H c r : PTm n) : Γ ⊢[PRAAx] (available H c r ≐ zero) ⋎ (available H c r ≐ one) := all_cases _ _ _
theorem unmarked_at (H c r k : PTm n) (h : Γ ⊢[PRAAx] unmarked H c r) (hk : Γ ⊢[PRAAx] lt k c) : Γ ⊢[PRAAx]
    neg (entry H k ≐ succ r) := by
  have rule : Γ ⊢[PRAAx] lt k c ⟶ neg (entry H k ≐ succ r) := by simpa [unmarked] using h.allE k
  exact .impE rule hk

theorem available_unmarked (H c r : PTm n) (h : Γ ⊢[PRAAx] available H c r ≐ one) : Γ ⊢[PRAAx] unmarked H c r := by
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] available (Syn.shift H) (Syn.shift c) (Syn.shift r) ≐ one := by
    simpa only [Fm.shift,Fm.subst_eq,subst_available,Syn.shift,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using h.shift
  have nonzero := all_elim differentBody (i := var 0) hs.wk Prf.hyp0
  have actual := (different_body_at (Γ := lt (var 0) (Syn.shift c) :: Γ.map Fm.shift) (Syn.shift H) (Syn.shift r) (var 0))
  have eqzero : (lt (var 0) (Syn.shift c)) :: Γ.map Fm.shift ⊢[PRAAx]
      eqb (entry (Syn.shift H) (var 0)) (succ (Syn.shift r)) ≐ zero :=
    Foundations.BoundedReflection.zero_of_compl_ne (.impI (.impE nonzero.wk (actual.wk.eqTrans Prf.hyp0)))
  exact .impI (succ_ne_zero ((eqb_of_eq Prf.hyp0).eqSymm.eqTrans eqzero.wk))

theorem unmarked_available (H c r : PTm n) (h : Γ ⊢[PRAAx] unmarked H c r) : Γ ⊢[PRAAx] available H c r ≐ one := by
  apply all_intro differentBody
  refine .allI (.impI ?_)
  simp only [Syn.shift,subst_markData]
  have hs : Γ.map Fm.shift ⊢[PRAAx] unmarked (Syn.shift H) (Syn.shift c) (Syn.shift r) := by
    simpa only [Fm.shift,subst_unmarked,Syn.shift] using h.shift
  have neq := unmarked_at (Syn.shift H) (Syn.shift c) (Syn.shift r) (var 0) hs.wk Prf.hyp0
  have actual := (different_body_at (Γ := lt (var 0) (Syn.shift c) :: Γ.map Fm.shift) (Syn.shift H) (Syn.shift r) (var 0)).eqTrans
    ((congrMonus (.eqRefl _) (eqb_of_ne neq)).eqTrans (monus_zero _))
  exact .impI (succ_ne_zero (actual.wk.eqSymm.eqTrans Prf.hyp0))

theorem fields_at (A H c p : PTm n) (i : Fin 4) : Γ ⊢[PRAAx] fields (data A H c p) i ≐ ![A,H,c,p] i := by
  have e0 := snd_pair (Γ := Γ) A (pairT H (pairT c p))
  have e1 := (congrSnd e0).eqTrans (snd_pair H (pairT c p))
  fin_cases i
  · exact fst_pair _ _
  · exact (congrFst e0).eqTrans (fst_pair _ _)
  · exact (congrFst e1).eqTrans (fst_pair _ _)
  · exact (congrSnd e1).eqTrans (snd_pair _ _)
theorem candidate_body_at (A H c p r : PTm n) : Γ ⊢[PRAAx]
    inst2 candidateBody r (data A H c p) ≐ candidate A H c p r := by
  simp only [candidateBody,inst2,subst_candidate,subst_fields,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  simpa only [subst_candidate,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (candidate (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      (σ := ![fields (data A H c p) 0,fields (data A H c p) 1,fields (data A H c p) 2,fields (data A H c p) 3,r])
      (σ' := ![A,H,c,p,r]) (fun i => by fin_cases i; exact fields_at _ _ _ _ 0; exact fields_at _ _ _ _ 1; exact fields_at _ _ _ _ 2; exact fields_at _ _ _ _ 3; exact .eqRefl _)

theorem candidate_one (A H c p r : PTm n) (h : Γ ⊢[PRAAx] eligible A H c p r) : Γ ⊢[PRAAx] candidate A H c p r ≐ one :=
  (congrMul (unmarked_available H c r (.andE₁ h)) ((congrMonus (.eqRefl _) (eqb_of_ne (.andE₂ h))).eqTrans (monus_zero _))).eqTrans (one_mul _)
theorem candidate_eligible (A H c p r : PTm n) (h : Γ ⊢[PRAAx] neg (candidate A H c p r ≐ zero)) : Γ ⊢[PRAAx] eligible A H c p r := by
  have av : Γ ⊢[PRAAx] available H c r ≐ one := by
    refine .orE (available_cases H c r) ?_ Prf.hyp0
    exact .botE _ (.impE h.wk ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)))
  refine .andI (available_unmarked H c r av) (.impI ?_)
  exact .impE h.wk ((congrMul (.eqRefl _) ((congrMonus (.eqRefl _) (eqb_of_eq Prf.hyp0)).eqTrans (monus_self _))).eqTrans (mul_zero _))

theorem flag_cases (A R H c p : PTm n) : Γ ⊢[PRAAx] (flag A R H c p ≐ zero) ⋎ (flag A R H c p ≐ one) := ex_cases _ _ _
theorem selected_bound (A R H c p : PTm n) : Γ ⊢[PRAAx] le (selected A R H c p) R :=
  .andE₁ (Search.search_spec (f := Foundations.BoundedReflection.nB candidateBody) R zero (data A H c p))
theorem selected_correct (A R H c p : PTm n) (h : Γ ⊢[PRAAx] flag A R H c p ≐ one) : Γ ⊢[PRAAx]
    lt (selected A R H c p) R ⋏ eligible A H c p (selected A R H c p) := by
  have witness := ex_elim candidateBody h
  exact .andI (.andE₁ witness) (candidate_eligible _ _ _ _ _ (.impI (.impE (Prf.andE₂ witness).wk ((candidate_body_at _ _ _ _ _).wk.eqTrans Prf.hyp0))))
theorem witness_success (A R H c p r : PTm n) (hr : Γ ⊢[PRAAx] lt r R) (h : Γ ⊢[PRAAx] eligible A H c p r) : Γ ⊢[PRAAx] flag A R H c p ≐ one := by
  have one := (candidate_body_at A H c p r).eqTrans (candidate_one _ _ _ _ _ h)
  exact ex_intro candidateBody (.impI (succ_ne_zero (one.wk.eqSymm.eqTrans Prf.hyp0))) hr

theorem failed_unmarked_zero (A R H c p r : PTm n) (hf : Γ ⊢[PRAAx] flag A R H c p ≐ zero)
    (hr : Γ ⊢[PRAAx] lt r R) (hu : Γ ⊢[PRAAx] unmarked H c r) : Γ ⊢[PRAAx] pivot A r p ≐ qzero := by
  refine .orE (eq_or_ne (pivot A r p) qzero) Prf.hyp0 ?_
  exact .botE _ (succ_ne_zero ((witness_success _ _ _ _ _ _ hr.wk (.andI hu.wk Prf.hyp0)).eqSymm.eqTrans hf.wk))
theorem earlier_unmarked_zero (A R H c p r : PTm n) (hr : Γ ⊢[PRAAx] lt r (selected A R H c p))
    (hu : Γ ⊢[PRAAx] unmarked H c r) : Γ ⊢[PRAAx] pivot A r p ≐ qzero := by
  have no := ex_least candidateBody hr
  refine .orE (eq_or_ne (pivot A r p) qzero) Prf.hyp0 ?_
  have one := (candidate_body_at (Γ := neg (pivot A r p ≐ qzero) :: Γ) A H c p r).eqTrans
    (candidate_one _ _ _ _ _ (.andI hu.wk Prf.hyp0))
  exact .botE _ (succ_ne_zero (one.eqSymm.eqTrans no.wk))

theorem selected_default (A R H c p : PTm n) (hf : Γ ⊢[PRAAx] flag A R H c p ≐ zero) : Γ ⊢[PRAAx]
    selected A R H c p ≐ R := by
  refine .orE (lt_or_eq_of_le (selected_bound A R H c p)) ?_ Prf.hyp0
  have hit := Prf.impE (Prf.andE₁ (Prf.andE₂ (Search.search_spec (Γ := lt (selected A R H c p) R :: Γ)
    (f := Foundations.BoundedReflection.nB candidateBody) R zero (data A H c p)))) Prf.hyp0
  have ne : (lt (selected A R H c p) R) :: Γ ⊢[PRAAx] neg (inst2 candidateBody (selected A R H c p) (data A H c p) ≐ zero) :=
    Foundations.BoundedReflection.ne_of_compl (by simpa only [Foundations.BoundedReflection.inst2_nB,selected,Foundations.BoundedReflection.wit] using hit)
  exact .botE _ (succ_ne_zero ((ex_intro candidateBody ne Prf.hyp0).eqSymm.eqTrans hf.wk))
theorem selected_le_witness (A R H c p r : PTm n) (hu : Γ ⊢[PRAAx] eligible A H c p r) : Γ ⊢[PRAAx]
    le (selected A R H c p) r := by
  refine .orE (lt_or_le r (selected A R H c p)) ?_ Prf.hyp0
  exact .botE _ (.impE (Prf.andE₂ hu).wk (earlier_unmarked_zero _ _ _ _ _ _ Prf.hyp0 (Prf.andE₁ hu).wk))

def hasEligible (A R H c p : PTm n) : Fm PTm n := .ex
  (lt (var 0) (Syn.shift R) ⋏ eligible (Syn.shift A) (Syn.shift H) (Syn.shift c) (Syn.shift p) (var 0))
@[simp] theorem subst_hasEligible {k : ℕ} (σ : Fin n → PTm k) (A R H c p : PTm n) :
    (hasEligible A R H c p).subst σ = hasEligible (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ H) (Syn.subst σ c) (Syn.subst σ p) := by
  simp [hasEligible,Syn.subst_shift,Syn.shift_subst]
theorem success_exists (A R H c p : PTm n) (hf : Γ ⊢[PRAAx] flag A R H c p ≐ one) : Γ ⊢[PRAAx] hasEligible A R H c p := by
  refine .exI (selected A R H c p) ?_
  simpa only [hasEligible,Fm.subst_and,subst_lt,subst_eligible,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using selected_correct A R H c p hf
theorem exists_success (A R H c p : PTm n) (h : Γ ⊢[PRAAx] hasEligible A R H c p) : Γ ⊢[PRAAx] flag A R H c p ≐ one := by
  refine .exE h ?_
  simpa only [Fm.shift,Fm.subst_eq,subst_flag,Syn.shift,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    witness_success (Syn.shift A) (Syn.shift R) (Syn.shift H) (Syn.shift c) (Syn.shift p) (var 0) (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0)
theorem success_iff (A R H c p : PTm n) : Γ ⊢[PRAAx] Fm.iff (flag A R H c p ≐ one) (hasEligible A R H c p) :=
  .andI (.impI (success_exists _ _ _ _ _ Prf.hyp0)) (.impI (exists_success _ _ _ _ _ Prf.hyp0))
theorem available_empty (H r : PTm n) : Γ ⊢[PRAAx] available H zero r ≐ one := Foundations.BoundedReflection.allB_zero _ _
theorem no_rows (A H c p : PTm n) : Γ ⊢[PRAAx] flag A zero H c p ≐ zero := by
  refine .orE (flag_cases A zero H c p) Prf.hyp0 ?_
  exact .botE _ (lt_zero_absurd _ (.andE₁ (selected_correct _ _ _ _ _ Prf.hyp0)))

/-! The actual total successor uses the old matrix literally on failure.
Its semantic input is only original rectangular shape and p<N. -/
def next (A R N H c p : PTm n) : PTm n := sel (flag A R H c p) (eliminate A R N (selected A R H c p) p) A
def tag (A R H c p : PTm n) : PTm n := flag A R H c p*succ (selected A R H c p)
@[simp] theorem subst_next {k : ℕ} (σ : Fin n → PTm k) (A R N H c p : PTm n) :
    Syn.subst σ (next A R N H c p) = next (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ H) (Syn.subst σ c) (Syn.subst σ p) := by simp [next,sel]
@[simp] theorem subst_tag {k : ℕ} (σ : Fin n → PTm k) (A R H c p : PTm n) :
    Syn.subst σ (tag A R H c p) = tag (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ H) (Syn.subst σ c) (Syn.subst σ p) := by simp [tag]
theorem next_success (A R N H c p : PTm n) (hf : Γ ⊢[PRAAx] flag A R H c p ≐ one) : Γ ⊢[PRAAx]
    next A R N H c p ≐ eliminate A R N (selected A R H c p) p := sel_one hf
theorem next_failure (A R N H c p : PTm n) (hf : Γ ⊢[PRAAx] flag A R H c p ≐ zero) : Γ ⊢[PRAAx]
    next A R N H c p ≐ A := sel_zero hf
theorem tag_success (A R H c p : PTm n) (hf : Γ ⊢[PRAAx] flag A R H c p ≐ one) : Γ ⊢[PRAAx]
    tag A R H c p ≐ succ (selected A R H c p) := (congrMul hf (.eqRefl _)).eqTrans (one_mul _)
theorem tag_failure (A R H c p : PTm n) (hf : Γ ⊢[PRAAx] flag A R H c p ≐ zero) : Γ ⊢[PRAAx]
    tag A R H c p ≐ zero := (congrMul hf (.eqRefl _)).eqTrans (zero_mul _)
theorem selected_input (A R N H c p : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) (hp : Γ ⊢[PRAAx] lt p N)
    (hf : Γ ⊢[PRAAx] flag A R H c p ≐ one) : Γ ⊢[PRAAx]
    GaussianRationalRowElimination.input A R N (selected A R H c p) p :=
  .andI hA (.andI (.andE₁ (selected_correct _ _ _ _ _ hf)) (.andI hp (.andE₂ (.andE₂ (selected_correct _ _ _ _ _ hf)))))
theorem shape_congr {A B R N : PTm n} (e : Γ ⊢[PRAAx] A ≐ B) (h : Γ ⊢[PRAAx] shape A R N) : Γ ⊢[PRAAx] shape B R N := by
  simpa only [GaussianRationalRowElimination.subst_shape,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqSubst (shape (var 0) (var 1) (var 2) : Fm PTm 3) ![A,R,N] ![B,R,N]
      (fun i => by fin_cases i; exact e; exact .eqRefl _; exact .eqRefl _)
      (by simpa only [GaussianRationalRowElimination.subst_shape,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using h)
theorem next_shape (A R N H c p : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) : Γ ⊢[PRAAx] shape (next A R N H c p) R N := by
  refine .orE (flag_cases A R H c p) ?_ ?_
  · exact shape_congr (next_failure _ _ _ _ _ _ Prf.hyp0).eqSymm hA.wk
  · exact shape_congr (next_success _ _ _ _ _ _ Prf.hyp0).eqSymm (GaussianRationalRowElimination.output_shape _ _ _ _ _)
theorem next_pivot_one (A R N H c p : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) (hp : Γ ⊢[PRAAx] lt p N)
    (hf : Γ ⊢[PRAAx] flag A R H c p ≐ one) : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminantTerms.cell (next A R N H c p) (selected A R H c p) p ≐ GaussianRationalSyntheticDivision.qone :=
  (Foundations.SequenceComposition.entry_congr (Foundations.SequenceComposition.entry_congr (next_success _ _ _ _ _ _ hf) (.eqRefl _)) (.eqRefl _)).eqTrans
    (GaussianRationalRowElimination.output_pivot_one _ _ _ _ _ (selected_input _ _ _ _ _ _ hA hp hf))
theorem next_pivot_zero (A R N H c p r : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) (hp : Γ ⊢[PRAAx] lt p N)
    (hf : Γ ⊢[PRAAx] flag A R H c p ≐ one) (hr : Γ ⊢[PRAAx] lt r R)
    (hne : Γ ⊢[PRAAx] neg (r ≐ selected A R H c p)) : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminantTerms.cell (next A R N H c p) r p ≐ qzero :=
  (Foundations.SequenceComposition.entry_congr (Foundations.SequenceComposition.entry_congr (next_success _ _ _ _ _ _ hf) (.eqRefl _)) (.eqRefl _)).eqTrans
    (GaussianRationalRowElimination.output_pivot_zero _ _ _ _ _ _ (selected_input _ _ _ _ _ _ hA hp hf) hr hne)
theorem next_null_equivalence (A R N H c p l : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) (hp : Γ ⊢[PRAAx] lt p N) : Γ ⊢[PRAAx]
    Fm.iff (nullRows A R N l) (nullRows (next A R N H c p) R N l) := by
  refine .orE (flag_cases A R H c p) ?_ ?_
  · exact .andI (.impI (GaussianRationalRowElimination.null_rows_congr (next_failure _ _ _ _ _ _ Prf.hyp1).eqSymm Prf.hyp0))
      (.impI (GaussianRationalRowElimination.null_rows_congr (next_failure _ _ _ _ _ _ Prf.hyp1) Prf.hyp0))
  · have step := GaussianRationalRowElimination.null_equivalence A R N (selected A R H c p) p l
      (selected_input _ _ _ _ _ _ hA.wk hp.wk Prf.hyp0)
    exact .andI (.impI (GaussianRationalRowElimination.null_rows_congr (next_success _ _ _ _ _ _ Prf.hyp1).eqSymm (step.wk.iffMp Prf.hyp0)))
      (.impI (step.wk.iffMpr (GaussianRationalRowElimination.null_rows_congr (next_success _ _ _ _ _ _ Prf.hyp1) Prf.hyp0)))

/-! Actual output carries next table, history tag, success bit and least row.
The vector in the null-system endpoint is an independent numerical query. -/
def output (A R N H c p : PTm n) : PTm n := pairT (next A R N H c p)
  (pairT (tag A R H c p) (pairT (flag A R H c p) (selected A R H c p)))
def outputF : PR 6 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (A R N H c p : PTm n) : PTm n := app outputF ![A,R,N,H,c,p]
@[simp] theorem subst_output {k : ℕ} (σ : Fin n → PTm k) (A R N H c p : PTm n) :
    Syn.subst σ (output A R N H c p) = output (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ H) (Syn.subst σ c) (Syn.subst σ p) := by simp [output]
@[simp] theorem subst_run {k : ℕ} (σ : Fin n → PTm k) (A R N H c p : PTm n) :
    Syn.subst σ (run A R N H c p) = run (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ H) (Syn.subst σ c) (Syn.subst σ p) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
theorem program_at (A R N H c p : PTm n) : Γ ⊢[PRAAx] run A R N H c p ≐ output A R N H c p := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![A,R,N,H,c,p]
theorem returned_fields (A R N H c p : PTm n) (i : Fin 4) : Γ ⊢[PRAAx]
    fields (run A R N H c p) i ≐ ![next A R N H c p,tag A R H c p,flag A R H c p,selected A R H c p] i := by
  have e0 := program_at (Γ := Γ) A R N H c p
  have e1 := (congrSnd e0).eqTrans (snd_pair _ _)
  have e2 := (congrSnd e1).eqTrans (snd_pair _ _)
  fin_cases i
  · exact (congrFst e0).eqTrans (fst_pair _ _)
  · exact (congrFst e1).eqTrans (fst_pair _ _)
  · exact (congrFst e2).eqTrans (fst_pair _ _)
  · exact (congrSnd e2).eqTrans (snd_pair _ _)
theorem returned_shape (A R N H c p : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) : Γ ⊢[PRAAx]
    shape (fields (run A R N H c p) 0) R N := shape_congr (returned_fields _ _ _ _ _ _ 0).eqSymm (next_shape _ _ _ _ _ _ hA)
theorem returned_null_equivalence (A R N H c p l : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (hp : Γ ⊢[PRAAx] lt p N) : Γ ⊢[PRAAx]
    Fm.iff (nullRows A R N l) (nullRows (fields (run A R N H c p) 0) R N l) := by
  have step := next_null_equivalence A R N H c p l hA hp
  exact .andI (.impI (GaussianRationalRowElimination.null_rows_congr (returned_fields _ _ _ _ _ _ 0).wk.eqSymm (step.wk.iffMp Prf.hyp0)))
    (.impI (step.wk.iffMpr (GaussianRationalRowElimination.null_rows_congr (returned_fields _ _ _ _ _ _ 0).wk Prf.hyp0)))

theorem actual_unmarked_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (Fm.iff (available (var 0) (var 1) (var 2) ≐ one) (unmarked (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.andI (.impI (available_unmarked _ _ _ Prf.hyp0)) (.impI (unmarked_available _ _ _ Prf.hyp0)))
theorem actual_search_success_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (flag (var 0) (var 1) (var 2) (var 3) (var 4) ≐ one ⟶
      (lt (selected (var 0) (var 1) (var 2) (var 3) (var 4)) (var 1) ⋏
        eligible (var 0) (var 2) (var 3) (var 4) (selected (var 0) (var 1) (var 2) (var 3) (var 4)))) :=
  closeUniv 5 (.impI (selected_correct _ _ _ _ _ Prf.hyp0))
theorem actual_search_exact_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (Fm.iff (flag (var 0) (var 1) (var 2) (var 3) (var 4) ≐ one) (hasEligible (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (success_iff _ _ _ _ _)
theorem actual_search_default_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (flag (var 0) (var 1) (var 2) (var 3) (var 4) ≐ zero ⟶
      selected (var 0) (var 1) (var 2) (var 3) (var 4) ≐ var 1) :=
  closeUniv 5 (.impI (selected_default _ _ _ _ _ Prf.hyp0))
theorem actual_search_failure_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (flag (var 0) (var 1) (var 2) (var 3) (var 4) ≐ zero ⟶ lt (var 5) (var 1) ⟶
      unmarked (var 2) (var 3) (var 5) ⟶ pivot (var 0) (var 5) (var 4) ≐ qzero) :=
  closeUniv 6 (.impI (.impI (.impI (failed_unmarked_zero _ _ _ _ _ _ (Prf.hyp (by simp)) Prf.hyp1 Prf.hyp0))))
theorem actual_search_least_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 5) (selected (var 0) (var 1) (var 2) (var 3) (var 4)) ⟶
      unmarked (var 2) (var 3) (var 5) ⟶ pivot (var 0) (var 5) (var 4) ≐ qzero) :=
  closeUniv 6 (.impI (.impI (earlier_unmarked_zero _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_selected_input_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (shape (var 0) (var 1) (var 2) ⟶ lt (var 5) (var 2) ⟶
      flag (var 0) (var 1) (var 3) (var 4) (var 5) ≐ one ⟶
        GaussianRationalRowElimination.input (var 0) (var 1) (var 2)
          (selected (var 0) (var 1) (var 3) (var 4) (var 5)) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (selected_input _ _ _ _ _ _ (Prf.hyp (by simp)) Prf.hyp1 Prf.hyp0))))
theorem actual_next_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (shape (var 0) (var 1) (var 2) ⟶ shape (next (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 1) (var 2)) :=
  closeUniv 6 (.impI (next_shape _ _ _ _ _ _ Prf.hyp0))
theorem actual_next_pivot_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (shape (var 0) (var 1) (var 2) ⟶ lt (var 5) (var 2) ⟶
      flag (var 0) (var 1) (var 3) (var 4) (var 5) ≐ one ⟶
        GaussianPolynomialDeterminantTerms.cell (next (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
          (selected (var 0) (var 1) (var 3) (var 4) (var 5)) (var 5) ≐ GaussianRationalSyntheticDivision.qone) :=
  closeUniv 6 (.impI (.impI (.impI (next_pivot_one _ _ _ _ _ _ (Prf.hyp (by simp)) Prf.hyp1 Prf.hyp0))))
theorem actual_next_null_transport_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (shape (var 0) (var 1) (var 2) ⟶ lt (var 5) (var 2) ⟶
      Fm.iff (nullRows (var 0) (var 1) (var 2) (var 6))
        (nullRows (next (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 1) (var 2) (var 6))) :=
  closeUniv 7 (.impI (.impI (next_null_equivalence _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_empty_history_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (available (var 0) zero (var 1) ≐ one) := closeUniv 2 (available_empty _ _)
theorem actual_empty_rows_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (flag (var 0) zero (var 1) (var 2) (var 3) ≐ zero) := closeUniv 4 (no_rows _ _ _ _)
theorem actual_skip_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (flag (var 0) (var 1) (var 3) (var 4) (var 5) ≐ zero ⟶
      ((next (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ var 0) ⋏
        (tag (var 0) (var 1) (var 3) (var 4) (var 5) ≐ zero))) :=
  closeUniv 6 (.impI (.andI (next_failure _ _ _ _ _ _ Prf.hyp0) (tag_failure _ _ _ _ _ Prf.hyp0)))
theorem actual_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (program_at _ _ _ _ _ _)
theorem actual_returned_null_transport_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (shape (var 0) (var 1) (var 2) ⟶ lt (var 5) (var 2) ⟶
      Fm.iff (nullRows (var 0) (var 1) (var 2) (var 6))
        (nullRows (fields (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) 0) (var 1) (var 2) (var 6))) :=
  closeUniv 7 (.impI (.impI (returned_null_equivalence _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalPivotSearch
