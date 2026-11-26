import IPRADerivations.Analysis.LinearAlgebra.Matrices.GaussianRationalMatrixFiniteSums
import IPRADerivations.Foundations.FilteredEnumerationCode

/-!
# Actual Gaussian block sums and the same bounded retained scan

Every sum is the existing sequence/Horner Gaussian fold. The block law is
proved from its genuine split. The filtering proof fixes the ORIGINAL
selector cutoff and inducts only over the processed prefix, using the
actual rank/sel inverse at each retained entry. No global range, desired
filter law or canonical original entry is assumed. Counts, cutoffs and
the independent selector and entry data are all numerical.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalBlockSums

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qadd canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qadd_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalFiniteSum (sum sum_canonical sum_index_congr)
open LeanProofs.IPRA.Foundations.FilteredEnumeration (rank sel rank_zero rank_succ sel_rank)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def blockBody (f : PTm 2) : PTm 2 := sum (offB f) (fstT (var 1))
  (pairT (fstT (var 1)*var 0) (sndT (var 1)))
def blockTotal (f : PTm 2) (B K x : PTm n) : PTm n := sum (blockBody f) K (pairT B x)
@[simp] theorem subst_blockTotal {l : ℕ} (σ : Fin n → PTm l) (f : PTm 2) (B K x : PTm n) :
    Syn.subst σ (blockTotal f B K x) = blockTotal f (Syn.subst σ B) (Syn.subst σ K) (Syn.subst σ x) := by simp [blockTotal]

theorem block_body_at (f : PTm 2) (B i x : PTm n) : Γ ⊢[PRAAx]
    inst2 (blockBody f) i (pairT B x) ≐ sum (offB f) B (pairT (B*i) x) := by
  simp only [blockBody,inst2,GaussianRationalFiniteSum.subst_sum,subst_pairT,PTm.subst_mul,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact sum_index_congr _ (fst_pair _ _)
    (congrPairT (congrMul (fst_pair _ _) (.eqRefl _)) (snd_pair _ _))

def blockLaw (f : PTm 2) (B K x : PTm n) : Fm PTm n := sum f (B*K) x ≐ blockTotal f B K x
@[simp] theorem subst_blockLaw {l : ℕ} (σ : Fin n → PTm l) (f : PTm 2) (B K x : PTm n) :
    (blockLaw f B K x).subst σ = blockLaw f (Syn.subst σ B) (Syn.subst σ K) (Syn.subst σ x) := by simp [blockLaw]

theorem block_zero (f : PTm 2) (B x : PTm n) : Γ ⊢[PRAAx] blockLaw f B zero x :=
  (sum_index_congr f (mul_zero B) (.eqRefl _)).eqTrans
    ((GaussianRationalFiniteSum.sum_zero _ _).eqTrans (GaussianRationalFiniteSum.sum_zero _ _).eqSymm)
theorem block_step (f : PTm 2) (B K x : PTm n) (ih : Γ ⊢[PRAAx] blockLaw f B K x) : Γ ⊢[PRAAx]
    blockLaw f B (succ K) x :=
  (sum_index_congr f (by ipra_ring : Γ ⊢[PRAAx] B*succ K ≐ B*K+B) (.eqRefl _)).eqTrans
    ((GaussianRationalMatrixFiniteSums.sum_split f (B*K) B x).eqTrans
      ((qadd_congr ih (block_body_at f B K x).eqSymm).eqTrans (GaussianRationalFiniteSum.sum_succ (blockBody f) K (pairT B x)).eqSymm))

theorem sum_blocks (f : PTm 2) (B K x : PTm n) : Γ ⊢[PRAAx]
    sum f (B*K) x ≐ blockTotal f B K x := by
  have all : Γ ⊢[PRAAx] .all (blockLaw f (Syn.shift B) (var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_blockLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact block_zero f B x
    · simp only [subst_blockLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact block_step f _ _ _ Prf.hyp0
  have result : Γ ⊢[PRAAx] blockLaw f B K x := by
    simpa only [subst_blockLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE K
  exact result

/-- The global cutoff P stays fixed; p and x are independent numerical data. -/
def filteredData (P p x : PTm n) : PTm n := pairT P (pairT p x)
def selectedBody (K f : PTm 2) : PTm 2 := inst2 f
  (sel K (var 0) (fstT (var 1)) (fstT (sndT (var 1)))) (sndT (sndT (var 1)))
def maskBody (K f : PTm 2) : PTm 2 := RationalArithmetic.select
  (Signum.sg (inst2 K (var 0) (fstT (var 1)))) qzero (inst2 f (var 0) (sndT (var 1)))
def selectedPrefix (K f : PTm 2) (P p x u : PTm n) : PTm n := sum (selectedBody K f) (rank K u p) (filteredData P p x)
def maskedPrefix (K f : PTm 2) (p x u : PTm n) : PTm n := sum (maskBody K f) u (pairT p x)
@[simp] theorem subst_filteredData {l : ℕ} (σ : Fin n → PTm l) (P p x : PTm n) :
    Syn.subst σ (filteredData P p x) = filteredData (Syn.subst σ P) (Syn.subst σ p) (Syn.subst σ x) := by simp [filteredData]
@[simp] theorem subst_selectedPrefix {l : ℕ} (σ : Fin n → PTm l) (K f : PTm 2) (P p x u : PTm n) :
    Syn.subst σ (selectedPrefix K f P p x u) = selectedPrefix K f (Syn.subst σ P) (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ u) := by
  simp [selectedPrefix,rank]
@[simp] theorem subst_maskedPrefix {l : ℕ} (σ : Fin n → PTm l) (K f : PTm 2) (p x u : PTm n) :
    Syn.subst σ (maskedPrefix K f p x u) = maskedPrefix K f (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ u) := by simp [maskedPrefix]

@[simp] theorem selected_entry (K f : PTm 2) (r y : PTm n) :
    inst2 (selectedBody K f) r y = inst2 f (sel K r (fstT y) (fstT (sndT y))) (sndT (sndT y)) := by
  simp only [selectedBody,inst2,Syn.subst_subst]
  congr 1
  funext i
  fin_cases i <;> simp [Foundations.FilteredEnumerationCode.subst_sel]

theorem selected_body_at (K f : PTm 2) (P p x r : PTm n) : Γ ⊢[PRAAx]
    inst2 (selectedBody K f) r (filteredData P p x) ≐ inst2 f (sel K r P p) x := by
  rw [selected_entry]
  exact congrInst2 f
    (Foundations.FilteredEnumerationCode.sel_congr K (.eqRefl _) (fst_pair _ _)
      ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)))
    ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))

@[simp] theorem mask_entry (K f : PTm 2) (i y : PTm n) :
    inst2 (maskBody K f) i y = RationalArithmetic.select (Signum.sg (inst2 K i (fstT y))) qzero (inst2 f i (sndT y)) := by
  have ks : Syn.subst ![i,y] (inst2 K (var 0) (fstT (var 1))) = inst2 K i (fstT y) := by
    simp only [inst2,Syn.subst_subst]
    congr 1
    funext j
    fin_cases j <;> simp
  have fs : Syn.subst ![i,y] (inst2 f (var 0) (sndT (var 1))) = inst2 f i (sndT y) := by
    simp only [inst2,Syn.subst_subst]
    congr 1
    funext j
    fin_cases j <;> simp
  change Syn.subst ![i,y] (RationalArithmetic.select (Signum.sg (inst2 K (var 0) (fstT (var 1)))) qzero
    (inst2 f (var 0) (sndT (var 1)))) = _
  simp only [RationalArithmetic.subst_select,Signum.sg,PTm.subst_monus,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,GaussianRationalHorner.subst_qzero,ks,fs]

theorem mask_body_at (K f : PTm 2) (p x i : PTm n) : Γ ⊢[PRAAx]
    inst2 (maskBody K f) i (pairT p x) ≐ RationalArithmetic.select (Signum.sg (inst2 K i p)) qzero (inst2 f i x) := by
  rw [mask_entry]
  exact GaussianRationalMonicReconstruction.select_congr
    (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (congrInst2 K (.eqRefl _) (fst_pair _ _)))) (.eqRefl _)
    (congrInst2 f (.eqRefl _) (snd_pair _ _))
theorem mask_zero (K f : PTm 2) (p x i : PTm n) (h : Γ ⊢[PRAAx] inst2 K i p ≐ zero) : Γ ⊢[PRAAx]
    inst2 (maskBody K f) i (pairT p x) ≐ qzero :=
  (mask_body_at _ _ _ _ _).eqTrans
    (RationalArithmetic.select_zero _ _ _ (Foundations.BoundedFormulas.sg_of_zero h))
theorem mask_kept (K f : PTm 2) (p x i : PTm n) (h : Γ ⊢[PRAAx] neg (inst2 K i p ≐ zero)) : Γ ⊢[PRAAx]
    inst2 (maskBody K f) i (pairT p x) ≐ inst2 f i x :=
  (mask_body_at _ _ _ _ _).eqTrans
    (RationalArithmetic.select_one _ _ _ (Foundations.FiniteGluing.sg_of_ne h))

def filterLaw (K f : PTm 2) (P p x u : PTm n) : Fm PTm n :=
  le u P ⟶ selectedPrefix K f P p x u ≐ maskedPrefix K f p x u
@[simp] theorem subst_filterLaw {l : ℕ} (σ : Fin n → PTm l) (K f : PTm 2) (P p x u : PTm n) :
    (filterLaw K f P p x u).subst σ = filterLaw K f (Syn.subst σ P) (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ u) := by simp [filterLaw]

theorem filter_zero (K f : PTm 2) (P p x : PTm n) : Γ ⊢[PRAAx]
    selectedPrefix K f P p x zero ≐ maskedPrefix K f p x zero :=
  (sum_index_congr _ (rank_zero _ _) (.eqRefl _)).eqTrans
    ((GaussianRationalFiniteSum.sum_zero _ _).eqTrans (GaussianRationalFiniteSum.sum_zero _ _).eqSymm)

theorem filter_step (K f : PTm 2) (P p x u : PTm n) (hu : Γ ⊢[PRAAx] lt u P)
    (ih : Γ ⊢[PRAAx] selectedPrefix K f P p x u ≐ maskedPrefix K f p x u) : Γ ⊢[PRAAx]
    selectedPrefix K f P p x (succ u) ≐ maskedPrefix K f p x (succ u) := by
  refine .orE (eq_or_ne (inst2 K u p) zero) ?_ ?_
  · have r : (inst2 K u p ≐ zero) :: Γ ⊢[PRAAx] rank K (succ u) p ≐ rank K u p :=
      (rank_succ _ _ _).eqTrans ((congrAdd (.eqRefl _) (Foundations.BoundedFormulas.sg_of_zero Prf.hyp0)).eqTrans (add_zero _))
    exact (sum_index_congr _ r (.eqRefl _)).eqTrans
      (ih.wk.eqTrans ((GaussianRationalFiniteSum.sum_succ _ _ _).eqTrans
        ((qadd_congr (.eqRefl _) (mask_zero _ _ _ _ _ Prf.hyp0)).eqTrans
          (GaussianReciprocalHorner.qadd_zero_right _ (sum_canonical _ _ _)))).eqSymm)
  · have r : neg (inst2 K u p ≐ zero) :: Γ ⊢[PRAAx] rank K (succ u) p ≐ succ (rank K u p) :=
      (rank_succ _ _ _).eqTrans ((congrAdd (.eqRefl _) (Foundations.FiniteGluing.sg_of_ne Prf.hyp0)).eqTrans (succ_eq_add_one _).eqSymm)
    exact (sum_index_congr _ r (.eqRefl _)).eqTrans
      ((GaussianRationalFiniteSum.sum_succ _ _ _).eqTrans
        ((qadd_congr ih.wk ((selected_body_at _ _ _ _ _ _).eqTrans
          (congrInst2 f (sel_rank K hu.wk Prf.hyp0) (.eqRefl _)))).eqTrans
            ((GaussianRationalFiniteSum.sum_succ _ _ _).eqTrans
              (qadd_congr (.eqRefl _) (mask_kept _ _ _ _ _ Prf.hyp0))).eqSymm))

theorem filter_prefix (K f : PTm 2) (P p x u : PTm n) (hu : Γ ⊢[PRAAx] le u P) : Γ ⊢[PRAAx]
    selectedPrefix K f P p x u ≐ maskedPrefix K f p x u := by
  have all : Γ ⊢[PRAAx] .all (filterLaw K f (Syn.shift P) (Syn.shift p) (Syn.shift x) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_filterLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (filter_zero _ _ _ _ _)
    · simp only [subst_filterLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact .impI (filter_step _ _ _ _ _ _ Prf.hyp0 (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)))
  have rule : Γ ⊢[PRAAx] filterLaw K f P p x u := by
    simpa only [subst_filterLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE u
  exact .impE rule hu

theorem filtered_sum (K f : PTm 2) (P p x : PTm n) : Γ ⊢[PRAAx]
    sum (selectedBody K f) (rank K P p) (filteredData P p x) ≐ sum (maskBody K f) P (pairT p x) :=
  filter_prefix K f P p x P (le_refl _)

theorem selected_list_at (K f : PTm 2) (P p x r : PTm n) (hr : Γ ⊢[PRAAx] lt r (rank K P p)) : Γ ⊢[PRAAx]
    inst2 (selectedBody K f) r (filteredData P p x) ≐
      inst2 f (Foundations.MasterCertificate.entry (Foundations.FilteredEnumerationCode.list K P p) r) x :=
  (selected_body_at _ _ _ _ _ _).eqTrans
    (congrInst2 f (Foundations.FilteredEnumerationCode.list_lookup K P p r hr).eqSymm (.eqRefl _))

/-- Both sums, the SAME retained list and its actual count are returned. -/
def output (K f : PTm 2) (P p x : PTm n) : PTm n := pairT
  (selectedPrefix K f P p x P) (pairT (maskedPrefix K f p x P)
    (pairT (Foundations.FilteredEnumerationCode.list K P p) (rank K P p)))
def outputF (K f : PTm 2) : PR 3 := PTm.toPR (output K f (var 0) (var 1) (var 2))
def run (K f : PTm 2) (P p x : PTm n) : PTm n := ap3 (outputF K f) P p x
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (K f : PTm 2) (P p x : PTm n) :
    Syn.subst σ (output K f P p x) = output K f (Syn.subst σ P) (Syn.subst σ p) (Syn.subst σ x) := by simp [output,rank]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (K f : PTm 2) (P p x : PTm n) :
    Syn.subst σ (run K f P p x) = run K f (Syn.subst σ P) (Syn.subst σ p) (Syn.subst σ x) := by simp [run]
theorem program_at (K f : PTm 2) (P p x : PTm n) : Γ ⊢[PRAAx] run K f P p x ≐ output K f P p x := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output K f (var 0) (var 1) (var 2) : PTm 3) ![P,p,x]
theorem returned_selected (K f : PTm 2) (P p x : PTm n) : Γ ⊢[PRAAx]
    fstT (run K f P p x) ≐ selectedPrefix K f P p x P :=
  (congrFst (program_at _ _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_masked (K f : PTm 2) (P p x : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run K f P p x)) ≐ maskedPrefix K f p x P :=
  (congrFst ((congrSnd (program_at _ _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_list (K f : PTm 2) (P p x : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run K f P p x))) ≐ Foundations.FilteredEnumerationCode.list K P p :=
  (congrFst ((congrSnd ((congrSnd (program_at _ _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_count (K f : PTm 2) (P p x : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run K f P p x))) ≐ rank K P p :=
  (congrSnd ((congrSnd ((congrSnd (program_at _ _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_equal (K f : PTm 2) (P p x : PTm n) : Γ ⊢[PRAAx]
    fstT (run K f P p x) ≐ fstT (sndT (run K f P p x)) :=
  (returned_selected _ _ _ _ _).eqTrans ((filtered_sum _ _ _ _ _).eqTrans (returned_masked _ _ _ _ _).eqSymm)

theorem actual_block_flatten_closed (f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (sum f (var 0*var 1) (var 2) ≐ blockTotal f (var 0) (var 1) (var 2)) := closeUniv 3 (sum_blocks _ _ _ _)
theorem actual_filtered_prefix_closed (K f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (var 0) ⟶ selectedPrefix K f (var 0) (var 1) (var 2) (var 3) ≐ maskedPrefix K f (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (filter_prefix _ _ _ _ _ _ Prf.hyp0))
theorem actual_filtered_sum_closed (K f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (sum (selectedBody K f) (rank K (var 0) (var 1)) (filteredData (var 0) (var 1) (var 2)) ≐
      sum (maskBody K f) (var 0) (pairT (var 1) (var 2))) := closeUniv 3 (filtered_sum _ _ _ _ _)
theorem actual_selected_list_entry_closed (K f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (rank K (var 0) (var 1)) ⟶ inst2 (selectedBody K f) (var 3) (filteredData (var 0) (var 1) (var 2)) ≐
      inst2 f (Foundations.MasterCertificate.entry (Foundations.FilteredEnumerationCode.list K (var 0) (var 1)) (var 3)) (var 2)) :=
  closeUniv 4 (.impI (selected_list_at _ _ _ _ _ _ Prf.hyp0))
theorem actual_filter_program_closed (K f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((run K f (var 0) (var 1) (var 2) ≐ output K f (var 0) (var 1) (var 2)) ⋏
      (sndT (sndT (sndT (run K f (var 0) (var 1) (var 2)))) ≐ rank K (var 0) (var 1))) :=
  closeUniv 3 (.andI (program_at _ _ _ _ _) (returned_count _ _ _ _ _))
theorem actual_returned_filter_equality_closed (K f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (fstT (run K f (var 0) (var 1) (var 2)) ≐ fstT (sndT (run K f (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (returned_equal _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalBlockSums
