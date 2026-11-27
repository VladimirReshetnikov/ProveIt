import IPRADerivations.Analysis.Polynomials.RootFinding.Reconstruction.GaussianRationalMonicReconstruction
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.Reindexing.GaussianRationalFubini

/-!
# Reindexing actual Gaussian-rational finite sums

All bounds, indices and data are numerical. Raw entries are normalized under
actual field addition; no raw code is identified with its canonical value.
Weighted delta and incidence sums, followed by genuine Gaussian Fubini,
derive reindexing from bounded local range and inverse facts, including N=0.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalPermutationSum

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qadd canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qadd_congr)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant (recode recode_canonical recode_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalMonicReconstruction
  (spike spike_congr spike_hit spike_miss spikeBody spikeData spikeSum
    spike_body_at spike_sum active active_on active_off)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def recodeBody (t : PTm 2) : PTm 2 := recode t
@[simp] theorem inst2_recodeBody (t : PTm 2) (i x : PTm n) :
    inst2 (recodeBody t) i x = recode (inst2 t i x) := by simp [inst2,recodeBody]

def recodingLaw (t : PTm 2) (N x : PTm n) : Fm PTm n :=
  GaussianRationalFiniteSum.sum (recodeBody t) N x ≐ GaussianRationalFiniteSum.sum t N x
ipra_subst recodingLaw

/-- Recoding every original entry leaves the actual canonical sum unchanged. -/
theorem sum_recode (t : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.sum (recodeBody t) N x ≐ GaussianRationalFiniteSum.sum t N x := by
  have all : Γ ⊢[PRAAx] .all (recodingLaw t (var 0) (Syn.shift x)) := by
    ipra_qfind [subst_recodingLaw]
    · exact (GaussianRationalFiniteSum.sum_zero _ _).eqTrans (GaussianRationalFiniteSum.sum_zero _ _).eqSymm
    · have step := GaussianRationalFiniteSum.sum_succ (Γ := recodingLaw t (var 0) (Syn.shift x) :: Γ.map Fm.shift)
        (recodeBody t) (var 0) (Syn.shift x)
      rw [inst2_recodeBody] at step
      exact step.eqTrans ((qadd_congr Prf.hyp0 (.eqRefl _)).eqTrans
        ((GaussianRationalSyntheticCoefficientValues.qadd_recode_right _ _).eqTrans
          (GaussianRationalFiniteSum.sum_succ t _ _).eqSymm))
  have result : Γ ⊢[PRAAx] recodingLaw t N x := by
    simpa only [subst_recodingLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N
  exact result

def deltaBody (t : PTm 2) : PTm 2 :=
  spike (fstT (var 1)) (recode (inst2 t (var 0) (sndT (var 1)))) (var 0)
def deltaSum (t : PTm 2) (N k x : PTm n) : PTm n := GaussianRationalFiniteSum.sum (deltaBody t) N (pairT k x)
ipra_subst deltaSum

theorem delta_body_at (t : PTm 2) (k i x : PTm n) : Γ ⊢[PRAAx]
    inst2 (deltaBody t) i (pairT k x) ≐ spike k (recode (inst2 t i x)) i := by
  have e : Syn.subst ![i,pairT k x] (Syn.subst ![var 0,sndT (var 1)] t) =
      inst2 t i (sndT (pairT k x)) := by
    simp only [inst2,Syn.subst_subst]
    congr 1
    funext j
    fin_cases j <;> simp
  simp only [deltaBody,inst2,GaussianRationalMonicReconstruction.subst_spike,
    GaussianTranslatedNonconstant.subst_recode,subst_inst2,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,e]
  exact spike_congr (fst_pair _ _) (recode_congr (congrInst2 t (.eqRefl _) (snd_pair _ _))) (.eqRefl _)

theorem delta_value_at (t : PTm 2) (k i x : PTm n) : Γ ⊢[PRAAx]
    spike k (recode (inst2 t i x)) i ≐ spike k (recode (inst2 t k x)) i := by
  refine .orE (eq_or_ne i k) ?_ ?_
  · exact spike_congr (.eqRefl _) (recode_congr (congrInst2 t Prf.hyp0 (.eqRefl _))) (.eqRefl _)
  · exact (spike_miss _ _ _ Prf.hyp0).eqTrans (spike_miss _ _ _ Prf.hyp0).eqSymm

theorem delta_as_spike (t : PTm 2) (N k x : PTm n) : Γ ⊢[PRAAx]
    deltaSum t N k x ≐ spikeSum k (recode (inst2 t k x)) N := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_pairT,GaussianRationalMonicReconstruction.subst_spikeData,
    GaussianTranslatedNonconstant.subst_recode,subst_inst2] using
    (delta_body_at (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) t (Syn.shift k) (var 0) (Syn.shift x)).eqTrans
      ((delta_value_at t (Syn.shift k) (var 0) (Syn.shift x)).eqTrans
        (spike_body_at (Syn.shift k) (recode (inst2 t (Syn.shift k) (Syn.shift x))) (var 0)).eqSymm)

theorem delta_sum (t : PTm 2) (N k x : PTm n) : Γ ⊢[PRAAx]
    deltaSum t N k x ≐ active k (recode (inst2 t k x)) N :=
  (delta_as_spike _ _ _ _).eqTrans (spike_sum _ _ _ (recode_canonical _))
theorem delta_selected (t : PTm 2) (N k x : PTm n) (hk : Γ ⊢[PRAAx] lt k N) : Γ ⊢[PRAAx]
    deltaSum t N k x ≐ recode (inst2 t k x) := (delta_sum _ _ _ _).eqTrans (active_on _ _ _ hk)
theorem delta_outside (t : PTm 2) (N k x : PTm n) (hk : Γ ⊢[PRAAx] le N k) : Γ ⊢[PRAAx]
    deltaSum t N k x ≐ qzero := (delta_sum _ _ _ _).eqTrans (active_off _ _ _ hk)

/-! The local domain contracts quantify only indices below the actual bound.
No global range assumption is needed, and the empty domain is allowed. -/
def boundedRange (p : PTm 2) (N x : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift N) ⟶ lt (inst2 p (var 0) (Syn.shift x)) (Syn.shift N))
def inverseLaw (p q : PTm 2) (N x : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift N) ⟶ inst2 q (inst2 p (var 0) (Syn.shift x)) (Syn.shift x) ≐ var 0)
ipra_subst boundedRange [Syn.subst_shift, Syn.shift_subst]
ipra_subst inverseLaw [Syn.subst_shift, Syn.shift_subst]
theorem range_at (p : PTm 2) (N x i : PTm n) (h : Γ ⊢[PRAAx] boundedRange p N x)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx] lt (inst2 p i x) N := by
  have gate : Γ ⊢[PRAAx] lt i N ⟶ lt (inst2 p i x) N := by simpa [boundedRange] using h.allE i
  exact .impE gate hi
theorem inverse_at (p q : PTm 2) (N x i : PTm n) (h : Γ ⊢[PRAAx] inverseLaw p q N x)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx] inst2 q (inst2 p i x) x ≐ i := by
  have gate : Γ ⊢[PRAAx] lt i N ⟶ inst2 q (inst2 p i x) x ≐ i := by simpa [inverseLaw] using h.allE i
  exact .impE gate hi

def mappedBody (t p : PTm 2) : PTm 2 := inst2 t (inst2 p (var 0) (var 1)) (var 1)
@[simp] theorem inst2_mappedBody (t p : PTm 2) (i x : PTm n) :
    inst2 (mappedBody t p) i x = inst2 t (inst2 p i x) x := by
  simp only [mappedBody,inst2,Syn.subst_subst]
  congr 1
  funext k
  fin_cases k <;> simp
  simp only [Syn.subst_subst]
  congr 1
  funext l
  fin_cases l <;> rfl

/-- A genuine numerical matrix whose row selects the image of that row. -/
def incidenceBody (t p : PTm 2) : PTm 3 :=
  spike (inst2 p (var 0) (var 2)) (recode (inst2 t (var 0) (var 2))) (var 1)
@[simp] theorem inst3_incidenceBody (t p : PTm 2) (i j x : PTm n) :
    inst3 (incidenceBody t p) i j x = spike (inst2 p i x) (recode (inst2 t i x)) j := by
  simp [inst3,incidenceBody]

theorem incidence_unique (t p q : PTm 2) (N x i j : PTm n)
    (hL : Γ ⊢[PRAAx] inverseLaw p q N x) (hR : Γ ⊢[PRAAx] inverseLaw q p N x)
    (hi : Γ ⊢[PRAAx] lt i N) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    spike (inst2 p i x) (recode (inst2 t i x)) j ≐
      spike (inst2 q j x) (recode (inst2 t (inst2 q j x) x)) i := by
  refine .orE (eq_or_ne i (inst2 q j x)) ?_ ?_
  · have image : (i ≐ inst2 q j x) :: Γ ⊢[PRAAx] inst2 p i x ≐ j :=
      (congrInst2 p Prf.hyp0 (.eqRefl _)).eqTrans (inverse_at q p N x j hR hj).wk
    exact (spike_hit _ _ _ image.eqSymm).eqTrans
      ((recode_congr (congrInst2 t Prf.hyp0 (.eqRefl _))).eqTrans
        (spike_hit _ _ _ Prf.hyp0).eqSymm)
  · have miss : neg (i ≐ inst2 q j x) :: Γ ⊢[PRAAx] neg (j ≐ inst2 p i x) := by
      refine .impI (.impE Prf.hyp1 ?_)
      exact (inverse_at p q N x i hL hi).wk.wk.eqSymm.eqTrans
        (congrInst2 q Prf.hyp0.eqSymm (.eqRefl _))
    exact (spike_miss _ _ _ miss).eqTrans (spike_miss _ _ _ Prf.hyp0).eqSymm

theorem incidence_row (t p : PTm 2) (N x i : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFubini.row (incidenceBody t p) i N x ≐
      spikeSum (inst2 p i x) (recode (inst2 t i x)) N := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  have entry := GaussianRationalFubini.row_entry
    (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) (incidenceBody t p) (Syn.shift i) (var 0) (Syn.shift x)
  rw [inst3_incidenceBody] at entry
  simpa only [Syn.shift,subst_pairT,GaussianRationalMonicReconstruction.subst_spikeData,
    GaussianTranslatedNonconstant.subst_recode,subst_inst2] using entry.eqTrans
      (spike_body_at (inst2 p (Syn.shift i) (Syn.shift x)) (recode (inst2 t (Syn.shift i) (Syn.shift x))) (var 0)).eqSymm

theorem incidence_row_selected (t p : PTm 2) (N x i : PTm n)
    (hr : Γ ⊢[PRAAx] boundedRange p N x) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    GaussianRationalFubini.row (incidenceBody t p) i N x ≐ recode (inst2 t i x) :=
  (incidence_row _ _ _ _ _).eqTrans
    ((spike_sum _ _ _ (recode_canonical _)).eqTrans (active_on _ _ _ (range_at p N x i hr hi)))

theorem incidence_column (t p q : PTm 2) (N x j : PTm n)
    (hL : Γ ⊢[PRAAx] inverseLaw p q N x) (hR : Γ ⊢[PRAAx] inverseLaw q p N x)
    (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    GaussianRationalFubini.column (incidenceBody t p) j N x ≐
      spikeSum (inst2 q j x) (recode (inst2 t (inst2 q j x) x)) N := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  have ls : Γ.map Fm.shift ⊢[PRAAx] inverseLaw p q (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,subst_inverseLaw,Syn.shift] using hL.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] inverseLaw q p (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,subst_inverseLaw,Syn.shift] using hR.shift
  have js : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (Syn.shift N) := by
    simpa only [Fm.shift,subst_lt,Syn.shift] using hj.shift
  have entry := GaussianRationalFubini.column_entry
    (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) (incidenceBody t p) (var 0) (Syn.shift j) (Syn.shift x)
  rw [inst3_incidenceBody] at entry
  simpa only [Syn.shift,subst_pairT,GaussianRationalMonicReconstruction.subst_spikeData,
    GaussianTranslatedNonconstant.subst_recode,subst_inst2] using entry.eqTrans
      ((incidence_unique t p q (Syn.shift N) (Syn.shift x) (var 0) (Syn.shift j) ls.wk rs.wk Prf.hyp0 js.wk).eqTrans
        (spike_body_at (inst2 q (Syn.shift j) (Syn.shift x))
          (recode (inst2 t (inst2 q (Syn.shift j) (Syn.shift x)) (Syn.shift x))) (var 0)).eqSymm)

theorem incidence_column_selected (t p q : PTm 2) (N x j : PTm n)
    (hr : Γ ⊢[PRAAx] boundedRange q N x)
    (hL : Γ ⊢[PRAAx] inverseLaw p q N x) (hR : Γ ⊢[PRAAx] inverseLaw q p N x)
    (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    GaussianRationalFubini.column (incidenceBody t p) j N x ≐ recode (inst2 t (inst2 q j x) x) :=
  (incidence_column _ _ _ _ _ _ hL hR hj).eqTrans
    ((spike_sum _ _ _ (recode_canonical _)).eqTrans (active_on _ _ _ (range_at q N x j hr hj)))

theorem incidence_rows (t p : PTm 2) (N x : PTm n)
    (hr : Γ ⊢[PRAAx] boundedRange p N x) : Γ ⊢[PRAAx]
    GaussianRationalFubini.rowFirst (incidenceBody t p) N N x ≐ GaussianRationalFiniteSum.sum t N x := by
  refine (GaussianRationalFiniteSum.sum_congr_bounded (GaussianRationalFubini.rowSumBody (incidenceBody t p))
    (recodeBody t) N (pairT N x) x ?_).eqTrans (sum_recode t N x)
  refine .allI (.impI ?_)
  rw [inst2_recodeBody,shift_pairT]
  have hs : Γ.map Fm.shift ⊢[PRAAx] boundedRange p (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,subst_boundedRange,Syn.shift] using hr.shift
  exact (GaussianRationalFubini.row_sum_at _ (var 0) (Syn.shift N) (Syn.shift x)).eqTrans
    (incidence_row_selected t p (Syn.shift N) (Syn.shift x) (var 0) hs.wk Prf.hyp0)

theorem incidence_columns (t p q : PTm 2) (N x : PTm n)
    (hr : Γ ⊢[PRAAx] boundedRange q N x)
    (hL : Γ ⊢[PRAAx] inverseLaw p q N x) (hR : Γ ⊢[PRAAx] inverseLaw q p N x) : Γ ⊢[PRAAx]
    GaussianRationalFubini.columnFirst (incidenceBody t p) N N x ≐ GaussianRationalFiniteSum.sum (mappedBody t q) N x := by
  refine (GaussianRationalFiniteSum.sum_congr_bounded (GaussianRationalFubini.columnSumBody (incidenceBody t p))
    (recodeBody (mappedBody t q)) N (pairT N x) x ?_).eqTrans (sum_recode (mappedBody t q) N x)
  refine .allI (.impI ?_)
  rw [inst2_recodeBody,inst2_mappedBody,shift_pairT]
  have rs : Γ.map Fm.shift ⊢[PRAAx] boundedRange q (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,subst_boundedRange,Syn.shift] using hr.shift
  have ls : Γ.map Fm.shift ⊢[PRAAx] inverseLaw p q (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,subst_inverseLaw,Syn.shift] using hL.shift
  have ls' : Γ.map Fm.shift ⊢[PRAAx] inverseLaw q p (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,subst_inverseLaw,Syn.shift] using hR.shift
  exact (GaussianRationalFubini.column_sum_at _ (var 0) (Syn.shift N) (Syn.shift x)).eqTrans
    (incidence_column_selected t p q (Syn.shift N) (Syn.shift x) (var 0) rs.wk ls.wk ls'.wk Prf.hyp0)

/-- Genuine finite field-sum reindexing from local range and inverse facts. -/
theorem permutation_sum (t p q : PTm 2) (N x : PTm n)
    (hp : Γ ⊢[PRAAx] boundedRange p N x) (hq : Γ ⊢[PRAAx] boundedRange q N x)
    (hL : Γ ⊢[PRAAx] inverseLaw p q N x) (hR : Γ ⊢[PRAAx] inverseLaw q p N x) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.sum (mappedBody t p) N x ≐ GaussianRationalFiniteSum.sum t N x :=
  (incidence_columns t q p N x hp hR hL).eqSymm.eqTrans
    ((GaussianRationalFubini.fubini (incidenceBody t q) N N x).eqSymm.eqTrans (incidence_rows t q N x hq))

theorem involution_sum (t p : PTm 2) (N x : PTm n)
    (hr : Γ ⊢[PRAAx] boundedRange p N x) (h : Γ ⊢[PRAAx] inverseLaw p p N x) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.sum (mappedBody t p) N x ≐ GaussianRationalFiniteSum.sum t N x :=
  permutation_sum t p p N x hr hr h h

def contract (p q : PTm 2) (N x : PTm n) : Fm PTm n := boundedRange p N x ⋏
  (boundedRange q N x ⋏ (inverseLaw p q N x ⋏ inverseLaw q p N x))
ipra_subst contract

/-- The payload really constructs the reindexed and original sums separately. -/
def output (t p : PTm 2) (N x : PTm n) : PTm n :=
  pairT (GaussianRationalFiniteSum.sum (mappedBody t p) N x) (GaussianRationalFiniteSum.sum t N x)
def outputF (t p : PTm 2) : PR 2 := PTm.toPR (output t p (var 0) (var 1))
def run (t p : PTm 2) (N x : PTm n) : PTm n := ap2 (outputF t p) N x
ipra_subst output
ipra_subst run
theorem program_at (t p : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx] run t p N x ≐ output t p N x := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output t p (var 0) (var 1) : PTm 2) ![N,x]
theorem returned_reindexed (t p : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx]
    fstT (run t p N x) ≐ GaussianRationalFiniteSum.sum (mappedBody t p) N x :=
  (program_at _ _ _ _).fstE
theorem returned_original (t p : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx]
    sndT (run t p N x) ≐ GaussianRationalFiniteSum.sum t N x :=
  (program_at _ _ _ _).sndE
theorem returned_reindexed_canonical (t p : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx] canonical (fstT (run t p N x)) :=
  GaussianRationalHorner.canonical_congr (returned_reindexed _ _ _ _) (GaussianRationalFiniteSum.sum_canonical _ _ _)
theorem returned_original_canonical (t p : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx] canonical (sndT (run t p N x)) :=
  GaussianRationalHorner.canonical_congr (returned_original _ _ _ _) (GaussianRationalFiniteSum.sum_canonical _ _ _)
theorem returned_equal (t p q : PTm 2) (N x : PTm n) (h : Γ ⊢[PRAAx] contract p q N x) : Γ ⊢[PRAAx]
    fstT (run t p N x) ≐ sndT (run t p N x) :=
  (returned_reindexed _ _ _ _).eqTrans ((permutation_sum t p q N x (.andE₁ h) (.andE₁ (.andE₂ h))
    (.andE₁ (.andE₂ (.andE₂ h))) (.andE₂ (.andE₂ (.andE₂ h)))).eqTrans (returned_original _ _ _ _).eqSymm)
theorem returned_involution (t p : PTm 2) (N x : PTm n)
    (hr : Γ ⊢[PRAAx] boundedRange p N x) (hi : Γ ⊢[PRAAx] inverseLaw p p N x) : Γ ⊢[PRAAx]
    fstT (run t p N x) ≐ sndT (run t p N x) :=
  (returned_reindexed _ _ _ _).eqTrans ((involution_sum t p N x hr hi).eqTrans (returned_original _ _ _ _).eqSymm)

theorem recoded_sum_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianRationalFiniteSum.sum (recodeBody t) (var 0) (var 1) ≐ GaussianRationalFiniteSum.sum t (var 0) (var 1)) :=
  closeUniv 2 (sum_recode _ _ _)
theorem gaussian_delta_selected_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (var 0) ⟶ deltaSum t (var 0) (var 1) (var 2) ≐ recode (inst2 t (var 1) (var 2))) :=
  closeUniv 3 (.impI (delta_selected _ _ _ _ Prf.hyp0))
theorem gaussian_delta_outside_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 0) (var 1) ⟶ deltaSum t (var 0) (var 1) (var 2) ≐ qzero) :=
  closeUniv 3 (.impI (delta_outside _ _ _ _ Prf.hyp0))
theorem bounded_permutation_sum_closed (t p q : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (contract p q (var 0) (var 1) ⟶
      GaussianRationalFiniteSum.sum (mappedBody t p) (var 0) (var 1) ≐ GaussianRationalFiniteSum.sum t (var 0) (var 1)) :=
  closeUniv 2 (.impI (permutation_sum t p q _ _ (.andE₁ Prf.hyp0) (.andE₁ (.andE₂ Prf.hyp0))
    (.andE₁ (.andE₂ (.andE₂ Prf.hyp0))) (.andE₂ (.andE₂ (.andE₂ Prf.hyp0)))))
theorem actual_reindex_program_closed (t p : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((run t p (var 0) (var 1) ≐ output t p (var 0) (var 1)) ⋏
      (canonical (fstT (run t p (var 0) (var 1))) ⋏ canonical (sndT (run t p (var 0) (var 1))))) :=
  closeUniv 2 (.andI (program_at _ _ _ _) (.andI (returned_reindexed_canonical _ _ _ _) (returned_original_canonical _ _ _ _)))
theorem returned_permutation_sum_closed (t p q : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (contract p q (var 0) (var 1) ⟶ fstT (run t p (var 0) (var 1)) ≐ sndT (run t p (var 0) (var 1))) :=
  closeUniv 2 (.impI (returned_equal _ _ _ _ _ Prf.hyp0))
theorem returned_involution_sum_closed (t p : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (boundedRange p (var 0) (var 1) ⟶ inverseLaw p p (var 0) (var 1) ⟶
      fstT (run t p (var 0) (var 1)) ≐ sndT (run t p (var 0) (var 1))) :=
  closeUniv 2 (.impI (.impI (returned_involution _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem empty_reindex_closed (t p : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    ((fstT (run t p zero (var 0)) ≐ qzero) ⋏ (sndT (run t p zero (var 0)) ≐ qzero)) :=
  closeUniv 1 (.andI ((returned_reindexed _ _ _ _).eqTrans (GaussianRationalFiniteSum.sum_zero _ _))
    ((returned_original _ _ _ _).eqTrans (GaussianRationalFiniteSum.sum_zero _ _)))

end LeanProofs.IPRA.Analysis.GaussianRationalPermutationSum
