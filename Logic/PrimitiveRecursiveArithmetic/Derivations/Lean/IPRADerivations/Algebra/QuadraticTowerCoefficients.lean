import IPRADerivations.Foundations.SequenceComposition
import IPRADerivations.Foundations.BoundedSyntaxInduction

/-!
# Actual coefficient arrays at numerical quadratic-tower depth

The input is a raw nested pair code, interpreted at numerical depth h.
An actual PR table stores every code below a persistent numerical cutoff.
At depth zero its cell is a singleton; the successor cell appends the
previous cells at the two decoded components. Thus the changed-argument
tree recursion is implemented by ordinary recursion on one stored table.
The compiled bounded invariants below prove its width and coherence.
Arithmetic, radicand validity and a uniform tower sign remain separate.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerCoefficients

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (sequence entry sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length append append_length entry_congr)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def singleton (x : PTm n) : PTm n := sequence (var 1) one x
def width (h : PTm n) : PTm n := pw two h
def baseBody : PTm 2 := singleton (var 0)
def nextBody : PTm 2 := append (entry (var 1) (fstT (var 0))) (entry (var 1) (sndT (var 0)))
def tableBase : PTm 1 := sequence baseBody (var 0) zero
def tableStep : PTm 3 := sequence nextBody (var 2) (var 1)
def tableF : PR 2 := rec2 tableBase tableStep
def table (h K : PTm n) : PTm n := ap2 tableF h K
def coefficients (h K x : PTm n) : PTm n := entry (table h K) x
def flatten (h x : PTm n) : PTm n := coefficients h (succ x) x

@[simp] theorem subst_singleton {k : ℕ} (σ : Fin n → PTm k) (x : PTm n) :
    Syn.subst σ (singleton x) = singleton (Syn.subst σ x) := by simp [singleton,one]
@[simp] theorem subst_width {k : ℕ} (σ : Fin n → PTm k) (h : PTm n) :
    Syn.subst σ (width h) = width (Syn.subst σ h) := by simp [width,two,one]
@[simp] theorem subst_table {k : ℕ} (σ : Fin n → PTm k) (h K : PTm n) :
    Syn.subst σ (table h K) = table (Syn.subst σ h) (Syn.subst σ K) := by simp [table]
@[simp] theorem subst_coefficients {k : ℕ} (σ : Fin n → PTm k) (h K x : PTm n) :
    Syn.subst σ (coefficients h K x) = coefficients (Syn.subst σ h) (Syn.subst σ K) (Syn.subst σ x) := by
  simp [coefficients]
@[simp] theorem subst_flatten {k : ℕ} (σ : Fin n → PTm k) (h x : PTm n) :
    Syn.subst σ (flatten h x) = flatten (Syn.subst σ h) (Syn.subst σ x) := by simp [flatten]

theorem singleton_length (x : PTm n) : Γ ⊢[PRAAx] length (singleton x) ≐ one := sequence_length _ _ _
theorem singleton_entry (x : PTm n) : Γ ⊢[PRAAx] entry (singleton x) zero ≐ x :=
  sequence_decode (var 1) (zero_lt_succ zero)
theorem width_zero : Γ ⊢[PRAAx] width (zero : PTm n) ≐ one := pw_zero two
theorem width_succ (h : PTm n) : Γ ⊢[PRAAx] width (succ h) ≐ width h+width h :=
  (pw_succ two h).eqTrans (by unfold width; ipra_ring)

theorem table_zero (K : PTm n) : Γ ⊢[PRAAx] table zero K ≐ sequence baseBody K zero := by
  simpa [table,tableF,tableBase] using rec2_zero (Γ := Γ) tableBase tableStep K
theorem table_succ (h K : PTm n) : Γ ⊢[PRAAx] table (succ h) K ≐ sequence nextBody K (table h K) := by
  simpa [table,tableF,tableStep] using rec2_succ (Γ := Γ) tableBase tableStep h K
theorem table_congr {h h' K K' : PTm n} (hh : Γ ⊢[PRAAx] h ≐ h') (hK : Γ ⊢[PRAAx] K ≐ K') :
    Γ ⊢[PRAAx] table h K ≐ table h' K' := congrAp2 tableF hh hK
theorem coefficients_congr {h h' K K' x x' : PTm n} (hh : Γ ⊢[PRAAx] h ≐ h')
    (hK : Γ ⊢[PRAAx] K ≐ K') (hx : Γ ⊢[PRAAx] x ≐ x') : Γ ⊢[PRAAx]
    coefficients h K x ≐ coefficients h' K' x' := entry_congr (table_congr hh hK) hx
theorem append_congr {a a' b b' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a')
    (hb : Γ ⊢[PRAAx] b ≐ b') : Γ ⊢[PRAAx] append a b ≐ append a' b' := by
  simpa using Prf.eqCongr (append (var 0) (var 1)) (σ := ![a,b]) (σ' := ![a',b'])
    (fun i => by fin_cases i; exact ha; exact hb)
theorem table_length (h K : PTm n) : Γ ⊢[PRAAx] length (table h K) ≐ K := by
  refine .orE (zero_or_succ h) ?_ ?_
  · exact (congrFst ((table_congr Prf.hyp0 (.eqRefl K)).eqTrans (table_zero K))).eqTrans (sequence_length _ _ _)
  · exact (congrFst ((table_congr Prf.hyp0 (.eqRefl K)).eqTrans (table_succ _ K))).eqTrans (sequence_length _ _ _)
theorem coefficients_zero (K x : PTm n) (hx : Γ ⊢[PRAAx] lt x K) : Γ ⊢[PRAAx]
    coefficients zero K x ≐ singleton x := by
  refine (entry_congr (table_zero K) (.eqRefl x)).eqTrans ?_
  simpa [baseBody,inst2] using sequence_decode (Γ := Γ) baseBody (x := zero) hx
theorem coefficients_succ (h K x : PTm n) (hx : Γ ⊢[PRAAx] lt x K) : Γ ⊢[PRAAx]
    coefficients (succ h) K x ≐ append (coefficients h K (fstT x)) (coefficients h K (sndT x)) := by
  refine (entry_congr (table_succ h K) (.eqRefl x)).eqTrans ?_
  simpa [nextBody,inst2,coefficients] using sequence_decode (Γ := Γ) nextBody (x := table h K) hx

theorem monus_bound (a b : PTm n) : Γ ⊢[PRAAx] le (monus a b) a := by
  refine .orE (lt_or_le a b) ?_ ?_
  · exact le_congr (le_of_lt Prf.hyp0 : (lt a b :: Γ) ⊢[PRAAx] monus a b ≐ zero).eqSymm (.eqRefl _) (zero_le _)
  · exact le_of_eq_add (d := b) ((eq_add_of_le Prf.hyp0).eqTrans (add_comm _ _))
theorem first_bound (x : PTm n) : Γ ⊢[PRAAx] le (fstT x) x := monus_bound _ _
theorem square_root_bound (x : PTm n) : Γ ⊢[PRAAx] le (isqrt x) x := by
  refine .orE (zero_or_succ (isqrt x)) ?_ ?_
  · exact le_congr Prf.hyp0.eqSymm (.eqRefl _) (zero_le _)
  · have h1 : ((isqrt x ≐ succ (PTm.pred (isqrt x))) :: Γ) ⊢[PRAAx] le one (isqrt x) :=
      le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
    have sq := mul_le_mul_right (isqrt x) h1
    exact le_trans (le_congr (one_mul _) (.eqRefl _) sq) (isqrt_le x)
theorem second_bound (x : PTm n) : Γ ⊢[PRAAx] le (sndT x) x := le_trans (monus_bound _ _) (square_root_bound x)

def sizeLaw (h K : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift K) ⟶
  length (coefficients (Syn.shift h) (Syn.shift K) (var 0)) ≐ width (Syn.shift h))
def sizeSyntax (h K : PTm n) : BFm n := .all K
  (.eq (length (coefficients (Syn.shift h) (Syn.shift K) (var 0))) (width (Syn.shift h)))
@[simp] theorem subst_sizeLaw {k : ℕ} (σ : Fin n → PTm k) (h K : PTm n) :
    (sizeLaw h K).subst σ = sizeLaw (Syn.subst σ h) (Syn.subst σ K) := by
  simp [sizeLaw,Syn.subst_shift,Syn.shift_subst]
theorem size_formula (h K : PTm n) : formula (sizeSyntax h K) = sizeLaw h K := by
  simp [sizeSyntax,sizeLaw,formula]
theorem size_at (h K x : PTm n) (hs : Γ ⊢[PRAAx] sizeLaw h K) (hx : Γ ⊢[PRAAx] lt x K) : Γ ⊢[PRAAx]
    length (coefficients h K x) ≐ width h := by
  have gate := hs.allE x
  simp only [Fm.subst_imp,Fm.subst_eq,subst_lt,subst_coefficients,
    Foundations.SequenceComposition.subst_length,subst_width,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] at gate
  exact .impE gate hx
theorem size_zero (K : PTm n) : Γ ⊢[PRAAx] sizeLaw zero K := by
  refine .allI (.impI ?_)
  simp only [Syn.shift,ConciseIPRA.PTm.subst_zero]
  exact (congrFst (coefficients_zero (Syn.shift K) (var 0) Prf.hyp0)).eqTrans
    ((singleton_length _).eqTrans width_zero.eqSymm)
theorem size_step (h K : PTm n) (hs : Γ ⊢[PRAAx] sizeLaw h K) : Γ ⊢[PRAAx] sizeLaw (succ h) K := by
  have ih : Γ.map Fm.shift ⊢[PRAAx] sizeLaw (Syn.shift h) (Syn.shift K) := by
    simpa only [Fm.shift,subst_sizeLaw,Syn.shift] using hs.shift
  refine .allI (.impI ?_)
  have left := size_at (Syn.shift h) (Syn.shift K) (fstT (var 0)) ih.wk
    (lt_of_le_of_lt (first_bound _) Prf.hyp0)
  have right := size_at (Syn.shift h) (Syn.shift K) (sndT (var 0)) ih.wk
    (lt_of_le_of_lt (second_bound _) Prf.hyp0)
  exact (congrFst (coefficients_succ _ _ _ Prf.hyp0)).eqTrans
    ((append_length _ _).eqTrans ((congrAdd left right).eqTrans (width_succ _).eqSymm))
theorem all_sizes (h K : PTm n) : Γ ⊢[PRAAx] sizeLaw h K := by
  have all : Γ ⊢[PRAAx] .all (formula (sizeSyntax (var 0) (Syn.shift K))) := by
    refine Foundations.BoundedSyntaxInduction.induction _ ?_ ?_
    · simpa only [size_formula,subst_sizeLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using size_zero (Γ := Γ) K
    · simpa only [size_formula,subst_sizeLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        size_step (Γ := formula (sizeSyntax (var 0) (Syn.shift K)) :: Γ.map Fm.shift)
          (var 0) (Syn.shift K) (by simpa only [size_formula] using (Prf.hyp0 (Ax := PRAAx)))
  simpa only [size_formula,subst_sizeLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE h
theorem coefficients_length (h K x : PTm n) (hx : Γ ⊢[PRAAx] lt x K) : Γ ⊢[PRAAx]
    length (coefficients h K x) ≐ width h := size_at _ _ _ (all_sizes h K) hx

def coherent (h K L : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift K) ⟶
  lt (var 0) (Syn.shift L) ⟶ coefficients (Syn.shift h) (Syn.shift K) (var 0) ≐
    coefficients (Syn.shift h) (Syn.shift L) (var 0))
def coherentSyntax (h K L : PTm n) : BFm n := .all K (.imp (.lt (var 0) (Syn.shift L))
  (.eq (coefficients (Syn.shift h) (Syn.shift K) (var 0)) (coefficients (Syn.shift h) (Syn.shift L) (var 0))))
@[simp] theorem subst_coherent {k : ℕ} (σ : Fin n → PTm k) (h K L : PTm n) :
    (coherent h K L).subst σ = coherent (Syn.subst σ h) (Syn.subst σ K) (Syn.subst σ L) := by
  simp [coherent,Syn.subst_shift,Syn.shift_subst]
theorem coherent_formula (h K L : PTm n) : formula (coherentSyntax h K L) = coherent h K L := by
  simp [coherentSyntax,coherent,formula,BFm.lt,BFm.le,lt,le]
theorem coherent_at (h K L x : PTm n) (ih : Γ ⊢[PRAAx] coherent h K L)
    (hx : Γ ⊢[PRAAx] lt x K) (hy : Γ ⊢[PRAAx] lt x L) : Γ ⊢[PRAAx]
    coefficients h K x ≐ coefficients h L x := by
  have gate := ih.allE x
  simp only [Fm.subst_imp,Fm.subst_eq,subst_lt,subst_coefficients,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] at gate
  exact .impE (.impE gate hx) hy
theorem coherent_zero (K L : PTm n) : Γ ⊢[PRAAx] coherent zero K L := by
  refine .allI (.impI (.impI ?_))
  simp only [Syn.shift,ConciseIPRA.PTm.subst_zero]
  exact (coefficients_zero (Syn.shift K) (var 0) Prf.hyp1).eqTrans
    (coefficients_zero (Syn.shift L) (var 0) Prf.hyp0).eqSymm
theorem coherent_step (h K L : PTm n) (ih : Γ ⊢[PRAAx] coherent h K L) : Γ ⊢[PRAAx] coherent (succ h) K L := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] coherent (Syn.shift h) (Syn.shift K) (Syn.shift L) := by
    simpa only [Fm.shift,subst_coherent,Syn.shift] using ih.shift
  refine .allI (.impI (.impI ?_))
  have a := coherent_at _ _ _ (fstT (var 0)) hs.wk.wk
    (lt_of_le_of_lt (first_bound _) Prf.hyp1) (lt_of_le_of_lt (first_bound _) Prf.hyp0)
  have b := coherent_at _ _ _ (sndT (var 0)) hs.wk.wk
    (lt_of_le_of_lt (second_bound _) Prf.hyp1) (lt_of_le_of_lt (second_bound _) Prf.hyp0)
  exact (coefficients_succ _ _ _ Prf.hyp1).eqTrans
    ((append_congr a b).eqTrans (coefficients_succ _ _ _ Prf.hyp0).eqSymm)
theorem all_coherent (h K L : PTm n) : Γ ⊢[PRAAx] coherent h K L := by
  have all : Γ ⊢[PRAAx] .all (formula (coherentSyntax (var 0) (Syn.shift K) (Syn.shift L))) := by
    refine Foundations.BoundedSyntaxInduction.induction _ ?_ ?_
    · simpa only [coherent_formula,subst_coherent,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using coherent_zero (Γ := Γ) K L
    · simpa only [coherent_formula,subst_coherent,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        coherent_step (Γ := formula (coherentSyntax (var 0) (Syn.shift K) (Syn.shift L)) :: Γ.map Fm.shift)
          (var 0) (Syn.shift K) (Syn.shift L) (by simpa only [coherent_formula] using (Prf.hyp0 (Ax := PRAAx)))
  simpa only [coherent_formula,subst_coherent,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE h
theorem coefficients_coherent (h K L x : PTm n) (hx : Γ ⊢[PRAAx] lt x K) (hy : Γ ⊢[PRAAx] lt x L) : Γ ⊢[PRAAx]
    coefficients h K x ≐ coefficients h L x := coherent_at _ _ _ _ (all_coherent h K L) hx hy

theorem flatten_length (h x : PTm n) : Γ ⊢[PRAAx] length (flatten h x) ≐ width h :=
  coefficients_length _ _ _ (le_refl _)
theorem flatten_zero (x : PTm n) : Γ ⊢[PRAAx] flatten zero x ≐ singleton x := coefficients_zero _ _ (le_refl _)
theorem flatten_at_cutoff (h K x : PTm n) (hx : Γ ⊢[PRAAx] lt x K) : Γ ⊢[PRAAx]
    coefficients h K x ≐ flatten h x := coefficients_coherent _ _ _ _ hx (le_refl _)
theorem flatten_succ (h x : PTm n) : Γ ⊢[PRAAx]
    flatten (succ h) x ≐ append (flatten h (fstT x)) (flatten h (sndT x)) :=
  (coefficients_succ _ _ _ (le_refl _)).eqTrans (append_congr
    (flatten_at_cutoff h (succ x) (fstT x) (lt_of_le_of_lt (first_bound x) (le_refl _)))
    (flatten_at_cutoff h (succ x) (sndT x) (lt_of_le_of_lt (second_bound x) (le_refl _))))

theorem flatten_congr {h h' x x' : PTm n} (hh : Γ ⊢[PRAAx] h ≐ h') (hx : Γ ⊢[PRAAx] x ≐ x') : Γ ⊢[PRAAx]
    flatten h x ≐ flatten h' x' := coefficients_congr hh (congrSucc hx) hx
theorem flatten_pair (h a b : PTm n) : Γ ⊢[PRAAx]
    flatten (succ h) (pairT a b) ≐ append (flatten h a) (flatten h b) :=
  (flatten_succ h _).eqTrans (append_congr (flatten_congr (.eqRefl _) (fst_pair _ _))
    (flatten_congr (.eqRefl _) (snd_pair _ _)))
theorem flatten_base_entry (x : PTm n) : Γ ⊢[PRAAx] entry (flatten zero x) zero ≐ x :=
  (entry_congr (flatten_zero x) (.eqRefl _)).eqTrans (singleton_entry x)
theorem flatten_left (h x i : PTm n) (hi : Γ ⊢[PRAAx] lt i (width h)) : Γ ⊢[PRAAx]
    entry (flatten (succ h) x) i ≐ entry (flatten h (fstT x)) i :=
  (entry_congr (flatten_succ h x) (.eqRefl _)).eqTrans
    (Foundations.SequenceComposition.append_left (lt_congr (.eqRefl _) (flatten_length _ _).eqSymm hi))
theorem flatten_right (h x i : PTm n) (hi : Γ ⊢[PRAAx] lt i (width h)) : Γ ⊢[PRAAx]
    entry (flatten (succ h) x) (width h+i) ≐ entry (flatten h (sndT x)) i :=
  (entry_congr (flatten_succ h x) (congrAdd (flatten_length h (fstT x)).eqSymm (.eqRefl _))).eqTrans
    (Foundations.SequenceComposition.append_right (lt_congr (.eqRefl _) (flatten_length _ _).eqSymm hi))
theorem depth_one_first (x : PTm n) : Γ ⊢[PRAAx] entry (flatten one x) zero ≐ fstT x :=
  (flatten_left zero x zero (lt_congr (.eqRefl _) width_zero.eqSymm (le_refl one))).eqTrans (flatten_base_entry _)
theorem depth_one_second (x : PTm n) : Γ ⊢[PRAAx] entry (flatten one x) one ≐ sndT x :=
  (entry_congr (.eqRefl _) ((add_zero _).eqTrans width_zero).eqSymm).eqTrans
    ((flatten_right zero x zero (lt_congr (.eqRefl _) width_zero.eqSymm (le_refl one))).eqTrans (flatten_base_entry _))

def flattenF : PR 2 := PTm.toPR (flatten (var 0) (var 1))
def run (h x : PTm n) : PTm n := ap2 flattenF h x
def output (h K x : PTm n) : PTm n := pairT (table h K) (pairT (coefficients h K x) (flatten h x))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def tableRun (h K x : PTm n) : PTm n := ap3 outputF h K x
@[simp] theorem subst_run {k : ℕ} (σ : Fin n → PTm k) (h x : PTm n) :
    Syn.subst σ (run h x) = run (Syn.subst σ h) (Syn.subst σ x) := by simp [run]
@[simp] theorem subst_output {k : ℕ} (σ : Fin n → PTm k) (h K x : PTm n) :
    Syn.subst σ (output h K x) = output (Syn.subst σ h) (Syn.subst σ K) (Syn.subst σ x) := by simp [output]
@[simp] theorem subst_tableRun {k : ℕ} (σ : Fin n → PTm k) (h K x : PTm n) :
    Syn.subst σ (tableRun h K x) = tableRun (Syn.subst σ h) (Syn.subst σ K) (Syn.subst σ x) := by simp [tableRun]
theorem program_at (h x : PTm n) : Γ ⊢[PRAAx] run h x ≐ flatten h x := by
  simpa [run,flattenF,ap2] using toPR_eq (Γ := Γ) (flatten (var 0) (var 1) : PTm 2) ![h,x]
theorem returned_length (h x : PTm n) : Γ ⊢[PRAAx] length (run h x) ≐ width h :=
  (congrFst (program_at _ _)).eqTrans (flatten_length _ _)
theorem table_program_at (h K x : PTm n) : Γ ⊢[PRAAx] tableRun h K x ≐ output h K x := by
  simpa [tableRun,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![h,K,x]
theorem returned_table (h K x : PTm n) : Γ ⊢[PRAAx] fstT (tableRun h K x) ≐ table h K :=
  (congrFst (table_program_at _ _ _)).eqTrans (fst_pair _ _)
theorem returned_cell (h K x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (tableRun h K x)) ≐ coefficients h K x :=
  (congrFst ((congrSnd (table_program_at _ _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_flatten (h K x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (tableRun h K x)) ≐ flatten h x :=
  (congrSnd ((congrSnd (table_program_at _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_table_length (h K x : PTm n) : Γ ⊢[PRAAx] length (fstT (tableRun h K x)) ≐ K :=
  (congrFst (returned_table _ _ _)).eqTrans (table_length _ _)
theorem returned_agreement (h K x : PTm n) (hx : Γ ⊢[PRAAx] lt x K) : Γ ⊢[PRAAx]
    fstT (sndT (tableRun h K x)) ≐ sndT (sndT (tableRun h K x)) :=
  (returned_cell _ _ _).eqTrans ((flatten_at_cutoff _ _ _ hx).eqTrans (returned_flatten _ _ _).eqSymm)

theorem actual_tower_coefficient_width_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (length (flatten (var 0) (var 1)) ≐ width (var 0)) := closeUniv 2 (flatten_length _ _)
theorem actual_tower_coefficient_base_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (entry (flatten zero (var 0)) zero ≐ var 0) := closeUniv 1 (flatten_base_entry _)
theorem actual_tower_coefficient_successor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (flatten (succ (var 0)) (var 1) ≐ append (flatten (var 0) (fstT (var 1))) (flatten (var 0) (sndT (var 1)))) :=
  closeUniv 2 (flatten_succ _ _)
theorem actual_tower_pair_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (flatten (succ (var 0)) (pairT (var 1) (var 2)) ≐ append (flatten (var 0) (var 1)) (flatten (var 0) (var 2))) :=
  closeUniv 3 (flatten_pair _ _ _)
theorem actual_tower_left_half_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (width (var 0)) ⟶ entry (flatten (succ (var 0)) (var 1)) (var 2) ≐
      entry (flatten (var 0) (fstT (var 1))) (var 2)) :=
  closeUniv 3 (.impI (flatten_left _ _ _ Prf.hyp0))
theorem actual_tower_right_half_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (width (var 0)) ⟶ entry (flatten (succ (var 0)) (var 1)) (width (var 0)+var 2) ≐
      entry (flatten (var 0) (sndT (var 1))) (var 2)) :=
  closeUniv 3 (.impI (flatten_right _ _ _ Prf.hyp0))
theorem actual_tower_cutoff_coherence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 1) ⟶ lt (var 3) (var 2) ⟶ coefficients (var 0) (var 1) (var 3) ≐
      coefficients (var 0) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (coefficients_coherent _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_computed_tower_cutoff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (var 1) ⟶ coefficients (var 0) (var 1) (var 2) ≐ flatten (var 0) (var 2)) :=
  closeUniv 3 (.impI (flatten_at_cutoff _ _ _ Prf.hyp0))
theorem actual_first_extension_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (entry (flatten one (var 0)) zero ≐ fstT (var 0) ⋏ entry (flatten one (var 0)) one ≐ sndT (var 0)) :=
  closeUniv 1 (.andI (depth_one_first _) (depth_one_second _))
theorem actual_tower_flatten_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ flatten (var 0) (var 1)) := closeUniv 2 (program_at _ _)
theorem actual_returned_tower_width_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (length (run (var 0) (var 1)) ≐ width (var 0)) := closeUniv 2 (returned_length _ _)
theorem actual_tower_table_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (tableRun (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (table_program_at _ _ _)
theorem actual_returned_tower_table_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (fstT (tableRun (var 0) (var 1) (var 2))) ≐ var 1 ⋏
      (lt (var 2) (var 1) ⟶ fstT (sndT (tableRun (var 0) (var 1) (var 2))) ≐
        sndT (sndT (tableRun (var 0) (var 1) (var 2))))) :=
  closeUniv 3 (.andI (returned_table_length _ _ _) (.impI (returned_agreement _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Algebra.QuadraticTowerCoefficients
