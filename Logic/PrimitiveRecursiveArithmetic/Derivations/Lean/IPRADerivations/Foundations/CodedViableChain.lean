import IPRADerivations.Foundations.ChainViability
import IPRADerivations.Foundations.SequenceComposition

/-!
# Actual coded finite viable chains

Source: `ipra_evidence_framework/report.tex`, theorem "PR backward viability
and certified finite chain". The actual PR sequence stores the checked
least-successor chain, with h+1 entries. Its explicit encoding bound uses
only the numerical candidate bounds, the horizon, and polynomial pairing.

Conversely, an arbitrary numerical code is checked by one object formula:
its length, bounded local tests, and bounded edge tests. A genuine QF
induction on the remaining level derives viability from this formula.
No external admissibility rule bundle or final viability premise is used.
The fixed instance and start term are syntax schemas; all parameter,
sequence-code, level and remaining-level arguments are internal numbers.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.CodedViableChain

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.PTm (monus)
open LeanProofs.IPRA.Foundations.BackwardViability
open LeanProofs.IPRA.Foundations.BackwardViability.Instance
open LeanProofs.IPRA.Foundations.ViableChain
open LeanProofs.IPRA.Foundations.MasterCertificate (sequence entry stack stackF stack_succ stack_zero)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr subst_length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def viableStart (I : Instance) (a p : PTm n) : Fm PTm n :=
  lt a (I.bd zero p) ⋏ I.V (I.h p) a p ≐ one

def localCode (I : Instance) (S p : PTm n) : Fm PTm n := .all
  (le (var 0) (I.h (Syn.shift p)) ⟶
    (lt (entry (Syn.shift S) (var 0)) (I.bd (var 0) (Syn.shift p)) ⋏
      neg (I.g (var 0) (entry (Syn.shift S) (var 0)) (Syn.shift p) ≐ zero)))

def edgeCode (I : Instance) (S p : PTm n) : Fm PTm n := .all
  (lt (var 0) (I.h (Syn.shift p)) ⟶
    neg (I.t (var 0) (entry (Syn.shift S) (var 0))
      (entry (Syn.shift S) (succ (var 0))) (Syn.shift p) ≐ zero))

def admissibleCode (I : Instance) (S p : PTm n) : Fm PTm n :=
  length S ≐ succ (I.h p) ⋏ (localCode I S p ⋏ edgeCode I S p)

def chainBody (I : Instance) (s : PTm 1) : PTm 2 := chain I s (var 0) (var 1)
def chainCode (I : Instance) (s : PTm 1) (p : PTm n) : PTm n :=
  sequence (chainBody I s) (succ (I.h p)) p
def chainF (I : Instance) (s : PTm 1) : PR 1 := PTm.toPR (chainCode I s (var 0))

def boundStep (I : Instance) : PTm 3 := pairT (I.bd (var 0) (var 2)) (var 1)
def boundStack (I : Instance) (r p : PTm n) : PTm n := ap2 (rec2 zero (boundStep I)) r p
def codeBound (I : Instance) (p : PTm n) : PTm n :=
  succ (pairT (succ (I.h p)) (boundStack I (succ (I.h p)) p))

def hasChain (I : Instance) (a p : PTm n) : Fm PTm n := .ex
  (lt (var 0) (codeBound I (Syn.shift p)) ⋏
    (admissibleCode I (var 0) (Syn.shift p) ⋏ entry (var 0) zero ≐ Syn.shift a))

@[simp] theorem subst_viableStart {m : ℕ} (σ : Fin n → PTm m) (I : Instance) (a p : PTm n) :
    (viableStart I a p).subst σ = viableStart I (Syn.subst σ a) (Syn.subst σ p) := by simp [viableStart]
@[simp] theorem subst_localCode {m : ℕ} (σ : Fin n → PTm m) (I : Instance) (S p : PTm n) :
    (localCode I S p).subst σ = localCode I (Syn.subst σ S) (Syn.subst σ p) := by
  simp [localCode,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_edgeCode {m : ℕ} (σ : Fin n → PTm m) (I : Instance) (S p : PTm n) :
    (edgeCode I S p).subst σ = edgeCode I (Syn.subst σ S) (Syn.subst σ p) := by
  simp [edgeCode,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_admissibleCode {m : ℕ} (σ : Fin n → PTm m) (I : Instance) (S p : PTm n) :
    (admissibleCode I S p).subst σ = admissibleCode I (Syn.subst σ S) (Syn.subst σ p) := by simp [admissibleCode]
@[simp] theorem subst_chainCode {m : ℕ} (σ : Fin n → PTm m) (I : Instance) (s : PTm 1) (p : PTm n) :
    Syn.subst σ (chainCode I s p) = chainCode I s (Syn.subst σ p) := by simp [chainCode]
@[simp] theorem subst_boundStack {m : ℕ} (σ : Fin n → PTm m) (I : Instance) (r p : PTm n) :
    Syn.subst σ (boundStack I r p) = boundStack I (Syn.subst σ r) (Syn.subst σ p) := by simp [boundStack]
@[simp] theorem subst_codeBound {m : ℕ} (σ : Fin n → PTm m) (I : Instance) (p : PTm n) :
    Syn.subst σ (codeBound I p) = codeBound I (Syn.subst σ p) := by simp [codeBound]
@[simp] theorem subst_hasChain {m : ℕ} (σ : Fin n → PTm m) (I : Instance) (a p : PTm n) :
    (hasChain I a p).subst σ = hasChain I (Syn.subst σ a) (Syn.subst σ p) := by
  simp [hasChain,Syn.subst_shift,Syn.shift_subst]

theorem g_values (I : Instance) (i a b p : PTm n) (hab : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] I.g i a p ≐ I.g i b p :=
  Prf.eqCongr I.G (fun j => by fin_cases j; exact .eqRefl _; exact hab; exact .eqRefl _)
theorem t_values (I : Instance) (i a b c d p : PTm n)
    (hac : Γ ⊢[PRAAx] a ≐ c) (hbd : Γ ⊢[PRAAx] b ≐ d) :
    Γ ⊢[PRAAx] I.t i a b p ≐ I.t i c d p :=
  Prf.eqCongr I.T (fun j => by fin_cases j; exact .eqRefl _; exact hac; exact hbd; exact .eqRefl _)
theorem nonzero_of_eq {a b : PTm n} (hab : Γ ⊢[PRAAx] a ≐ b)
    (hb : Γ ⊢[PRAAx] neg (b ≐ zero)) : Γ ⊢[PRAAx] neg (a ≐ zero) :=
  .impI (.impE hb.wk (hab.wk.eqSymm.eqTrans Prf.hyp0))

theorem chain_at (I : Instance) (s : PTm 1) (p : PTm n) : Γ ⊢[PRAAx]
    ap1 (chainF I s) p ≐ chainCode I s p := by
  simpa [chainF,ap1] using toPR_eq (Γ := Γ) (chainCode I s (var 0)) ![p]
theorem chain_length (I : Instance) (s : PTm 1) (p : PTm n) : Γ ⊢[PRAAx]
    length (chainCode I s p) ≐ succ (I.h p) := MasterCertificate.sequence_length _ _ _
theorem chain_lookup (I : Instance) (s : PTm 1) (p t : PTm n)
    (ht : Γ ⊢[PRAAx] le t (I.h p)) : Γ ⊢[PRAAx]
    entry (chainCode I s p) t ≐ chain I s t p := by
  have e := MasterCertificate.sequence_decode (chainBody I s) (x := p)
    ((succ_monus_succ _ _).eqTrans ht)
  simpa [chainCode,chainBody,inst2] using e
theorem chain_start (I : Instance) (s : PTm 1) (p : PTm n) : Γ ⊢[PRAAx]
    entry (chainCode I s p) zero ≐ start s p :=
  (chain_lookup I s p zero (zero_le _)).eqTrans (chain_zero I s p)

theorem local_at (I : Instance) (S p t : PTm n) (h : Γ ⊢[PRAAx] admissibleCode I S p)
    (ht : Γ ⊢[PRAAx] le t (I.h p)) : Γ ⊢[PRAAx]
    lt (entry S t) (I.bd t p) ⋏ neg (I.g t (entry S t) p ≐ zero) := by
  have rule : Γ ⊢[PRAAx] le t (I.h p) ⟶
      (lt (entry S t) (I.bd t p) ⋏ neg (I.g t (entry S t) p ≐ zero)) := by
    simpa [localCode] using (Prf.andE₁ (Prf.andE₂ h)).allE t
  exact .impE rule ht
theorem edge_at (I : Instance) (S p t : PTm n) (h : Γ ⊢[PRAAx] admissibleCode I S p)
    (ht : Γ ⊢[PRAAx] lt t (I.h p)) : Γ ⊢[PRAAx]
    neg (I.t t (entry S t) (entry S (succ t)) p ≐ zero) := by
  have rule : Γ ⊢[PRAAx] lt t (I.h p) ⟶ neg (I.t t (entry S t) (entry S (succ t)) p ≐ zero) := by
    simpa [edgeCode] using (Prf.andE₂ (Prf.andE₂ h)).allE t
  exact .impE rule ht

theorem produced_admissible (I : Instance) (s : PTm 1) (p : PTm n)
    (h : Γ ⊢[PRAAx] viableStart I (start s p) p) : Γ ⊢[PRAAx]
    admissibleCode I (chainCode I s p) p := by
  refine .andI (chain_length I s p) (.andI ?_ ?_)
  · refine .allI (.impI ?_)
    have hs : Γ.map Fm.shift ⊢[PRAAx] viableStart I (start s (Syn.shift p)) (Syn.shift p) := by
      simpa only [Fm.shift,subst_viableStart,subst_start,Syn.shift] using h.shift
    simpa only [subst_chainCode,Syn.shift] using
      (.andI (lt_congr (chain_lookup I s (Syn.shift p) (var 0) Prf.hyp0).eqSymm (.eqRefl _)
          (Prf.andE₁ (chain_inv (Prf.andE₁ hs).wk (Prf.andE₂ hs).wk Prf.hyp0)))
        (nonzero_of_eq (g_values I _ _ _ _ (chain_lookup I s (Syn.shift p) (var 0) Prf.hyp0))
          (chain_local (Prf.andE₁ hs).wk (Prf.andE₂ hs).wk Prf.hyp0)))
  · refine .allI (.impI ?_)
    have hs : Γ.map Fm.shift ⊢[PRAAx] viableStart I (start s (Syn.shift p)) (Syn.shift p) := by
      simpa only [Fm.shift,subst_viableStart,subst_start,Syn.shift] using h.shift
    simpa only [subst_chainCode,Syn.shift] using
      nonzero_of_eq (t_values I _ _ _ _ _ _
        (chain_lookup I s (Syn.shift p) (var 0) (le_of_lt Prf.hyp0))
        (chain_lookup I s (Syn.shift p) (succ (var 0)) Prf.hyp0))
        (chain_edge (Prf.andE₁ hs).wk (Prf.andE₂ hs).wk Prf.hyp0)

theorem coded_viable_zero (I : Instance) (S p : PTm n)
    (h : Γ ⊢[PRAAx] admissibleCode I S p) : Γ ⊢[PRAAx]
    I.V zero (entry S (monus (I.h p) zero)) p ≐ one := by
  have terminal := local_at I S p (I.h p) h (le_refl _)
  exact (V_congr I (.eqRefl _) (entry_congr (.eqRefl _) (monus_zero _))).eqTrans
    ((V_zero I (Prf.andE₁ terminal)).eqTrans (FiniteGluing.sg_of_ne (Prf.andE₂ terminal)))

theorem coded_viable_step (I : Instance) (S p j : PTm n)
    (h : Γ ⊢[PRAAx] admissibleCode I S p) (hj : Γ ⊢[PRAAx] lt j (I.h p))
    (ih : Γ ⊢[PRAAx] I.V j (entry S (monus (I.h p) j)) p ≐ one) : Γ ⊢[PRAAx]
    I.V (succ j) (entry S (monus (I.h p) (succ j))) p ≐ one := by
  have now := local_at I S p (monus (I.h p) (succ j)) h (ChainViability.monus_le _ _)
  have next := local_at I S p (monus (I.h p) j) h (ChainViability.monus_le _ _)
  have edge := edge_at I S p _ h (ChainViability.monus_succ_lt hj)
  have positions := entry_congr (Γ := Γ) (.eqRefl S) (succ_monus hj)
  have correct := nonzero_of_eq (t_values I _ _ _ _ _ _ (.eqRefl _) positions).eqSymm edge
  exact V_fold I (Prf.andE₁ now) (Prf.andE₂ now) (Prf.andE₁ next) correct ih

def remainingLaw (I : Instance) (S p j : PTm n) : Fm PTm n :=
  le j (I.h p) ⟶ I.V j (entry S (monus (I.h p) j)) p ≐ one
@[simp] theorem subst_remainingLaw {m : ℕ} (σ : Fin n → PTm m) (I : Instance) (S p j : PTm n) :
    (remainingLaw I S p j).subst σ = remainingLaw I (Syn.subst σ S) (Syn.subst σ p) (Syn.subst σ j) := by
  simp [remainingLaw]

theorem coded_viable (I : Instance) (S p j : PTm n) (h : Γ ⊢[PRAAx] admissibleCode I S p)
    (hj : Γ ⊢[PRAAx] le j (I.h p)) : Γ ⊢[PRAAx]
    I.V j (entry S (monus (I.h p) j)) p ≐ one := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] admissibleCode I (Syn.shift S) (Syn.shift p) := by
    simpa only [Fm.shift,subst_admissibleCode,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (remainingLaw I (Syn.shift S) (Syn.shift p) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_remainingLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (coded_viable_zero I S p h.wk)
    · simp only [subst_remainingLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact .impI (coded_viable_step I _ _ _ hs.wk.wk Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)))
  have rule : Γ ⊢[PRAAx] remainingLaw I S p j := by
    simpa only [subst_remainingLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE rule hj

theorem coded_start_viable (I : Instance) (S p : PTm n) (h : Γ ⊢[PRAAx] admissibleCode I S p) :
    Γ ⊢[PRAAx] viableStart I (entry S zero) p :=
  .andI (Prf.andE₁ (local_at I S p zero h (zero_le _)))
    ((V_congr I (.eqRefl _) (entry_congr (.eqRefl _) (monus_self _))).eqSymm.eqTrans
      (coded_viable I S p (I.h p) h (le_refl _)))

theorem pair_mono {a b A B : PTm n} (ha : Γ ⊢[PRAAx] le a A) (hb : Γ ⊢[PRAAx] le b B) :
    Γ ⊢[PRAAx] le (pairT a b) (pairT A B) := by
  have sum := add_le_add₂ ha hb
  exact add_le_add₂ (le_trans (mul_le_mul_right (a+b) sum)
    (le_congr (mul_comm (a+b) (A+B)) (.eqRefl _) (mul_le_mul_right (A+B) sum))) ha
theorem boundStack_zero (I : Instance) (p : PTm n) : Γ ⊢[PRAAx] boundStack I zero p ≐ zero := by
  simpa [boundStack] using rec2_zero (Γ := Γ) zero (boundStep I) p
theorem boundStack_succ (I : Instance) (r p : PTm n) : Γ ⊢[PRAAx]
    boundStack I (succ r) p ≐ pairT (I.bd r p) (boundStack I r p) := by
  simpa [boundStep,boundStack] using rec2_succ (Γ := Γ) zero (boundStep I) r p

def sizeLaw (I : Instance) (s : PTm 1) (p r : PTm n) : Fm PTm n :=
  le r (succ (I.h p)) ⟶ le (stack (chainBody I s) r p) (boundStack I r p)
@[simp] theorem subst_sizeLaw {m : ℕ} (σ : Fin n → PTm m) (I : Instance) (s : PTm 1) (p r : PTm n) :
    (sizeLaw I s p r).subst σ = sizeLaw I s (Syn.subst σ p) (Syn.subst σ r) := by simp [sizeLaw,stack]

theorem stack_bound_step (I : Instance) (s : PTm 1) (p r : PTm n)
    (h : Γ ⊢[PRAAx] viableStart I (start s p) p) (hr : Γ ⊢[PRAAx] le r (I.h p))
    (ih : Γ ⊢[PRAAx] le (stack (chainBody I s) r p) (boundStack I r p)) : Γ ⊢[PRAAx]
    le (stack (chainBody I s) (succ r) p) (boundStack I (succ r) p) := by
  have bound := le_of_lt (Prf.andE₁ (chain_inv (Prf.andE₁ h) (Prf.andE₂ h) hr))
  have step := stack_succ (Γ := Γ) (chainBody I s) r p
  have body : inst2 (chainBody I s) r p = chain I s r p := by simp [chainBody,inst2]
  rw [body] at step
  exact le_congr step.eqSymm (boundStack_succ I r p).eqSymm (pair_mono bound ih)

theorem produced_size_bound (I : Instance) (s : PTm 1) (p : PTm n)
    (h : Γ ⊢[PRAAx] viableStart I (start s p) p) : Γ ⊢[PRAAx]
    lt (chainCode I s p) (codeBound I p) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] viableStart I (start s (Syn.shift p)) (Syn.shift p) := by
    simpa only [Fm.shift,subst_viableStart,subst_start,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (sizeLaw I s (Syn.shift p) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp only [subst_sizeLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (le_congr (stack_zero _ _).eqSymm (boundStack_zero _ _).eqSymm (le_refl zero))
    · simp only [subst_sizeLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI (stack_bound_step I s _ _ hs.wk.wk ?_
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)))
      exact (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  have final : Γ ⊢[PRAAx] sizeLaw I s p (succ (I.h p)) := by
    simpa only [subst_sizeLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE (succ (I.h p))
  have bound : Γ ⊢[PRAAx] le (chainCode I s p)
      (pairT (succ (I.h p)) (boundStack I (succ (I.h p)) p)) :=
    pair_mono (le_refl _) (.impE final (le_refl _))
  exact (succ_monus_succ _ _).eqTrans bound

theorem chain_exists (I : Instance) (s : PTm 1) (p : PTm n)
    (h : Γ ⊢[PRAAx] viableStart I (start s p) p) : Γ ⊢[PRAAx] hasChain I (start s p) p := by
  apply Prf.exI (t := chainCode I s p)
  simpa [hasChain] using .andI (produced_size_bound I s p h)
    (.andI (produced_admissible I s p h) (chain_start I s p))

theorem exists_start_viable (I : Instance) (a p : PTm n)
    (h : Γ ⊢[PRAAx] hasChain I a p) : Γ ⊢[PRAAx] viableStart I a p := by
  refine .exE h ?_
  let Δ := (lt (var 0) (codeBound I (Syn.shift p)) ⋏
    (admissibleCode I (var 0) (Syn.shift p) ⋏ entry (var 0) zero ≐ Syn.shift a)) :: Γ.map Fm.shift
  have correct := coded_start_viable (Γ := Δ) I (var 0) (Syn.shift p) (Prf.andE₁ (Prf.andE₂ Prf.hyp0))
  have initial : Δ ⊢[PRAAx] entry (var 0) zero ≐ Syn.shift a := Prf.andE₂ (Prf.andE₂ Prf.hyp0)
  have moved : Δ ⊢[PRAAx] viableStart I (Syn.shift a) (Syn.shift p) := by
    refine .andI (lt_congr initial (.eqRefl _) (Prf.andE₁ correct)) ?_
    exact (V_congr I (.eqRefl _) initial.eqSymm).eqTrans (Prf.andE₂ correct)
  simpa only [Δ,Fm.shift,subst_viableStart,Syn.shift] using moved

theorem coded_chain_iff (I : Instance) (s : PTm 1) (p : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (viableStart I (start s p) p) (hasChain I (start s p) p) :=
  .andI (.impI (chain_exists I s p Prf.hyp0)) (.impI (exists_start_viable I _ p Prf.hyp0))

theorem actual_chain_program_closed (I : Instance) (s : PTm 1) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (ap1 (chainF I s) (var 0) ≐ chainCode I s (var 0)) := closeUniv 1 (chain_at I s _)
theorem actual_chain_lookup_closed (I : Instance) (s : PTm 1) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (var 1) (I.h (var 0)) ⟶ entry (chainCode I s (var 0)) (var 1) ≐ chain I s (var 1) (var 0)) :=
  closeUniv 2 (.impI (chain_lookup I s _ _ Prf.hyp0))
theorem produced_admissible_code_closed (I : Instance) (s : PTm 1) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (viableStart I (start s (var 0)) (var 0) ⟶
      (admissibleCode I (chainCode I s (var 0)) (var 0) ⋏ lt (chainCode I s (var 0)) (codeBound I (var 0)))) :=
  closeUniv 1 (.impI (.andI (produced_admissible I s _ Prf.hyp0) (produced_size_bound I s _ Prf.hyp0)))
theorem arbitrary_coded_chain_viable_closed (I : Instance) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (admissibleCode I (var 1) (var 0) ⟶ le (var 2) (I.h (var 0)) ⟶
      I.V (var 2) (entry (var 1) (monus (I.h (var 0)) (var 2))) (var 0) ≐ one) :=
  closeUniv 3 (.impI (.impI (coded_viable I _ _ _ Prf.hyp1 Prf.hyp0)))
theorem coded_viability_equivalence_closed (I : Instance) (s : PTm 1) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (Fm.iff (viableStart I (start s (var 0)) (var 0)) (hasChain I (start s (var 0)) (var 0))) :=
  closeUniv 1 (coded_chain_iff I s _)

end LeanProofs.IPRA.Foundations.CodedViableChain
