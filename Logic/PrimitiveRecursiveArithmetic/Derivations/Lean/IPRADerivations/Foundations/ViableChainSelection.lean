import IPRADerivations.Foundations.CodedViableChain
import IPRADerivations.Core.SubstCommand

/-!
# Automatic initial selection and tagged coded viable chains

Source: `ipra_evidence_framework/report.tex`, theorem "PR backward viability
and certified finite chain", lines 44--52. The initial test is the actual
backward row bit. Bounded search selects its least successful candidate.
The output pairs the success bit with the genuine h+1 chain code, or zero
on failure. Success is proved equivalent to bounded existence of ANY
admissible full-horizon coded chain, with no supplied success or selector
contract. A size bound for the entire tagged output is independent of the
tests and the chosen start. All parameters and candidate/code indices are
internal; only the fixed finite compatibility instance is external syntax.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.ViableChainSelection

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.BackwardViability
open LeanProofs.IPRA.Foundations.BackwardViability.Instance
open LeanProofs.IPRA.Foundations.ViableChain (start)
open LeanProofs.IPRA.Foundations.CodedViableChain (viableStart admissibleCode codeBound)
open LeanProofs.IPRA.Foundations.BoundedReflection (exB wit ex_cases ex_elim ex_intro ex_least one_ne_zero)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def initialBody (I : Instance) : PTm 2 := I.V (I.h (var 1)) (var 0) (var 1)
def flag (I : Instance) (p : PTm n) : PTm n := exB (initialBody I) (I.bd zero p) p
def selected (I : Instance) (p : PTm n) : PTm n := wit (initialBody I) (I.bd zero p) p
def startBody (I : Instance) : PTm 1 := selected I (var 0)
def rawChain (I : Instance) (p : PTm n) : PTm n := CodedViableChain.chainCode I (startBody I) p
def payload (I : Instance) (p : PTm n) : PTm n := flag I p*rawChain I p
def output (I : Instance) (p : PTm n) : PTm n := pairT (flag I p) (payload I p)
def outputF (I : Instance) : PR 1 := PTm.toPR (output I (var 0))
def returnBound (I : Instance) (p : PTm n) : PTm n := succ (pairT one (codeBound I p))
def hasChain (I : Instance) (p : PTm n) : Fm PTm n := .ex
  (lt (var 0) (codeBound I (Syn.shift p)) ⋏ admissibleCode I (var 0) (Syn.shift p))

ipra_subst flag [BoundedReflection.exB]
ipra_subst selected
ipra_subst rawChain
ipra_subst payload
ipra_subst output
ipra_subst returnBound
ipra_subst hasChain [Syn.subst_shift, Syn.shift_subst]

theorem initial_at (I : Instance) (a p : PTm n) : inst2 (initialBody I) a p = I.V (I.h p) a p := by
  simp [initialBody,inst2]
theorem start_at (I : Instance) (p : PTm n) : start (startBody I) p = selected I p := by simp [start,startBody]
theorem flag_bit (I : Instance) (p : PTm n) : Γ ⊢[PRAAx] (flag I p ≐ zero) ⋎ (flag I p ≐ one) :=
  ex_cases _ _ _
theorem viability_bit (I : Instance) (a p : PTm n) : Γ ⊢[PRAAx]
    (I.V (I.h p) a p ≐ zero) ⋎ (I.V (I.h p) a p ≐ one) :=
  bit_of_lt_two (FiniteSetExponential.dg_lt two_pos _ _)
theorem nonzero_of_one {a : PTm n} (h : Γ ⊢[PRAAx] a ≐ one) : Γ ⊢[PRAAx] neg (a ≐ zero) :=
  .impI (one_ne_zero _ (h.wk.eqSymm.eqTrans Prf.hyp0))

theorem selected_viable (I : Instance) (p : PTm n) (h : Γ ⊢[PRAAx] flag I p ≐ one) :
    Γ ⊢[PRAAx] viableStart I (selected I p) p := by
  have witness := ex_elim (initialBody I) h
  have nonzero : Γ ⊢[PRAAx] neg (I.V (I.h p) (selected I p) p ≐ zero) := by
    simpa only [initial_at,selected] using Prf.andE₂ witness
  exact .andI (Prf.andE₁ witness) (FiniteGluing.one_of_ne (viability_bit I _ p) nonzero)

/-- Earlier candidates really have zero viability, including the default
search case. This is least initial viability, not raw-code tie breaking. -/
theorem least_initial (I : Instance) (p a : PTm n) (ha : Γ ⊢[PRAAx] lt a (selected I p)) :
    Γ ⊢[PRAAx] I.V (I.h p) a p ≐ zero := by
  simpa only [initial_at] using ex_least (initialBody I) ha

theorem rawChain_length (I : Instance) (p : PTm n) : Γ ⊢[PRAAx]
    length (rawChain I p) ≐ succ (I.h p) := CodedViableChain.chain_length _ _ _
theorem rawChain_start (I : Instance) (p : PTm n) : Γ ⊢[PRAAx]
    entry (rawChain I p) zero ≐ selected I p := by
  simpa only [start_at,rawChain] using CodedViableChain.chain_start (Γ := Γ) I (startBody I) p
theorem rawChain_correct (I : Instance) (p : PTm n) (h : Γ ⊢[PRAAx] flag I p ≐ one) :
    Γ ⊢[PRAAx] admissibleCode I (rawChain I p) p := by
  have hs : Γ ⊢[PRAAx] viableStart I (start (startBody I) p) p := by
    simpa only [start_at] using selected_viable I p h
  exact CodedViableChain.produced_admissible I (startBody I) p hs
theorem rawChain_bound (I : Instance) (p : PTm n) (h : Γ ⊢[PRAAx] flag I p ≐ one) :
    Γ ⊢[PRAAx] lt (rawChain I p) (codeBound I p) := by
  have hs : Γ ⊢[PRAAx] viableStart I (start (startBody I) p) p := by
    simpa only [start_at] using selected_viable I p h
  exact CodedViableChain.produced_size_bound I (startBody I) p hs

theorem payload_success (I : Instance) (p : PTm n) (h : Γ ⊢[PRAAx] flag I p ≐ one) :
    Γ ⊢[PRAAx] payload I p ≐ rawChain I p := (congrMul h (.eqRefl _)).eqTrans (one_mul _)
theorem payload_failure (I : Instance) (p : PTm n) (h : Γ ⊢[PRAAx] flag I p ≐ zero) :
    Γ ⊢[PRAAx] payload I p ≐ zero := (congrMul h (.eqRefl _)).eqTrans (zero_mul _)
theorem output_success (I : Instance) (p : PTm n) (h : Γ ⊢[PRAAx] flag I p ≐ one) :
    Γ ⊢[PRAAx] output I p ≐ pairT one (rawChain I p) := congrPairT h (payload_success I p h)
theorem output_failure (I : Instance) (p : PTm n) (h : Γ ⊢[PRAAx] flag I p ≐ zero) :
    Γ ⊢[PRAAx] output I p ≐ pairT zero zero := congrPairT h (payload_failure I p h)

theorem chain_implies_success (I : Instance) (S p : PTm n)
    (h : Γ ⊢[PRAAx] admissibleCode I S p) : Γ ⊢[PRAAx] flag I p ≐ one := by
  have viable := CodedViableChain.coded_start_viable I S p h
  have test : Γ ⊢[PRAAx] neg (inst2 (initialBody I) (entry S zero) p ≐ zero) := by
    simpa only [initial_at] using nonzero_of_one (Prf.andE₂ viable)
  exact ex_intro (initialBody I) test (Prf.andE₁ viable)

theorem success_hasChain (I : Instance) (p : PTm n) (h : Γ ⊢[PRAAx] flag I p ≐ one) :
    Γ ⊢[PRAAx] hasChain I p := by
  apply Prf.exI (t := rawChain I p)
  simpa [hasChain] using .andI (rawChain_bound I p h) (rawChain_correct I p h)
theorem hasChain_success (I : Instance) (p : PTm n) (h : Γ ⊢[PRAAx] hasChain I p) :
    Γ ⊢[PRAAx] flag I p ≐ one := by
  refine .exE h ?_
  simpa only [Fm.shift,Fm.subst_eq,subst_flag,Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    chain_implies_success (Γ := (lt (var 0) (codeBound I (Syn.shift p)) ⋏
      admissibleCode I (var 0) (Syn.shift p)) :: Γ.map Fm.shift)
      I (var 0) (Syn.shift p) (Prf.andE₂ Prf.hyp0)
theorem success_iff_hasChain (I : Instance) (p : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (flag I p ≐ one) (hasChain I p) :=
  .andI (.impI (success_hasChain I p Prf.hyp0)) (.impI (hasChain_success I p Prf.hyp0))
theorem failure_excludes_chain (I : Instance) (S p : PTm n) (h : Γ ⊢[PRAAx] flag I p ≐ zero) :
    Γ ⊢[PRAAx] neg (admissibleCode I S p) :=
  .impI (one_ne_zero _ ((chain_implies_success I S p Prf.hyp0).eqSymm.eqTrans h.wk))

theorem output_bound (I : Instance) (p : PTm n) : Γ ⊢[PRAAx] lt (output I p) (returnBound I p) := by
  refine .orE (flag_bit I p) ?_ ?_
  · have native := CodedViableChain.pair_mono (Γ := (flag I p ≐ zero) :: Γ)
      (zero_le one) (zero_le (codeBound I p))
    exact (succ_monus_succ _ _).eqTrans (le_congr (output_failure I p Prf.hyp0).eqSymm (.eqRefl _) native)
  · have native := CodedViableChain.pair_mono (Γ := (flag I p ≐ one) :: Γ)
      (le_refl one) (le_of_lt (rawChain_bound I p Prf.hyp0))
    exact (succ_monus_succ _ _).eqTrans (le_congr (output_success I p Prf.hyp0).eqSymm (.eqRefl _) native)

theorem output_at (I : Instance) (p : PTm n) : Γ ⊢[PRAAx]
    ap1 (outputF I) p ≐ output I p := by
  simpa [outputF,ap1] using toPR_eq (Γ := Γ) (output I (var 0)) ![p]
theorem returned_flag (I : Instance) (p : PTm n) : Γ ⊢[PRAAx]
    fstT (ap1 (outputF I) p) ≐ flag I p :=
  (congrFst (output_at I p)).eqTrans (fst_pair _ _)
theorem returned_payload (I : Instance) (p : PTm n) : Γ ⊢[PRAAx]
    sndT (ap1 (outputF I) p) ≐ payload I p :=
  (congrSnd (output_at I p)).eqTrans (snd_pair _ _)
theorem returned_admissible (I : Instance) (p : PTm n) (h : Γ ⊢[PRAAx] flag I p ≐ one) :
    Γ ⊢[PRAAx] admissibleCode I (sndT (ap1 (outputF I) p)) p := by
  have e := (returned_payload I p).eqTrans (payload_success I p h)
  simpa only [CodedViableChain.subst_admissibleCode,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    Prf.eqSubst (admissibleCode I (var 0) (Syn.shift p)) (Syn.inst (rawChain I p))
    (Syn.inst (sndT (ap1 (outputF I) p))) (fun i => by
      cases i using Fin.cases
      · exact e.eqSymm
      · exact .eqRefl _) (by simpa using rawChain_correct I p h)
theorem returned_bound (I : Instance) (p : PTm n) : Γ ⊢[PRAAx]
    lt (ap1 (outputF I) p) (returnBound I p) := lt_congr (output_at I p).eqSymm (.eqRefl _) (output_bound I p)

theorem least_initial_candidate_closed (I : Instance) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (selected I (var 0)) ⟶ I.V (I.h (var 0)) (var 1) (var 0) ≐ zero) :=
  closeUniv 2 (.impI (least_initial I _ _ Prf.hyp0))
theorem selected_start_viable_closed (I : Instance) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (flag I (var 0) ≐ one ⟶ viableStart I (selected I (var 0)) (var 0)) :=
  closeUniv 1 (.impI (selected_viable I _ Prf.hyp0))
theorem automatic_coded_chain_existence_closed (I : Instance) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (Fm.iff (flag I (var 0) ≐ one) (hasChain I (var 0))) := closeUniv 1 (success_iff_hasChain I _)
theorem arbitrary_chain_success_closed (I : Instance) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (admissibleCode I (var 1) (var 0) ⟶ flag I (var 0) ≐ one) :=
  closeUniv 2 (.impI (chain_implies_success I _ _ Prf.hyp0))
theorem tagged_chain_program_closed (I : Instance) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (ap1 (outputF I) (var 0) ≐ output I (var 0) ⋏
      (fstT (ap1 (outputF I) (var 0)) ≐ flag I (var 0) ⋏
        sndT (ap1 (outputF I) (var 0)) ≐ payload I (var 0))) :=
  closeUniv 1 (.andI (output_at I _) (.andI (returned_flag I _) (returned_payload I _)))
theorem tagged_chain_success_closed (I : Instance) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (flag I (var 0) ≐ one ⟶
      (admissibleCode I (sndT (ap1 (outputF I) (var 0))) (var 0) ⋏
        lt (ap1 (outputF I) (var 0)) (returnBound I (var 0)))) :=
  closeUniv 1 (.impI (.andI (returned_admissible I _ Prf.hyp0) (returned_bound I _)))
theorem tagged_chain_failure_closed (I : Instance) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (flag I (var 0) ≐ zero ⟶ ap1 (outputF I) (var 0) ≐ pairT zero zero) :=
  closeUniv 1 (.impI ((output_at I _).eqTrans (output_failure I _ Prf.hyp0)))
theorem tagged_chain_size_bound_closed (I : Instance) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (lt (ap1 (outputF I) (var 0)) (returnBound I (var 0))) := closeUniv 1 (returned_bound I _)

end LeanProofs.IPRA.Foundations.ViableChainSelection
