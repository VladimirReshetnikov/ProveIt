import IPRADerivations.Foundations.BoundedEnumeration
import IPRADerivations.Foundations.CodedViableChain

/-!
# Actual stored increasing lists for bounded decidable subsets

The fixed syntax K decides retention by nonzeroness. Numerical P and p are
packed as data; an actual PR2 program stores every selected label in the
checked sequence encoding. Length, lookup, boundedness, retainedness,
completeness and increasing order are derived from rank/select, never
supplied as properties of the returned code. Zero count and zero cutoff
are included. The size bound is a separate PR pairing stack of the label
bound P and the computed count; it does not inspect the produced list.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Foundations.FilteredEnumerationCode

open_ipra exports
open LeanProofs.IPRA.Foundations.FilteredEnumeration (rank sel sel_spec sel_rank rank_lt_size rank_mono)
open LeanProofs.IPRA.Foundations.MasterCertificate (sequence entry stack stack_zero stack_succ)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (P p : PTm n) : PTm n := pairT P p
def count (K : PTm 2) (P p : PTm n) : PTm n := rank K P p
def values (K : PTm 2) : PTm 2 := sel K (var 0) (fstT (var 1)) (sndT (var 1))
def list (K : PTm 2) (P p : PTm n) : PTm n := sequence (values K) (count K P p) (data P p)
def outputF (K : PTm 2) : PR 2 := PTm.toPR (list K (var 0) (var 1))
def run (K : PTm 2) (P p : PTm n) : PTm n := ap2 (outputF K) P p
def boundStep : PTm 3 := pairT (var 2) (var 1)
def boundF : PR 2 := rec2 zero boundStep
def boundStack (P r : PTm n) : PTm n := ap2 boundF r P
def codeBound (K : PTm 2) (P p : PTm n) : PTm n :=
  succ (pairT (count K P p) (boundStack P (count K P p)))
def boundProgramF (K : PTm 2) : PR 2 := PTm.toPR (codeBound K (var 0) (var 1))

ipra_subst data
ipra_subst count [rank]
ipra_subst sel [BoundedReflection.wit]
ipra_subst list
ipra_subst run
ipra_subst boundStack
ipra_subst codeBound

theorem sel_congr (K : PTm 2) {r r' P P' p p' : PTm n}
    (hr : Γ ⊢[PRAAx] r ≐ r') (hP : Γ ⊢[PRAAx] P ≐ P') (hp : Γ ⊢[PRAAx] p ≐ p') : Γ ⊢[PRAAx]
    sel K r P p ≐ sel K r' P' p' := by
  ipra_congr (sel K (var 0) (var 1) (var 2) : PTm 3) with [hr, hP, hp]

theorem values_at (K : PTm 2) (r P p : PTm n) : Γ ⊢[PRAAx]
    inst2 (values K) r (data P p) ≐ sel K r P p := by
  simpa only [values,inst2,subst_sel,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,data] using
    sel_congr K (.eqRefl r) (fst_pair P p) (snd_pair P p)

theorem list_length (K : PTm 2) (P p : PTm n) : Γ ⊢[PRAAx]
    length (list K P p) ≐ count K P p := MasterCertificate.sequence_length _ _ _
theorem list_lookup (K : PTm 2) (P p r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count K P p)) : Γ ⊢[PRAAx]
    entry (list K P p) r ≐ sel K r P p :=
  (MasterCertificate.sequence_decode (values K) (x := data P p) hr).eqTrans (values_at K r P p)
theorem entry_bound (K : PTm 2) (P p r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count K P p)) : Γ ⊢[PRAAx]
    lt (entry (list K P p) r) P :=
  lt_congr (list_lookup K P p r hr).eqSymm (.eqRefl _) (Prf.andE₁ (sel_spec K hr))
theorem entry_valid (K : PTm 2) (P p r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count K P p)) : Γ ⊢[PRAAx]
    neg (inst2 K (entry (list K P p) r) p ≐ zero) := by
  refine .impI ?_
  have e : (inst2 K (entry (list K P p) r) p ≐ zero) :: Γ ⊢[PRAAx]
      inst2 K (entry (list K P p) r) p ≐ inst2 K (sel K r P p) p :=
    congrInst2 K (list_lookup K P p r hr).wk (.eqRefl p)
  exact .impE (Prf.andE₁ (Prf.andE₂ (sel_spec K hr))).wk (e.eqSymm.eqTrans Prf.hyp0)

theorem listed (K : PTm 2) (P p a : PTm n) (ha : Γ ⊢[PRAAx] lt a P)
    (hK : Γ ⊢[PRAAx] neg (inst2 K a p ≐ zero)) : Γ ⊢[PRAAx]
    lt (rank K a p) (count K P p) ⋏ entry (list K P p) (rank K a p) ≐ a :=
  .andI (rank_lt_size K ha hK) ((list_lookup K P p _ (rank_lt_size K ha hK)).eqTrans (sel_rank K ha hK))

theorem selected_increasing (K : PTm 2) (P p r s : PTm n)
    (hrs : Γ ⊢[PRAAx] lt r s) (hs : Γ ⊢[PRAAx] lt s (count K P p)) : Γ ⊢[PRAAx]
    lt (sel K r P p) (sel K s P p) := by
  have hr := lt_of_lt_of_le hrs (le_of_lt hs)
  have er := Prf.andE₂ (Prf.andE₂ (sel_spec K hr))
  have es := Prf.andE₂ (Prf.andE₂ (sel_spec K hs))
  refine .orE (lt_or_le (sel K r P p) (sel K s P p)) Prf.hyp0 ?_
  exact .botE _ (le_lt_absurd _ (le_congr es.wk er.wk (rank_mono K Prf.hyp0 p)) hrs.wk)
theorem increasing (K : PTm 2) (P p r s : PTm n)
    (hrs : Γ ⊢[PRAAx] lt r s) (hs : Γ ⊢[PRAAx] lt s (count K P p)) : Γ ⊢[PRAAx]
    lt (entry (list K P p) r) (entry (list K P p) s) :=
  lt_congr (list_lookup K P p r (lt_of_lt_of_le hrs (le_of_lt hs))).eqSymm
    (list_lookup K P p s hs).eqSymm (selected_increasing K P p r s hrs hs)

alias sg_le_one := Common.sg_le_one

theorem count_le (K : PTm 2) (P p : PTm n) : Γ ⊢[PRAAx] le (count K P p) P := by
  have all : Γ ⊢[PRAAx] .all (le (count K (var 0) (Syn.shift p)) (var 0)) := by
    ipra_qfind (le_QF _ _) [subst_le, subst_count]
    · exact le_congr (FilteredEnumeration.rank_zero K p).eqSymm (.eqRefl _) (le_refl zero)
    · exact le_congr (FilteredEnumeration.rank_succ K _ _).eqSymm (succ_eq_add_one _).eqSymm
        (add_le_add₂ Prf.hyp0 (sg_le_one _))
  simpa only [subst_le,subst_count,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE P

theorem bound_zero (P : PTm n) : Γ ⊢[PRAAx] boundStack P zero ≐ zero := by
  simpa [boundStack,boundF] using rec2_zero (Γ := Γ) zero boundStep P
theorem bound_succ (P r : PTm n) : Γ ⊢[PRAAx] boundStack P (succ r) ≐ pairT P (boundStack P r) := by
  simpa [boundStep,boundStack,boundF] using rec2_succ (Γ := Γ) zero boundStep r P

def sizeLaw (K : PTm 2) (P p r : PTm n) : Fm PTm n :=
  le r (count K P p) ⟶ le (stack (values K) r (data P p)) (boundStack P r)
ipra_subst sizeLaw [stack]

theorem stack_bound_step (K : PTm 2) (P p r : PTm n)
    (hr : Γ ⊢[PRAAx] lt r (count K P p))
    (ih : Γ ⊢[PRAAx] le (stack (values K) r (data P p)) (boundStack P r)) : Γ ⊢[PRAAx]
    le (stack (values K) (succ r) (data P p)) (boundStack P (succ r)) := by
  have actual := (stack_succ (Γ := Γ) (values K) r (data P p)).eqTrans
    (congrPairT (values_at K r P p) (.eqRefl _))
  exact le_congr actual.eqSymm (bound_succ P r).eqSymm
    (CodedViableChain.pair_mono (le_of_lt (Prf.andE₁ (sel_spec K hr))) ih)

theorem size_bound (K : PTm 2) (P p : PTm n) : Γ ⊢[PRAAx] lt (list K P p) (codeBound K P p) := by
  let inv := le (stack (values K) (var 0) (data (Syn.shift P) (Syn.shift p))) (boundStack (Syn.shift P) (var 0))
  have result : Γ ⊢[PRAAx] inv.subst (Syn.inst (count K P p)) := by
    refine qfIndUpTo (count K P p) (le_QF _ _) ?_ ?_
    · simpa [inv] using le_congr (stack_zero (Γ := Γ) (values K) _).eqSymm (bound_zero P).eqSymm (le_refl zero)
    · have shiftBound : Syn.shift (count K P p) = count K (Syn.shift P) (Syn.shift p) := by simp [Syn.shift]
      simp [inv, shiftBound]
      exact .impI (stack_bound_step K _ _ _ Prf.hyp0 Prf.hyp1)
  exact (succ_monus_succ _ _).eqTrans
    (CodedViableChain.pair_mono (le_refl _) (by simpa [inv] using result))

theorem output_at (K : PTm 2) (P p : PTm n) : Γ ⊢[PRAAx] run K P p ≐ list K P p := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (list K (var 0) (var 1) : PTm 2) ![P,p]
theorem returned_length (K : PTm 2) (P p : PTm n) : Γ ⊢[PRAAx]
    length (run K P p) ≐ count K P p := (congrFst (output_at K P p)).eqTrans (list_length K P p)
theorem returned_lookup (K : PTm 2) (P p r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count K P p)) : Γ ⊢[PRAAx]
    entry (run K P p) r ≐ sel K r P p :=
  (entry_congr (output_at K P p) (.eqRefl _)).eqTrans (list_lookup K P p r hr)
theorem returned_entry_bound (K : PTm 2) (P p r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count K P p)) : Γ ⊢[PRAAx]
    lt (entry (run K P p) r) P :=
  lt_congr (entry_congr (output_at K P p) (.eqRefl _)).eqSymm (.eqRefl _) (entry_bound K P p r hr)
theorem returned_entry_valid (K : PTm 2) (P p r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count K P p)) : Γ ⊢[PRAAx]
    neg (inst2 K (entry (run K P p) r) p ≐ zero) :=
  CodedViableChain.nonzero_of_eq (congrInst2 K (entry_congr (output_at K P p) (.eqRefl _)) (.eqRefl _))
    (entry_valid K P p r hr)
theorem returned_listed (K : PTm 2) (P p a : PTm n) (ha : Γ ⊢[PRAAx] lt a P)
    (hK : Γ ⊢[PRAAx] neg (inst2 K a p ≐ zero)) : Γ ⊢[PRAAx]
    lt (rank K a p) (count K P p) ⋏ entry (run K P p) (rank K a p) ≐ a :=
  .andI (Prf.andE₁ (listed K P p a ha hK))
    ((entry_congr (output_at K P p) (.eqRefl _)).eqTrans (Prf.andE₂ (listed K P p a ha hK)))
theorem returned_increasing (K : PTm 2) (P p r s : PTm n)
    (hrs : Γ ⊢[PRAAx] lt r s) (hs : Γ ⊢[PRAAx] lt s (count K P p)) : Γ ⊢[PRAAx]
    lt (entry (run K P p) r) (entry (run K P p) s) :=
  lt_congr (entry_congr (output_at K P p) (.eqRefl _)).eqSymm
    (entry_congr (output_at K P p) (.eqRefl _)).eqSymm (increasing K P p r s hrs hs)
theorem returned_size_bound (K : PTm 2) (P p : PTm n) : Γ ⊢[PRAAx] lt (run K P p) (codeBound K P p) :=
  lt_congr (output_at K P p).eqSymm (.eqRefl _) (size_bound K P p)
theorem bound_program_at (K : PTm 2) (P p : PTm n) : Γ ⊢[PRAAx]
    ap2 (boundProgramF K) P p ≐ codeBound K P p := by
  simpa [boundProgramF,ap2] using toPR_eq (Γ := Γ) (codeBound K (var 0) (var 1) : PTm 2) ![P,p]

theorem actual_stored_list_program_closed (K : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run K (var 0) (var 1) ≐ list K (var 0) (var 1) ⋏
      length (run K (var 0) (var 1)) ≐ count K (var 0) (var 1)) :=
  closeUniv 2 (.andI (output_at K _ _) (returned_length K _ _))
theorem actual_stored_list_lookup_closed (K : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (count K (var 0) (var 1)) ⟶
      entry (run K (var 0) (var 1)) (var 2) ≐ sel K (var 2) (var 0) (var 1)) :=
  closeUniv 3 (.impI (returned_lookup K _ _ _ Prf.hyp0))
theorem actual_stored_list_complete_closed (K : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (var 0) ⟶ neg (inst2 K (var 2) (var 1) ≐ zero) ⟶
      (lt (rank K (var 2) (var 1)) (count K (var 0) (var 1)) ⋏
        entry (run K (var 0) (var 1)) (rank K (var 2) (var 1)) ≐ var 2)) :=
  closeUniv 3 (.impI (.impI (returned_listed K _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_stored_list_sound_closed (K : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (count K (var 0) (var 1)) ⟶
      (lt (entry (run K (var 0) (var 1)) (var 2)) (var 0) ⋏
        neg (inst2 K (entry (run K (var 0) (var 1)) (var 2)) (var 1) ≐ zero))) :=
  closeUniv 3 (.impI (.andI (returned_entry_bound K _ _ _ Prf.hyp0) (returned_entry_valid K _ _ _ Prf.hyp0)))
theorem actual_stored_list_increasing_closed (K : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 2) (var 3) ⟶ lt (var 3) (count K (var 0) (var 1)) ⟶
      lt (entry (run K (var 0) (var 1)) (var 2)) (entry (run K (var 0) (var 1)) (var 3))) :=
  closeUniv 4 (.impI (.impI (returned_increasing K _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_stored_list_size_closed (K : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (count K (var 0) (var 1)) (var 0) ⋏ lt (run K (var 0) (var 1)) (codeBound K (var 0) (var 1))) :=
  closeUniv 2 (.andI (count_le K _ _) (returned_size_bound K _ _))
theorem actual_list_bound_program_closed (K : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 (boundProgramF K) (var 0) (var 1) ≐ codeBound K (var 0) (var 1)) :=
  closeUniv 2 (bound_program_at K _ _)

end LeanProofs.IPRA.Foundations.FilteredEnumerationCode
