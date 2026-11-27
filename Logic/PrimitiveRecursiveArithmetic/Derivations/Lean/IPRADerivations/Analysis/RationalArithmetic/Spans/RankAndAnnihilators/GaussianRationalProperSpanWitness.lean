import IPRADerivations.Analysis.LinearAlgebra.Cofactors.Vectors.GaussianRationalAnnihilatorVector
import IPRADerivations.Analysis.RationalArithmetic.Spans.GaussianRationalRowSpan

/-!
# An actual vector outside the original row span

The actual deficient pivot count supplies a free column and a computed
nonzero annihilator. The numerical unit vector at that column pairs to
one with the SAME annihilator, by the genuine finite delta-sum theorem.
Every original row combination pairs to zero, so no numerical coefficient
vector represents the produced unit vector in the original row span.

All dimensions and data remain numerical. No outside-vector, dot-product
or successful search law is an input, and no full-rank converse is used.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalProperSpanWitness

open_ipra
open GaussianRationalHorner (qzero canonical canonical_congr)
open GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr)
open GaussianTranslatedNonconstant (recode recode_congr recode_eq)
open GaussianRationalRowSpan (vectorDot membership)
open GaussianRationalFiberVandermonde (delta delta_canonical)
open GaussianRationalAnnihilatorVector (freeColumn)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def unitBody : PTm 2 := delta (var 1) (var 0)
def unit (N s : PTm n) : PTm n := sequence unitBody N s
def entryBody : PTm 2 := entry (var 1) (var 0)
def annihilator (A R N : PTm n) : PTm n := GaussianRationalAnnihilatorVector.run A R N
def witness (A R N : PTm n) : PTm n := unit N (freeColumn A R N)
def input (A R N : PTm n) : Fm PTm n := GaussianRationalAnnihilatorVector.input A R N
/-- No numerical list of coefficients gives the original row membership. -/
def outside (A R N v : PTm n) : Fm PTm n := .all
  (neg (membership (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0) (Syn.shift v)))
def certificate (A R N v : PTm n) : Fm PTm n := length v ≐ N ⋏ outside A R N v
def properSpan (A R N : PTm n) : Fm PTm n := .ex
  (certificate (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0))

ipra_subst unit
ipra_subst annihilator
ipra_subst witness
ipra_subst input
ipra_subst outside [Syn.subst_shift, Syn.shift_subst]
ipra_subst certificate
ipra_subst properSpan [Syn.subst_shift, Syn.shift_subst]

theorem unit_body_at (s j : PTm n) : inst2 unitBody j s = delta s j := by simp [unitBody,inst2]
theorem entry_body_at (v j : PTm n) : inst2 entryBody j v = entry v j := by simp [entryBody,inst2]
theorem unit_length (N s : PTm n) : Γ ⊢[PRAAx] length (unit N s) ≐ N := sequence_length _ _ _
theorem unit_lookup (N s j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    entry (unit N s) j ≐ delta s j := by
  simpa only [unit,unit_body_at] using sequence_decode (Γ := Γ) unitBody (x := s) hj
theorem unit_canonical (N s j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    canonical (entry (unit N s) j) := canonical_congr (unit_lookup N s j hj) (delta_canonical s j)
theorem unit_selected (N s : PTm n) (hs : Γ ⊢[PRAAx] lt s N) : Γ ⊢[PRAAx] entry (unit N s) s ≐ qone :=
  (unit_lookup N s s hs).eqTrans (GaussianRationalLagrangeCardinals.delta_equal s s (.eqRefl s))

/-- The true dot fold selects the canonical recode of an arbitrary raw entry. -/
theorem unit_dot (N s v : PTm n) (hs : Γ ⊢[PRAAx] lt s N) : Γ ⊢[PRAAx]
    vectorDot N (unit N s) v ≐ recode (entry v s) := by
  have same : Γ ⊢[PRAAx] vectorDot N (unit N s) v ≐ GaussianRationalMatrixFiniteSums.deltaSum entryBody N s v := by
    refine GaussianRationalFiniteSum.sum_congr_bounded GaussianRationalRowElimination.dotBody
      (GaussianRationalMatrixFiniteSums.deltaBody entryBody) N
      (GaussianRationalRowElimination.dotData (GaussianRationalMonicReduction.singleton (unit N s)) v zero) (pairT s v)
      (.allI (.impI ?_))
    let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
    have low := (GaussianRationalRowSpan.vector_dot_term (Γ := Δ) (unit (Syn.shift N) (Syn.shift s)) (Syn.shift v) (var 0)).eqTrans
      (qmul_congr (unit_lookup (Syn.shift N) (Syn.shift s) (var 0) Prf.hyp0) (.eqRefl _))
    have high := GaussianRationalMatrixFiniteSums.delta_body_at (Γ := Δ) entryBody (Syn.shift s) (var 0) (Syn.shift v)
    simp only [entry_body_at] at high
    simpa only [Δ,Syn.shift,GaussianRationalRowElimination.subst_dotData,
      GaussianRationalMonicReduction.subst_singleton,subst_unit,subst_pairT,ConciseIPRA.PTm.subst_zero] using low.eqTrans high.eqSymm
  exact same.eqTrans (by simpa only [entry_body_at] using GaussianRationalMatrixFiniteSums.sum_delta entryBody N s v hs)

theorem witness_length (A R N : PTm n) : Γ ⊢[PRAAx] length (witness A R N) ≐ N := unit_length _ _
theorem selected_annihilator (A R N : PTm n) (h : Γ ⊢[PRAAx] input A R N) : Γ ⊢[PRAAx]
    entry (annihilator A R N) (freeColumn A R N) ≐ qone :=
  (entry_congr (GaussianRationalAnnihilatorVector.program_at A R N) (.eqRefl _)).eqTrans
    (GaussianRationalAnnihilatorVector.selected_one A R N h)
theorem dot_one (A R N : PTm n) (h : Γ ⊢[PRAAx] input A R N) : Γ ⊢[PRAAx]
    vectorDot N (witness A R N) (annihilator A R N) ≐ qone :=
  (unit_dot N (freeColumn A R N) (annihilator A R N) (.andE₁ (GaussianRationalAnnihilatorVector.free_correct A R N h))).eqTrans
    ((recode_congr (selected_annihilator A R N h)).eqTrans (recode_eq _ qone_canonical))

theorem coefficient_impossible (A R N C : PTm n) (h : Γ ⊢[PRAAx] input A R N) : Γ ⊢[PRAAx]
    neg (membership A R N C (witness A R N)) := by
  have null := Prf.andE₂ (Prf.andE₂ (GaussianRationalAnnihilatorVector.returned_certificate A R N h))
  refine .impI (.impE GaussianRationalCurveFibers.gaussian_one_nonzero ?_)
  exact (dot_one A R N h.wk).eqSymm.eqTrans
    (GaussianRationalRowSpan.membership_zero A R N C (witness A R N) (annihilator A R N) Prf.hyp0 null.wk)
theorem witness_outside (A R N : PTm n) (h : Γ ⊢[PRAAx] input A R N) : Γ ⊢[PRAAx]
    outside A R N (witness A R N) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift A) (Syn.shift R) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI ?_
  simpa only [Syn.shift,subst_witness] using coefficient_impossible (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0) hs
theorem witness_certificate (A R N : PTm n) (h : Γ ⊢[PRAAx] input A R N) : Γ ⊢[PRAAx]
    certificate A R N (witness A R N) := .andI (witness_length _ _ _) (witness_outside A R N h)

def unitF : PR 2 := PTm.toPR (unit (var 0) (var 1))
def witnessF : PR 3 := PTm.toPR (witness (var 0) (var 1) (var 2))
def run (A R N : PTm n) : PTm n := app witnessF ![A,R,N]
ipra_subst run
theorem unit_program_at (N s : PTm n) : Γ ⊢[PRAAx] app unitF ![N,s] ≐ unit N s := by
  simpa [unitF] using toPR_eq (Γ := Γ) (unit (var 0) (var 1) : PTm 2) ![N,s]
theorem program_at (A R N : PTm n) : Γ ⊢[PRAAx] run A R N ≐ witness A R N := by
  simpa [run,witnessF] using toPR_eq (Γ := Γ) (witness (var 0) (var 1) (var 2) : PTm 3) ![A,R,N]
theorem certificate_congr {A R N v w : PTm n} (e : Γ ⊢[PRAAx] v ≐ w)
    (h : Γ ⊢[PRAAx] certificate A R N v) : Γ ⊢[PRAAx] certificate A R N w := by
  simpa only [subst_certificate,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqSubst (certificate (var 0) (var 1) (var 2) (var 3) : Fm PTm 4) ![A,R,N,v] ![A,R,N,w]
      (fun i => by fin_cases i; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _; exact e)
      (by simpa only [subst_certificate,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using h)
theorem returned_certificate (A R N : PTm n) (h : Γ ⊢[PRAAx] input A R N) : Γ ⊢[PRAAx]
    certificate A R N (run A R N) := certificate_congr (program_at A R N).eqSymm (witness_certificate A R N h)
theorem proper_span (A R N : PTm n) (h : Γ ⊢[PRAAx] input A R N) : Γ ⊢[PRAAx] properSpan A R N := by
  refine .exI (run A R N) ?_
  simpa only [properSpan,subst_certificate,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using returned_certificate A R N h

theorem actual_unit_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (length (unit (var 0) (var 1)) ≐ var 0) := closeUniv 2 (unit_length _ _)
theorem actual_raw_unit_dot_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (var 0) ⟶ vectorDot (var 0) (unit (var 0) (var 1)) (var 2) ≐ recode (entry (var 2) (var 1))) :=
  closeUniv 3 (.impI (unit_dot _ _ _ Prf.hyp0))
theorem actual_annihilator_pairing_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input (var 0) (var 1) (var 2) ⟶ vectorDot (var 2) (witness (var 0) (var 1) (var 2)) (annihilator (var 0) (var 1) (var 2)) ≐ qone) :=
  closeUniv 3 (.impI (dot_one _ _ _ Prf.hyp0))
theorem actual_no_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) ⟶ neg (membership (var 0) (var 1) (var 2) (var 3) (witness (var 0) (var 1) (var 2)))) :=
  closeUniv 4 (.impI (coefficient_impossible _ _ _ _ Prf.hyp0))
theorem actual_proper_witness_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input (var 0) (var 1) (var 2) ⟶ certificate (var 0) (var 1) (var 2) (witness (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (witness_certificate _ _ _ Prf.hyp0))
theorem actual_proper_span_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input (var 0) (var 1) (var 2) ⟶ properSpan (var 0) (var 1) (var 2)) := closeUniv 3 (.impI (proper_span _ _ _ Prf.hyp0))
theorem actual_unit_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (app unitF ![var 0,var 1] ≐ unit (var 0) (var 1)) := closeUniv 2 (unit_program_at _ _)
theorem actual_witness_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ witness (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_returned_proper_witness_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input (var 0) (var 1) (var 2) ⟶ certificate (var 0) (var 1) (var 2) (run (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (returned_certificate _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalProperSpanWitness
