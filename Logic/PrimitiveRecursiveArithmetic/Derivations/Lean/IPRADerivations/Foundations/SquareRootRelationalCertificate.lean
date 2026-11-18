import IPRADerivations.Foundations.SquareRootRelationalCandidates
import IPRADerivations.Foundations.ViableChainSelection

/-!
# Actual certified finite relational square-root paths

For the exact nonnegative rational u/v, the numerical parameter also stores
an arbitrary requested horizon. Candidates are indices in the actual stored
lists of `SquareRootRelationalCandidates`. Local and edge tests are actual
PR zero bits of the original residual and adjacent dyadic compatibility.

The everywhere defined least-crossing positions prove an object-level coded
path admissible from v>=1 alone. Backward viability and the automatic least
initial selector then independently produce their own checked finite path.
No supplied path, success bit, selector law or admissibility rule bundle is
an input. There is no assertion of an infinite branch or of represented-input
selection. All rational inputs, levels, horizons, codes and indices are internal.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.SquareRootRelationalCertificate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.PTm (monus)
open LeanProofs.IPRA.Foundations.BackwardViability
open LeanProofs.IPRA.Foundations.BackwardViability.Instance
open LeanProofs.IPRA.Foundations.MasterCertificate (sequence entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (u v h : PTm n) : PTm n := pairT u (pairT v h)
def inputNumerator (p : PTm n) : PTm n := fstT p
def inputDenominator (p : PTm n) : PTm n := fstT (sndT p)
def horizon (p : PTm n) : PTm n := sndT (sndT p)
def zeroBit (z : PTm n) : PTm n := monus one (Signum.sg z)
def edgeDefect (j l : PTm n) : PTm n :=
  monus (two*j) (l+(SquareRootRelationalCandidates.three+SquareRootRelationalCandidates.three))+
    monus l (two*j+(SquareRootRelationalCandidates.three+SquareRootRelationalCandidates.three))
def gridLabel (i a p : PTm n) : PTm n :=
  entry (SquareRootRelationalCandidates.candidateList (inputNumerator p) (inputDenominator p) i) a
def observation (i a p : PTm n) : PTm n := SquareRootRelationalCandidates.point (gridLabel i a p) i
def bound (i p : PTm n) : PTm n := SquareRootRelationalCandidates.count (inputNumerator p) (inputDenominator p) i
def localTest (i a p : PTm n) : PTm n :=
  zeroBit (SquareRootRelationalCandidates.defect (inputNumerator p) (inputDenominator p) i (gridLabel i a p))
def edgeTest (i a b p : PTm n) : PTm n :=
  zeroBit (edgeDefect (gridLabel i a p) (gridLabel (succ i) b p))

def compatibility : Instance where
  G := localTest (var 0) (var 1) (var 2)
  T := edgeTest (var 0) (var 1) (var 2) (var 3)
  B := bound (var 0) (var 1)
  hz := horizon (var 0)

def witnessAt (i p : PTm n) : PTm n :=
  SquareRootRelationalCandidates.position (inputNumerator p) (inputDenominator p) i
    (SquareRootRelationalCandidates.candidate (inputNumerator p) (inputDenominator p) i)
def witnessBody : PTm 2 := witnessAt (var 0) (var 1)
def witnessCode (p : PTm n) : PTm n := sequence witnessBody (succ (horizon p)) p

def flag (p : PTm n) : PTm n := ViableChainSelection.flag compatibility p
def chain (p : PTm n) : PTm n := ViableChainSelection.rawChain compatibility p

def outputF : PR 1 := ViableChainSelection.outputF compatibility
def run (u v h : PTm n) : PTm n := ap1 outputF (data u v h)
def selectedCode (u v h : PTm n) : PTm n := sndT (run u v h)
def codeBound (u v h : PTm n) : PTm n := CodedViableChain.codeBound compatibility (data u v h)
def outputBound (u v h : PTm n) : PTm n := ViableChainSelection.returnBound compatibility (data u v h)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (u v h : PTm n) :
    Syn.subst σ (data u v h) = data (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ h) := by simp [data]
@[simp] theorem subst_inputNumerator {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) :
    Syn.subst σ (inputNumerator p) = inputNumerator (Syn.subst σ p) := by simp [inputNumerator]
@[simp] theorem subst_inputDenominator {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) :
    Syn.subst σ (inputDenominator p) = inputDenominator (Syn.subst σ p) := by simp [inputDenominator]
@[simp] theorem subst_horizon {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) :
    Syn.subst σ (horizon p) = horizon (Syn.subst σ p) := by simp [horizon]
@[simp] theorem subst_zeroBit {m : ℕ} (σ : Fin n → PTm m) (z : PTm n) :
    Syn.subst σ (zeroBit z) = zeroBit (Syn.subst σ z) := by simp [zeroBit]
@[simp] theorem subst_edgeDefect {m : ℕ} (σ : Fin n → PTm m) (j l : PTm n) :
    Syn.subst σ (edgeDefect j l) = edgeDefect (Syn.subst σ j) (Syn.subst σ l) := by simp [edgeDefect]
@[simp] theorem subst_gridLabel {m : ℕ} (σ : Fin n → PTm m) (i a p : PTm n) :
    Syn.subst σ (gridLabel i a p) = gridLabel (Syn.subst σ i) (Syn.subst σ a) (Syn.subst σ p) := by simp [gridLabel]
@[simp] theorem subst_observation {m : ℕ} (σ : Fin n → PTm m) (i a p : PTm n) :
    Syn.subst σ (observation i a p) = observation (Syn.subst σ i) (Syn.subst σ a) (Syn.subst σ p) := by simp [observation]
@[simp] theorem subst_bound {m : ℕ} (σ : Fin n → PTm m) (i p : PTm n) :
    Syn.subst σ (bound i p) = bound (Syn.subst σ i) (Syn.subst σ p) := by simp [bound]
@[simp] theorem subst_localTest {m : ℕ} (σ : Fin n → PTm m) (i a p : PTm n) :
    Syn.subst σ (localTest i a p) = localTest (Syn.subst σ i) (Syn.subst σ a) (Syn.subst σ p) := by simp [localTest]
@[simp] theorem subst_edgeTest {m : ℕ} (σ : Fin n → PTm m) (i a b p : PTm n) :
    Syn.subst σ (edgeTest i a b p) = edgeTest (Syn.subst σ i) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ p) := by simp [edgeTest]
@[simp] theorem subst_witnessAt {m : ℕ} (σ : Fin n → PTm m) (i p : PTm n) :
    Syn.subst σ (witnessAt i p) = witnessAt (Syn.subst σ i) (Syn.subst σ p) := by simp [witnessAt]
@[simp] theorem subst_witnessCode {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) :
    Syn.subst σ (witnessCode p) = witnessCode (Syn.subst σ p) := by simp [witnessCode]

theorem numerator_at (u v h : PTm n) : Γ ⊢[PRAAx] inputNumerator (data u v h) ≐ u := fst_pair _ _
theorem denominator_at (u v h : PTm n) : Γ ⊢[PRAAx] inputDenominator (data u v h) ≐ v :=
  (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
theorem horizon_at (u v h : PTm n) : Γ ⊢[PRAAx] horizon (data u v h) ≐ h :=
  (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
theorem instance_bound (i p : PTm n) : compatibility.bd i p = bound i p := by simp [Instance.bd,compatibility]
theorem instance_local (i a p : PTm n) : compatibility.g i a p = localTest i a p := by simp [Instance.g,compatibility]
theorem instance_edge (i a b p : PTm n) : compatibility.t i a b p = edgeTest i a b p := by simp [Instance.t,compatibility]
theorem instance_horizon (p : PTm n) : compatibility.h p = horizon p := by simp [Instance.h,compatibility]

theorem zeroBit_of_zero {z : PTm n} (h : Γ ⊢[PRAAx] z ≐ zero) : Γ ⊢[PRAAx] zeroBit z ≐ one :=
  BoundedFormulas.not_of_zero (BoundedFormulas.sg_of_zero h)
theorem zeroBit_nonzero {z : PTm n} (h : Γ ⊢[PRAAx] z ≐ zero) : Γ ⊢[PRAAx] neg (zeroBit z ≐ zero) :=
  ViableChainSelection.nonzero_of_one (zeroBit_of_zero h)
theorem zero_of_zeroBit {z : PTm n} (h : Γ ⊢[PRAAx] neg (zeroBit z ≐ zero)) : Γ ⊢[PRAAx] z ≐ zero := by
  have h' : Γ ⊢[PRAAx] neg (inst2 (BoundedEnumeration.vb (var 0 : PTm 2)) z zero ≐ zero) := by
    simpa [zeroBit,BoundedEnumeration.vb,inst2] using h
  simpa only [inst2,Syn.subst_var,Matrix.cons_val_zero] using
    BoundedEnumeration.valid_of_kept h'
theorem edge_of_compatible (j l : PTm n) (h : Γ ⊢[PRAAx] SquareRootRelationalCandidates.compatible j l) : Γ ⊢[PRAAx]
    edgeDefect j l ≐ zero := (congrAdd (Prf.andE₁ h) (Prf.andE₂ h)).eqTrans (add_zero zero)
theorem compatible_of_edge (j l : PTm n) (h : Γ ⊢[PRAAx] edgeDefect j l ≐ zero) : Γ ⊢[PRAAx]
    SquareRootRelationalCandidates.compatible j l := .andI (add_eq_zero_left h) (add_eq_zero_left ((add_comm _ _).eqTrans h))

theorem witness_bound (i p : PTm n) (hv : Γ ⊢[PRAAx] le one (inputDenominator p)) : Γ ⊢[PRAAx]
    lt (witnessAt i p) (compatibility.bd i p) := by
  rw [instance_bound]
  exact Prf.andE₁ (SquareRootRelationalCandidates.actual_candidate_listed (inputNumerator p) (inputDenominator p) i hv)
theorem witness_label (i p : PTm n) (hv : Γ ⊢[PRAAx] le one (inputDenominator p)) : Γ ⊢[PRAAx]
    gridLabel i (witnessAt i p) p ≐ SquareRootRelationalCandidates.candidate (inputNumerator p) (inputDenominator p) i :=
  Prf.andE₂ (SquareRootRelationalCandidates.actual_candidate_listed _ _ _ hv)
theorem witness_local (i p : PTm n) (hv : Γ ⊢[PRAAx] le one (inputDenominator p)) : Γ ⊢[PRAAx]
    neg (compatibility.g i (witnessAt i p) p ≐ zero) := by
  rw [instance_local]
  apply zeroBit_nonzero
  have actual := SquareRootRelationalCandidates.defect_of_local _ _ _ _
    (SquareRootRelationalCandidates.entry_residual (inputNumerator p) (inputDenominator p) i (witnessAt i p)
      (by simpa only [instance_bound,bound] using witness_bound i p hv))
  exact actual

theorem witness_edge (i p : PTm n) (hv : Γ ⊢[PRAAx] le one (inputDenominator p)) : Γ ⊢[PRAAx]
    neg (compatibility.t i (witnessAt i p) (witnessAt (succ i) p) p ≐ zero) := by
  rw [instance_edge]
  apply zeroBit_nonzero
  have e : Γ ⊢[PRAAx] edgeDefect (gridLabel i (witnessAt i p) p) (gridLabel (succ i) (witnessAt (succ i) p) p) ≐
      edgeDefect (SquareRootRelationalCandidates.candidate (inputNumerator p) (inputDenominator p) i)
        (SquareRootRelationalCandidates.candidate (inputNumerator p) (inputDenominator p) (succ i)) := by
    simpa using Prf.eqCongr (edgeDefect (var 0) (var 1) : PTm 2)
      (σ := ![gridLabel i (witnessAt i p) p,gridLabel (succ i) (witnessAt (succ i) p) p])
      (σ' := ![SquareRootRelationalCandidates.candidate (inputNumerator p) (inputDenominator p) i,
        SquareRootRelationalCandidates.candidate (inputNumerator p) (inputDenominator p) (succ i)])
      (fun j => by fin_cases j; exact witness_label i p hv; exact witness_label (succ i) p hv)
  exact e.eqTrans (edge_of_compatible _ _ (SquareRootRelationalCandidates.candidate_compatible _ _ _ hv))

theorem witness_lookup (p i : PTm n) (hi : Γ ⊢[PRAAx] le i (horizon p)) : Γ ⊢[PRAAx]
    entry (witnessCode p) i ≐ witnessAt i p := by
  simpa only [witnessCode,witnessBody,inst2,subst_witnessAt,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    MasterCertificate.sequence_decode witnessBody (x := p) ((succ_monus_succ _ _).eqTrans hi)

theorem witness_admissible (p : PTm n) (hv : Γ ⊢[PRAAx] le one (inputDenominator p)) : Γ ⊢[PRAAx]
    CodedViableChain.admissibleCode compatibility (witnessCode p) p := by
  simp only [CodedViableChain.admissibleCode,CodedViableChain.localCode,
    CodedViableChain.edgeCode,instance_horizon]
  refine .andI ?_ (.andI ?_ ?_)
  · simpa only [witnessCode,length] using
      MasterCertificate.sequence_length (Γ := Γ) witnessBody (succ (horizon p)) p
  · refine .allI (.impI ?_)
    have vh : Γ.map Fm.shift ⊢[PRAAx] le one (inputDenominator (Syn.shift p)) := by
      simpa only [Fm.shift,subst_le,subst_inputDenominator,ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero,Syn.shift] using hv.shift
    have lookup := witness_lookup (Γ := (le (var 0) (horizon (Syn.shift p))) :: Γ.map Fm.shift)
      (Syn.shift p) (var 0) Prf.hyp0
    simpa only [subst_witnessCode,Syn.shift] using
      (.andI (lt_congr lookup.eqSymm (.eqRefl _) (witness_bound (var 0) (Syn.shift p) vh.wk))
        (CodedViableChain.nonzero_of_eq (CodedViableChain.g_values compatibility _ _ _ _ lookup)
          (witness_local (var 0) (Syn.shift p) vh.wk)))
  · refine .allI (.impI ?_)
    have vh : Γ.map Fm.shift ⊢[PRAAx] le one (inputDenominator (Syn.shift p)) := by
      simpa only [Fm.shift,subst_le,subst_inputDenominator,ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero,Syn.shift] using hv.shift
    simpa only [subst_witnessCode,Syn.shift] using
      CodedViableChain.nonzero_of_eq (CodedViableChain.t_values compatibility _ _ _ _ _ _
        (witness_lookup (Syn.shift p) (var 0) (le_of_lt Prf.hyp0))
        (witness_lookup (Syn.shift p) (succ (var 0)) Prf.hyp0))
        (witness_edge (var 0) (Syn.shift p) vh.wk)

theorem success (p : PTm n) (hv : Γ ⊢[PRAAx] le one (inputDenominator p)) : Γ ⊢[PRAAx] flag p ≐ one :=
  ViableChainSelection.chain_implies_success compatibility (witnessCode p) p (witness_admissible p hv)
theorem chain_correct (p : PTm n) (hv : Γ ⊢[PRAAx] le one (inputDenominator p)) : Γ ⊢[PRAAx]
    CodedViableChain.admissibleCode compatibility (chain p) p :=
  ViableChainSelection.rawChain_correct compatibility p (success p hv)


/-- The local and edge meanings are the original rational observations,
not just acceptance by a renamed checker. -/
theorem local_rational_residual (S p i : PTm n)
    (hv : Γ ⊢[PRAAx] le one (inputDenominator p))
    (h : Γ ⊢[PRAAx] CodedViableChain.admissibleCode compatibility S p)
    (hi : Γ ⊢[PRAAx] le i (horizon p)) : Γ ⊢[PRAAx]
    SquareRootRelationalCandidates.rationalResidual (inputNumerator p) (inputDenominator p) i (gridLabel i (entry S i) p) := by
  have gate := CodedViableChain.local_at compatibility S p i h (by simpa only [instance_horizon] using hi)
  have test : Γ ⊢[PRAAx] neg (zeroBit
      (SquareRootRelationalCandidates.defect (inputNumerator p) (inputDenominator p) i (gridLabel i (entry S i) p)) ≐ zero) := by
    simpa only [instance_local,localTest] using Prf.andE₂ gate
  exact SquareRootRelationalCandidates.rational_residual _ _ _ _ hv
    (SquareRootRelationalCandidates.local_of_defect _ _ _ _ (zero_of_zeroBit test))

theorem edge_rational_radius (S p i : PTm n)
    (h : Γ ⊢[PRAAx] CodedViableChain.admissibleCode compatibility S p)
    (hi : Γ ⊢[PRAAx] lt i (horizon p)) : Γ ⊢[PRAAx]
    Analysis.RationalValueBounds.radius (observation i (entry S i) p) (observation (succ i) (entry S (succ i)) p)
      SquareRootRelationalCandidates.three (SquareRootRelationalCandidates.unit i) := by
  have edge := CodedViableChain.edge_at compatibility S p i h (by simpa only [instance_horizon] using hi)
  have test : Γ ⊢[PRAAx] neg (zeroBit (edgeDefect (gridLabel i (entry S i) p)
      (gridLabel (succ i) (entry S (succ i)) p)) ≐ zero) := by
    simpa only [instance_edge,edgeTest] using edge
  exact SquareRootRelationalCandidates.rational_compatible _ _ _
    (compatible_of_edge _ _ (zero_of_zeroBit test))

theorem success_at (u v h : PTm n) (hv : Γ ⊢[PRAAx] le one v) : Γ ⊢[PRAAx] flag (data u v h) ≐ one :=
  success _ (le_congr (.eqRefl _) (denominator_at _ _ _).eqSymm hv)
theorem returned_flag (u v h : PTm n) (hv : Γ ⊢[PRAAx] le one v) : Γ ⊢[PRAAx] fstT (run u v h) ≐ one :=
  (ViableChainSelection.returned_flag compatibility _).eqTrans (success_at _ _ _ hv)
theorem returned_correct (u v h : PTm n) (hv : Γ ⊢[PRAAx] le one v) : Γ ⊢[PRAAx]
    CodedViableChain.admissibleCode compatibility (selectedCode u v h) (data u v h) :=
  ViableChainSelection.returned_admissible compatibility _ (success_at _ _ _ hv)
theorem actual_horizon (u v h : PTm n) : Γ ⊢[PRAAx] compatibility.h (data u v h) ≐ h := by
  simpa only [instance_horizon] using horizon_at (Γ := Γ) u v h

theorem returned_length (u v h : PTm n) (hv : Γ ⊢[PRAAx] le one v) : Γ ⊢[PRAAx]
    length (selectedCode u v h) ≐ succ h :=
  (Prf.andE₁ (returned_correct _ _ _ hv)).eqTrans (congrSucc (actual_horizon _ _ _))
theorem returned_code_size (u v h : PTm n) (hv : Γ ⊢[PRAAx] le one v) : Γ ⊢[PRAAx]
    lt (selectedCode u v h) (codeBound u v h) := by
  have actual : Γ ⊢[PRAAx] selectedCode u v h ≐ ViableChainSelection.rawChain compatibility (data u v h) :=
    (ViableChainSelection.returned_payload compatibility _).eqTrans
      (ViableChainSelection.payload_success compatibility _ (success_at _ _ _ hv))
  exact lt_congr actual.eqSymm (.eqRefl _)
    (ViableChainSelection.rawChain_bound compatibility _ (success_at _ _ _ hv))
theorem returned_output_size (u v h : PTm n) : Γ ⊢[PRAAx] lt (run u v h) (outputBound u v h) :=
  ViableChainSelection.returned_bound compatibility _

def selectedIndex (u v h i : PTm n) : PTm n := entry (selectedCode u v h) i
def selectedObservation (u v h i : PTm n) : PTm n := observation i (selectedIndex u v h i) (data u v h)
def programF : PR 3 := PTm.toPR (run (var 0) (var 1) (var 2))
def observationF : PR 4 := PTm.toPR (selectedObservation (var 0) (var 1) (var 2) (var 3))
def boundF : PR 3 := PTm.toPR (outputBound (var 0) (var 1) (var 2))

@[simp] theorem subst_flag {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) :
    Syn.subst σ (flag p) = flag (Syn.subst σ p) := by simp [flag]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (u v h : PTm n) :
    Syn.subst σ (run u v h) = run (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ h) := by simp [run]
@[simp] theorem subst_selectedCode {m : ℕ} (σ : Fin n → PTm m) (u v h : PTm n) :
    Syn.subst σ (selectedCode u v h) = selectedCode (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ h) := by simp [selectedCode]
@[simp] theorem subst_codeBound {m : ℕ} (σ : Fin n → PTm m) (u v h : PTm n) :
    Syn.subst σ (codeBound u v h) = codeBound (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ h) := by simp [codeBound]
@[simp] theorem subst_outputBound {m : ℕ} (σ : Fin n → PTm m) (u v h : PTm n) :
    Syn.subst σ (outputBound u v h) = outputBound (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ h) := by simp [outputBound]
@[simp] theorem subst_selectedIndex {m : ℕ} (σ : Fin n → PTm m) (u v h i : PTm n) :
    Syn.subst σ (selectedIndex u v h i) = selectedIndex (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ h) (Syn.subst σ i) := by simp [selectedIndex]
@[simp] theorem subst_selectedObservation {m : ℕ} (σ : Fin n → PTm m) (u v h i : PTm n) :
    Syn.subst σ (selectedObservation u v h i) = selectedObservation (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ h) (Syn.subst σ i) := by simp [selectedObservation]

theorem program_at (u v h : PTm n) : Γ ⊢[PRAAx] ap3 programF u v h ≐ run u v h := by
  simpa [programF,ap3] using toPR_eq (Γ := Γ) (run (var 0) (var 1) (var 2) : PTm 3) ![u,v,h]
theorem observation_at (u v h i : PTm n) : Γ ⊢[PRAAx] app observationF ![u,v,h,i] ≐ selectedObservation u v h i := by
  simpa [observationF] using toPR_eq (Γ := Γ) (selectedObservation (var 0) (var 1) (var 2) (var 3) : PTm 4) ![u,v,h,i]
theorem bound_at (u v h : PTm n) : Γ ⊢[PRAAx] ap3 boundF u v h ≐ outputBound u v h := by
  simpa [boundF,ap3] using toPR_eq (Γ := Γ) (outputBound (var 0) (var 1) (var 2) : PTm 3) ![u,v,h]

theorem returned_index_bound (u v h i : PTm n) (hv : Γ ⊢[PRAAx] le one v)
    (hi : Γ ⊢[PRAAx] le i h) : Γ ⊢[PRAAx]
    lt (selectedIndex u v h i) (bound i (data u v h)) := by
  have hi' : Γ ⊢[PRAAx] le i (compatibility.h (data u v h)) :=
    le_congr (.eqRefl _) (actual_horizon _ _ _).eqSymm hi
  simpa only [instance_bound,selectedIndex] using
    Prf.andE₁ (CodedViableChain.local_at compatibility _ _ _ (returned_correct _ _ _ hv) hi')
theorem defect_input_congr {u u' v v' : PTm n} (i j : PTm n)
    (hu : Γ ⊢[PRAAx] u ≐ u') (hv : Γ ⊢[PRAAx] v ≐ v') : Γ ⊢[PRAAx]
    SquareRootRelationalCandidates.defect u v i j ≐ SquareRootRelationalCandidates.defect u' v' i j := by
  have value := congrMul (congrMul hv (.eqRefl j)) (.eqRefl j)
  have target := congrMul hu (.eqRefl (SquareRootRelationalCandidates.unit i*SquareRootRelationalCandidates.unit i))
  have budget := congrMul (congrAdd (congrMul (.eqRefl two) hu)
    (congrMul (.eqRefl SquareRootRelationalCandidates.three) hv)) (.eqRefl (SquareRootRelationalCandidates.unit i))
  exact congrAdd (congrMonus value (congrAdd target budget)) (congrMonus target (congrAdd value budget))

theorem returned_rational_residual (u v h i : PTm n) (hv : Γ ⊢[PRAAx] le one v)
    (hi : Γ ⊢[PRAAx] le i h) : Γ ⊢[PRAAx]
    SquareRootRelationalCandidates.rationalResidual u v i (gridLabel i (selectedIndex u v h i) (data u v h)) := by
  have gate := CodedViableChain.local_at compatibility (selectedCode u v h) (data u v h) i
    (returned_correct _ _ _ hv) (le_congr (.eqRefl _) (actual_horizon _ _ _).eqSymm hi)
  have test : Γ ⊢[PRAAx] neg (zeroBit
      (SquareRootRelationalCandidates.defect (inputNumerator (data u v h)) (inputDenominator (data u v h)) i
        (gridLabel i (selectedIndex u v h i) (data u v h))) ≐ zero) := by
    simpa only [instance_local,localTest,selectedIndex] using Prf.andE₂ gate
  have native := (defect_input_congr i (gridLabel i (selectedIndex u v h i) (data u v h))
    (numerator_at (Γ := Γ) u v h) (denominator_at u v h)).eqSymm.eqTrans (zero_of_zeroBit test)
  exact SquareRootRelationalCandidates.rational_residual _ _ _ _ hv
    (SquareRootRelationalCandidates.local_of_defect _ _ _ _ native)

theorem returned_rational_radius (u v h i : PTm n) (hv : Γ ⊢[PRAAx] le one v)
    (hi : Γ ⊢[PRAAx] lt i h) : Γ ⊢[PRAAx]
    Analysis.RationalValueBounds.radius (selectedObservation u v h i) (selectedObservation u v h (succ i))
      SquareRootRelationalCandidates.three (SquareRootRelationalCandidates.unit i) :=
  edge_rational_radius _ _ _ (returned_correct _ _ _ hv) (lt_congr (.eqRefl _) (horizon_at _ _ _).eqSymm hi)

theorem computed_witness_admissible_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (inputDenominator (var 0)) ⟶ CodedViableChain.admissibleCode compatibility (witnessCode (var 0)) (var 0)) :=
  closeUniv 1 (.impI (witness_admissible _ Prf.hyp0))
theorem automatic_success_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ flag (data (var 0) (var 1) (var 2)) ≐ one) :=
  closeUniv 3 (.impI (success_at _ _ _ Prf.hyp0))
theorem finite_horizon_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶
      (fstT (run (var 0) (var 1) (var 2)) ≐ one ⋏
        (CodedViableChain.admissibleCode compatibility (selectedCode (var 0) (var 1) (var 2)) (data (var 0) (var 1) (var 2)) ⋏
          (length (selectedCode (var 0) (var 1) (var 2)) ≐ succ (var 2) ⋏
            (lt (selectedCode (var 0) (var 1) (var 2)) (codeBound (var 0) (var 1) (var 2)) ⋏
              lt (run (var 0) (var 1) (var 2)) (outputBound (var 0) (var 1) (var 2))))))) :=
  closeUniv 3 (.impI (.andI (returned_flag _ _ _ Prf.hyp0)
    (.andI (returned_correct _ _ _ Prf.hyp0) (.andI (returned_length _ _ _ Prf.hyp0)
      (.andI (returned_code_size _ _ _ Prf.hyp0) (returned_output_size _ _ _))))))
theorem returned_candidate_index_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ le (var 3) (var 2) ⟶
      lt (selectedIndex (var 0) (var 1) (var 2) (var 3)) (bound (var 3) (data (var 0) (var 1) (var 2)))) :=
  closeUniv 4 (.impI (.impI (returned_index_bound _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem returned_original_residual_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ le (var 3) (var 2) ⟶
      SquareRootRelationalCandidates.rationalResidual (var 0) (var 1) (var 3)
        (gridLabel (var 3) (selectedIndex (var 0) (var 1) (var 2) (var 3)) (data (var 0) (var 1) (var 2)))) :=
  closeUniv 4 (.impI (.impI (returned_rational_residual _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem returned_original_compatibility_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ lt (var 3) (var 2) ⟶
      Analysis.RationalValueBounds.radius (selectedObservation (var 0) (var 1) (var 2) (var 3))
        (selectedObservation (var 0) (var 1) (var 2) (succ (var 3)))
        SquareRootRelationalCandidates.three (SquareRootRelationalCandidates.unit (var 3))) :=
  closeUniv 4 (.impI (.impI (returned_rational_radius _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 programF (var 0) (var 1) (var 2) ≐ run (var 0) (var 1) (var 2) ⋏
      ap3 boundF (var 0) (var 1) (var 2) ≐ outputBound (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.andI (program_at _ _ _) (bound_at _ _ _))
theorem actual_observation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (app observationF ![var 0,var 1,var 2,var 3] ≐ selectedObservation (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (observation_at _ _ _ _)

end LeanProofs.IPRA.Foundations.SquareRootRelationalCertificate
