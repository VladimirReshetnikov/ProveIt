import DiophantineConsistency.AnnotatedRenameScanPR

/-! # Supplied arithmetic certificates for the four actual ZF schema maps

A fixed finite list of already checked renaming operations is program data.
The witness gives each intermediate code and its local renaming table. -/
namespace DiophantineConsistency.AnnotatedSchemaMaps

open SetTheory SetTheory.Form AnnotatedProofCode AnnotatedRename
open ScalarPRCode DirectScalar
open AnnotatedRenameLocal (truth truth_eq_one)

set_option maxRecDepth 16000
set_option maxHeartbeats 1200000
attribute [local irreducible] Nat.unpair AnnotatedRenameScan.checkNat

structure Step where
  mode : Nat
  parameter : Nat
  depth : Nat
  deriving DecidableEq, Repr

def Step.apply (s : Step) (f : Form) : Form := renamed s.mode s.parameter s.depth f

def stepValue (s : Step) (input output table : Nat) : Nat :=
  AnnotatedRenameScan.checkNat s.mode s.parameter s.depth input output table

private theorem stepValue_eq (s : Step) (input output table : Nat) :
    stepValue s input output table=truth (checkCode s.mode s.parameter s.depth input output table) :=
  AnnotatedRenameScan.checkNat_eq_checkCode _ _ _ _ _ _

theorem exists_step_iff (s : Step) (f : Form) (output : Nat) :
    (∃ table,stepValue s (formCode f) output table=1) ↔ output=formCode (s.apply f) := by
  simp only [stepValue_eq,truth_eq_one]
  exact exists_code_iff s.mode s.parameter s.depth f output

/-- Literal six-argument application of the frozen complete rename program. -/
def stepProgram {i o t : Nat → Nat} (s : Step) (pi : R i) (po : R o) (pt : R t) :
    R (fun n => stepValue s (i n) (o n) (t n)) :=
  (AnnotatedRenameScanPR.P.program.comp
    ((constant s.mode).pair ((constant s.parameter).pair ((constant s.depth).pair
      (pi.pair (po.pair pt)))))).ofEq (fun _ => by
        simp only [AnnotatedRenameScanPR.P.value,decodeRow,Nat.unpair_pair,stepValue])

/-- The finite chain is fixed program data, not an untrusted formula parser. -/
def chainForm : List Step → Form → Form
  | [],f => f
  | s::steps,f => chainForm steps (s.apply f)

def inputCode (input output evidence : Nat) : Nat := Nat.pair input (Nat.pair output evidence)

/-- Each witness entry is `(nextFormulaCode,renameTableCode)`; the right
component holds the remaining entries. Unused terminal evidence is ignored. -/
def chainValue : List Step → Nat → Nat
  | [],n => if n.unpair.1=n.unpair.2.unpair.1 then 1 else 0
  | s::steps,n =>
    let entry := n.unpair.2.unpair.2.unpair.1
    let remaining := n.unpair.2.unpair.2.unpair.2
    stepValue s n.unpair.1 entry.unpair.1 entry.unpair.2 *
      chainValue steps (inputCode entry.unpair.1 n.unpair.2.unpair.1 remaining)

def chainProgram : (steps : List Step) → R (chainValue steps)
  | [] => ifEq Realizes.left (Realizes.left.comp Realizes.right) (constant 1) Realizes.zero
  | s::steps => by
    let i := Realizes.left
    let o := Realizes.left.comp Realizes.right
    let evidence := Realizes.right.comp Realizes.right
    let entry := Realizes.left.comp evidence
    let remaining := Realizes.right.comp evidence
    let next := Realizes.left.comp entry
    let table := Realizes.right.comp entry
    let first := stepProgram s i next table
    let rest := (chainProgram steps).comp (next.pair (o.pair remaining))
    refine (mul first rest).ofEq ?_
    intro n
    simp only [chainValue,inputCode]

theorem mul_eq_one_nat (a b : Nat) : a*b=1 ↔ a=1 ∧ b=1 := by
  constructor
  · intro h
    exact ⟨Nat.eq_one_of_mul_eq_one_right h,Nat.eq_one_of_mul_eq_one_left h⟩
  · rintro ⟨rfl,rfl⟩
    rfl

/-- Exact chain acceptance on all external formulas, with no selected
intermediate code in the supplied executable program. -/
theorem exists_chain_iff (steps : List Step) (f : Form) (output : Nat) :
    (∃ evidence,chainValue steps (inputCode (formCode f) output evidence)=1) ↔
      output=formCode (chainForm steps f) := by
  induction steps generalizing f with
  | nil => simp [chainValue,inputCode,chainForm,eq_comm]
  | cons s steps ih =>
    constructor
    · rintro ⟨evidence,h⟩
      simp only [chainValue,inputCode,Nat.unpair_pair,mul_eq_one_nat] at h
      have hn := (exists_step_iff s f evidence.unpair.1.unpair.1).mp
        ⟨evidence.unpair.1.unpair.2,h.1⟩
      have hh := h.2
      rw [hn] at hh
      exact (ih (s.apply f)).mp ⟨evidence.unpair.2,hh⟩
    · intro h
      obtain ⟨remaining,hr⟩ := (ih (s.apply f)).mpr h
      obtain ⟨table,ht⟩ := (exists_step_iff s f (formCode (s.apply f))).mpr rfl
      refine ⟨Nat.pair (Nat.pair (formCode (s.apply f)) table) remaining,?_⟩
      simpa only [chainValue,inputCode,Nat.unpair_pair,ht,hr,Nat.one_mul]

/-- The first guarded renaming step validates an arbitrary input code. No
external formula parser is assumed for this all-natural-input implication. -/
theorem chainValue_sound (s : Step) (steps : List Step) (input output evidence : Nat)
    (h : chainValue (s::steps) (inputCode input output evidence)=1) :
    ∃ f : Form,input=formCode f ∧ output=formCode (chainForm (s::steps) f) := by
  simp only [chainValue,inputCode,Nat.unpair_pair,mul_eq_one_nat] at h
  have hs := h.1
  rw [stepValue_eq,truth_eq_one] at hs
  obtain ⟨f,hi,ho⟩ := checkCode_sound s.mode s.parameter s.depth input
    evidence.unpair.1.unpair.1 evidence.unpair.1.unpair.2 hs
  refine ⟨f,hi,?_⟩
  have hr := h.2
  rw [ho] at hr
  exact (exists_chain_iff steps (s.apply f) output).mp ⟨evidence.unpair.2,hr⟩

theorem chainProgram_primrec (steps : List Step) :
    Nat.Primrec (chainProgram steps).val.eval := (chainProgram steps).val.primrec

/-- These four lists are exact decompositions of the source schema maps. -/
def separationSteps : List Step := [⟨0,0,1⟩,⟨0,0,1⟩]
def functionFirstSteps : List Step := [⟨0,0,0⟩]
def functionSecondSteps : List Step := [⟨0,0,1⟩]
def imageSteps : List Step := [⟨0,0,2⟩,⟨0,0,2⟩,⟨0,0,2⟩,⟨1,1,0⟩]

theorem rsep_eq : rsep=fun n => index 0 0 1 (index 0 0 1 n) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp [rsep,index]

theorem rf1_eq : rf1=index 0 0 0 := by
  funext n
  cases n with
  | zero => rfl
  | succ n => cases n <;> simp [rf1,index]

theorem rf2_eq : rf2=index 0 0 1 := by
  funext n
  cases n with
  | zero => rfl
  | succ n => cases n <;> simp [rf2,index]

theorem ri_eq : ri=fun n => index 1 1 0
    (index 0 0 2 (index 0 0 2 (index 0 0 2 n))) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n =>
      have h0 : ¬n+1+1<2 := by omega
      have h1 : ¬n+1+1+1<2 := by omega
      have h2 : ¬n+1+1+1+1<2 := by omega
      simp [ri,index,h0,h1,h2]

theorem separation_chain (f : Form) : chainForm separationSteps f=rename rsep f := by
  simp only [separationSteps,chainForm,Step.apply,renamed,rename_comp,←rsep_eq]

theorem functionFirst_chain (f : Form) : chainForm functionFirstSteps f=rename rf1 f := by
  simp only [functionFirstSteps,chainForm,Step.apply,renamed,←rf1_eq]

theorem functionSecond_chain (f : Form) : chainForm functionSecondSteps f=rename rf2 f := by
  simp only [functionSecondSteps,chainForm,Step.apply,renamed,←rf2_eq]

theorem image_chain (f : Form) : chainForm imageSteps f=rename ri f := by
  simp only [imageSteps,chainForm,Step.apply,renamed,rename_comp,←ri_eq]

theorem exists_separation_iff (f : Form) (output : Nat) :
    (∃ evidence,(chainProgram separationSteps).val.eval (inputCode (formCode f) output evidence)=1) ↔
      output=formCode (rename rsep f) := by
  simp only [(chainProgram separationSteps).property]
  simpa only [separation_chain] using exists_chain_iff separationSteps f output

theorem exists_functionFirst_iff (f : Form) (output : Nat) :
    (∃ evidence,(chainProgram functionFirstSteps).val.eval (inputCode (formCode f) output evidence)=1) ↔
      output=formCode (rename rf1 f) := by
  simp only [(chainProgram functionFirstSteps).property]
  simpa only [functionFirst_chain] using exists_chain_iff functionFirstSteps f output

theorem exists_functionSecond_iff (f : Form) (output : Nat) :
    (∃ evidence,(chainProgram functionSecondSteps).val.eval (inputCode (formCode f) output evidence)=1) ↔
      output=formCode (rename rf2 f) := by
  simp only [(chainProgram functionSecondSteps).property]
  simpa only [functionSecond_chain] using exists_chain_iff functionSecondSteps f output

theorem exists_image_iff (f : Form) (output : Nat) :
    (∃ evidence,(chainProgram imageSteps).val.eval (inputCode (formCode f) output evidence)=1) ↔
      output=formCode (rename ri f) := by
  simp only [(chainProgram imageSteps).property]
  simpa only [image_chain] using exists_chain_iff imageSteps f output

theorem separation_nodeCount : (chainProgram separationSteps).val.nodeCount=7409 := by decide
theorem functionFirst_nodeCount : (chainProgram functionFirstSteps).val.nodeCount=3739 := by decide
theorem functionSecond_nodeCount : (chainProgram functionSecondSteps).val.nodeCount=3741 := by decide
theorem image_nodeCount : (chainProgram imageSteps).val.nodeCount=14753 := by decide

end DiophantineConsistency.AnnotatedSchemaMaps
