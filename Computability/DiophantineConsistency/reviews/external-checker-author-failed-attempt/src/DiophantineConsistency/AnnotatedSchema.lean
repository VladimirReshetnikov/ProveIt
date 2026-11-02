import DiophantineConsistency.AnnotatedSchemaMaps
import DiophantineConsistency.AnnotatedBoundScan

/-! # Literal formula assembly and arithmetic certificates for sealed schemas -/
namespace DiophantineConsistency.AnnotatedSchema

open SetTheory SetTheory.Form AnnotatedProofCode AnnotatedRename
open ScalarPRCode DirectScalar
open AnnotatedRenameLocal.Program (left right tag depth first second input output)

set_option maxRecDepth 20000
set_option maxHeartbeats 1200000
attribute [local irreducible] Nat.unpair AnnotatedSchemaMaps.chainValue
  AnnotatedBoundScan.sealValue

def iffCode (a b : Nat) : Nat := binaryCode 4 (binaryCode 3 a b) (binaryCode 3 b a)
def allCode (a : Nat) : Nat := unaryCode 6 a
def exCode (a : Nat) : Nat := unaryCode 7 a

def separationBody (renamed : Nat) : Nat :=
  allCode (exCode (allCode (iffCode (variableCode 0 0 1)
    (binaryCode 4 (variableCode 0 0 2) renamed))))

def functionBody (a b : Nat) : Nat :=
  allCode (allCode (allCode (binaryCode 3 (binaryCode 4 a b) (variableCode 1 1 0))))

def imageBody (renamed : Nat) : Nat :=
  allCode (exCode (allCode (iffCode (variableCode 0 0 1)
    (exCode (binaryCode 4 (variableCode 0 0 3) renamed)))))

def replacementBody (a b c : Nat) : Nat := binaryCode 3 (functionBody a b) (imageBody c)

theorem separationBody_formCode (f : Form) :
    separationBody (formCode (rename rsep f))=formCode (Sep_form f) := rfl

theorem replacementBody_formCode (f : Form) :
    replacementBody (formCode (rename rf1 f)) (formCode (rename rf2 f))
      (formCode (rename ri f))=formCode (Repl_form f) := rfl

/-- Compile supplied finite formula syntax using constructors. Large fixed
formula-code numerals are not expanded into that many successor nodes. -/
def formulaProgram : (f : Form) → R (fun _ => formCode f)
  | .fMem i j => AnnotatedRenameArithmetic.variableNode (constant 0) (constant i) (constant j)
  | .fEq i j => AnnotatedRenameArithmetic.variableNode (constant 1) (constant i) (constant j)
  | .fBot => AnnotatedRenameArithmetic.fork
      (AnnotatedRenameArithmetic.atom (constant 2)) (AnnotatedRenameArithmetic.atom (constant 0))
  | .fImp a b => AnnotatedRenameArithmetic.binary (constant 3) (formulaProgram a) (formulaProgram b)
  | .fAnd a b => AnnotatedRenameArithmetic.binary (constant 4) (formulaProgram a) (formulaProgram b)
  | .fOr a b => AnnotatedRenameArithmetic.binary (constant 5) (formulaProgram a) (formulaProgram b)
  | .fAll a => AnnotatedRenameArithmetic.unary (constant 6) (formulaProgram a)
  | .fEx a => AnnotatedRenameArithmetic.unary (constant 7) (formulaProgram a)

def all {f : Nat → Nat} (p : R f) : R (fun n => allCode (f n)) :=
  AnnotatedRenameArithmetic.unary (constant 6) p

def ex {f : Nat → Nat} (p : R f) : R (fun n => exCode (f n)) :=
  AnnotatedRenameArithmetic.unary (constant 7) p

def binary {f g : Nat → Nat} (label : Nat) (p : R f) (q : R g) :
    R (fun n => binaryCode label (f n) (g n)) :=
  AnnotatedRenameArithmetic.binary (constant label) p q

def iffProgram {f g : Nat → Nat} (p : R f) (q : R g) :
    R (fun n => iffCode (f n) (g n)) := binary 4 (binary 3 p q) (binary 3 q p)

def separationBodyProgram : R separationBody :=
  all (ex (all (iffProgram (formulaProgram (.fMem 0 1))
    (binary 4 (formulaProgram (.fMem 0 2)) identity))))

def replacementBodyProgram : R (fun n =>
    replacementBody n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2) :=
  binary 3
    (all (all (all (binary 3 (binary 4 Realizes.left (left Realizes.right))
      (formulaProgram (.fEq 1 0))))))
    (all (ex (all (iffProgram (formulaProgram (.fMem 0 1))
      (ex (binary 4 (formulaProgram (.fMem 0 3)) (right Realizes.right)))))))

private theorem exists_sealValue_iff (f : Form) (out : Nat) :
    (∃ table length,AnnotatedBoundScan.sealValue
      (AnnotatedBoundScan.sealInput (formCode f) out length table)=1) ↔
        out=formCode (sealF f) := by
  simpa only [AnnotatedBoundScan.sealProgram.property] using
    AnnotatedBoundScan.exists_seal_program_iff f out

/-- Six coordinates are argument, renamed code, goal, chain evidence,
closing length, bound table. -/
def separationInput (argument goal renamed evidence length table : Nat) : Nat :=
  rowCode ⟨argument,renamed,goal,evidence,length,table⟩

def separationValue (n : Nat) : Nat :=
  let r := decodeRow n
  AnnotatedSchemaMaps.chainValue AnnotatedSchemaMaps.separationSteps
    (AnnotatedSchemaMaps.inputCode r.tag r.depth r.second) *
  AnnotatedBoundScan.sealValue
    (AnnotatedBoundScan.sealInput (separationBody r.depth) r.first r.input r.output)

def separationProgram : R separationValue := by
  let chain := (AnnotatedSchemaMaps.chainProgram AnnotatedSchemaMaps.separationSteps).comp
    ((tag identity).pair ((depth identity).pair (second identity)))
  let body := separationBodyProgram.comp (depth identity)
  let sealed := AnnotatedBoundScan.sealProgram.comp
    (body.pair ((first identity).pair ((input identity).pair (output identity))))
  refine (mul chain sealed).ofEq ?_
  intro n
  simp only [separationValue,AnnotatedSchemaMaps.inputCode,AnnotatedBoundScan.sealInput,id_eq]

theorem separationProgram_input (argument goal renamed evidence length table : Nat) :
    separationProgram.val.eval (separationInput argument goal renamed evidence length table)=
      AnnotatedSchemaMaps.chainValue AnnotatedSchemaMaps.separationSteps
        (AnnotatedSchemaMaps.inputCode argument renamed evidence) *
      AnnotatedBoundScan.sealValue
        (AnnotatedBoundScan.sealInput (separationBody renamed) goal length table) := by
  rw [separationProgram.property]
  simp only [separationValue,separationInput,decodeRow_rowCode]

theorem exists_separation_program_iff (f : Form) (goal : Nat) :
    (∃ renamed evidence length table,separationProgram.val.eval
      (separationInput (formCode f) goal renamed evidence length table)=1) ↔
        goal=formCode (sealF (Sep_form f)) := by
  simp only [separationProgram_input,AnnotatedSchemaMaps.mul_eq_one_nat]
  constructor
  · rintro ⟨renamed,evidence,length,table,hc,hs⟩
    have hr := (AnnotatedSchemaMaps.exists_chain_iff AnnotatedSchemaMaps.separationSteps f renamed).mp
      ⟨evidence,hc⟩
    rw [AnnotatedSchemaMaps.separation_chain] at hr
    rw [hr,separationBody_formCode] at hs
    exact (exists_sealValue_iff (Sep_form f) goal).mp ⟨table,length,hs⟩
  · intro h
    obtain ⟨evidence,hc⟩ := (AnnotatedSchemaMaps.exists_chain_iff
      AnnotatedSchemaMaps.separationSteps f (formCode (rename rsep f))).mpr
        (by rw [AnnotatedSchemaMaps.separation_chain])
    obtain ⟨table,length,hs⟩ := (exists_sealValue_iff (Sep_form f) goal).mpr h
    exact ⟨formCode (rename rsep f),evidence,length,table,hc,
      by simpa only [separationBody_formCode] using hs⟩

/-- Accepted raw inputs determine a real schema argument; a parser premise
is unnecessary because the first renaming table validates that code. -/
theorem separationProgram_sound (argument goal renamed evidence length table : Nat)
    (h : separationProgram.val.eval
      (separationInput argument goal renamed evidence length table)=1) :
    ∃ f : Form,argument=formCode f ∧ goal=formCode (sealF (Sep_form f)) := by
  rw [separationProgram_input,AnnotatedSchemaMaps.mul_eq_one_nat] at h
  obtain ⟨f,hi,ho⟩ := AnnotatedSchemaMaps.chainValue_sound ⟨0,0,1⟩ [⟨0,0,1⟩]
    argument renamed evidence h.1
  refine ⟨f,hi,?_⟩
  exact (exists_separation_program_iff f goal).mp
    ⟨renamed,evidence,length,table,by simpa only [←hi] using
      (show separationProgram.val.eval
        (separationInput argument goal renamed evidence length table)=1 by
          rw [separationProgram_input,AnnotatedSchemaMaps.mul_eq_one_nat]; exact h)⟩

theorem separationProgram_primrec : Nat.Primrec separationProgram.val.eval :=
  separationProgram.val.primrec

theorem separationProgram_axiom (argument goal renamed evidence length table : Nat)
    (h : separationProgram.val.eval
      (separationInput argument goal renamed evidence length table)=1) :
    ∃ a : Form,LeanProofs.BoundedZFCConsistency.ZFCax_s a ∧ goal=formCode a := by
  obtain ⟨f,_,ho⟩ := separationProgram_sound argument goal renamed evidence length table h
  exact ⟨sealF (Sep_form f),AnnotatedProofChecker.AxiomTag.sound (.separation f),ho⟩

theorem separationBodyProgram_nodeCount : separationBodyProgram.val.nodeCount=461 := by decide
theorem replacementBodyProgram_nodeCount : replacementBodyProgram.val.nodeCount=773 := by decide
theorem separationProgram_nodeCount : separationProgram.val.nodeCount=10241 := by decide
theorem optimizedSeparationProgram_nodeCount :
    separationProgram.optimize.val.nodeCount=9333 := by decide

end DiophantineConsistency.AnnotatedSchema
