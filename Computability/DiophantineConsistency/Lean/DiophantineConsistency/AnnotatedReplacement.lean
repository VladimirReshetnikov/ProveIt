import DiophantineConsistency.AnnotatedSchema

/-! # A supplied arithmetic certificate validator for actual sealed Replacement -/
namespace DiophantineConsistency.AnnotatedReplacement

open SetTheory SetTheory.Form AnnotatedProofCode AnnotatedRename AnnotatedSchema
open ScalarPRCode DirectScalar
open AnnotatedRenameLocal.Program (tag depth first second input output)

set_option maxRecDepth 20000
set_option maxHeartbeats 1200000
attribute [local irreducible] Nat.unpair AnnotatedSchemaMaps.chainValue
  AnnotatedBoundScan.sealValue

/-- The outer six fields contain the argument, three renamed codes, first
chain evidence, and a second six-field packet. Its fields contain the two
remaining chain witnesses, goal, closing length, bound table, and zero. -/
def inputCode (argument goal a b c evidence1 evidence2 evidence3 length table : Nat) : Nat :=
  rowCode ⟨argument,a,b,c,evidence1,rowCode ⟨evidence2,evidence3,goal,length,table,0⟩⟩

def value (n : Nat) : Nat :=
  let r := decodeRow n
  let q := decodeRow r.output
  AnnotatedSchemaMaps.chainValue AnnotatedSchemaMaps.functionFirstSteps
    (AnnotatedSchemaMaps.inputCode r.tag r.depth r.input) *
  AnnotatedSchemaMaps.chainValue AnnotatedSchemaMaps.functionSecondSteps
    (AnnotatedSchemaMaps.inputCode r.tag r.first q.tag) *
  AnnotatedSchemaMaps.chainValue AnnotatedSchemaMaps.imageSteps
    (AnnotatedSchemaMaps.inputCode r.tag r.second q.depth) *
  AnnotatedBoundScan.sealValue
    (AnnotatedBoundScan.sealInput (replacementBody r.depth r.first r.second) q.first q.second q.input)

def program : R value := by
  let r := identity
  let q := output r
  let c1 := (AnnotatedSchemaMaps.chainProgram AnnotatedSchemaMaps.functionFirstSteps).comp
    ((tag r).pair ((depth r).pair (input r)))
  let c2 := (AnnotatedSchemaMaps.chainProgram AnnotatedSchemaMaps.functionSecondSteps).comp
    ((tag r).pair ((first r).pair (tag q)))
  let c3 := (AnnotatedSchemaMaps.chainProgram AnnotatedSchemaMaps.imageSteps).comp
    ((tag r).pair ((second r).pair (depth q)))
  let body := replacementBodyProgram.comp ((depth r).pair ((first r).pair (second r)))
  let sealed := AnnotatedBoundScan.sealProgram.comp
    (body.pair ((first q).pair ((second q).pair (input q))))
  refine (mul (mul (mul c1 c2) c3) sealed).ofEq ?_
  intro n
  simp only [value,AnnotatedSchemaMaps.inputCode,AnnotatedBoundScan.sealInput,
    Nat.unpair_pair,id_eq]

theorem program_input (argument goal a b c evidence1 evidence2 evidence3 length table : Nat) :
    program.val.eval (inputCode argument goal a b c evidence1 evidence2 evidence3 length table)=
      AnnotatedSchemaMaps.chainValue AnnotatedSchemaMaps.functionFirstSteps
        (AnnotatedSchemaMaps.inputCode argument a evidence1) *
      AnnotatedSchemaMaps.chainValue AnnotatedSchemaMaps.functionSecondSteps
        (AnnotatedSchemaMaps.inputCode argument b evidence2) *
      AnnotatedSchemaMaps.chainValue AnnotatedSchemaMaps.imageSteps
        (AnnotatedSchemaMaps.inputCode argument c evidence3) *
      AnnotatedBoundScan.sealValue
        (AnnotatedBoundScan.sealInput (replacementBody a b c) goal length table) := by
  rw [program.property]
  simp only [value,inputCode,decodeRow_rowCode]

private theorem exists_sealValue_iff (f : Form) (out : Nat) :
    (∃ table length,AnnotatedBoundScan.sealValue
      (AnnotatedBoundScan.sealInput (formCode f) out length table)=1) ↔
        out=formCode (sealF f) := by
  simpa only [AnnotatedBoundScan.sealProgram.property] using
    AnnotatedBoundScan.exists_seal_program_iff f out

theorem exists_program_iff (f : Form) (goal : Nat) :
    (∃ a b c e1 e2 e3 length table,program.val.eval
      (inputCode (formCode f) goal a b c e1 e2 e3 length table)=1) ↔
        goal=formCode (sealF (Repl_form f)) := by
  simp only [program_input,AnnotatedSchemaMaps.mul_eq_one_nat]
  constructor
  · rintro ⟨a,b,c,e1,e2,e3,length,table,⟨⟨hc1,hc2⟩,hc3⟩,hs⟩
    have ha := (AnnotatedSchemaMaps.exists_chain_iff
      AnnotatedSchemaMaps.functionFirstSteps f a).mp ⟨e1,hc1⟩
    have hb := (AnnotatedSchemaMaps.exists_chain_iff
      AnnotatedSchemaMaps.functionSecondSteps f b).mp ⟨e2,hc2⟩
    have hc := (AnnotatedSchemaMaps.exists_chain_iff
      AnnotatedSchemaMaps.imageSteps f c).mp ⟨e3,hc3⟩
    rw [AnnotatedSchemaMaps.functionFirst_chain] at ha
    rw [AnnotatedSchemaMaps.functionSecond_chain] at hb
    rw [AnnotatedSchemaMaps.image_chain] at hc
    rw [ha,hb,hc,replacementBody_formCode] at hs
    exact (exists_sealValue_iff (Repl_form f) goal).mp ⟨table,length,hs⟩
  · intro h
    obtain ⟨e1,hc1⟩ := (AnnotatedSchemaMaps.exists_chain_iff
      AnnotatedSchemaMaps.functionFirstSteps f (formCode (rename rf1 f))).mpr
        (by rw [AnnotatedSchemaMaps.functionFirst_chain])
    obtain ⟨e2,hc2⟩ := (AnnotatedSchemaMaps.exists_chain_iff
      AnnotatedSchemaMaps.functionSecondSteps f (formCode (rename rf2 f))).mpr
        (by rw [AnnotatedSchemaMaps.functionSecond_chain])
    obtain ⟨e3,hc3⟩ := (AnnotatedSchemaMaps.exists_chain_iff
      AnnotatedSchemaMaps.imageSteps f (formCode (rename ri f))).mpr
        (by rw [AnnotatedSchemaMaps.image_chain])
    obtain ⟨table,length,hs⟩ := (exists_sealValue_iff (Repl_form f) goal).mpr h
    exact ⟨formCode (rename rf1 f),formCode (rename rf2 f),formCode (rename ri f),
      e1,e2,e3,length,table,⟨⟨hc1,hc2⟩,hc3⟩,
        by simpa only [replacementBody_formCode] using hs⟩

/-- Any accepted raw input determines an actual schema formula. -/
theorem program_sound (argument goal a b c e1 e2 e3 length table : Nat)
    (h : program.val.eval (inputCode argument goal a b c e1 e2 e3 length table)=1) :
    ∃ f : Form,argument=formCode f ∧ goal=formCode (sealF (Repl_form f)) := by
  have hh := h
  rw [program_input,AnnotatedSchemaMaps.mul_eq_one_nat,
    AnnotatedSchemaMaps.mul_eq_one_nat,AnnotatedSchemaMaps.mul_eq_one_nat] at hh
  obtain ⟨f,hi,ho⟩ := AnnotatedSchemaMaps.chainValue_sound ⟨0,0,0⟩ [] argument a e1 hh.1.1.1
  refine ⟨f,hi,(exists_program_iff f goal).mp ?_⟩
  exact ⟨a,b,c,e1,e2,e3,length,table,by simpa only [←hi] using h⟩

theorem program_primrec : Nat.Primrec program.val.eval := program.val.primrec

theorem program_axiom (argument goal a b c e1 e2 e3 length table : Nat)
    (h : program.val.eval (inputCode argument goal a b c e1 e2 e3 length table)=1) :
    ∃ ax : Form,LeanProofs.BoundedZFCConsistency.ZFCax_s ax ∧ goal=formCode ax := by
  obtain ⟨f,_,ho⟩ := program_sound argument goal a b c e1 e2 e3 length table h
  exact ⟨sealF (Repl_form f),AnnotatedProofChecker.AxiomTag.sound (.replacement f),ho⟩

theorem program_nodeCount : program.val.nodeCount=25535 := by decide
theorem optimizedProgram_nodeCount : program.optimize.val.nodeCount=23463 := by decide

end DiophantineConsistency.AnnotatedReplacement
