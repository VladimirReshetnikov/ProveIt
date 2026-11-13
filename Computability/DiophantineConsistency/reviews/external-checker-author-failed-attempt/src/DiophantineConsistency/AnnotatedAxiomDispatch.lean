import DiophantineConsistency.AnnotatedReplacement
import DiophantineConsistency.ArithmeticFiniteSwitch
import Mathlib.Tactic.FinCases

/-! # Supplied numeric dispatch for the actual sealed ZFC axioms -/
namespace DiophantineConsistency.AnnotatedAxiomDispatch
open SetTheory SetTheory.Form LeanProofs.BoundedZFCConsistency
open AnnotatedProofCode AnnotatedProofChecker AnnotatedRename
open ScalarPRCode DirectScalar
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000
attribute [local irreducible] Nat.unpair AnnotatedBoundScan.sealValue

/-- Fixed axiom bodies use a certified bound/closing table, rather than an
untrusted asserted closing length. Input is `(goal,(length,table))`. -/
def fixedValue (f : Form) (n : Nat) : Nat :=
  AnnotatedBoundScan.sealValue (AnnotatedBoundScan.sealInput (formCode f)
    n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2)

/-- Payload is `(goal,evidence)`. Separation evidence has fields
`argument,renamed,chainEvidence,length,boundTable,unused`. -/
def separationValue (n : Nat) : Nat :=
  let r := decodeRow n.unpair.2
  AnnotatedSchema.separationValue
    (AnnotatedSchema.separationInput r.tag n.unpair.1 r.depth r.first r.second r.input)

/-- Replacement evidence has fields `argument,a,b,c,chain1,inner`, with inner
fields `chain2,chain3,length,boundTable,unused,unused`. -/
def replacementValue (n : Nat) : Nat :=
  let r := decodeRow n.unpair.2
  let q := decodeRow r.output
  AnnotatedReplacement.value (AnnotatedReplacement.inputCode r.tag n.unpair.1
    r.depth r.first r.second r.input q.tag q.depth q.first q.second)

def body : Nat → Nat → Nat
  | 0 => fixedValue Ext_form
  | 1 => fixedValue Reg_form
  | 2 => fixedValue Pow_form
  | 3 => fixedValue Pair_form
  | 4 => fixedValue Union_form
  | 5 => fixedValue Inf_form
  | 6 => separationValue
  | 7 => replacementValue
  | 8 => fixedValue Choice_form
  | _ => fun _ => 0

/-- Invalid tags reject. The tag order is exactly the frozen `AxiomTag`
constructor order; schema arguments live in the evidence packet. -/
def value (tag goal evidence : Nat) : Nat :=
  if tag<9 then body tag (Nat.pair goal evidence) else 0

def tagNumber : AxiomTag → Nat
  | .ext => 0 | .reg => 1 | .powerset => 2 | .pair => 3 | .union => 4
  | .infinity => 5 | .separation _ => 6 | .replacement _ => 7 | .choice => 8

private theorem fixed_sound (f : Form) (n : Nat) (h : fixedValue f n=1) :
    n.unpair.1=formCode (sealF f) := by
  apply (AnnotatedBoundScan.exists_seal_program_iff f n.unpair.1).mp
  refine ⟨n.unpair.2.unpair.2,n.unpair.2.unpair.1,?_⟩
  rw [AnnotatedBoundScan.sealProgram.property]
  exact h

private theorem separation_sound (n : Nat) (h : separationValue n=1) :
    ∃ f : Form,ZFCax_s f ∧ n.unpair.1=formCode f := by
  apply AnnotatedSchema.separationProgram_axiom
    (decodeRow n.unpair.2).tag n.unpair.1 (decodeRow n.unpair.2).depth
    (decodeRow n.unpair.2).first (decodeRow n.unpair.2).second (decodeRow n.unpair.2).input
  rw [AnnotatedSchema.separationProgram.property]
  exact h

private theorem replacement_sound (n : Nat) (h : replacementValue n=1) :
    ∃ f : Form,ZFCax_s f ∧ n.unpair.1=formCode f := by
  let r := decodeRow n.unpair.2
  let q := decodeRow r.output
  apply AnnotatedReplacement.program_axiom r.tag n.unpair.1 r.depth r.first r.second
    r.input q.tag q.depth q.first q.second
  rw [AnnotatedReplacement.program.property]
  exact h

private theorem body_sound (tag : Fin 9) (n : Nat) (h : body tag.val n=1) :
    ∃ f : Form,ZFCax_s f ∧ n.unpair.1=formCode f := by
  fin_cases tag
  · exact ⟨_,AxiomTag.sound .ext,fixed_sound _ _ h⟩
  · exact ⟨_,AxiomTag.sound .reg,fixed_sound _ _ h⟩
  · exact ⟨_,AxiomTag.sound .powerset,fixed_sound _ _ h⟩
  · exact ⟨_,AxiomTag.sound .pair,fixed_sound _ _ h⟩
  · exact ⟨_,AxiomTag.sound .union,fixed_sound _ _ h⟩
  · exact ⟨_,AxiomTag.sound .infinity,fixed_sound _ _ h⟩
  · exact separation_sound n h
  · exact replacement_sound n h
  · exact ⟨_,AxiomTag.sound .choice,fixed_sound _ _ h⟩

theorem sound (tag goal evidence : Nat) (h : value tag goal evidence=1) :
    ∃ f : Form,ZFCax_s f ∧ goal=formCode f := by
  by_cases ht : tag<9
  · have hh : body tag (Nat.pair goal evidence)=1 := by simpa only [value,ht,if_true] using h
    simpa only [Nat.unpair_pair] using body_sound ⟨tag,ht⟩ (Nat.pair goal evidence) hh
  · simp only [value,ht,if_false] at h
    contradiction

private theorem fixed_complete (f : Form) :
    ∃ evidence,fixedValue f (Nat.pair (formCode (sealF f)) evidence)=1 := by
  obtain ⟨table,length,h⟩ := (AnnotatedBoundScan.exists_seal_program_iff f _).mpr rfl
  refine ⟨Nat.pair length table,?_⟩
  simpa only [fixedValue,Nat.unpair_pair,AnnotatedBoundScan.sealProgram.property] using h

private theorem separation_complete (f : Form) :
    ∃ evidence,separationValue (Nat.pair (formCode (sealF (Sep_form f))) evidence)=1 := by
  obtain ⟨a,e,length,table,h⟩ := (AnnotatedSchema.exists_separation_program_iff f _).mpr rfl
  refine ⟨rowCode ⟨formCode f,a,e,length,table,0⟩,?_⟩
  simpa only [separationValue,Nat.unpair_pair,decodeRow_rowCode,
    AnnotatedSchema.separationProgram.property] using h

private theorem replacement_complete (f : Form) :
    ∃ evidence,replacementValue (Nat.pair (formCode (sealF (Repl_form f))) evidence)=1 := by
  obtain ⟨a,b,c,e1,e2,e3,length,table,h⟩ := (AnnotatedReplacement.exists_program_iff f _).mpr rfl
  refine ⟨rowCode ⟨formCode f,a,b,c,e1,rowCode ⟨e2,e3,length,table,0,0⟩⟩,?_⟩
  simpa only [replacementValue,Nat.unpair_pair,decodeRow_rowCode,
    AnnotatedReplacement.program.property] using h

theorem complete (tag : AxiomTag) :
    ∃ evidence,value (tagNumber tag) (formCode tag.form) evidence=1 := by
  cases tag with
  | ext => simpa only [tagNumber,AxiomTag.form,value,body,if_pos (by decide : 0<9)] using fixed_complete Ext_form
  | reg => simpa only [tagNumber,AxiomTag.form,value,body,if_pos (by decide : 1<9)] using fixed_complete Reg_form
  | powerset => simpa only [tagNumber,AxiomTag.form,value,body,if_pos (by decide : 2<9)] using fixed_complete Pow_form
  | pair => simpa only [tagNumber,AxiomTag.form,value,body,if_pos (by decide : 3<9)] using fixed_complete Pair_form
  | union => simpa only [tagNumber,AxiomTag.form,value,body,if_pos (by decide : 4<9)] using fixed_complete Union_form
  | infinity => simpa only [tagNumber,AxiomTag.form,value,body,if_pos (by decide : 5<9)] using fixed_complete Inf_form
  | separation f => simpa only [tagNumber,AxiomTag.form,value,body,if_pos (by decide : 6<9)] using separation_complete f
  | replacement f => simpa only [tagNumber,AxiomTag.form,value,body,if_pos (by decide : 7<9)] using replacement_complete f
  | choice => simpa only [tagNumber,AxiomTag.form,value,body,if_pos (by decide : 8<9)] using fixed_complete Choice_form

theorem exists_value_iff (f : Form) :
    (∃ tag evidence,value tag (formCode f) evidence=1) ↔ ZFCax_s f := by
  constructor
  · rintro ⟨tag,evidence,h⟩
    obtain ⟨f',hf,he⟩ := sound tag _ evidence h
    exact formCode_injective he ▸ hf
  · intro hf
    obtain ⟨tag,ht⟩ := axiomTag_exists hf
    obtain ⟨evidence,he⟩ := complete tag
    exact ⟨tagNumber tag,evidence,by simpa only [ht] using he⟩

attribute [local irreducible] fixedValue separationValue replacementValue body value

namespace P
open AnnotatedRenameLocal.Program (left right tag depth first second input output)

def rowProgram {a b c d e f : Nat → Nat} (pa : R a) (pb : R b) (pc : R c)
    (pd : R d) (pe : R e) (pf : R f) :
    R (fun n => rowCode ⟨a n,b n,c n,d n,e n,f n⟩) := pa.pair (pb.pair (pc.pair (pd.pair (pe.pair pf))))

def fixedProgram (f : Form) : R (fixedValue f) :=
  (AnnotatedBoundScan.sealProgram.comp ((AnnotatedSchema.formulaProgram f).pair
    (Realizes.left.pair ((left Realizes.right).pair (right Realizes.right))))).ofEq
      (fun _ => by simp only [fixedValue,AnnotatedBoundScan.sealInput])

def separationProgram : R separationValue :=
  (AnnotatedSchema.separationProgram.comp (rowProgram (tag Realizes.right) (depth Realizes.right)
    Realizes.left (first Realizes.right) (second Realizes.right) (input Realizes.right))).ofEq
      (fun _ => by simp only [separationValue,AnnotatedSchema.separationInput])

def replacementProgram : R replacementValue := by
  let r := Realizes.right
  let q := output r
  let inner := rowProgram (tag q) (depth q) Realizes.left (first q) (second q) Realizes.zero
  let outer := rowProgram (tag r) (depth r) (first r) (second r) (input r) inner
  refine (AnnotatedReplacement.program.comp outer).ofEq ?_
  intro n
  simp only [replacementValue,AnnotatedReplacement.inputCode]

def bodyProgram : (tag : Nat) → R (body tag)
  | 0 => (fixedProgram Ext_form).ofEq (fun _ => by simp only [body])
  | 1 => (fixedProgram Reg_form).ofEq (fun _ => by simp only [body])
  | 2 => (fixedProgram Pow_form).ofEq (fun _ => by simp only [body])
  | 3 => (fixedProgram Pair_form).ofEq (fun _ => by simp only [body])
  | 4 => (fixedProgram Union_form).ofEq (fun _ => by simp only [body])
  | 5 => (fixedProgram Inf_form).ofEq (fun _ => by simp only [body])
  | 6 => separationProgram.ofEq (fun _ => by simp only [body])
  | 7 => replacementProgram.ofEq (fun _ => by simp only [body])
  | 8 => (fixedProgram Choice_form).ofEq (fun _ => by simp only [body])
  | _+9 => Realizes.zero.ofEq (fun _ => by simp only [body])

def inputValue (n : Nat) : Nat := value n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2

def program : R inputValue :=
  ((ArithmeticFiniteSwitch.program body bodyProgram) 9).ofEq
    (fun _ => by simp only [ArithmeticFiniteSwitch.value,inputValue,value,Nat.pair_unpair])
end P

def inputCode (tag goal evidence : Nat) : Nat := Nat.pair tag (Nat.pair goal evidence)

theorem program_input (tag goal evidence : Nat) :
    P.program.val.eval (inputCode tag goal evidence)=value tag goal evidence := by
  rw [P.program.property]
  simp only [P.inputValue,inputCode,Nat.unpair_pair]

theorem program_sound (raw : Nat) (h : P.program.val.eval raw=1) :
    ∃ f : Form,ZFCax_s f ∧ raw.unpair.2.unpair.1=formCode f := by
  rw [P.program.property] at h
  exact sound _ _ _ h

theorem exists_program_iff (f : Form) :
    (∃ tag evidence,P.program.val.eval (inputCode tag (formCode f) evidence)=1) ↔ ZFCax_s f := by
  simp only [program_input]
  exact exists_value_iff f

theorem program_primrec : Nat.Primrec P.program.val.eval := P.program.val.primrec

def optimizedProgram : R P.inputValue := P.program.optimize

end DiophantineConsistency.AnnotatedAxiomDispatch
