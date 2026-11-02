import DiophantineConsistency.AnnotatedAxiomContext
import DiophantineConsistency.AnnotatedLineScan

/-! # A supplied primitive-recursive sealed-ZFC refutation checker

The input is entirely untrusted numeric certificate data. The theorem is
about the original sealed-ZFC calculus, without a machine/calculus translation
or a syntax-parser premise. It remains an external natural-number theorem.
-/
namespace DiophantineConsistency.AnnotatedRefutationPR
open SetTheory SetTheory.Form LeanProofs.BoundedZFCConsistency
open AnnotatedProofCode AnnotatedCodeArithmetic AnnotatedContext AnnotatedRename
open ScalarPRCode DirectScalar
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000
attribute [local irreducible] Nat.unpair

/-- Certificate fields are context code, axiom-scanner fuel, axiom evidence,
line-scanner fuel, line evidence, and an unused field. -/
def value (goal certificate : Nat) : Nat :=
  let r := decodeRow certificate
  AnnotatedAxiomContext.checkNat r.tag r.depth r.first *
    AnnotatedLineScan.checkNat (forkCode r.tag goal) r.second r.input

theorem forkCode_eq_iff (a b c d : Nat) : forkCode a b=forkCode c d ↔ a=c ∧ b=d := by
  simp only [forkCode,Nat.add_right_cancel_iff,Nat.pair_eq_pair]

/-- Even an arbitrary claimed formula code must denote an actual formula
whenever its complete numeric certificate is accepted. -/
theorem raw_sound (goal certificate : Nat) (h : value goal certificate=1) :
    ∃ f : Form,goal=formCode f ∧ BProv ZFCax_s [] f := by
  simp only [value,AnnotatedSchemaMaps.mul_eq_one_nat] at h
  obtain ⟨G,hctx,hG⟩ := AnnotatedAxiomContext.checkNat_sound _ _ _ h.1
  obtain ⟨j,hj,hP⟩ := AnnotatedLineScan.checkNat_sound _ _ _ h.2
  change forkCode (decodeRow certificate).tag goal=
    forkCode (contextCode j.context) (formCode j.conclusion) at hj
  obtain ⟨hc,hf⟩ := (forkCode_eq_iff _ _ _ _).mp hj
  have hcontext : G=j.context := contextCode_injective (hctx.symm.trans hc)
  refine ⟨j.conclusion,hf,j.context,?_,?_⟩
  · exact hcontext ▸ hG
  · simpa only [List.append_nil,AnnotatedProofChecker.Judgment.Provable] using hP

theorem sound (f : Form) (certificate : Nat) (h : value (formCode f) certificate=1) :
    BProv ZFCax_s [] f := by
  obtain ⟨f',he,hf⟩ := raw_sound _ _ h
  exact formCode_injective he ▸ hf

theorem complete (f : Form) (h : BProv ZFCax_s [] f) :
    ∃ certificate,value (formCode f) certificate=1 := by
  obtain ⟨G,hG,hP⟩ := h
  simp only [List.append_nil] at hP
  obtain ⟨axiomFuel,axiomEvidence,ha⟩ := AnnotatedAxiomContext.checkNat_complete G hG
  obtain ⟨lineFuel,lineEvidence,hl⟩ := AnnotatedLineScan.checkNat_complete ⟨G,f⟩ hP
  refine ⟨rowCode ⟨contextCode G,axiomFuel,axiomEvidence,lineFuel,lineEvidence,0⟩,?_⟩
  change AnnotatedLineScan.checkNat (forkCode (contextCode G) (formCode f)) lineFuel lineEvidence=1 at hl
  simp only [value,decodeRow_rowCode,ha,hl,Nat.one_mul]

theorem exists_value_iff (f : Form) :
    (∃ certificate,value (formCode f) certificate=1) ↔ BProv ZFCax_s [] f :=
  ⟨fun ⟨certificate,h⟩ => sound f certificate h,complete f⟩

attribute [local irreducible] value

namespace P
open AnnotatedRenameLocal.Program (left right tag depth first second input)

def contextProgram : R (fun n => AnnotatedAxiomContext.checkNat (decodeRow n.unpair.2).tag
    (decodeRow n.unpair.2).depth (decodeRow n.unpair.2).first) :=
  (AnnotatedAxiomContext.P.program.comp ((tag Realizes.right).pair
    ((depth Realizes.right).pair (first Realizes.right)))).ofEq
      (fun _ => by simp only [AnnotatedAxiomContext.P.value,Nat.unpair_pair])

def proofProgram : R (fun n => AnnotatedLineScan.checkNat
    (forkCode (decodeRow n.unpair.2).tag n.unpair.1) (decodeRow n.unpair.2).second
      (decodeRow n.unpair.2).input) :=
  (AnnotatedLineScan.P.program.comp ((AnnotatedRenameArithmetic.fork (tag Realizes.right) Realizes.left).pair
    ((second Realizes.right).pair (input Realizes.right)))).ofEq
      (fun _ => by simp only [AnnotatedLineScan.P.value,Nat.unpair_pair])

def inputValue (n : Nat) : Nat := value n.unpair.1 n.unpair.2

def program : R inputValue :=
  (mul contextProgram proofProgram).ofEq (fun _ => by simp only [inputValue,value])
end P

theorem program_input (goal certificate : Nat) :
    P.program.val.eval (Nat.pair goal certificate)=value goal certificate := by
  rw [P.program.property]
  simp only [P.inputValue,Nat.unpair_pair]

theorem program_raw_sound (raw : Nat) (h : P.program.val.eval raw=1) :
    ∃ f : Form,raw.unpair.1=formCode f ∧ BProv ZFCax_s [] f := by
  rw [P.program.property] at h
  exact raw_sound _ _ h

theorem exists_program_iff (f : Form) :
    (∃ certificate,P.program.val.eval (Nat.pair (formCode f) certificate)=1) ↔ BProv ZFCax_s [] f := by
  simp only [program_input]
  exact exists_value_iff f

theorem program_primrec : Nat.Primrec P.program.val.eval := P.program.val.primrec

/-- Closed literal unary program; the bottom formula code is constructed from
its syntax, rather than expanded as that many successor instructions. -/
def refutationProgram : R (value (formCode fBot)) :=
  (P.program.comp ((AnnotatedSchema.formulaProgram fBot).pair identity)).ofEq
    (fun _ => by simp only [P.inputValue,Nat.unpair_pair,id_eq])

theorem refutationProgram_input (certificate : Nat) :
    refutationProgram.val.eval certificate=value (formCode fBot) certificate := refutationProgram.property certificate

theorem exists_refutation_iff :
    (∃ certificate,refutationProgram.val.eval certificate=1) ↔ BProv ZFCax_s [] fBot := by
  simp only [refutationProgram_input]
  exact exists_value_iff fBot

theorem no_refutation_iff :
    (¬∃ certificate,refutationProgram.val.eval certificate=1) ↔ ¬ BProv ZFCax_s [] fBot := by
  exact not_congr exists_refutation_iff

theorem refutationProgram_primrec : Nat.Primrec refutationProgram.val.eval := refutationProgram.val.primrec

def optimizedProgram : R (value (formCode fBot)) := refutationProgram.optimize

end DiophantineConsistency.AnnotatedRefutationPR
