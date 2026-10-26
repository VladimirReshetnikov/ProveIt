import DiophantineConsistency.AnnotatedContextLookup

/-! # A literal raw-sound arithmetic validator for the original assumption rule -/
namespace DiophantineConsistency.AnnotatedAssumption

open SetTheory SetTheory.Form AnnotatedProofCode AnnotatedRename AnnotatedContext
open ScalarPRCode DirectScalar
open AnnotatedRenameLocal.Program (tag depth first second input)
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000
attribute [local irreducible] Nat.unpair AnnotatedContext.checkNat

/-- Five fields are context, conclusion, shifted context, shift evidence,
and membership index. The final field is unused. -/
def inputCode (context conclusion shifted evidence index : Nat) : Nat :=
  rowCode ⟨context,conclusion,shifted,evidence,index,0⟩

def value (n : Nat) : Nat :=
  let r := decodeRow n
  AnnotatedContext.checkNat r.tag r.first r.second *
    AnnotatedContextLookup.referenceValue (Nat.pair r.tag (Nat.pair r.input r.depth))

def program : R value := by
  let r := identity
  let context := AnnotatedContextPR.P.program.comp
    ((tag r).pair ((first r).pair (second r)))
  let member := AnnotatedContextLookup.referenceProgram.comp
    ((tag r).pair ((input r).pair (depth r)))
  refine (mul context member).ofEq ?_
  intro n
  simp only [value,AnnotatedContextPR.P.value,Nat.unpair_pair,id_eq]

theorem program_input (context conclusion shifted evidence index : Nat) :
    program.val.eval (inputCode context conclusion shifted evidence index)=
      AnnotatedContext.checkNat context shifted evidence *
        AnnotatedContextLookup.referenceValue (Nat.pair context (Nat.pair index conclusion)) := by
  rw [program.property]
  simp only [inputCode,value,decodeRow_rowCode]

private theorem lookup_mem {G : List Form} {index : Nat} {f : Form}
    (h : G[index]?=some f) : f∈G :=
  List.mem_of_getElem? h

private theorem exists_lookup (G : List Form) (f : Form) (h : f∈G) :
    ∃ index : Nat,G[index]?=some f :=
  List.getElem?_of_mem h

/-- Raw accepted codes determine an actual context and a member formula. -/
theorem program_sound (context conclusion shifted evidence index : Nat)
    (h : program.val.eval (inputCode context conclusion shifted evidence index)=1) :
    ∃ G : List Form,∃ f : Form,context=contextCode G ∧ conclusion=formCode f ∧ f∈G := by
  rw [program_input,AnnotatedSchemaMaps.mul_eq_one_nat] at h
  obtain ⟨G,hG,_⟩ := AnnotatedContext.checkNat_sound context shifted evidence h.1
  have hm := h.2
  rw [hG] at hm
  obtain ⟨f,hf,hcode⟩ := AnnotatedContextLookup.reference_raw G index conclusion hm
  exact ⟨G,f,hG,hcode,lookup_mem hf⟩

theorem exists_program_iff (G : List Form) (f : Form) :
    (∃ shifted evidence index,program.val.eval
      (inputCode (contextCode G) (formCode f) shifted evidence index)=1) ↔ f∈G := by
  constructor
  · rintro ⟨shifted,evidence,index,h⟩
    rw [program_input,AnnotatedSchemaMaps.mul_eq_one_nat] at h
    exact lookup_mem ((AnnotatedContextLookup.reference_context G index f).mp h.2)
  · intro h
    obtain ⟨index,hi⟩ := exists_lookup G f h
    obtain ⟨evidence,he⟩ := (AnnotatedContext.exists_check_iff G
      (contextCode (G.map (rename Nat.succ)))).mpr rfl
    refine ⟨contextCode (G.map (rename Nat.succ)),evidence,index,?_⟩
    rw [program_input,AnnotatedSchemaMaps.mul_eq_one_nat]
    exact ⟨he,(AnnotatedContextLookup.reference_context G index f).mpr hi⟩

/-- Exact agreement with the frozen original parent-index checker on the
assumption line, including its empty premise list. -/
theorem exists_program_iff_line (G : List Form) (f : Form) :
    (∃ shifted evidence index,program.val.eval
      (inputCode (contextCode G) (formCode f) shifted evidence index)=1) ↔
        (AnnotatedProofChecker.Line.mk (.ass G f) []).valid []=true := by
  rw [exists_program_iff]
  simp [AnnotatedProofChecker.Line.valid,AnnotatedProofChecker.Rule.side,
    AnnotatedProofChecker.Rule.premises]

theorem program_provable (context conclusion shifted evidence index : Nat)
    (h : program.val.eval (inputCode context conclusion shifted evidence index)=1) :
    ∃ G : List Form,∃ f : Form,context=contextCode G ∧ conclusion=formCode f ∧ Prov G f := by
  obtain ⟨G,f,hG,hf,hm⟩ := program_sound context conclusion shifted evidence index h
  exact ⟨G,f,hG,hf,.P_ass G f hm⟩

theorem program_primrec : Nat.Primrec program.val.eval := program.val.primrec

def optimizedProgram : R value := program.optimize

theorem program_nodeCount : program.val.nodeCount=4753 := by decide
theorem optimizedProgram_nodeCount : optimizedProgram.val.nodeCount=4391 := by decide

end DiophantineConsistency.AnnotatedAssumption
