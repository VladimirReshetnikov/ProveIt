import DiophantineConsistency.AnnotatedContextPR

/-! # Exact supplied lookup on the frozen quoted-context wire format -/
namespace DiophantineConsistency.AnnotatedContextLookup
open ScalarPRCode DirectScalar AnnotatedProofCode AnnotatedCodeArithmetic AnnotatedContext
open SetTheory SetTheory.Form
set_option maxRecDepth 16000
set_option maxHeartbeats 1200000
attribute [local irreducible] Nat.unpair

def head (code : Nat) : Nat := if code=1 then 0 else treeLeftChild code+1
def tail (code : Nat) : Nat := if code=1 then 1 else treeRight code

def drop (code index : Nat) : Nat := index.rec code (fun _ acc => tail acc)
def lookup (code index : Nat) : Nat := head (drop code index)

def headProgram : R head :=
  ifEq identity (constant 1) Realizes.zero (successor treeLeftChildProgram)

def tailProgram : R tail :=
  ifEq identity (constant 1) (constant 1) treeRightProgram

def dropProgram : R (fun n => drop n.unpair.1 n.unpair.2) :=
  recursion (g := fun _ _ acc => tail acc) identity
    (tailProgram.comp (Realizes.right.comp Realizes.right))

def lookupProgram : R (fun n => lookup n.unpair.1 n.unpair.2) := headProgram.comp dropProgram

private theorem cons_ne_one (f : Form) (G : List Form) : contextCode (f::G)≠1 := by
  have h := Nat.left_le_pair (formCode f+1) (contextCode G)
  rw [contextCode_cons]
  unfold AnnotatedRename.forkCode
  omega

@[simp] theorem head_nil : head (contextCode [])=0 := rfl
@[simp] theorem tail_nil : tail (contextCode [])=contextCode [] := rfl
@[simp] theorem head_cons (f : Form) (G : List Form) :
    head (contextCode (f::G))=formCode f+1 := by
  have hn := cons_ne_one f G
  simp only [head,hn,if_false]
  simp only [contextCode_cons,treeLeftChild,treeLeft,
    AnnotatedRename.forkCode,Nat.pred_eq_sub_one,Nat.add_sub_cancel,Nat.unpair_pair]

@[simp] theorem tail_cons (f : Form) (G : List Form) :
    tail (contextCode (f::G))=contextCode G := by
  have hn := cons_ne_one f G
  simp only [tail,hn,if_false]
  simp only [contextCode_cons,treeRight,AnnotatedRename.forkCode,
    Nat.pred_eq_sub_one,Nat.add_sub_cancel,Nat.unpair_pair]

theorem drop_succ (code index : Nat) : drop code (index+1)=drop (tail code) index := by
  simpa only [drop] using NatIterate.rec_succ tail code index

theorem lookup_contextCode (G : List Form) (index : Nat) :
    lookup (contextCode G) index=optionCode ((G[index]?).map formCode) := by
  induction G generalizing index with
  | nil =>
    change head (drop (contextCode []) index)=0
    rw [show drop (contextCode []) index = contextCode [] from
      NatIterate.rec_fixed tail _ tail_nil index]
    exact head_nil
  | cons f G ih =>
    cases index with
    | zero => exact head_cons f G
    | succ index =>
      rw [lookup,drop_succ,tail_cons]
      exact ih index

def referenceValue (n : Nat) : Nat :=
  if lookup n.unpair.1 n.unpair.2.unpair.1=n.unpair.2.unpair.2+1 then 1 else 0

def referenceProgram : R referenceValue := by
  let looked : R (fun n => lookup n.unpair.1 n.unpair.2.unpair.1) :=
    (lookupProgram.comp (Realizes.left.pair (Realizes.left.comp Realizes.right))).ofEq
      (fun _ => by simp only [Nat.unpair_pair])
  exact ifEq looked (successor (Realizes.right.comp Realizes.right)) (constant 1) Realizes.zero

theorem reference_raw (G : List Form) (index code : Nat)
    (h : referenceValue (Nat.pair (contextCode G) (Nat.pair index code))=1) :
    ∃ f : Form,G[index]?=some f ∧ code=formCode f := by
  simp only [referenceValue,Nat.unpair_pair,lookup_contextCode] at h
  cases hf : G[index]? with
  | none => simp [hf,optionCode] at h
  | some f =>
    simp only [hf,Option.map_some,optionCode] at h
    have hc : code=formCode f := by split_ifs at h; omega
    exact ⟨f,rfl,hc⟩

theorem reference_context (G : List Form) (index : Nat) (f : Form) :
    referenceValue (Nat.pair (contextCode G) (Nat.pair index (formCode f)))=1 ↔
      G[index]?=some f := by
  constructor
  · intro h
    obtain ⟨a,ha,he⟩ := reference_raw G index (formCode f) h
    have hfa := AnnotatedRename.formCode_injective he
    simpa only [←hfa] using ha
  · intro h
    simp only [referenceValue,Nat.unpair_pair,lookup_contextCode,h,Option.map_some,
      optionCode,if_true]

theorem lookupProgram_primrec : Nat.Primrec lookupProgram.val.eval := lookupProgram.val.primrec

theorem lookupProgram_nodeCount : lookupProgram.val.nodeCount=207 := by decide
theorem referenceProgram_nodeCount : referenceProgram.val.nodeCount=501 := by decide
theorem optimizedReferenceProgram_nodeCount : referenceProgram.optimize.val.nodeCount=485 := by decide

end DiophantineConsistency.AnnotatedContextLookup
