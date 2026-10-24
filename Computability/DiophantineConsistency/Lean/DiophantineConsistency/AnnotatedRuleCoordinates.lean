import DiophantineConsistency.AnnotatedContextPR
import DiophantineConsistency.AnnotatedBoundScan

/-! # Supplied validation of the coordinates shared by the seventeen rules

Raw coordinates are validated by one context table, one bound table for B,
two instantiation tables for A, and one shift table for C. The latter tables
also establish that the raw A and C codes denote actual formulas. -/
namespace DiophantineConsistency.AnnotatedRuleCoordinates

open SetTheory SetTheory.Form AnnotatedProofCode AnnotatedRename
open ScalarPRCode DirectScalar
open AnnotatedRenameLocal (truth_eq_one)
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000
attribute [local irreducible] Nat.unpair AnnotatedContext.checkNat
  AnnotatedBoundScan.checkNat AnnotatedRenameScan.checkNat

structure Coordinates where
  context : Nat
  shifted : Nat
  a : Nat
  b : Nat
  c : Nat
  instI : Nat
  instJ : Nat
  shiftC : Nat
  i : Nat
  j : Nat
  deriving DecidableEq, Repr

/-- The two rows store five coordinates each; their final tail is ignored. -/
def encode (r : Coordinates) : Nat := rowCode ⟨r.context,r.shifted,r.a,r.b,r.c,
  rowCode ⟨r.instI,r.instJ,r.shiftC,r.i,r.j,0⟩⟩

def decode (n : Nat) : Coordinates :=
  let r := decodeRow n
  let q := decodeRow r.output
  ⟨r.tag,r.depth,r.first,r.second,r.input,q.tag,q.depth,q.first,q.second,q.input⟩

@[simp] theorem decode_encode (r : Coordinates) : decode (encode r)=r := by
  cases r
  simp only [decode,encode,decodeRow_rowCode]

def quote (G : List Form) (a b c : Form) (i j : Nat) : Coordinates :=
  ⟨AnnotatedContext.contextCode G,AnnotatedContext.contextCode (G.map (rename Nat.succ)),
    formCode a,formCode b,formCode c,formCode (rename (inst i) a),
    formCode (rename (inst j) a),formCode (rename Nat.succ c),i,j⟩

def Good (r : Coordinates) : Prop :=
  ∃ G : List Form,∃ a b c : Form,r=quote G a b c r.i r.j

/-- Evidence fields are context table, bound of B, bound table for B,
inst-i table, inst-j table, and C-shift table. -/
def check (r : Coordinates) (e : Row) : Nat :=
  AnnotatedContext.checkNat r.context r.shifted e.tag *
    (AnnotatedBoundScan.checkNat r.b e.depth e.first *
      (AnnotatedRenameScan.checkNat 1 r.i 0 r.a r.instI e.second *
        (AnnotatedRenameScan.checkNat 1 r.j 0 r.a r.instJ e.input *
          AnnotatedRenameScan.checkNat 0 0 0 r.c r.shiftC e.output)))

private theorem bound_raw (input bound table : Nat)
    (h : AnnotatedBoundScan.checkNat input bound table=1) :
    ∃ f : Form,input=formCode f := by
  rw [AnnotatedBoundScan.checkNat_eq_checkCode,truth_eq_one] at h
  obtain ⟨f,hi,_⟩ := AnnotatedBound.checkCode_sound input bound table h
  exact ⟨f,hi⟩

private theorem rename_raw (mode parameter input output table : Nat)
    (h : AnnotatedRenameScan.checkNat mode parameter 0 input output table=1) :
    ∃ f : Form,input=formCode f ∧ output=formCode (renamed mode parameter 0 f) := by
  rw [AnnotatedRenameScan.checkNat_eq_checkCode,truth_eq_one] at h
  exact checkCode_sound mode parameter 0 input output table h

private theorem rename_output (mode parameter : Nat) (f : Form) (output table : Nat)
    (h : AnnotatedRenameScan.checkNat mode parameter 0 (formCode f) output table=1) :
    output=formCode (renamed mode parameter 0 f) := by
  rw [AnnotatedRenameScan.checkNat_eq_checkCode,truth_eq_one] at h
  exact (exists_code_iff mode parameter 0 f output).mp ⟨table,h⟩

/-- Every raw accepted coordinate packet has genuine formula/context data. -/
theorem check_sound (r : Coordinates) (e : Row) (h : check r e=1) : Good r := by
  simp only [check,AnnotatedSchemaMaps.mul_eq_one_nat] at h
  rcases h with ⟨hG,hB,hI,hJ,hC⟩
  obtain ⟨G,hG,hGs⟩ := AnnotatedContext.checkNat_sound _ _ _ hG
  obtain ⟨b,hb⟩ := bound_raw _ _ _ hB
  obtain ⟨a,ha,hi⟩ := rename_raw _ _ _ _ _ hI
  obtain ⟨c,hc,hsc⟩ := rename_raw _ _ _ _ _ hC
  have hj := hJ
  rw [ha] at hj
  have hj := rename_output 1 r.j a r.instJ e.input hj
  simp only [renamed,index_inst 1 _ (by decide)] at hi hj
  simp only [renamed,index_shift] at hsc
  refine ⟨G,a,b,c,?_⟩
  cases r
  simp only [quote,Coordinates.mk.injEq]
  exact ⟨hG,hGs,ha,hb,hc,hi,hj,hsc,by trivial⟩

/-- Witness existence is proved in Prop; no witness is selected into program data. -/
theorem check_complete (G : List Form) (a b c : Form) (i j : Nat) :
    ∃ e : Row,check (quote G a b c i j) e=1 := by
  obtain ⟨contextTable,hG⟩ := (AnnotatedContext.exists_check_iff G
    (AnnotatedContext.contextCode (G.map (rename Nat.succ)))).mpr rfl
  obtain ⟨boundTable,hB⟩ := (AnnotatedBound.exists_code_iff b (bound b)).mpr rfl
  obtain ⟨iTable,hI⟩ := (exists_code_iff 1 i 0 a (formCode (rename (inst i) a))).mpr
    (by simp only [renamed,index_inst 1 _ (by decide)])
  obtain ⟨jTable,hJ⟩ := (exists_code_iff 1 j 0 a (formCode (rename (inst j) a))).mpr
    (by simp only [renamed,index_inst 1 _ (by decide)])
  obtain ⟨cTable,hC⟩ := (exists_code_iff 0 0 0 c (formCode (rename Nat.succ c))).mpr
    (by simp only [renamed,index_shift])
  refine ⟨⟨contextTable,bound b,boundTable,iTable,jTable,cTable⟩,?_⟩
  simp only [check,quote,AnnotatedSchemaMaps.mul_eq_one_nat,
    AnnotatedBoundScan.checkNat_eq_checkCode,AnnotatedRenameScan.checkNat_eq_checkCode,truth_eq_one]
  exact ⟨hG,hB,hI,hJ,hC⟩

attribute [local irreducible] check

namespace P
open AnnotatedRenameLocal.Program (tag depth first second input output)

/-- A genuinely variable parameter is supplied to the frozen rename program. -/
def renameProgram {m k d i o t : Nat → Nat}
    (pm : R m) (pk : R k) (pd : R d) (pi : R i) (po : R o) (pt : R t) :
    R (fun n => AnnotatedRenameScan.checkNat (m n) (k n) (d n) (i n) (o n) (t n)) :=
  (AnnotatedRenameScanPR.P.program.comp (pm.pair (pk.pair (pd.pair (pi.pair (po.pair pt)))))).ofEq
    (fun _ => by simp only [AnnotatedRenameScanPR.P.value,decodeRow,Nat.unpair_pair])

def boundProgram {i b t : Nat → Nat} (pi : R i) (pb : R b) (pt : R t) :
    R (fun n => AnnotatedBoundScan.checkNat (i n) (b n) (t n)) :=
  (AnnotatedBoundScan.P.program.comp (pi.pair (pb.pair pt))).ofEq
    (fun _ => by simp only [AnnotatedBoundScan.P.value,Nat.unpair_pair])

def value (n : Nat) : Nat := check (decode n.unpair.1) (decodeRow n.unpair.2)

def contextProgram : R (fun n => AnnotatedContext.checkNat
    (decode n.unpair.1).context (decode n.unpair.1).shifted (decodeRow n.unpair.2).tag) :=
  (AnnotatedContextPR.P.program.comp
    ((tag Realizes.left).pair ((depth Realizes.left).pair (tag Realizes.right)))).ofEq
      (fun _ => by simp only [AnnotatedContextPR.P.value,Nat.unpair_pair,decode])

def bProgram : R (fun n => AnnotatedBoundScan.checkNat
    (decode n.unpair.1).b (decodeRow n.unpair.2).depth (decodeRow n.unpair.2).first) :=
  boundProgram (second Realizes.left) (depth Realizes.right) (first Realizes.right)

def iProgram : R (fun n => AnnotatedRenameScan.checkNat 1 (decode n.unpair.1).i 0
    (decode n.unpair.1).a (decode n.unpair.1).instI (decodeRow n.unpair.2).second) :=
  renameProgram (constant 1) (second (output Realizes.left)) Realizes.zero
    (first Realizes.left) (tag (output Realizes.left)) (second Realizes.right)

def jProgram : R (fun n => AnnotatedRenameScan.checkNat 1 (decode n.unpair.1).j 0
    (decode n.unpair.1).a (decode n.unpair.1).instJ (decodeRow n.unpair.2).input) :=
  renameProgram (constant 1) (input (output Realizes.left)) Realizes.zero
    (first Realizes.left) (depth (output Realizes.left)) (input Realizes.right)

def cProgram : R (fun n => AnnotatedRenameScan.checkNat 0 0 0
    (decode n.unpair.1).c (decode n.unpair.1).shiftC (decodeRow n.unpair.2).output) :=
  renameProgram Realizes.zero Realizes.zero Realizes.zero
    (input Realizes.left) (first (output Realizes.left)) (output Realizes.right)

def program : R value := by
  refine (mul contextProgram (mul bProgram (mul iProgram (mul jProgram cProgram)))).ofEq ?_
  intro n
  simp only [value,check]

end P

theorem program_input (r : Coordinates) (e : Row) :
    P.program.val.eval (Nat.pair (encode r) (rowCode e))=check r e := by
  rw [P.program.property]
  simp only [P.value,Nat.unpair_pair,decode_encode,decodeRow_rowCode]

theorem program_sound (n : Nat) (h : P.program.val.eval n=1) : Good (decode n.unpair.1) := by
  rw [P.program.property] at h
  exact check_sound _ _ h

theorem exists_program_iff (r : Coordinates) :
    (∃ evidence : Nat,P.program.val.eval (Nat.pair (encode r) evidence)=1) ↔ Good r := by
  constructor
  · rintro ⟨evidence,h⟩
    simpa only [Nat.unpair_pair,decode_encode] using program_sound _ h
  · rintro ⟨G,a,b,c,hr⟩
    obtain ⟨e,he⟩ := check_complete G a b c r.i r.j
    refine ⟨rowCode e,?_⟩
    rw [program_input,hr]
    exact he

theorem program_primrec : Nat.Primrec P.program.val.eval := P.program.val.primrec

def optimizedProgram : R P.value := P.program.optimize

theorem program_nodeCount : P.program.val.nodeCount=17371 := by decide
theorem optimizedProgram_nodeCount : optimizedProgram.val.nodeCount=15933 := by decide

end DiophantineConsistency.AnnotatedRuleCoordinates
