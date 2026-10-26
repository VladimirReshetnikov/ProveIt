import DiophantineConsistency.AnnotatedSchemaMaps

/-! # Guarded arithmetic checking of complete backward-parent lists -/
namespace DiophantineConsistency.AnnotatedParents
open ScalarPRCode DirectScalar AnnotatedCodeArithmetic AnnotatedProofChecker
set_option maxRecDepth 16000
set_option maxHeartbeats 1200000
attribute [local irreducible] Nat.unpair

/-- The fuel is fixed compiler data. Both list spines must terminate together;
each positive cell checks a guarded reference, including the successor marker. -/
def check : Nat → Nat → Nat → Nat → Nat
  | 0,_,expected,parents => if expected=0 then if parents=0 then 1 else 0 else 0
  | fuel+1,history,expected,parents =>
    if expected=0 then if parents=0 then 1 else 0 else
      if parents=0 then 0 else
        referenceCheck (Nat.pair history (Nat.pair parents.pred.unpair.1 expected.pred.unpair.1)) *
          check fuel history expected.pred.unpair.2 parents.pred.unpair.2

theorem check_nil (fuel history parents : Nat) : check fuel history 0 parents=1 ↔ parents=0 := by
  cases fuel <;> simp [check]

theorem check_cons (fuel history expected parent : Nat) (es ps : List Nat) :
    check (fuel+1) history (listCode (expected::es)) (listCode (parent::ps))=
      referenceCheck (Nat.pair history (Nat.pair parent expected)) *
        check fuel history (listCode es) (listCode ps) := by
  simp [check,listCode]

theorem check_lists (fuel : Nat) (history expected parents : List Nat)
    (hf : expected.length≤fuel) :
    check fuel (listCode history) (listCode expected) (listCode parents)=1 ↔
      parents.map (fun i => history[i]?)=expected.map some := by
  induction expected generalizing fuel parents with
  | nil =>
    cases parents <;> simp [check_nil,listCode]
  | cons e es ih =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      cases parents with
      | nil => simp [check,listCode]
      | cons p ps =>
        rw [check_cons,AnnotatedSchemaMaps.mul_eq_one_nat,referenceCheck_listCode,
          ih fuel ps (by simpa only [List.length_cons,Nat.succ_le_succ_iff] using hf)]
        simp only [List.map_cons,List.cons.injEq]

/-- A fixed bounded checker reconstructs the complete parent spine directly;
no recursive formula parser or unbounded list decoder is assumed. -/
theorem check_raw_iff (fuel : Nat) (history expected : List Nat) (parents : Nat)
    (hf : expected.length≤fuel) :
    check fuel (listCode history) (listCode expected) parents=1 ↔
      ∃ indices : List Nat,parents=listCode indices ∧
        indices.map (fun i => history[i]?)=expected.map some := by
  constructor
  · intro h
    obtain ⟨rows, hr⟩ :=
      AnnotatedRenameScan.decodeTable_total parents parents (Nat.le_refl _)
    have he : AnnotatedCodeArithmetic.listCode (rows.map AnnotatedRename.rowCode) = parents :=
      AnnotatedRenameScan.tableCode_of_decode hr
    refine ⟨rows.map AnnotatedRename.rowCode, he.symm, ?_⟩
    exact (check_lists fuel history expected _ hf).mp (by simpa only [he] using h)
  · rintro ⟨indices, rfl, h⟩
    exact (check_lists fuel history expected indices hf).mpr h

attribute [local irreducible] check

theorem lookup_code_maps_iff (history expected : List Judgment) (parents : List Nat) :
    parents.map (fun i => (history.map judgmentCode)[i]?)=(expected.map judgmentCode).map some ↔
      parents.map (fun i => history[i]?)=expected.map some := by
  have ho : Function.Injective (Option.map judgmentCode) :=
    Option.map_injective judgmentCode_injective
  have hl : parents.map (fun i => (history.map judgmentCode)[i]?)=
      (parents.map (fun i => history[i]?)).map (Option.map judgmentCode) := by
    simp only [List.getElem?_map,List.map_map,Function.comp_def]
  have hr : (expected.map judgmentCode).map some=
      (expected.map some).map (Option.map judgmentCode) := by
    simp only [List.map_map,Option.map_some,Function.comp_def]
  rw [hl,hr,(List.map_injective_iff.mpr ho).eq_iff]

theorem check_judgments (fuel : Nat) (history expected : List Judgment) (parents : List Nat)
    (hf : expected.length≤fuel) :
    check fuel (listCode (history.map judgmentCode)) (listCode (expected.map judgmentCode))
      (listCode parents)=1 ↔ parents.map (fun i => history[i]?)=expected.map some := by
  rw [check_lists fuel _ _ parents (by simpa only [List.length_map] using hf),lookup_code_maps_iff]

theorem check_judgments_raw (fuel : Nat) (history expected : List Judgment) (parents : Nat)
    (hf : expected.length≤fuel) :
    check fuel (listCode (history.map judgmentCode)) (listCode (expected.map judgmentCode)) parents=1 ↔
      ∃ indices : List Nat,parents=listCode indices ∧
        indices.map (fun i => history[i]?)=expected.map some := by
  rw [check_raw_iff fuel _ _ parents (by simpa only [List.length_map] using hf)]
  simp only [lookup_code_maps_iff]

namespace P
open AnnotatedRenameLocal.Program (left right)

def value (fuel n : Nat) : Nat := check fuel n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2

def program : (fuel : Nat) → R (value fuel)
  | 0 => (ifZero (left Realizes.right)
      (ifZero (right Realizes.right) (constant 1) Realizes.zero) Realizes.zero).ofEq
        (fun _ => by simp only [value,check])
  | fuel+1 => by
    let history := Realizes.left
    let expected := left Realizes.right
    let parents := right Realizes.right
    let ep := pred expected
    let pp := pred parents
    let referenced := AnnotatedCodeArithmetic.referenceProgram.comp
      (history.pair ((left pp).pair (left ep)))
    let remaining := (program fuel).comp (history.pair ((right ep).pair (right pp)))
    let body := mul referenced remaining
    let p := ifZero expected (ifZero parents (constant 1) Realizes.zero)
      (ifZero parents Realizes.zero body)
    refine p.ofEq ?_
    intro n
    simp only [value,check,Nat.unpair_pair]

end P

theorem program_input (fuel history expected parents : Nat) :
    (P.program fuel).val.eval (Nat.pair history (Nat.pair expected parents))=
      check fuel history expected parents := by
  rw [(P.program fuel).property]
  simp only [P.value,Nat.unpair_pair]

theorem program_primrec (fuel : Nat) : Nat.Primrec (P.program fuel).val.eval := (P.program fuel).val.primrec

end DiophantineConsistency.AnnotatedParents
