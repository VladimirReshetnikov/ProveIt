module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.EndpointInternalCarryNatBridge
public import M6PA.Model.PAInternalTraceAppend
public import M6PA.Scheduler.ActualTableCoding
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualWordCoding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open InternalTrace.CarryCode

/-- The already accepted physical-file HFS encoder is reused for command-atom
vectors. Its entries are different data, not a new pairing convention. -/
noncomputable abbrev encode (xs : List Nat) : Nat := fileCode xs

@[simp] theorem encode_nil : encode []=0 := rfl
@[simp] theorem encode_cons (x : Nat) (xs : List Nat) : encode (x::xs)=x ∷ encode xs := rfl

theorem encode_prefix (xs : List Nat) :
    encode xs = HaltingFormula.encodePrefix xs.length (fun i => xs.getD i 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [encode_cons,HaltingFormula.encodePrefix,List.length_cons,List.getD_cons_zero,List.getD_cons_succ] using congrArg (fun ys : Nat => x ∷ ys) ih

@[simp] theorem len_encode (xs : List Nat) : len (encode xs)=xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem nth_encode (xs : List Nat) (i : Nat) : nth (encode xs) i=xs.getD i 0 := by
  by_cases hi : i<xs.length
  · rw [encode_prefix]
    exact HaltingFormula.nth_encodePrefix _ _ _ hi
  · have hz : nth (encode xs) i=0 := nth_lt_len (by
      change len (encode xs)=i ∨ len (encode xs)<i
      rw [len_encode]
      omega)
    rw [hz,List.getD_eq_default xs 0 (Nat.le_of_not_gt hi)]

theorem encode_append (xs ys : List Nat) :
    encode (xs++ys)=InternalTrace.HFSAppend.append (encode xs) (encode ys) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem encode_concat (xs : List Nat) (x : Nat) :
    encode (xs++[x])=concat (encode xs) x := by
  induction xs with
  | nil => simp
  | cons y ys ih => simp [ih]

/-- A fuel row is an HFS vector whose entries are themselves HFS words. -/
noncomputable def encodeRows (rows : List (List Nat)) : Nat := encode (rows.map encode)

theorem nth_encodeRows (rows : List (List Nat)) (i : Nat) :
    nth (encodeRows rows) i=encode (rows.getD i []) := by
  rw [encodeRows,nth_encode]
  exact List.getD_map rows [] encode

#print axioms encode_prefix
#print axioms nth_encode
#print axioms encode_append
#print axioms nth_encodeRows
end M6.PA.ActualWordCoding

