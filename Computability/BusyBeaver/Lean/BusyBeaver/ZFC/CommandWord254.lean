import BusyBeaver.ZFC.EnumStackBarrier254

/-!
A total shifted code for actual Enum254 command lists. Empty word0 is distinct
from the genuine raw candidate0=MP0, whose shifted nonempty word code is1.
This supplies finite numeric data operations; no internal arithmetic or
compiler execution contract is inferred here.
-/
namespace SetTheory.BusyBeaver.ZFC.CommandWord254
open Code254 Enum254 EnumStackBarrier254
attribute [local irreducible] Code254.P
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Every nonempty word is its actual Enum254 candidate code plus one. -/
def encode : List Cmd → Nat
  | [] => 0
  | c :: cs => pack c (encode cs) + 1

theorem encode_cons (c : Cmd) (cs : List Cmd) : encode (c :: cs) = encL c cs + 1 := by
  induction cs generalizing c with
  | nil => rfl
  | cons d ds ih =>
    change pack c (encode (d :: ds)) + 1 = pack c (encL d ds + 1) + 1
    rw [ih d]

/-- Total inverse; every natural is a shifted finite command word. -/
def decode : Nat → List Cmd
  | 0 => []
  | n + 1 => (EnumStackBarrier254.decode n).1 :: (EnumStackBarrier254.decode n).2

@[simp] theorem encode_decode (n : Nat) : encode (decode n) = n := by
  cases n with
  | zero => rfl
  | succ n => rw [decode, encode_cons, encL_decode]

@[simp] theorem decode_encode (cs : List Cmd) : decode (encode cs) = cs := by
  cases cs with
  | nil => rfl
  | cons c cs => rw [encode_cons, decode, decode_encL]

theorem encode_injective : Function.Injective encode := by
  intro xs ys h
  have := congrArg decode h
  simpa only [decode_encode] using this

@[simp] theorem encode_eq_zero (cs : List Cmd) : encode cs = 0 ↔ cs = [] := by
  cases cs <;> simp [encode]

/-- The rest pointer of the actual command decoded from a raw candidate. -/
def tail (z : Nat) : Nat := (unpack z).2

/-- Replace only that rest pointer, preserving the exact actual command. -/
def replaceRest (z rest : Nat) : Nat := pack (unpack z).1 rest

theorem tail_le (z : Nat) : tail z ≤ z := unpack_rest_le z

@[simp] theorem tail_pack (c : Cmd) (rest : Nat) : tail (pack c rest) = rest := by
  simp [tail, unpack_pack]

@[simp] theorem replaceRest_pack (c : Cmd) (old rest : Nat) :
    replaceRest (pack c old) rest = pack c rest := by simp [replaceRest, unpack_pack]

theorem replaceRest_self (z : Nat) : replaceRest z (tail z) = z := pack_unpack z

/-- Numeric append on EVERY pair of word codes, not only quoted examples. -/
def append (left right : Nat) : Nat :=
  if left = 0 then right
  else replaceRest (left - 1) (append (tail (left - 1)) right) + 1
termination_by left
decreasing_by
  have := tail_le (left - 1)
  omega

@[simp] theorem append_zero (right : Nat) : append 0 right = right := by rw [append, if_pos rfl]

theorem append_succ (z right : Nat) :
    append (z + 1) right = replaceRest z (append (tail z) right) + 1 := by
  rw [append, if_neg (by omega)]
  simp only [Nat.add_sub_cancel]

theorem append_encode (xs ys : List Cmd) :
    append (encode xs) (encode ys) = encode (xs ++ ys) := by
  induction xs with
  | nil => exact append_zero _
  | cons c cs ih =>
    rw [show encode (c :: cs) = pack c (encode cs) + 1 from rfl, append_succ]
    rw [tail_pack, ih, replaceRest_pack]
    rfl

/-- Total all-input adapter, using the exact total decoding above. -/
theorem append_decode (left right : Nat) :
    append left right = encode (decode left ++ decode right) := by
  simpa only [encode_decode] using append_encode (decode left) (decode right)

@[simp] theorem append_right_zero (left : Nat) : append left 0 = left := by
  rw [append_decode]
  change encode (decode left ++ []) = left
  simp only [List.append_nil, encode_decode]

theorem append_assoc (a b c : Nat) : append (append a b) c = append a (append b c) := by
  rw [append_decode a b, append_decode b c, append_decode, append_decode]
  simp only [decode_encode, List.append_assoc]

/-- These two constants must stay distinct. -/
theorem raw_zero_is_nonempty : encode [.mp 0] = 1 := by
  simp [encode, pack, P, Cantor.toNat, Cantor.tri]

theorem word_zero_is_empty : decode 0 = [] := rfl

/-- Explicit numeric field formulas for later arithmetic representation. -/
def tailFormula (z : Nat) : Nat :=
  if (unP z).1 < 3 then (unP (unP z).2).2
  else (unP (unP (unP (unP z).2).2).2).2

def replaceRestFormula (z rest : Nat) : Nat :=
  let op := (unP z).1
  let p := (unP z).2
  let x := (unP p).1
  let r := (unP p).2
  if op < 3 then P op (P x rest)
  else P op (P x (P (unP r).1 (P (unP (unP r).2).1 rest)))

theorem tail_formula (z : Nat) : tail z = tailFormula z := by
  unfold tail tailFormula unpack
  dsimp only
  split <;> simp_all <;> omega

theorem replaceRest_formula (z rest : Nat) : replaceRest z rest = replaceRestFormula z rest := by
  unfold replaceRest replaceRestFormula unpack
  dsimp only
  split <;> simp_all [pack] <;> omega

@[simp] theorem tail_replaceRest (z rest : Nat) : tail (replaceRest z rest) = rest := by
  unfold replaceRest
  exact tail_pack _ _

theorem replaceRest_replaceRest (z old rest : Nat) :
    replaceRest (replaceRest z old) rest = replaceRest z rest := by
  unfold replaceRest
  simp only [unpack_pack]


end SetTheory.BusyBeaver.ZFC.CommandWord254
