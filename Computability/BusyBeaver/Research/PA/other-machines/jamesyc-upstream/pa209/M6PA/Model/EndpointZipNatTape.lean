module
public import M6PA.Model.PANatTape
public import M6PA.Model.PANativeTable
@[expose] public section

/-! Exact connection from the native finite-list zipper interpreter to the
two-natural stack semantics and hence to the literal functional-tape machine.
Trailing zero padding is erased by the encoding, as required by `Zip.trim`.
-/

namespace M6.Arithmetic.PA.ZipNatTape
open M6

open NatTape

def bits : List Bool → Nat
  | [] => 0
  | b :: bs => push b (bits bs)

@[simp] theorem bits_nil : bits [] = 0 := rfl
@[simp] theorem bits_cons (b : Bool) (bs : List Bool) : bits (b :: bs) = push b (bits bs) := rfl

@[simp] theorem bits_trim (bs : List Bool) : bits (Zip.trim bs) = bits bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [Zip.trim_cons]
    split
    · rename_i h
      have hb : b = false := h.1
      have hz : bits bs = 0 := by rw [← ih, h.2]; rfl
      simp [hb, hz, push]
    · simp [ih]

@[simp] theorem bits_head (bs : List Bool) : (bits bs).testBit 0 = bs.headD false := by
  cases bs with
  | nil => rfl
  | cons b bs => exact push_head b (bits bs)

@[simp] theorem bits_tail (bs : List Bool) : bits bs.tail = bits bs / 2 := by
  cases bs with
  | nil => rfl
  | cons b bs => simp

@[simp] theorem inverse_labelControl (q : Control) :
    NativeTable.inverse (NativeTable.labelControl q) = q := by
  cases q with
  | none => decide
  | some q => exact NativeTable.inverse_label q

def encode (c : Zip.Conf) : NatTape.Configuration :=
  ⟨NativeTable.inverse c.q, bits c.l, bits c.r⟩

theorem step_forward {c d : Zip.Conf} (h : Zip.step NativeTable.machine c=some d) :
    NatTape.step (encode c)=some (encode d) := by
  cases hm : NativeTable.machine c.q (c.r.headD false) with
  | none => simp only [Zip.step,hm,reduceCtorEq] at h
  | some a =>
    rcases a with ⟨w,dir,q'⟩
    obtain ⟨q,hi,hr⟩ := NativeTable.row_of_native hm
    cases dir <;>
      simp only [Zip.step,hm,Option.some.injEq] at h <;> subst d <;>
      simp only [encode,NatTape.step,hi,bits_head,hr,Option.map_some,advance,
        Zip.zc,Zip.zl,bits_trim,bits_cons,bits_tail,Bool.false_eq_true,ite_false,ite_true]

theorem run_forward (n : Nat) (c d : Zip.Conf)
    (h : Zip.run NativeTable.machine n c=some d) :
    NatTape.run n (encode c)=some (encode d) := by
  induction n generalizing c with
  | zero =>
    simp only [Zip.run,Option.some.injEq] at h
    subst d
    rfl
  | succ n ih =>
    cases hs : Zip.step NativeTable.machine c with
    | none => simp [Zip.run,hs] at h
    | some c' =>
      have ht : Zip.run NativeTable.machine n c'=some d := by simpa only [Zip.run,hs] using h
      simpa only [NatTape.run,step_forward hs,Option.bind_some] using ih c' ht
#print axioms run_forward
end M6.Arithmetic.PA.ZipNatTape
