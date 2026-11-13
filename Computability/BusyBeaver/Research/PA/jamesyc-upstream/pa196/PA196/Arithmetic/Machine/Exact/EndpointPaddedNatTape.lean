module
/- Exact PA196 zipper and arithmetic-tape correspondence. -/
public import PA196.Arithmetic.Machine.Exact.PANatTape
public import PA196.Arithmetic.Machine.Exact.PANativeTable
public import PA196.Arithmetic.Machine.Exact.EndpointPaddedBridge
@[expose] public section

/-! Exact connection from the native finite-list zipper interpreter to the
two-natural stack semantics and hence to the literal functional-tape machine.
Trailing zero padding is erased by the encoding, as required by `Zip.trim`.
-/

namespace PA196.Arithmetic.Machine.Exact.PA.PaddedNatTape
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

theorem step_commutes (c : Zip.Conf) :
    (Zip.step PaddedBridge.machine c).map encode = NatTape.step (encode c) := by
  cases hi : NativeTable.inverse c.q with
  | none => simp [Zip.step, PaddedBridge.machine, NatTape.step, encode, hi]
  | some q =>
    cases ha : row q (c.r.headD false) with
    | mk w d next =>
      cases d <;>
        simp only [Zip.step, PaddedBridge.machine, NatTape.step, encode, hi, bits_head, ha,
          advance, Zip.zc, Zip.zl, Option.map_some, bits_trim, bits_cons, bits_tail,
          inverse_labelControl, Bool.false_eq_true, ite_false, ite_true]

theorem run_commutes (n : Nat) (c : Zip.Conf) :
    (Zip.run PaddedBridge.machine n c).map encode = NatTape.run n (encode c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    have h := step_commutes c
    cases hs : Zip.step PaddedBridge.machine c with
    | none => simp [hs] at h; simp [Zip.run, hs, NatTape.run, ← h]
    | some c' =>
      simp [hs] at h
      simp [Zip.run, hs, NatTape.run, ← h, ← ih]

theorem terminal_iff (c : Zip.Conf) :
    Zip.step PaddedBridge.machine c = none ↔ (encode c).control = halt := by
  cases hi : NativeTable.inverse c.q with
  | none => simp [Zip.step, PaddedBridge.machine, encode, hi, halt]
  | some q =>
    cases ha : row q (c.r.headD false) with
    | mk w d next => cases d <;> simp only [Zip.step, PaddedBridge.machine, encode, hi, ha, halt, Option.map_some,
        reduceCtorEq]

theorem halts_iff (c : Zip.Conf) :
    Zip.Halts PaddedBridge.machine c ↔ NatTape.Halts (encode c) := by
  constructor
  · rintro ⟨c', ⟨n, hn⟩, ht⟩
    refine ⟨n, encode c', ?_, (terminal_iff c').mp ht⟩
    rw [← run_commutes, hn]
    rfl
  · rintro ⟨n, s', hn, ht⟩
    have hmap : (Zip.run PaddedBridge.machine n c).map encode = some s' :=
      (run_commutes n c).trans hn
    cases hc : Zip.run PaddedBridge.machine n c with
    | none => simp [hc] at hmap
    | some c' =>
      have he : encode c' = s' := by simpa [hc] using hmap
      exact ⟨c', ⟨n, hc⟩, (terminal_iff c').mpr (he ▸ ht)⟩

def nativeBlank : Zip.Conf := Zip.zc 0 [] []

theorem encode_nativeBlank : encode nativeBlank = NatTape.blank := by decide

theorem native_blank_halts_iff :
    Zip.Halts PaddedBridge.machine nativeBlank ↔ PA196.Arithmetic.Machine.Exact.Halts PA196.Arithmetic.Machine.Exact.blank := by
  rw [halts_iff, encode_nativeBlank]
  exact NatTape.blank_halts_iff

#print axioms step_commutes
#print axioms run_commutes
#print axioms terminal_iff
#print axioms native_blank_halts_iff

end PA196.Arithmetic.Machine.Exact.PA.PaddedNatTape

