import DiophantineConsistency.MFNativeRadixDigits
import DiophantineConsistency.NativeCyclicConvolution
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Radix digit reconstruction and periodic finite words -/

namespace DiophantineConsistency.NativeRadixDigits

open NativeCyclicConvolution Jones1982
open scoped BigOperators

variable {n : ℕ} [NeZero n]

noncomputable def digitArray (r g : ℕ) (k : ZMod n) : ℕ := (digitsPad r g n).getD k.val 0

theorem digitArray_lt {r g : ℕ} (hr : 1 < r) (hg : g < r ^ n) (k : ZMod n) :
    digitArray r g k < r := by
  unfold digitArray
  rw [List.getD_eq_getElem _ _ (by rw [digitsPad_length hr hg]; exact k.val_lt)]
  exact digitsPad_lt hr (List.getElem_mem _)

theorem word_digitArray {r g : ℕ} (hr : 1 < r) (hg : g < r ^ n) :
    word r (digitArray (n := n) r g) = g := by
  rw [word_eq_ofDigits, ofDigits_ofFn]
  simp only [digitArray, finEquiv_val]
  rw [Fin.sum_univ_eq_sum_range (fun j => (digitsPad r g n).getD j 0 * r ^ j) n]
  have hlen := digitsPad_length hr hg
  have he := ofDigits_eq_sum_getD r (digitsPad r g n)
  rw [hlen] at he
  rw [← he, ofDigits_digitsPad]

theorem word_origin (r : ℕ) (a : ℕ) :
    word r (fun k : ZMod n => if k = 0 then a else 0) = a :=
  MF.NativeRadixDigits.word_origin (n := n) r a

/-- Every exponent is a fixed digit capacity. At the origin the mask
forbids even its low bit before the source's final increment. -/
def originMask (r : ℕ) (bits : ZMod n → ℕ) (k : ZMod n) : ℕ :=
  r - 2 ^ (if k = 0 then 0 else bits k)

theorem mask_capacity {v b d : ℕ} (hb : b ≤ v) (hd : d < 2 ^ v) :
    d &&& (2 ^ v - 2 ^ b) = 0 ↔ d < 2 ^ b := by
  rw [← τ_two_eq_zero_iff, τ_comm]
  exact (lemma_2_7 hb hd).symm

/-- This reconstruction supplies the assignment word and all digit bounds;
neither is an input. Only the literal mask-word binding remains external. -/
theorem decode_originMask {v C : ℕ} (hv : 1 ≤ v) (hC : 0 < C)
    (hClt : C < (2 ^ v) ^ n) (bits : ZMod n → ℕ)
    (hbits : ∀ k, bits k ≤ v) (hfirst : 1 ≤ bits 0)
    (hmask : (C - 1) &&& word (2 ^ v) (originMask (2 ^ v) bits) = 0) :
    ∃ c : ZMod n → ℕ, word (2 ^ v) c = C ∧ c 0 = 1 ∧
      ∀ k, c k < 2 ^ bits k := by
  have hr : 1 < 2 ^ v := Nat.one_lt_two_pow (by omega)
  have hg : C - 1 < (2 ^ v) ^ n := by omega
  let d := digitArray (n := n) (2 ^ v) (C - 1)
  have hd (k : ZMod n) : d k < 2 ^ v := digitArray_lt hr hg k
  have hm (k : ZMod n) : originMask (2 ^ v) bits k < 2 ^ v := by
    unfold originMask
    have hp : 0 < 2 ^ (if k = 0 then 0 else bits k) := by positivity
    have hb : (if k = 0 then 0 else bits k) ≤ v := by split_ifs; omega; exact hbits k
    have hle := Nat.pow_le_pow_right (n := 2) (by decide) hb
    omega
  have hmasks : ∀ k, d k &&& originMask (2 ^ v) bits k = 0 := by
    apply (mask_word_iff rfl d _ hd hm).mp
    change word (2 ^ v) (digitArray (2 ^ v) (C - 1)) &&& _ = 0
    rwa [word_digitArray hr hg]
  have hcapacity (k : ZMod n) : d k < 2 ^ (if k = 0 then 0 else bits k) := by
    apply (mask_capacity (by split_ifs; omega; exact hbits k) (hd k)).mp
    exact hmasks k
  have hd0 : d 0 = 0 := by have hh := hcapacity 0; simp only [ite_true, pow_zero] at hh; omega
  let c := fun k : ZMod n => d k + if k = 0 then 1 else 0
  refine ⟨c, ?_, ?_, ?_⟩
  · rw [show c = (fun k => d k + if k = 0 then 1 else 0) from rfl, word_add, word_origin]
    change word (2 ^ v) (digitArray (2 ^ v) (C - 1)) + 1 = C
    rw [word_digitArray hr hg, Nat.sub_add_cancel hC]
  · simp only [c, hd0, ite_true, zero_add]
  · intro k
    by_cases hk : k = 0
    · subst k
      simpa only [c, hd0, ite_true, zero_add] using
        (Nat.one_lt_two_pow (by omega : bits 0 ≠ 0))
    · simpa only [c, hk, if_false, add_zero] using hcapacity k

omit [NeZero n] in
theorem periodic_sum (r L N : ℕ) (hL : 0 < L) (a : Fin L → ℕ) :
    (∑ i : Fin (N * L), a ⟨i.val % L, Nat.mod_lt _ hL⟩ * r ^ i.val) =
      (∑ j : Fin L, a j * r ^ j.val) * (∑ k : Fin N, (r ^ L) ^ k.val) :=
  MF.NativeRadixDigits.periodic_sum r L N hL a

end DiophantineConsistency.NativeRadixDigits
