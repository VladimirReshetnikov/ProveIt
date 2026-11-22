import Arithmetic
import FiniteRamsey

/-! A verified bridge from ordered vertex lists to the bounded first-order census.
The decode/encode lemmas include the empty subset and rank zero. -/
namespace Ramsey.MaskBridge

open Arithmetic FiniteRamsey

/-- Enumerate the set bits below n in increasing order. -/
def decode (a : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => if a.testBit n then decode a n ++ [n] else decode a n

theorem mask_append (xs ys : List Nat) : mask (xs ++ ys) = mask xs + mask ys := by
  induction xs with
  | nil => simp [mask]
  | cons x xs ih => simp [mask, ih, Nat.add_assoc]

private theorem mod_double (a k : Nat) (hk : 0 < k) :
    a % (k * 2) = a % k + k * (a / k % 2) := by
  let z := a / k
  let v := a % k + k * (z % 2)
  have hv : v < k * 2 := by
    have hr := Nat.mod_lt a hk
    rcases Nat.mod_two_eq_zero_or_one z with hz | hz <;> simp [v, hz] <;> omega
  have split : a = v + (k * 2) * (z / 2) := calc
    a = a % k + k * z := (Nat.mod_add_div a k).symm
    _ = a % k + k * (z % 2 + 2 * (z / 2)) :=
      congrArg (fun j => a % k + k * j) (Nat.mod_add_div z 2).symm
    _ = v + (k * 2) * (z / 2) := by simp [v, Nat.mul_add, Nat.add_assoc, Nat.mul_assoc]
  calc
    a % (k * 2) = (v + (k * 2) * (z / 2)) % (k * 2) := congrArg (· % (k * 2)) split
    _ = v := (Nat.add_mul_mod_self_left ..).trans (Nat.mod_eq_of_lt hv)

theorem mask_decode (a n : Nat) : mask (decode a n) = a % (2 ^ n) := by
  induction n with
  | zero => simp [decode, mask, Nat.mod_one]
  | succ n ih =>
    rw [Nat.pow_succ, mod_double a _ (Nat.pow_pos (by decide))]
    rcases Nat.mod_two_eq_zero_or_one (a / 2^n) with h | h <;>
      simp [decode, Nat.testBit_to_div_mod, h, ih, mask_append, mask]

theorem length_decode (a n : Nat) : (decode a n).length = card a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases Nat.mod_two_eq_zero_or_one (a / 2^n) with h | h <;>
      simp [decode, card, digit, Nat.testBit_to_div_mod, h, ih]

theorem decode_congr {a b n : Nat} (bits : ∀ i < n, a.testBit i = b.testBit i) :
    decode a n = decode b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [decode, decode, bits n (Nat.lt_succ_self _), ih (fun i hi => bits i (Nat.lt_succ_of_lt hi))]

theorem decode_mask {n : Nat} {xs : List Nat} (h : xs.Sublist (List.range n)) :
    mask xs < 2^n ∧ decode (mask xs) n = xs := by
  induction n generalizing xs with
  | zero =>
    have he : xs = [] := List.sublist_nil.mp h
    subst xs
    decide
  | succ n ih =>
    rw [List.range_succ, List.sublist_append_iff] at h
    obtain ⟨ys, endPart, rfl, hy, hh⟩ := h
    obtain ⟨small, roundtrip⟩ := ih hy
    have high : (mask ys).testBit n = false := Nat.testBit_lt_two_pow small
    rcases List.sublist_cons_iff.mp hh with hzero | ⟨zs, rfl, hz⟩
    · have hnil := List.sublist_nil.mp hzero
      subst endPart
      simp only [List.append_nil]
      exact ⟨by rw [Nat.pow_succ]; omega, by simp [decode, high, roundtrip]⟩
    · have hnil := List.sublist_nil.mp hz
      subst zs
      have eq : mask (ys ++ [n]) = 2^n + mask ys := by
        simp [mask_append, mask, Nat.add_comm]
      have low : decode (2^n + mask ys) n = decode (mask ys) n :=
        decode_congr (fun i hi => Nat.testBit_two_pow_add_gt hi _)
      rw [eq]
      exact ⟨by rw [Nat.pow_succ]; omega,
        by simp [decode, Nat.testBit_two_pow_add_eq, high, low, roundtrip]⟩

theorem decode_mono {a b n : Nat} (bits : ∀ i < n, a.testBit i = true → b.testBit i = true) :
    (decode a n).Sublist (decode b n) := by
  induction n with
  | zero => exact .slnil
  | succ n ih =>
    have low := ih (fun i hi => bits i (Nat.lt_succ_of_lt hi))
    cases ha : a.testBit n with
    | false =>
      cases hb : b.testBit n with
      | false => simpa [decode, ha, hb] using low
      | true => simpa [decode, ha, hb] using low.trans (List.sublist_append_left _ [n])
    | true =>
      have hb := bits n (Nat.lt_succ_self n) ha
      simpa [decode, ha, hb] using low.append_right [n]

theorem inside_sublist {a b n : Nat} (h : inside n a b = true) :
    (decode a n).Sublist (decode b n) := by
  apply decode_mono
  intro i hi ha
  have hab : digit 2 a i ≤ digit 2 b i := of_decide_eq_true ((allBelow_spec _ _).mp h i hi)
  have ha' : a / 2^i % 2 = 1 := of_decide_eq_true (Nat.testBit_to_div_mod ▸ ha)
  rw [Nat.testBit_to_div_mod]
  apply decide_eq_true
  change a / 2^i % 2 ≤ b / 2^i % 2 at hab
  have hb := Nat.mod_lt (b / 2^i) (by decide : 0 < 2)
  omega

/-- The ordinary finite theorem implies that the single natural-number census
bit is 1 at every sufficient size. -/
theorem census_true (q : Nat) (hq : 0 < q) (t r n : Nat)
    (size : bound q t r ≤ n) : census q t r n = true := by
  apply (census_spec ..).mpr
  intro C _ validC
  obtain ⟨ys, d, hys, hlen, mono⟩ := rangeRamsey hq t r n (tableColor q hq C) size
  obtain ⟨hmask, hdecode⟩ := decode_mask hys
  let h := mask ys
  let w := q * h + d.val
  have wdiv : w / q = h := by simp [w, Nat.mul_add_div hq, Nat.div_eq_of_lt d.isLt]
  have wmod : w % q = d.val := by simp [w, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt d.isLt]
  have wbound : w < q * 2^n := calc
    w < q * h + q := Nat.add_lt_add_left d.isLt _
    _ = q * (h+1) := (Nat.mul_succ ..).symm
    _ ≤ q * 2^n := Nat.mul_le_mul_left _ hmask
  have hc : card h n = t := by
    rw [← length_decode, (show decode h n = ys from hdecode), hlen]
  refine ⟨w, wbound, ?_⟩
  simp only [check, wdiv, wmod, Bool.and_eq_true]
  refine ⟨decide_eq_true ⟨hmask, d.isLt, hc⟩, (allBelow_spec ..).mpr ?_⟩
  intro a ha
  cases hinside : inside n a h with
  | false => simp
  | true =>
    by_cases harity : card a n = r
    · have hsub : (decode a n).Sublist ys := hdecode ▸ inside_sublist hinside
      have hcolor := congrArg Fin.val (mono (decode a n) hsub ((length_decode ..).trans harity))
      have hm : mask (decode a n) = a := (mask_decode ..).trans (Nat.mod_eq_of_lt ha)
      have hv : digit (base q) C a < q := of_decide_eq_true ((allBelow_spec ..).mp validC a ha)
      change (digit (base q) C (mask (decode a n))) % q = d.val at hcolor
      rw [hm, Nat.mod_eq_of_lt hv] at hcolor
      simp [harity, hcolor]
    · simp [harity]

/-- The numerical selector returns the least accepted certificate for a valid input. -/
theorem winner_correct (q : Nat) (hq : 0 < q) (t r n C : Nat)
    (size : bound q t r ≤ n) (hC : C < tableLimit q n) (good : valid q n C = true) :
    win q t r n C < q * 2^n ∧ check q t r n C (win q t r n C) = true ∧
      ∀ j < win q t r n C, check q t r n C j = false := by
  obtain ⟨w, hw, accepted⟩ := (census_spec ..).mp (census_true q hq t r n size) C hC good
  have found := firstBelow_found hw accepted
  exact ⟨found.1, found.2, (firstBelow_spec (check q t r n C) (q * 2^n)).2.2⟩

/-- Least vertex count satisfying the finite Ramsey arrow. The sufficient bound
is included in the bounded search by taking a successor. -/
def exactRamsey (q t r : Nat) : Nat :=
  firstBelow (census q t r) (bound q t r + 1)

theorem exactRamsey_spec (q : Nat) (hq : 0 < q) (t r : Nat) :
    exactRamsey q t r ≤ bound q t r ∧
    census q t r (exactRamsey q t r) = true ∧
    ∀ n < exactRamsey q t r, census q t r n = false := by
  have hit := firstBelow_found (Nat.lt_succ_self (bound q t r))
    (census_true q hq t r (bound q t r) (Nat.le_refl _))
  exact ⟨Nat.le_of_lt_succ hit.1, hit.2,
    (firstBelow_spec (census q t r) (bound q t r + 1)).2.2⟩

private theorem failedFold (p : Nat → Bool) (n : Nat) (h : allBelow p n = false) :
    ∃ j < n, p j = false := by
  induction n with
  | zero => cases h
  | succ n ih =>
    cases prev : allBelow p n with
    | true => exact ⟨n, Nat.lt_succ_self n, by simpa [allBelow, prev] using h⟩
    | false =>
      obtain ⟨j, hj, hjb⟩ := ih prev
      exact ⟨j, Nat.lt_succ_of_lt hj, hjb⟩

/-- Least valid table with no accepted certificate, when one exists. -/
def counterColor (q t r n : Nat) : Nat :=
  firstBelow (fun C => valid q n C && !(decide (win q t r n C < q * 2^n)))
    (tableLimit q n)

theorem counterColor_spec (q : Nat) (hq : 0 < q) (t r n : Nat)
    (small : n < exactRamsey q t r) :
    counterColor q t r n < tableLimit q n ∧ valid q n (counterColor q t r n) = true ∧
    ∀ w < q * 2^n, check q t r n (counterColor q t r n) w = false := by
  have failed := (exactRamsey_spec q hq t r).2.2 n small
  obtain ⟨C, hC, bad⟩ := failedFold _ _ failed
  let p := fun C => valid q n C && !(decide (win q t r n C < q * 2^n))
  have hp : p C = true := by
    change (!valid q n C || decide (win q t r n C < q * 2^n)) = false at bad
    cases hv : valid q n C <;> cases hw : decide (win q t r n C < q * 2^n) <;>
      simp [p, hv, hw] at *
  obtain ⟨lt, hit⟩ := firstBelow_found hC hp
  let D := counterColor q t r n
  have both : valid q n D = true ∧ (!(decide (win q t r n D < q * 2^n))) = true :=
    by simpa only [p, Bool.and_eq_true] using hit
  have miss : ¬win q t r n D < q * 2^n := by simpa using both.2
  refine ⟨lt, both.1, ?_⟩
  intro w hw
  exact (firstBelow_spec (check q t r n D) (q * 2^n)).2.2 w
    (Nat.lt_of_lt_of_le hw (Nat.le_of_not_gt miss))

end Ramsey.MaskBridge
