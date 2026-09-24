import Diophantine.Paper1982.Carries

/-!
# Jones 1982, Lemma 2.9: transferring digits from base `z` to base `B`

> **Lemma 2.9.** Let `0 ≤ n ≤ m ≤ k` be integers, `z ≥ 2`, `z pow 2`, `B pow 2`, and
> `2 z^(m+1) ≤ B`.  Suppose `Y ≥ 0` is an integer and `y = Σ_{i=0}^n yᵢ zⁱ` (`0 ≤ yᵢ < z`).
> Then in order that `Y = Σ_{i=0}^n yᵢ Bⁱ`, it is necessary and sufficient that
> (i) `Y ≡ y (mod B − z)`, (ii) `Y < z Bᵐ`, (iii) `τ₂(Y, Σ_{i=0}^{k-1} (B − z) Bⁱ) = 0`.

The digits `yᵢ` are given as a list `ys` (with `y = ofDigits z ys`, the number with these
digits in base `z`), of length at most `n + 1`.  The mask of (iii) is `mask29 B z k`.
-/

namespace Jones1982

open Nat Finset

/-- The mask `Σ_{i<k} (B − z) Bⁱ` of Lemma 2.9 (iii). -/
def mask29 (B z k : ℕ) : ℕ := ofDigits B (List.replicate k (B - z))

theorem mask29_zero (B z : ℕ) : mask29 B z 0 = 0 := rfl

theorem mask29_succ (B z k : ℕ) : mask29 B z (k + 1) = (B - z) + mask29 B z k * B := by
  unfold mask29; rw [List.replicate_succ, ofDigits_cons, mul_comm]

/-- `ofDigits B (replicate k d) = d Σ_{i<k} Bⁱ`. -/
theorem ofDigits_replicate (B d k : ℕ) :
    ofDigits B (List.replicate k d) = d * ∑ i ∈ range k, B ^ i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, ofDigits_cons, ih, Finset.sum_range_succ']
    simp only [pow_succ, pow_zero]
    rw [← Finset.sum_mul]
    ring

theorem mask29_eq (B z k : ℕ) : mask29 B z k = (B - z) * ∑ i ∈ range k, B ^ i :=
  ofDigits_replicate B (B - z) k

/-- The `j`-th base-`B` digit of `ofDigits B L` is the `j`-th entry of `L` (or `0`). -/
theorem ofDigits_div_pow_mod {B : ℕ} (hB : 0 < B) {L : List ℕ} (hL : ∀ x ∈ L, x < B) (j : ℕ) :
    ofDigits B L / B ^ j % B = L.getD j 0 := by
  rw [ofDigits_div_pow_eq_ofDigits_drop j hB L hL]
  rcases Nat.lt_or_ge j L.length with hj | hj
  · rw [List.drop_eq_getElem_cons hj, ofDigits_cons, List.getD_eq_getElem _ _ hj,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hL _ (List.getElem_mem hj))]
  · rw [List.drop_of_length_le hj, List.getD_eq_default _ _ hj]; simp [ofDigits]

/-- A number with digits `< z ≤ B` in base `B` (list of length `l ≥ 1`) is `< z B^(l−1)`. -/
theorem ofDigits_lt_mul_pow {B z : ℕ} (hB : 1 < B) (hzB : z ≤ B) :
    ∀ (L : List ℕ), (∀ x ∈ L, x < z) → L ≠ [] → ofDigits B L < z * B ^ (L.length - 1)
  | [], _, h => (h rfl).elim
  | [x], hL, _ => by simpa [ofDigits] using hL x (by simp)
  | x :: y :: t, hL, _ => by
    have ih := ofDigits_lt_mul_pow hB hzB (y :: t) (fun w hw => hL w (by simp [hw])) (by simp)
    rw [ofDigits_cons]
    have hx : x < B := lt_of_lt_of_le (hL x (by simp)) hzB
    have hl : (y :: t).length - 1 + 1 = (x :: y :: t).length - 1 := by simp
    have h1 : B * (ofDigits B (y :: t) + 1) ≤ B * (z * B ^ ((y :: t).length - 1)) :=
      Nat.mul_le_mul_left _ ih
    have h2 : B * (z * B ^ ((y :: t).length - 1)) = z * B ^ ((x :: y :: t).length - 1) := by
      rw [← hl, pow_succ]; ring
    rw [h2] at h1
    have h3 : B * (ofDigits B (y :: t) + 1) = B * ofDigits B (y :: t) + B := by ring
    omega

/-- Lemma 2.9 (iii) blockwise: `τ₂(Y, mask) = 0` iff every base-`B` digit of `Y` below `Bᵏ`
is `< z` (`z = 2ˢ`, `B = 2ᵗ`, `s ≤ t`). -/
theorem mask29_τ_iff {s t : ℕ} (hst : s ≤ t) :
    ∀ (k Y : ℕ), τ 2 Y (mask29 (2 ^ t) (2 ^ s) k) = 0 ↔ ∀ j < k, Y / (2 ^ t) ^ j % 2 ^ t < 2 ^ s
  | 0, Y => by
    rw [mask29_zero, τ_two_eq_zero_iff, Nat.and_zero]
    simp
  | k + 1, Y => by
    rw [mask29_succ]
    have hB : 0 < 2 ^ t := by positivity
    have hz : 2 ^ s ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) hst
    have hz0 : 0 < 2 ^ s := by positivity
    have hY : Y = Y % 2 ^ t + (Y / 2 ^ t) * 2 ^ t := by
      have := Nat.div_add_mod Y (2 ^ t); rw [mul_comm]; omega
    conv_lhs => rw [hY]
    rw [← lemma_2_10 (Nat.mod_lt _ hB) (by omega), τ_comm 2 (Y % 2 ^ t),
      ← lemma_2_7 hst (Nat.mod_lt _ hB), mask29_τ_iff hst k]
    constructor
    · rintro ⟨h0, h⟩ j hj
      rcases j with _ | j
      · simpa using h0
      · rw [pow_succ', ← Nat.div_div_eq_div_mul]
        exact h j (by omega)
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun j hj => ?_⟩
      rw [Nat.div_div_eq_div_mul, ← pow_succ']
      exact h (j + 1) (by omega)

/-- Lemma 2.9. -/
theorem lemma_2_9 {s t n m k : ℕ} (hs : 1 ≤ s) (hst : s ≤ t) (hnm : n ≤ m) (hmk : m ≤ k)
    (hzB : 2 * (2 ^ s) ^ (m + 1) ≤ 2 ^ t)
    {ys : List ℕ} (hys : ∀ x ∈ ys, x < 2 ^ s) (hlen : ys.length ≤ n + 1) (Y : ℕ) :
    Y = ofDigits (2 ^ t) ys ↔
      (Y ≡ ofDigits (2 ^ s) ys [MOD 2 ^ t - 2 ^ s] ∧ Y < 2 ^ s * (2 ^ t) ^ m ∧
        τ 2 Y (mask29 (2 ^ t) (2 ^ s) k) = 0) := by
  have hz1 : 1 < 2 ^ s := Nat.one_lt_two_pow_iff.2 (by omega)
  have hzB' : 2 ^ s ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) hst
  have hB1 : 1 < 2 ^ t := lt_of_lt_of_le hz1 hzB'
  have hzm : 2 ^ s ≤ (2 ^ s) ^ (m + 1) := Nat.le_self_pow (by omega) _
  have hzmB : (2 ^ s) ^ (m + 1) ≤ 2 ^ t - 2 ^ s := by omega
  have hmod : 2 ^ s ≡ 2 ^ t [MOD 2 ^ t - 2 ^ s] := (Nat.modEq_iff_dvd' hzB').2 dvd_rfl
  have hysB : ∀ x ∈ ys, x < 2 ^ t := fun x hx => lt_of_lt_of_le (hys x hx) hzB'
  constructor
  · rintro rfl
    refine ⟨(ofDigits_modEq' _ _ _ hmod ys).symm, ?_, ?_⟩
    · rcases ys with _ | ⟨y, ys⟩
      · simp [ofDigits]
      · have h1 := ofDigits_lt_mul_pow hB1 hzB' (y :: ys) hys (by simp)
        have h2 : (2 ^ t) ^ ((y :: ys).length - 1) ≤ (2 ^ t) ^ m :=
          Nat.pow_le_pow_right (by positivity) (by simp at hlen ⊢; omega)
        calc ofDigits (2 ^ t) (y :: ys) < 2 ^ s * (2 ^ t) ^ ((y :: ys).length - 1) := h1
          _ ≤ 2 ^ s * (2 ^ t) ^ m := Nat.mul_le_mul_left _ h2
    · rw [mask29_τ_iff hst]
      intro j _
      rw [ofDigits_div_pow_mod (by positivity) hysB]
      rcases Nat.lt_or_ge j ys.length with hj | hj
      · rw [List.getD_eq_getElem _ _ hj]; exact hys _ (List.getElem_mem hj)
      · rw [List.getD_eq_default _ _ hj]; positivity
  · rintro ⟨hi, hii, hiii⟩
    -- the base-`B` digits of `Y`, padded to length `m + 1`
    have hYB : Y < (2 ^ t) ^ (m + 1) := by
      calc Y < 2 ^ s * (2 ^ t) ^ m := hii
        _ ≤ 2 ^ t * (2 ^ t) ^ m := Nat.mul_le_mul_right _ hzB'
        _ = (2 ^ t) ^ (m + 1) := by ring
    have hdl : ((2 ^ t).digits Y).length ≤ m + 1 := (digits_length_le_iff hB1 Y).2 hYB
    obtain ⟨ds, hds⟩ : ∃ ds, ds = (2 ^ t).digits Y ++
        List.replicate (m + 1 - ((2 ^ t).digits Y).length) 0 := ⟨_, rfl⟩
    have hdslen : ds.length = m + 1 := by rw [hds]; simp; omega
    have hdsB : ∀ x ∈ ds, x < 2 ^ t := by
      intro x hx
      rw [hds, List.mem_append] at hx
      rcases hx with hx | hx
      · exact digits_lt_base hB1 hx
      · rw [List.mem_replicate] at hx; rw [hx.2]; positivity
    have hYds : ofDigits (2 ^ t) ds = Y := by
      rw [hds, ofDigits_append_replicate_zero, ofDigits_digits]
    -- every digit is `< z`
    have hdsz : ∀ x ∈ ds, x < 2 ^ s := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
      rw [← List.getD_eq_getElem _ 0 hj, ← ofDigits_div_pow_mod (by positivity) hdsB, hYds]
      rw [hdslen] at hj
      rcases Nat.lt_or_ge j k with hjk | hjk
      · exact (mask29_τ_iff hst k Y).1 hiii j hjk
      · have hjm : j = m := by omega
        rw [hjm]
        calc Y / (2 ^ t) ^ m % 2 ^ t ≤ Y / (2 ^ t) ^ m := Nat.mod_le _ _
          _ < 2 ^ s := (Nat.div_lt_iff_lt_mul (by positivity)).2 hii
    -- the same digits in base `z` give `y`
    have hy' : ofDigits (2 ^ s) ds ≡ ofDigits (2 ^ s) ys [MOD 2 ^ t - 2 ^ s] :=
      ((ofDigits_modEq' _ _ _ hmod ds).trans (hYds ▸ hi))
    have hy'lt : ofDigits (2 ^ s) ds < 2 ^ t - 2 ^ s := by
      calc ofDigits (2 ^ s) ds < (2 ^ s) ^ ds.length := ofDigits_lt_base_pow_length hz1 hdsz
        _ = (2 ^ s) ^ (m + 1) := by rw [hdslen]
        _ ≤ 2 ^ t - 2 ^ s := hzmB
    have hylt : ofDigits (2 ^ s) ys < 2 ^ t - 2 ^ s := by
      calc ofDigits (2 ^ s) ys < (2 ^ s) ^ ys.length := ofDigits_lt_base_pow_length hz1 hys
        _ ≤ (2 ^ s) ^ (m + 1) := Nat.pow_le_pow_right (by positivity) (by omega)
        _ ≤ 2 ^ t - 2 ^ s := hzmB
    have heq := Nat.ModEq.eq_of_lt_of_lt hy' hy'lt hylt
    -- pad `ys` to length `m + 1` and compare digit lists
    obtain ⟨ys', hys'⟩ : ∃ ys', ys' = ys ++ List.replicate (m + 1 - ys.length) 0 := ⟨_, rfl⟩
    have hys'len : ys'.length = m + 1 := by rw [hys']; simp; omega
    have hys'z : ∀ x ∈ ys', x < 2 ^ s := by
      intro x hx
      rw [hys', List.mem_append] at hx
      rcases hx with hx | hx
      · exact hys x hx
      · rw [List.mem_replicate] at hx; rw [hx.2]; positivity
    have h1 : ofDigits (2 ^ s) ys' = ofDigits (2 ^ s) ys := by
      rw [hys', ofDigits_append_replicate_zero]
    have h2 : ofDigits (2 ^ t) ys' = ofDigits (2 ^ t) ys := by
      rw [hys', ofDigits_append_replicate_zero]
    have hdsys : ds = ys' :=
      ofDigits_inj_of_len_eq hz1 (by rw [hdslen, hys'len]) hdsz hys'z (by rw [heq, h1])
    rw [← hYds, hdsys, h2]

end Jones1982
