import Diophantine.Paper1982.Master2

/-!
# Jones 1982, §5: recovering a code from the shorter first mask

The mask `M₁ = B^L − 1 − (b−1)l` has only `L = 5^(ν+1)` digits.
At the positions `5^i`, `1 ≤ i ≤ ν`, its digits are `B−b`; elsewhere
they are `B−1`. For powers of two `b ≤ B`, the carry test therefore
allows precisely the bounded coefficients of `gpoly`. The additive mask
identity below also establishes the nonnegativity of the signed expression.
-/

namespace Jones1982

open Polynomial Finset

section Mask

variable (ν : ℕ)

/-- The `L` digits of the first mask (D11). -/
noncomputable def shortMsList (b B : ℕ) : List ℕ :=
  (List.range (L4 ν)).map fun j => B - 1 - (b - 1) * ((lpoly ν 4).coeff j).toNat

theorem shortMsList_length (b B : ℕ) : (shortMsList ν b B).length = L4 ν := by
  simp [shortMsList]

theorem shortMsList_getD (b B : ℕ) {j : ℕ} (hj : j < L4 ν) :
    (shortMsList ν b B).getD j 0 = B - 1 - (b - 1) * ((lpoly ν 4).coeff j).toNat := by
  unfold shortMsList
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

theorem shortMsList_getD_of_mem {b B : ℕ} (hb : 1 ≤ b) (hbB : b ≤ B)
    {i : ℕ} (hi : i ∈ Finset.Icc 1 ν) (hj : 5 ^ i < L4 ν) :
    (shortMsList ν b B).getD (5 ^ i) 0 = B - b := by
  rw [shortMsList_getD ν b B hj, coeff_lpoly_of_mem ν hi]
  simp only [Int.toNat_one, mul_one]
  omega

theorem shortMsList_getD_of_not (b B : ℕ) {j : ℕ} (hj : j < L4 ν)
    (h : ¬ ∃ i ∈ Finset.Icc 1 ν, 5 ^ i = j) :
    (shortMsList ν b B).getD j 0 = B - 1 := by
  rw [shortMsList_getD ν b B hj, coeff_lpoly_of_not ν h]
  simp

theorem five_pow_lt_L4 {i : ℕ} (hi : i ≤ ν) : 5 ^ i < L4 ν := by
  rw [L4_eq]
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem mem_shortMsList {b B x : ℕ} (hB : 1 ≤ B) (hx : x ∈ shortMsList ν b B) : x < B := by
  unfold shortMsList at hx
  rw [List.mem_map] at hx
  obtain ⟨j, _, rfl⟩ := hx
  omega

theorem short_l_eq_sum {B l : ℕ} (hl : (l : ℤ) = (lpoly ν 4).eval (B : ℤ)) :
    l = ∑ j ∈ range (L4 ν), ((lpoly ν 4).coeff j).toNat * B ^ j := by
  have h1 := ofDigits_coeffList_eq_eval (lpoly ν 4) (fun i => (coeff_lpoly_bounds ν i).1) B
    (n := L4 ν) (lt_of_le_of_lt (natDegree_lpoly_le ν) (five_pow_lt_L4 ν le_rfl))
  rw [← hl] at h1
  have h2 : l = Nat.ofDigits B (coeffList (lpoly ν 4) (L4 ν)) := by exact_mod_cast h1.symm
  rw [h2]
  unfold coeffList
  rw [ofDigits_map_range]

/-- The additive mask identity proves that none of the subtractions truncate. -/
theorem ofDigits_shortMsList_add {b B l : ℕ} (hb : 1 ≤ b) (hbB : b ≤ B)
    (hl : (l : ℤ) = (lpoly ν 4).eval (B : ℤ)) :
    Nat.ofDigits B (shortMsList ν b B) + (b - 1) * l + 1 = B ^ L4 ν := by
  unfold shortMsList
  rw [ofDigits_map_range]
  have hB : 1 ≤ B := hb.trans hbB
  have hgeom := geom_sum_mul_add (B - 1) (L4 ν)
  rw [Nat.sub_add_cancel hB] at hgeom
  have hsum : ∑ j ∈ range (L4 ν), (B - 1 - (b - 1) * ((lpoly ν 4).coeff j).toNat) * B ^ j
      + (b - 1) * l = (∑ j ∈ range (L4 ν), B ^ j) * (B - 1) := by
    rw [short_l_eq_sum ν hl, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hc := coeff_lpoly_bounds ν j
    have hc1 : ((lpoly ν 4).coeff j).toNat ≤ 1 := by
      rw [Int.toNat_le]
      exact_mod_cast hc.2
    have : (b - 1) * ((lpoly ν 4).coeff j).toNat ≤ B - 1 := by
      calc (b - 1) * ((lpoly ν 4).coeff j).toNat ≤ (b - 1) * 1 := Nat.mul_le_mul_left _ hc1
        _ ≤ B - 1 := by omega
    have e : (B - 1 - (b - 1) * ((lpoly ν 4).coeff j).toNat) +
        (b - 1) * ((lpoly ν 4).coeff j).toNat = B - 1 := by omega
    calc (B - 1 - (b - 1) * ((lpoly ν 4).coeff j).toNat) * B ^ j +
          (b - 1) * (((lpoly ν 4).coeff j).toNat * B ^ j)
        = ((B - 1 - (b - 1) * ((lpoly ν 4).coeff j).toNat) +
            (b - 1) * ((lpoly ν 4).coeff j).toNat) * B ^ j := by ring
      _ = B ^ j * (B - 1) := by rw [e]; ring
  omega

theorem ofDigits_shortMsList {b B l : ℕ} (hb : 1 ≤ b) (hbB : b ≤ B)
    (hl : (l : ℤ) = (lpoly ν 4).eval (B : ℤ)) :
    Nat.ofDigits B (shortMsList ν b B) = B ^ L4 ν - 1 - (b - 1) * l := by
  have := ofDigits_shortMsList_add ν hb hbB hl
  omega

/-- Exact integer semantics of the first mask (D11). -/
theorem shortMask_int_eq {b B l : ℕ} (hb : 1 ≤ b) (hbB : b ≤ B)
    (hl : (l : ℤ) = (lpoly ν 4).eval (B : ℤ)) :
    (B : ℤ) ^ L4 ν - 1 - ((b : ℤ) - 1) * l = Nat.ofDigits B (shortMsList ν b B) := by
  have h := congrArg (fun n : ℕ => (n : ℤ)) (ofDigits_shortMsList_add ν hb hbB hl)
  push_cast [Nat.cast_sub hb] at h ⊢
  linarith

theorem shortMask_nonneg {b B l : ℕ} (hb : 1 ≤ b) (hbB : b ≤ B)
    (hl : (l : ℤ) = (lpoly ν 4).eval (B : ℤ)) :
    0 ≤ (B : ℤ) ^ L4 ν - 1 - ((b : ℤ) - 1) * l := by
  rw [shortMask_int_eq ν hb hbB hl]
  positivity

end Mask

section Code

variable {ν : ℕ}

set_option maxHeartbeats 1000000 in
/-- The first short-mask carry test recovers exactly the bounded code digits. -/
theorem short_code_of_tau1 {b B w v g l x : ℕ} (hb : b = 2 ^ w) (hB : B = 2 ^ v)
    (hB2 : 2 ≤ B) (hbB : b ≤ B) (hxb : x < b)
    (hl : (l : ℤ) = (lpoly ν 4).eval (B : ℤ)) (hg : g < B ^ L4 ν)
    (hτ : τ 2 g (B ^ L4 ν - 1 - (b - 1) * l) = 0) :
    ∃ zs : Fin (ν + 1) → ℕ, zs 0 = x ∧ (∀ i, zs i < b) ∧
      (g : ℤ) = (gpoly ν zs).eval (B : ℤ) := by
  have hb1 : 1 ≤ b := by rw [hb]; exact Nat.one_le_two_pow
  have hwv : w ≤ v := by
    apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1
    rwa [← hb, ← hB]
  rw [← ofDigits_shortMsList ν hb1 hbB hl, ← ofDigits_digitsPad B g (L4 ν)] at hτ
  rw [tau_ofDigits_iff hB (n := L4 ν) (fun x hx => digitsPad_lt hB2 hx)
    (fun x hx => mem_shortMsList ν (by omega) hx) (digitsPad_length hB2 hg)
    (shortMsList_length ν b B)] at hτ
  have hdig : ∀ j < L4 ν, (digitsPad B g (L4 ν)).getD j 0 < 2 ^ v := by
    intro j hj
    rw [List.getD_eq_getElem _ _ (by rw [digitsPad_length hB2 hg]; exact hj), ← hB]
    exact digitsPad_lt hB2 (List.getElem_mem _)
  have hpos : ∀ i ∈ Finset.Icc 1 ν, (digitsPad B g (L4 ν)).getD (5 ^ i) 0 < b := by
    intro i hi
    have hj : 5 ^ i < L4 ν := five_pow_lt_L4 ν (Finset.mem_Icc.1 hi).2
    have := hτ (5 ^ i) hj
    have e : B - b = 2 ^ v - 2 ^ w := by rw [hB, hb]
    rw [shortMsList_getD_of_mem ν hb1 hbB hi hj, e, τ_comm] at this
    have h := (lemma_2_7 hwv (hdig _ hj)).2 this
    rwa [← hb] at h
  have hzero : ∀ j < L4 ν, (¬ ∃ i ∈ Finset.Icc 1 ν, 5 ^ i = j) →
      (digitsPad B g (L4 ν)).getD j 0 = 0 := by
    intro j hj hne
    have := hτ j hj
    have e : B - 1 = 2 ^ v - 1 := by rw [hB]
    rw [shortMsList_getD_of_not ν b B hj hne, e, τ_comm] at this
    exact (lemma_2_7' (hdig _ hj)).2 this
  refine ⟨fun i => if i = 0 then x else (digitsPad B g (L4 ν)).getD (5 ^ (i : ℕ)) 0,
    by simp, fun i => ?_, ?_⟩
  · dsimp only
    by_cases hi : i = 0
    · rw [if_pos hi]; exact hxb
    · rw [if_neg hi]
      have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
      exact hpos i (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  · have h1 : (g : ℤ) = ((Nat.ofDigits B (digitsPad B g (L4 ν)) : ℕ) : ℤ) := by
      rw [ofDigits_digitsPad]
    have h2 := ofDigits_coeffList_eq_eval (gpoly ν fun i =>
        if i = 0 then x else (digitsPad B g (L4 ν)).getD (5 ^ (i : ℕ)) 0)
      (coeff_gpoly_nonneg ν _) B (n := L4 ν)
      (lt_of_le_of_lt (natDegree_gpoly_le ν _) (five_pow_lt_L4 ν le_rfl))
    rw [h1, ← h2]
    congr 2
    apply List.ext_getElem
    · rw [digitsPad_length hB2 hg, coeffList_length]
    · intro j hj₁ hj₂
      rw [← List.getD_eq_getElem _ 0 hj₁, ← List.getD_eq_getElem _ 0 hj₂]
      rw [digitsPad_length hB2 hg] at hj₁
      rw [coeffList_getD _ _ _ hj₁]
      by_cases h : ∃ i' : Fin (ν + 1), i' ≠ 0 ∧ 5 ^ (i' : ℕ) = j
      · obtain ⟨i', hi', rfl⟩ := h
        rw [coeff_gpoly_of_ne ν _ hi', if_neg hi', Int.toNat_natCast]
      · rw [coeff_gpoly_of_not ν _ h, Int.toNat_zero, hzero j hj₁]
        rw [exists_Icc_iff]
        exact h

set_option maxHeartbeats 1000000 in
/-- A bounded code satisfies the first short-mask carry condition and fits below `Q`. -/
theorem short_tau1_of_code {b B w v l : ℕ} (hb : b = 2 ^ w) (hB : B = 2 ^ v)
    (hB2 : 2 ≤ B) (hbB : b ≤ B) (hl : (l : ℤ) = (lpoly ν 4).eval (B : ℤ))
    (zs : Fin (ν + 1) → ℕ) (hzs : ∀ i, zs i < b)
    {g : ℕ} (hg : (g : ℤ) = (gpoly ν zs).eval (B : ℤ)) :
    τ 2 g (B ^ L4 ν - 1 - (b - 1) * l) = 0 ∧ g < B ^ L4 ν := by
  have hb1 : 1 ≤ b := by rw [hb]; exact Nat.one_le_two_pow
  have hwv : w ≤ v := by
    apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1
    rwa [← hb, ← hB]
  have hgL : g = Nat.ofDigits B (coeffList (gpoly ν zs) (L4 ν)) := by
    have := ofDigits_coeffList_eq_eval (gpoly ν zs) (coeff_gpoly_nonneg ν zs) B
      (n := L4 ν) (lt_of_le_of_lt (natDegree_gpoly_le ν _) (five_pow_lt_L4 ν le_rfl))
    rw [← hg] at this
    exact_mod_cast this.symm
  have hcoeff : ∀ j, ((gpoly ν zs).coeff j).toNat < b := by
    intro j
    by_cases h : ∃ i' : Fin (ν + 1), i' ≠ 0 ∧ 5 ^ (i' : ℕ) = j
    · obtain ⟨i', hi', rfl⟩ := h
      rw [coeff_gpoly_of_ne ν _ hi', Int.toNat_natCast]
      exact hzs i'
    · rw [coeff_gpoly_of_not ν _ h]
      simp
      omega
  have hcoeffB : ∀ x ∈ coeffList (gpoly ν zs) (L4 ν), x < B := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_coeffList hx
    exact (hcoeff i).trans_le hbB
  constructor
  · rw [← ofDigits_shortMsList ν hb1 hbB hl, hgL]
    rw [tau_ofDigits_iff hB (n := L4 ν) hcoeffB
      (fun x hx => mem_shortMsList ν (by omega) hx) (coeffList_length _ _)
      (shortMsList_length ν b B)]
    intro j hj
    rw [coeffList_getD _ _ _ hj]
    by_cases h : ∃ i ∈ Finset.Icc 1 ν, 5 ^ i = j
    · obtain ⟨i, hi, rfl⟩ := h
      rw [shortMsList_getD_of_mem ν hb1 hbB hi hj, hB, hb]
      have hi' : ∃ i' : Fin (ν + 1), i' ≠ 0 ∧ 5 ^ (i' : ℕ) = 5 ^ i :=
        (exists_Icc_iff ν _).1 ⟨i, hi, rfl⟩
      obtain ⟨i', hi'0, hii'⟩ := hi'
      rw [← hii', coeff_gpoly_of_ne ν _ hi'0, Int.toNat_natCast]
      have hzi : zs i' < 2 ^ w := by rw [← hb]; exact hzs i'
      have hzi' : zs i' < 2 ^ v :=
        hzi.trans_le (Nat.pow_le_pow_right (by norm_num) hwv)
      rw [τ_comm]
      exact (lemma_2_7 hwv hzi').1 hzi
    · rw [coeff_gpoly_of_not ν _ (by rw [← exists_Icc_iff]; exact h)]
      simp only [Int.toNat_zero]
      exact τ_zero_left _
  · rw [hgL]
    have := Nat.ofDigits_lt_base_pow_length (b := B)
      (l := coeffList (gpoly ν zs) (L4 ν)) hB2 hcoeffB
    rwa [coeffList_length] at this

/-- The complete equivalence between the bounded first block and a bounded code. -/
theorem short_code_iff {b B w v g l x : ℕ} (hb : b = 2 ^ w) (hB : B = 2 ^ v)
    (hB2 : 2 ≤ B) (hbB : b ≤ B) (hxb : x < b)
    (hl : (l : ℤ) = (lpoly ν 4).eval (B : ℤ)) :
    (g < B ^ L4 ν ∧ τ 2 g (B ^ L4 ν - 1 - (b - 1) * l) = 0) ↔
      ∃ zs : Fin (ν + 1) → ℕ, zs 0 = x ∧ (∀ i, zs i < b) ∧
        (g : ℤ) = (gpoly ν zs).eval (B : ℤ) := by
  constructor
  · rintro ⟨hg, hτ⟩
    exact short_code_of_tau1 hb hB hB2 hbB hxb hl hg hτ
  · rintro ⟨zs, _, hzs, hg⟩
    obtain ⟨hτ, hbound⟩ := short_tau1_of_code hb hB hB2 hbB hl zs hzs hg
    exact ⟨hbound, hτ⟩

end Code

end Jones1982
