import Diophantine.Paper1980.Decode93

/-!
# Necessity: the coding witnesses (Section 7, part 1)

Given an accepting assignment `X` of the circuit at the input `x ≥ 1`, the
physical digits are `z = assign X x j_H` (three-way splits with bit `j_H`
clear), the radix is a power of two `B = 2^{j_H+1} · 2^N` exceeding `2H₀`,
`H + 4 + x`, every digit, and `7x²`; then

  `b = B − H − 4`, `β = b − x`, `θ = B − 4`, `q = B^L`, `n = q⁸`,
  `l = ℓ₀(B)`, `e = e₀(B)`, `α = q − l − e`, `λ = Σ_{h<2L} B^h`,
  `g = Σᵢ zᵢ B^{vᵢ}`, `Ω = λ − e`, `σ = Ω (q − (x+g)²)`,
  `S = g + q²(l + eq + q²σ)`, `T⁺ = (q² − 1 − bl) + θλq² + θlq⁴ + 1`,
  `r = S(n² − n) + T⁺(n² − 1)`.

This file defines these witnesses and proves the size bounds and the coding
equations `E1, E1b, E2, E3, E6, E7, ES, EΩ`, the congruence `E45` with its
positive quotient `t`, and the positivity of every coding unknown.
-/

namespace Jones1980

namespace Iso

open Layout Polynomial Finset
open Diophantine Pell

noncomputable section

section Defs

variable (C : Gates.Circuit) (x : ℕ) (X : Fin C.m → ℕ)

/-- The physical digits. -/
@[irreducible] def zW : Fin (nphys C.m) → ℕ := assign C.m X x (jH C)
/-- The size parameter of the radix. -/
@[irreducible] def NW : ℕ := x + 7 * x ^ 2 + Finset.univ.sup (zW C x X)
@[irreducible] def mBW : ℕ := jH C + 1 + NW C x X
/-- The radix. -/
@[irreducible] def BW : ℕ := 2 ^ mBW C x X
@[irreducible] def bW : ℕ := BW C x X - cH C - 4
@[irreducible] def qW : ℕ := BW C x X ^ cL C
@[irreducible] def nW : ℕ := qW C x X ^ 8
@[irreducible] def lW : ℕ := Nat.ofDigits (BW C x X) (ell0d (nphys C.m) (cs C) (cL C))
@[irreducible] def eW : ℕ := Nat.ofDigits (BW C x X) (e0d (nphys C.m) (cs C) (cD C))
@[irreducible] def lamW : ℕ := ∑ h ∈ range (2 * cL C), BW C x X ^ h
@[irreducible] def gW : ℕ := ∑ i : Fin (nphys C.m), zW C x X i * BW C x X ^ (v i)
@[irreducible] def ΩW : ℕ := lamW C x X - eW C x X
@[irreducible] def σW : ℕ := ΩW C x X * (qW C x X - (x + gW C x X) ^ 2)
@[irreducible] def SW : ℕ :=
  gW C x X + qW C x X ^ 2 * (lW C x X + eW C x X * qW C x X + qW C x X ^ 2 * σW C x X)
@[irreducible] def TW : ℕ :=
  (qW C x X ^ 2 - 1 - bW C x X * lW C x X) + (BW C x X - 4) * lamW C x X * qW C x X ^ 2 +
    (BW C x X - 4) * lW C x X * qW C x X ^ 4 + 1
@[irreducible] def rW : ℕ :=
  SW C x X * (nW C x X ^ 2 - nW C x X) + TW C x X * (nW C x X ^ 2 - 1)

end Defs

section Bounds

variable (C : Gates.Circuit) (x : ℕ) (X : Fin C.m → ℕ)

theorem BW_eq : BW C x X = 2 ^ (jH C + 1) * 2 ^ NW C x X := by
  unfold BW mBW; rw [pow_add]

theorem BW_pow : ∃ mB, BW C x X = 2 ^ mB := by unfold BW; exact ⟨_, rfl⟩

theorem NW_lt_two_pow : NW C x X < 2 ^ NW C x X := Nat.lt_two_pow_self

theorem two_H0_le_BW : 2 * H0 C ≤ BW C x X := by
  rw [BW_eq, pow_succ]
  unfold H0
  rw [show 2 ^ jH C * 2 * 2 ^ NW C x X = (2 * 2 ^ jH C) * 2 ^ NW C x X by ring]
  exact Nat.le_mul_of_pos_right _ Nat.one_le_two_pow

theorem H0_le_BW : H0 C ≤ BW C x X := by have := two_H0_le_BW C x X; omega

theorem BW_ge_64 : 64 ≤ BW C x X := by have := H0_le_BW C x X; have := H0_ge_1024 C; omega

theorem NW_lt_BW : NW C x X + 2 * H0 C ≤ BW C x X := by
  rw [BW_eq, pow_succ]
  unfold H0
  have h1 : NW C x X + 1 ≤ 2 ^ NW C x X := NW_lt_two_pow C x X
  have h2 : 1 ≤ 2 ^ jH C := Nat.one_le_two_pow
  have h3 : (2 * 2 ^ jH C) * (NW C x X + 1) ≤ (2 * 2 ^ jH C) * 2 ^ NW C x X :=
    Nat.mul_le_mul_left _ h1
  have h4 : NW C x X ≤ (2 * 2 ^ jH C) * NW C x X := Nat.le_mul_of_pos_left _ (by omega)
  rw [show 2 ^ jH C * 2 * 2 ^ NW C x X = (2 * 2 ^ jH C) * 2 ^ NW C x X by ring]
  rw [Nat.mul_add, mul_one] at h3
  omega

theorem zW_le_NW (i : Fin (nphys C.m)) : zW C x X i ≤ NW C x X := by
  unfold NW
  have := Finset.le_sup (f := zW C x X) (Finset.mem_univ i)
  omega

theorem zW_lt_BW (i : Fin (nphys C.m)) : zW C x X i < BW C x X := by
  have := zW_le_NW C x X i; have := NW_lt_BW C x X; have := H0_ge_1024 C; omega

theorem x_le_NW : x ≤ NW C x X := by unfold NW; omega

theorem sevenx_le_NW : 7 * x ^ 2 ≤ NW C x X := by unfold NW; omega

theorem sevenx_lt_BW : 7 * x ^ 2 < BW C x X := by
  have := sevenx_le_NW C x X; have := NW_lt_BW C x X; have := H0_ge_1024 C; omega

theorem cH_eq : cH C = H0 C - 3 := by unfold cH; rfl

theorem cH_add_lt_BW : cH C + 4 + x < BW C x X := by
  have := x_le_NW C x X; have := NW_lt_BW C x X; have := H0_ge_1024 C; have := cH_eq C; omega

theorem bW_eq : bW C x X = BW C x X - cH C - 4 := by unfold bW; rfl

theorem radix_eq : cH C + bW C x X + 4 = BW C x X := by
  rw [bW_eq]; have := cH_add_lt_BW C x X; omega

theorem x_lt_bW : x < bW C x X := by rw [bW_eq]; have := cH_add_lt_BW C x X; omega

theorem cL_ge : 2 ≤ cL C := by unfold cL; omega

theorem cK_le_cL : cK C + 1 ≤ cL C := by unfold cL; omega

theorem cK_eq : cK C = K (nphys C.m) (cs C) := by unfold cK; rfl

theorem cK_pos : 3 ≤ cK C := by rw [cK_eq]; unfold K; omega

theorem three_cL_le_BW : 3 * cL C ≤ BW C x X := by
  have := H0_ge_L C; have := H0_le_BW C x X; omega

theorem qW_eq : qW C x X = BW C x X ^ cL C := by unfold qW; rfl

theorem nW_eq : nW C x X = qW C x X ^ 8 := by unfold nW; rfl

theorem BW_le_qW : BW C x X ≤ qW C x X := by
  rw [qW_eq]; exact Nat.le_self_pow (by have := cL_ge C; omega) _

theorem qW_pow : ∃ jq, 1 ≤ jq ∧ qW C x X = 2 ^ jq := by
  obtain ⟨mB, hmB⟩ := BW_pow C x X
  refine ⟨mB * cL C, ?_, by rw [qW_eq, hmB, ← pow_mul]⟩
  have : 1 ≤ mB := by
    by_contra h
    have : mB = 0 := by omega
    rw [this] at hmB; have := BW_ge_64 C x X; omega
  have := cL_ge C
  nlinarith

theorem qW_ge : 64 ≤ qW C x X := le_trans (BW_ge_64 C x X) (BW_le_qW C x X)

theorem nW_ge : qW C x X ≤ nW C x X := by rw [nW_eq]; exact Nat.le_self_pow (by norm_num) _

theorem qW7_lt_nW : qW C x X ^ 7 < nW C x X := by
  rw [nW_eq]; exact Nat.pow_lt_pow_right (by have := qW_ge C x X; omega) (by norm_num)

/-- `ℓ₀(B) = Σ_{h<L} ind h B^h`. -/
theorem lW_sum : lW C x X = ∑ h ∈ range (cL C), ind (nphys C.m) (cs C) h * BW C x X ^ h := by
  unfold lW; rw [ofDigits_ell0d]

theorem lW_sum_K : lW C x X = ∑ h ∈ range (cK C), ind (nphys C.m) (cs C) h * BW C x X ^ h := by
  rw [lW_sum]
  symm
  apply Finset.sum_subset (Finset.range_mono (by have := cK_le_cL C; omega))
  intro h _ hh
  rw [Finset.mem_range] at hh
  rw [ind_eq_zero_of_ge (show K (nphys C.m) (cs C) ≤ h by rw [← cK_eq]; omega), zero_mul]

theorem ell0d_digit_lt (N : ℕ) : ∀ y ∈ ell0d (nphys C.m) (cs C) N, y < BW C x X := by
  intro y hy
  have := ell0d_mem_le (nphys C.m) (cs C) N y hy
  have := BW_ge_64 C x X
  omega

theorem e0d_digit_lt : ∀ y ∈ e0d (nphys C.m) (cs C) (cD C), y < BW C x X := by
  intro y hy
  have := e0d_mem_le (nphys C.m) (cs C) (cD C) (cD_abs C) y hy
  have := BW_ge_64 C x X
  omega

theorem lW_lt : lW C x X < BW C x X ^ cK C := by
  rw [lW_sum_K, ← ofDigits_ell0d]
  have := Nat.ofDigits_lt_base_pow_length (b := BW C x X) (l := ell0d (nphys C.m) (cs C) (cK C))
    (by have := BW_ge_64 C x X; omega) (ell0d_digit_lt C x X (cK C))
  rwa [ell0d_length] at this

theorem eW_lt : eW C x X < BW C x X ^ cK C := by
  unfold eW
  have := Nat.ofDigits_lt_base_pow_length (b := BW C x X)
    (l := e0d (nphys C.m) (cs C) (cD C)) (by have := BW_ge_64 C x X; omega) (e0d_digit_lt C x X)
  rwa [e0d_length, ← cK_eq] at this

theorem eW_cast : (eW C x X : ℤ) =
    ∑ h ∈ range (K (nphys C.m) (cs C)), (1 + (cD C).coeff h) * (BW C x X : ℤ) ^ h := by
  unfold eW; exact ofDigits_e0d (nphys C.m) (cs C) (BW C x X) (cD C) (cD_abs C)

theorem pow_cK_le_qW : BW C x X ^ (cK C + 1) ≤ qW C x X := by
  rw [qW_eq]; exact Nat.pow_le_pow_right (by have := BW_ge_64 C x X; omega) (cK_le_cL C)

theorem lW_add_eW_lt : lW C x X + eW C x X < qW C x X := by
  have h1 := lW_lt C x X; have h2 := eW_lt C x X; have h3 := pow_cK_le_qW C x X
  have h4 : BW C x X ^ (cK C + 1) = BW C x X ^ cK C * BW C x X := pow_succ _ _
  have h5 : 2 ≤ BW C x X := by have := BW_ge_64 C x X; omega
  nlinarith

theorem lW_lt_qW : lW C x X < qW C x X := by have := lW_add_eW_lt C x X; omega
theorem eW_lt_qW : eW C x X < qW C x X := by have := lW_add_eW_lt C x X; omega

theorem gW_sum : gW C x X = ∑ i : Fin (nphys C.m), zW C x X i * BW C x X ^ (v i) := by
  unfold gW; rfl

/-- `g < B^K`. -/
theorem gW_lt : gW C x X < BW C x X ^ cK C := by
  rw [gW_sum]
  have hB := BW_ge_64 C x X
  have hM : M (nphys C.m) + 1 ≤ cK C := by
    rw [cK_eq]; unfold K; have := t_ge_two_M (nphys C.m) (cs C) (cs C - 1); omega
  calc ∑ i : Fin (nphys C.m), zW C x X i * BW C x X ^ (v i)
      ≤ ∑ i : Fin (nphys C.m), (BW C x X - 1) * BW C x X ^ (v i) :=
        Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (by have := zW_lt_BW C x X i; omega)
    _ = ∑ h ∈ (Finset.univ : Finset (Fin (nphys C.m))).image (fun i : Fin (nphys C.m) => v i),
          (BW C x X - 1) * BW C x X ^ h := by
        rw [Finset.sum_image (fun i _ k _ h => v_inj h)]
    _ ≤ ∑ h ∈ range (M (nphys C.m) + 1), (BW C x X - 1) * BW C x X ^ h := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro h hh
          rw [Finset.mem_image] at hh
          obtain ⟨i, _, rfl⟩ := hh
          rw [Finset.mem_range]; have := v_le_M i.2; omega
        · intro _ _ _; exact Nat.zero_le _
    _ < BW C x X ^ (M (nphys C.m) + 1) := by
        have := sum_pred_mul_pow (B := BW C x X) (by omega) (M (nphys C.m) + 1); omega
    _ ≤ BW C x X ^ cK C := Nat.pow_le_pow_right (by omega) hM

theorem C_lt : x + gW C x X < BW C x X ^ (cK C + 1) := by
  have h1 := gW_lt C x X; have h2 := x_lt_bW C x X; have h3 := radix_eq C x X
  have h4 : BW C x X ^ (cK C + 1) = BW C x X ^ cK C * BW C x X := pow_succ _ _
  have h5 : 1 ≤ BW C x X ^ cK C := Nat.one_le_pow _ _ (by have := BW_ge_64 C x X; omega)
  have h6 : 64 ≤ BW C x X := BW_ge_64 C x X
  nlinarith

theorem Csq_lt_qW : (x + gW C x X) ^ 2 < qW C x X := by
  have h1 := C_lt C x X
  have h2 : (BW C x X ^ (cK C + 1)) ^ 2 ≤ qW C x X := by
    rw [qW_eq, ← pow_mul]
    exact Nat.pow_le_pow_right (by have := BW_ge_64 C x X; omega) (by unfold cL; omega)
  exact lt_of_lt_of_le (Nat.pow_lt_pow_left h1 two_ne_zero) h2

theorem lamW_sum : lamW C x X = ∑ h ∈ range (2 * cL C), BW C x X ^ h := by unfold lamW; rfl

/-- The geometric equation `λ(B − 1) = q² − 1`. -/
theorem lamW_mul : lamW C x X * (BW C x X - 1) = qW C x X ^ 2 - 1 := by
  rw [lamW_sum, qW_eq, ← pow_mul, mul_comm (cL C) 2]
  have h := sum_pred_mul_pow (B := BW C x X) (by have := BW_ge_64 C x X; omega) (2 * cL C)
  have : (∑ h ∈ range (2 * cL C), BW C x X ^ h) * (BW C x X - 1) =
      ∑ h ∈ range (2 * cL C), (BW C x X - 1) * BW C x X ^ h := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun h _ => mul_comm _ _
  omega

theorem E2W : lamW C x X + qW C x X ^ 2 = 1 + lamW C x X * (cH C + bW C x X + 4) := by
  rw [radix_eq]
  have h := lamW_mul C x X
  have hB : 1 ≤ BW C x X := by have := BW_ge_64 C x X; omega
  have hq : 1 ≤ qW C x X ^ 2 := Nat.one_le_pow _ _ (by have := qW_ge C x X; omega)
  have : lamW C x X * (BW C x X - 1) = lamW C x X * BW C x X - lamW C x X := by
    rw [Nat.mul_sub, mul_one]
  have : lamW C x X ≤ lamW C x X * BW C x X := Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem lamW_lt_qW_sq : lamW C x X < qW C x X ^ 2 := by
  have h := lamW_mul C x X
  have hB : 2 ≤ BW C x X := by have := BW_ge_64 C x X; omega
  have : lamW C x X ≤ lamW C x X * (BW C x X - 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hq : 1 ≤ qW C x X ^ 2 := Nat.one_le_pow _ _ (by have := qW_ge C x X; omega)
  omega

theorem eW_lt_lamW : eW C x X < lamW C x X := by
  have h1 := eW_lt C x X
  have h2 : BW C x X ^ cK C ≤ lamW C x X := by
    rw [lamW_sum]
    have hmem : cK C ∈ range (2 * cL C) := Finset.mem_range.2 (by have := cK_le_cL C; omega)
    exact Finset.single_le_sum (fun h _ => Nat.zero_le _) hmem
  omega

theorem θW_eq : cH C + bW C x X = BW C x X - 4 := by have := radix_eq C x X; omega

/-- `θ λ = mask29 B 4 (2L)`. -/
theorem θlamW_eq_mask : (BW C x X - 4) * lamW C x X = Jones1982.mask29 (BW C x X) 4 (2 * cL C) :=
  theta_lam_eq_mask (by have := BW_ge_64 C x X; omega) (by have := BW_ge_64 C x X; omega)
    (by rw [lamW_mul, qW_eq, ← pow_mul, mul_comm (cL C) 2])

theorem θlamW_lt : (BW C x X - 4) * lamW C x X < qW C x X ^ 2 := by
  have h := lamW_mul C x X
  have hq : 1 ≤ qW C x X ^ 2 := Nat.one_le_pow _ _ (by have := qW_ge C x X; omega)
  have hB : 4 ≤ BW C x X := by have := BW_ge_64 C x X; omega
  have : (BW C x X - 4) * lamW C x X ≤ (BW C x X - 1) * lamW C x X :=
    Nat.mul_le_mul_right _ (by omega)
  rw [mul_comm] at h
  omega

theorem bW_lt_BW : bW C x X < BW C x X := by have := radix_eq C x X; omega

theorem bWlW_lt : bW C x X * lW C x X + 1 < qW C x X ^ 2 := by
  have h1 := bW_lt_BW C x X; have h2 := BW_le_qW C x X; have h3 := lW_lt_qW C x X
  have h4 : bW C x X ≤ qW C x X - 1 := by omega
  have h5 : lW C x X ≤ qW C x X - 1 := by omega
  have h6 := qW_ge C x X
  have := Nat.mul_le_mul h4 h5
  obtain ⟨q', hq'⟩ : ∃ q', qW C x X = q' + 1 := ⟨qW C x X - 1, by omega⟩
  rw [hq'] at this ⊢
  simp only [Nat.add_sub_cancel] at this
  nlinarith

theorem ΩW_eq : ΩW C x X = lamW C x X - eW C x X := by unfold ΩW; rfl

theorem ΩW_pos : 0 < ΩW C x X := by rw [ΩW_eq]; have := eW_lt_lamW C x X; omega

theorem ΩW_le : ΩW C x X ≤ lamW C x X := by rw [ΩW_eq]; omega

theorem σW_eq : σW C x X = ΩW C x X * (qW C x X - (x + gW C x X) ^ 2) := by unfold σW; rfl

theorem σW_pos : 0 < σW C x X := by
  rw [σW_eq]
  exact Nat.mul_pos (ΩW_pos C x X) (by have := Csq_lt_qW C x X; omega)

theorem σW_lt : σW C x X < qW C x X ^ 3 := by
  rw [σW_eq]
  have h1 := ΩW_le C x X; have h2 := lamW_lt_qW_sq C x X
  have h3 : qW C x X - (x + gW C x X) ^ 2 ≤ qW C x X := Nat.sub_le _ _
  calc ΩW C x X * (qW C x X - (x + gW C x X) ^ 2) ≤ lamW C x X * qW C x X :=
        Nat.mul_le_mul h1 h3
    _ < qW C x X ^ 2 * qW C x X := Nat.mul_lt_mul_of_pos_right h2 (by have := qW_ge C x X; omega)
    _ = qW C x X ^ 3 := by ring

theorem S2W_lt : lW C x X + eW C x X * qW C x X < qW C x X ^ 2 := by
  have h1 := lW_lt_qW C x X; have h2 := eW_lt_qW C x X
  have h3 : (eW C x X + 1) * qW C x X ≤ qW C x X * qW C x X := Nat.mul_le_mul_right _ h2
  rw [add_mul, one_mul, ← sq] at h3
  omega

theorem gW_lt_qW : gW C x X < qW C x X := by
  have := gW_lt C x X; have := pow_cK_le_qW C x X
  have : BW C x X ^ cK C ≤ BW C x X ^ (cK C + 1) :=
    Nat.pow_le_pow_right (by have := BW_ge_64 C x X; omega) (by omega)
  omega

theorem SW_eq : SW C x X =
    gW C x X + qW C x X ^ 2 * (lW C x X + eW C x X * qW C x X + qW C x X ^ 2 * σW C x X) := by
  unfold SW; rfl

theorem SW_lt : SW C x X < qW C x X ^ 7 := by
  rw [SW_eq]
  have hg := gW_lt_qW C x X; have hS2 := S2W_lt C x X; have hσ := σW_lt C x X
  have hq := qW_ge C x X
  set q := qW C x X
  have h1 : lW C x X + eW C x X * q ≤ q ^ 2 - 1 := by omega
  have h2 : σW C x X ≤ q ^ 3 - 1 := by omega
  have h3 : gW C x X ≤ q - 1 := by omega
  have h4 : q ^ 2 * (lW C x X + eW C x X * q + q ^ 2 * σW C x X) ≤
      q ^ 2 * ((q ^ 2 - 1) + q ^ 2 * (q ^ 3 - 1)) :=
    Nat.mul_le_mul_left _ (add_le_add h1 (Nat.mul_le_mul_left _ h2))
  have h5 : q ^ 2 * ((q ^ 2 - 1) + q ^ 2 * (q ^ 3 - 1)) = q ^ 7 - q ^ 2 := by
    have e1 : q ^ 2 - 1 + q ^ 2 * (q ^ 3 - 1) = q ^ 5 - 1 := by
      have : q ^ 2 * (q ^ 3 - 1) = q ^ 5 - q ^ 2 := by
        rw [Nat.mul_sub, mul_one, ← pow_add]
      have : q ^ 2 ≤ q ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
      have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    rw [e1, Nat.mul_sub, mul_one, ← pow_add]
  have h6 : q ^ 2 ≤ q ^ 7 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h7 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  omega

theorem TW_eq : TW C x X =
    (qW C x X ^ 2 - 1 - bW C x X * lW C x X) + (BW C x X - 4) * lamW C x X * qW C x X ^ 2 +
      (BW C x X - 4) * lW C x X * qW C x X ^ 4 + 1 := by unfold TW; rfl

theorem θlW_lt : (BW C x X - 4) * lW C x X < qW C x X ^ 2 := by
  have h1 := BW_le_qW C x X; have h2 := lW_lt_qW C x X; have hq := qW_ge C x X
  calc (BW C x X - 4) * lW C x X ≤ (qW C x X - 1) * (qW C x X - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
    _ < qW C x X ^ 2 := by
        obtain ⟨q', hq'⟩ : ∃ q', qW C x X = q' + 1 := ⟨qW C x X - 1, by omega⟩
        rw [hq']; simp only [Nat.add_sub_cancel]; nlinarith

/-- `T⁺ − 1 < q⁷`. -/
theorem TW_lt : (qW C x X ^ 2 - 1 - bW C x X * lW C x X) + (BW C x X - 4) * lamW C x X * qW C x X ^ 2 +
    (BW C x X - 4) * lW C x X * qW C x X ^ 4 < qW C x X ^ 7 := by
  have h1 := θlamW_lt C x X; have h2 := θlW_lt C x X; have hq := qW_ge C x X
  set q := qW C x X
  have a1 : q ^ 2 - 1 - bW C x X * lW C x X ≤ q ^ 2 - 1 := Nat.sub_le _ _
  have a2 : (BW C x X - 4) * lamW C x X * q ^ 2 ≤ (q ^ 2 - 1) * q ^ 2 :=
    Nat.mul_le_mul_right _ (by omega)
  have a3 : (BW C x X - 4) * lW C x X * q ^ 4 ≤ (q ^ 2 - 1) * q ^ 4 :=
    Nat.mul_le_mul_right _ (by omega)
  have e : (q ^ 2 - 1) + (q ^ 2 - 1) * q ^ 2 + (q ^ 2 - 1) * q ^ 4 = q ^ 6 - 1 := by
    have : (q ^ 2 - 1) * (1 + q ^ 2 + q ^ 4) = q ^ 6 - 1 := by
      have h1' : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
      obtain ⟨p, hp⟩ : ∃ p, q ^ 2 = p + 1 := ⟨q ^ 2 - 1, by omega⟩
      have e4 : q ^ 4 = (p + 1) ^ 2 := by rw [← hp]; ring
      have e6 : q ^ 6 = (p + 1) ^ 3 := by rw [← hp]; ring
      rw [hp, e4, e6, Nat.add_sub_cancel]
      have : (p + 1) ^ 3 = p * (1 + (p + 1) + (p + 1) ^ 2) + 1 := by ring
      omega
    rw [← this]; ring
  have h6 : q ^ 6 < q ^ 7 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

theorem TW_pos : 0 < TW C x X := by rw [TW_eq]; omega

theorem rW_eq : rW C x X = SW C x X * (nW C x X ^ 2 - nW C x X) + TW C x X * (nW C x X ^ 2 - 1) := by
  unfold rW; rfl

theorem nW_le_rW : nW C x X ≤ rW C x X := by
  rw [rW_eq]
  have hT := TW_pos C x X
  have hn : 64 ≤ nW C x X := le_trans (qW_ge C x X) (nW_ge C x X)
  have h1 : nW C x X ^ 2 - 1 ≤ TW C x X * (nW C x X ^ 2 - 1) := Nat.le_mul_of_pos_left _ hT
  have h2 : nW C x X ≤ nW C x X ^ 2 - 1 := by
    have : nW C x X * 2 ≤ nW C x X * nW C x X := Nat.mul_le_mul_left _ (by omega)
    rw [sq]; omega
  omega

theorem rW_ge_two : 2 ≤ rW C x X := le_trans (by have := qW_ge C x X; have := nW_ge C x X; omega)
  (nW_le_rW C x X)

/-- The equation `E7` in `ℤ`. -/
theorem E7W : (rW C x X : ℤ) =
    ((gW C x X : ℤ) + qW C x X ^ 2 * (lW C x X + eW C x X * qW C x X + qW C x X ^ 2 * σW C x X)) *
      ((nW C x X : ℤ) ^ 2 - nW C x X) +
    ((qW C x X : ℤ) ^ 2 * (1 + (cH C + bW C x X) * lamW C x X) - bW C x X * lW C x X +
      (cH C + bW C x X) * lW C x X * qW C x X ^ 4) * ((nW C x X : ℤ) ^ 2 - 1) := by
  rw [rW_eq, SW_eq, TW_eq]
  have hbl := bWlW_lt C x X
  have hq2 : 1 ≤ qW C x X ^ 2 := Nat.one_le_pow _ _ (by have := qW_ge C x X; omega)
  have hn2 : nW C x X ≤ nW C x X ^ 2 := Nat.le_self_pow two_ne_zero _
  have hn1 : 1 ≤ nW C x X ^ 2 := Nat.one_le_pow _ _ (by have := qW_ge C x X; have := nW_ge C x X; omega)
  have hθ : ((cH C + bW C x X : ℕ) : ℤ) = (BW C x X : ℤ) - 4 := by
    rw [θW_eq]; push_cast [Nat.cast_sub (show 4 ≤ BW C x X by have := BW_ge_64 C x X; omega)]; rfl
  push_cast [Nat.cast_sub (show 1 ≤ qW C x X ^ 2 by omega),
    Nat.cast_sub (show bW C x X * lW C x X ≤ qW C x X ^ 2 - 1 by omega), Nat.cast_sub hn2,
    Nat.cast_sub hn1, Nat.cast_sub (show 4 ≤ BW C x X by have := BW_ge_64 C x X; omega)]
  have : ((cH C : ℤ) + bW C x X) = (BW C x X : ℤ) - 4 := by
    have := hθ; push_cast at this; exact this
  rw [this]
  ring

theorem ESW : (σW C x X : ℤ) = ((lamW C x X : ℤ) - eW C x X) * (qW C x X - ((x : ℤ) + gW C x X) ^ 2) := by
  rw [σW_eq, ΩW_eq]
  have h1 := eW_lt_lamW C x X; have h2 := Csq_lt_qW C x X
  push_cast [Nat.cast_sub h1.le, Nat.cast_sub h2.le]
  ring

theorem EΩW : (ΩW C x X : ℤ) = lamW C x X - eW C x X := by
  rw [ΩW_eq]; have := eW_lt_lamW C x X; push_cast [Nat.cast_sub this.le]; rfl

theorem E1W : lW C x X + eW C x X + (qW C x X - lW C x X - eW C x X) = qW C x X := by
  have := lW_add_eW_lt C x X; omega

theorem αW_pos : 0 < qW C x X - lW C x X - eW C x X := by have := lW_add_eW_lt C x X; omega

theorem E1bW : bW C x X = x + (bW C x X - x) := by have := x_lt_bW C x X; omega

theorem βW_pos : 0 < bW C x X - x := by have := x_lt_bW C x X; omega

end Bounds

end

end Iso

end Jones1980
