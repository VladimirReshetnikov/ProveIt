import Diophantine.Paper1980.NecessityCode90a
import Diophantine.Paper1980.NecessityCode93b

/-!
# Necessity: the three masks of the constructed witnesses (part 2)

At the constructed witnesses the three masks hold:

* `g & (q² − 1 − bl) = 0`: the digits of `g` vanish off the indicator support
  and have bit `j_H` clear on it, while the mask has digit
  `B − 1 − b = H₀ = 2^{j_H}` there;
* `(l + eq) & θλ = 0`: the canonical code is binary (Lemma 2.9 of 1982);
* `σ & θl = 0`: below the least exponent of `D` the digits of `σ` vanish, and
  at every tested start the window shows `0` (seeds, reverses, paired rows,
  negative positions) or `1` (unit rows), since `2x² < B` kills the padding
  carry.

Hence `n² ∣ C(2r, r)` (`centralW`).  The file also proves the congruence `E45`
with its positive quotient `t`.
-/

namespace Jones1980

namespace L90

open Layout (Row)
open Polynomial Finset
open Diophantine Pell
open Jones1982 (τ)
open Iso (absSum absSum_nonneg nphys gP gQ gR gU iδ iδ' SN assign negRow negRow_val unitRow
  unitRow_val)

noncomputable section

/-- A binary digit is disjoint from `2^m − 2`. -/
theorem land_pow_sub_two_eq_zero {x m : ℕ} (hm : 1 ≤ m) (hx : x ≤ 1) : x &&& (2 ^ m - 2) = 0 := by
  rw [Jones1982.land_eq_zero_iff]
  intro p hp
  have hp1 : p < 1 := by
    by_contra h
    push Not at h
    have : x.testBit p = false := Nat.testBit_lt_two_pow (lt_of_le_of_lt hx (by
      calc (1 : ℕ) < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) h))
    rw [this] at hp; exact absurd hp (by decide)
  have e : 2 ^ m - 2 = (2 ^ (m - 1) - 1) * 2 ^ 1 := by
    have : 2 ^ m = 2 ^ (m - 1) * 2 ^ 1 := by rw [← pow_add]; congr 1; omega
    rw [this, Nat.sub_mul, one_mul]; norm_num
  rw [e, Nat.testBit_mul_two_pow]
  simp [show ¬ (1 ≤ p) by omega]

section Masks

variable (C : Gates.Circuit) (x : ℕ) (X : Fin C.m → ℕ)

theorem t0_ge : 32 * M (nphys C.m) + 16 ≤ t (nphys C.m) (cs C) 0 := t_zero_ge _ _

/-- The digit function of `g`. -/
def gd (h : ℕ) : ℕ := ∑ i : Fin (nphys C.m), if h = v i then zW C x X i else 0

theorem gd_v (i : Fin (nphys C.m)) : gd C x X (v i) = zW C x X i := by
  unfold gd
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk; rw [if_neg]; intro h; exact hk (Fin.ext (v_inj h)).symm
  · simp

theorem gd_of_not_mem (h : ℕ)
    (hh : h ∉ (Finset.univ : Finset (Fin (nphys C.m))).image (fun i : Fin (nphys C.m) => v i)) :
    gd C x X h = 0 := by
  unfold gd
  apply Finset.sum_eq_zero
  intro i _
  rw [if_neg]
  intro he
  exact hh (Finset.mem_image.2 ⟨i, Finset.mem_univ _, he.symm⟩)

theorem gd_lt (h : ℕ) : gd C x X h < BW C x X := by
  by_cases hh : h ∈ (Finset.univ : Finset (Fin (nphys C.m))).image (fun i : Fin (nphys C.m) => v i)
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hh
    rw [gd_v]; exact zW_lt_BW C x X i
  · rw [gd_of_not_mem C x X h hh]; have := BW_ge_64 C x X; omega

theorem gW_eq_sum : gW C x X = ∑ h ∈ range (cL C), gd C x X h * BW C x X ^ h := by
  rw [gW_sum]
  unfold gd
  have e : ∀ h, (∑ i : Fin (nphys C.m), if h = v i then zW C x X i else 0) * BW C x X ^ h =
      ∑ i : Fin (nphys C.m), if h = v i then zW C x X i * BW C x X ^ h else 0 := by
    intro h
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  simp_rw [e]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_ite_eq' (range (cL C)) (v i) (fun h => zW C x X i * BW C x X ^ h),
    if_pos (Finset.mem_range.2 (v_lt_cL C i))]

theorem gW_digit (i : ℕ) :
    gW C x X / BW C x X ^ i % BW C x X = if i < cL C then gd C x X i else 0 := by
  rw [gW_eq_sum]
  exact Iso.digit_sum (by have := BW_ge_64 C x X; omega) i _ (gd_lt C x X) (cL C)

theorem maskW_lt : qW C x X ^ 2 - 1 - bW C x X * lW C x X < BW C x X ^ (2 * cL C) := by
  have : qW C x X ^ 2 = BW C x X ^ (2 * cL C) := by rw [qW_eq, ← pow_mul, mul_comm]
  have : 1 ≤ qW C x X ^ 2 := Nat.one_le_pow _ _ (by have := qW_ge C x X; omega)
  omega

theorem image_v_subset_supp {i : ℕ}
    (hi : i ∈ (Finset.univ : Finset (Fin (nphys C.m))).image (fun i : Fin (nphys C.m) => v i)) :
    i ∈ supp (crows C) := by
  obtain ⟨i', _, rfl⟩ := Finset.mem_image.1 hi
  exact v_mem_supp (crows C) i'

theorem BW_sub_bW : BW C x X - 1 - bW C x X = 2 ^ jH C := by
  have h1 := radix_eq C x X
  have h2 := cH_eq C
  have h3 := H0_ge_1024 C
  have : BW C x X - 1 - bW C x X = H0 C := by omega
  rw [this]; unfold H0; rfl

/-- The first mask. -/
theorem mask1W : τ 2 (gW C x X) (qW C x X ^ 2 - 1 - bW C x X * lW C x X) = 0 := by
  obtain ⟨mB, hBm⟩ := BW_pow C x X
  have hB64 := BW_ge_64 C x X
  have hmB : 0 < mB := by
    rcases Nat.eq_zero_or_pos mB with h | h
    · rw [h] at hBm; omega
    · exact h
  rw [τ_eq_zero_iff_digits _ _ mB hmB]
  intro i
  rw [Iso.digit_pow_two hBm, Iso.digit_pow_two hBm]
  by_cases hi2 : 2 * cL C ≤ i
  · have : (qW C x X ^ 2 - 1 - bW C x X * lW C x X) / BW C x X ^ i = 0 :=
      Nat.div_eq_of_lt (lt_of_lt_of_le (maskW_lt C x X) (Nat.pow_le_pow_right (by omega) hi2))
    rw [this, Nat.zero_mod, Nat.and_zero]
  · push Not at hi2
    rw [mask_digit (crows C) (by omega) (bW_lt_BW C x X) (hKL_W C) (lW_sum C x X) (qW_eq C x X)
      hi2]
    by_cases hiL : i < cL C
    · rw [gW_digit, if_pos hiL]
      by_cases hsupp : i ∈ supp (crows C)
      · rw [(ind_eq_one_iff (crows C) i).2 hsupp, mul_one, BW_sub_bW]
        by_cases him : i ∈ (Finset.univ : Finset (Fin (nphys C.m))).image
            (fun i : Fin (nphys C.m) => v i)
        · obtain ⟨i', _, rfl⟩ := Finset.mem_image.1 him
          rw [gd_v]; exact Iso.land_two_pow_eq_zero (zW_bit C x X i')
        · rw [gd_of_not_mem C x X i him, Nat.zero_and]
      · rw [(ind_eq_zero_iff (crows C) i).2 hsupp, mul_zero, Nat.sub_zero,
          gd_of_not_mem C x X i (fun him => hsupp (image_v_subset_supp C him)), Nat.zero_and]
    · rw [gW_digit, if_neg hiL, Nat.zero_and]

/-- The canonical code as a digit list. -/
theorem code_eq : lW C x X + eW C x X * qW C x X =
    Nat.ofDigits (BW C x X) (ell0d (crows C) (cL C) ++ e0d (crows C) (chel C) (cPX C)) := by
  rw [ofDigits_append_eq, ell0d_length, qW_eq]; unfold lW eW; rfl

theorem ys_digits : ∀ y ∈ ell0d (crows C) (cL C) ++ e0d (crows C) (chel C) (cPX C), y < 2 := by
  intro y hy
  rw [List.mem_append] at hy
  rcases hy with hy | hy
  · have := ell0d_mem_le (crows C) (cL C) y hy; omega
  · have := e0d_mem_le (crows C) (chel C) (cPX C) (layoutOk C) y hy; omega

theorem ys_length : (ell0d (crows C) (cL C) ++ e0d (crows C) (chel C) (cPX C)).length ≤
    2 * cL C := by
  rw [List.length_append, ell0d_length, e0d_length]; have := hKL_W C; omega

/-- The middle mask. -/
theorem mask2W : τ 2 (lW C x X + eW C x X * qW C x X) ((BW C x X - 2) * lamW C x X) = 0 := by
  obtain ⟨mB, hBm⟩ := BW_pow C x X
  have hB64 := BW_ge_64 C x X
  have hmB : 1 ≤ mB := by
    by_contra h; push Not at h
    interval_cases mB; simp at hBm; omega
  have hH := H0_ge_pow C
  have hHB := H0_le_BW C x X
  have key := Jones1982.lemma_2_9 (s := 1) (t := mB) (n := 2 * cL C) (m := 2 * cL C) (k := 2 * cL C)
    le_rfl hmB le_rfl le_rfl (by rw [← hBm, pow_one]; omega)
    (ys := ell0d (crows C) (cL C) ++ e0d (crows C) (chel C) (cPX C))
    (fun y hy => by rw [pow_one]; exact ys_digits C y hy) (by have := ys_length C; omega)
    (Nat.ofDigits (2 ^ mB) (ell0d (crows C) (cL C) ++ e0d (crows C) (chel C) (cPX C)))
  have hmask := (key.1 rfl).2.2
  rw [← hBm] at hmask
  simp only [pow_one] at hmask
  rw [code_eq, θlamW_eq_mask]
  exact hmask

/-- Every paired row vanishes at the constructed digits. -/
theorem hrowsW (hx : 1 ≤ x) (hX : X C.inp = x) (hR : ∀ ρ ∈ C.rows, ρ.Holds X) :
    ∀ R ∈ pairedRows90 C, R.val (x : ℤ) (fun i => (zW C x X i : ℤ)) = 0 := by
  rw [zW_eq]; exact witness_rows90 hx hX hR (by have := jH_ge_ten C; omega)

theorem SN_V0 : SN (gV0 C.m) (zW C x X) = x := by
  rw [zW_eq]; exact witness_V0 (by have := jH_ge_ten C; omega)

theorem SN_V1 : SN (gV1 C.m) (zW C x X) = x := by
  rw [zW_eq]; exact witness_V1 (by have := jH_ge_ten C; omega)

theorem SN_X (hX : X C.inp = x) : SN (gP C.m C.inp) (zW C x X) = x := by
  rw [zW_eq, witness_P (by have := jH_ge_ten C; omega), hX]

/-- Every helper group is `V₀` or `V₁`. -/
theorem chel_mem (j : Fin (cs C)) : chel C j = gV0 C.m ∨ chel C j = gV1 C.m := by
  have hmem := crows_mem C j
  rcases (mem_allRows_iff C _).1 hmem with hh | hl | hu
  · unfold headRows at hh
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hh
    rcases hh with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr h
    · exact Or.inl h
  · unfold l1 at hl
    simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hl
    obtain ⟨R, _, ⟨_, h⟩ | ⟨_, h⟩⟩ := hl
    · exact Or.inr h
    · exact Or.inr h
  · unfold unitPair at hu
    rw [Prod.mk.injEq] at hu
    exact Or.inr hu.2

theorem S_hel (j : Fin (cs C)) : S (chel C j) (fun i => (zW C x X i : ℤ)) = x := by
  rw [S_cast90]
  rcases chel_mem C j with h | h
  · rw [h, SN_V0]
  · rw [h, SN_V1]

theorem hC_W : ((x + gW C x X : ℕ) : ℤ) =
    (Cmain (x : ℤ) (fun i => (zW C x X i : ℤ)) +
      Cdum (cs C) (crows C) (fun _ _ => 0)).eval (BW C x X : ℤ) := by
  rw [eval_Cmain_add_Cdum, gW_sum]
  push_cast
  simp

/-- The decomposition of `σ`. -/
theorem σW_decomp : ∃ High : ℤ, (σW C x X : ℤ) =
    ∑ p ∈ range (K (nphys C.m) (cs C)),
      (D (cs C) (crows C) (chel C) (cPX C) *
        (Cmain (x : ℤ) (fun i => (zW C x X i : ℤ)) +
          Cdum (cs C) (crows C) (fun _ _ => 0)) ^ 2).coeff p * (BW C x X : ℤ) ^ p +
      (BW C x X : ℤ) ^ (K (nphys C.m) (cs C)) * High :=
  sigma_decomp (crows C) (chel C) (cPX C) (layoutOk C) (hKL_W C) (by unfold eW; rfl)
    (by unfold lW; rfl) _ (hC_W C x X) (ESW C x X)

/-- The digits of `σ` below `t₀ − 4M − 4` vanish. -/
theorem σW_low_digit (i : ℕ) (hi : i + 4 * M (nphys C.m) + 4 < t (nphys C.m) (cs C) 0) :
    σW C x X / BW C x X ^ i % BW C x X = 0 := by
  obtain ⟨High, hσ⟩ := σW_decomp C x X
  have hB := BW_ge_64 C x X
  set a : ℕ → ℤ := fun p => (D (cs C) (crows C) (chel C) (cPX C) *
    (Cmain (x : ℤ) (fun i => (zW C x X i : ℤ)) +
      Cdum (cs C) (crows C) (fun _ _ => 0)) ^ 2).coeff p with ha
  obtain ⟨u, hu⟩ : ∃ u, u = t (nphys C.m) (cs C) 0 - 4 * M (nphys C.m) - 4 := ⟨_, rfl⟩
  have huK : u ≤ K (nphys C.m) (cs C) := by
    have := t_mono (m := nphys C.m) (s := cs C) (Nat.zero_le (cs C - 1)); unfold K tl; omega
  have hzero : ∀ p, p < u → a p = 0 := fun p hp =>
    Iso.coeff_mul_eq_zero_of_lt (A := u) (B := 0)
      (fun i hi => coeff_D_eq_zero_of_lt _ _ _ i (by omega))
      (fun j hj => absurd hj (Nat.not_lt_zero _)) (by omega)
  rw [Iso.sum_range_split a _ huK, Finset.sum_eq_zero (fun p hp => by
    rw [hzero p (Finset.mem_range.1 hp), zero_mul]), zero_add] at hσ
  obtain ⟨W, hσW⟩ : ∃ W : ℤ, (σW C x X : ℤ) = (BW C x X : ℤ) ^ u * W := by
    refine ⟨(∑ p ∈ range (K (nphys C.m) (cs C) - u), a (u + p) * (BW C x X : ℤ) ^ p) +
      (BW C x X : ℤ) ^ (K (nphys C.m) (cs C) - u) * High, ?_⟩
    rw [hσ, show (BW C x X : ℤ) ^ (K (nphys C.m) (cs C)) =
      (BW C x X : ℤ) ^ u * (BW C x X : ℤ) ^ (K (nphys C.m) (cs C) - u) by
        rw [← pow_add]; congr 1; omega]
    ring
  have hBu : (0 : ℤ) < (BW C x X : ℤ) ^ u := by positivity
  have hW0 : 0 ≤ W := by
    by_contra hneg
    push Not at hneg
    have : (BW C x X : ℤ) ^ u * W < 0 := mul_neg_of_pos_of_neg hBu hneg
    have : (0 : ℤ) ≤ σW C x X := by exact_mod_cast Nat.zero_le _
    linarith
  obtain ⟨W', hW'⟩ : ∃ W' : ℕ, (W' : ℤ) = W := ⟨W.toNat, Int.toNat_of_nonneg hW0⟩
  have hσN : σW C x X = BW C x X ^ u * W' := by
    have : (σW C x X : ℤ) = ((BW C x X ^ u * W' : ℕ) : ℤ) := by push_cast; rw [hW', hσW]
    exact_mod_cast this
  have hiu : i < u := by omega
  rw [hσN, show u = i + (u - i) by omega, pow_add, mul_assoc,
    Nat.mul_div_cancel_left _ (by positivity)]
  exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _)

theorem hD1_W : 128 * absSum (cD C) * ((nphys C.m : ℤ) + 1) ^ 2 < (BW C x X : ℤ) := by
  have h1 := H0_gt_D1 C
  have h2 : (H0 C : ℤ) ≤ BW C x X := by exact_mod_cast H0_le_BW C x X
  linarith

theorem x_lt_BW : x < BW C x X := lt_trans (x_lt_bW C x X) (bW_lt_BW C x X)

/-- The residue of the window of a start `r`. -/
theorem σW_window (hx : 1 ≤ x) (j : Fin (cs C)) {r : ℕ} (hr : r ∈ starts (cs C) (crows C) j) :
    ((σW C x X / BW C x X ^ r : ℕ) : ℤ) % (BW C x X : ℤ) ^ 3 =
      (L90.a (crows C) (chel C) (cPX C) x (fun i => (zW C x X i : ℤ)) r +
        L90.a (crows C) (chel C) (cPX C) x (fun i => (zW C x X i : ℤ)) (r - 1) / BW C x X) %
        (BW C x X : ℤ) ^ 3 := by
  obtain ⟨High, hσ⟩ := σW_decomp C x X
  exact (window_residue (crows C) (chel C) (cPX C) (layoutOk C) (BW_ge_64 C x X) hx
    (x_lt_BW C x X) (fun i => (zW C x X i : ℤ)) (fun i => by positivity)
    (fun i => by exact_mod_cast (zW_lt_BW C x X i).le) (fun _ _ => 0) (hD1_W C x X) High hσ j
    hr).1

/-- The row value at every row: `0` before the unit rows, `1` at the unit rows. -/
theorem crows_val (hx : 1 ≤ x) (hX : X C.inp = x) (hR : ∀ ρ ∈ C.rows, ρ.Holds X)
    (j : Fin (cs C)) :
    (crows C j).val x (fun i => (zW C x X i : ℤ)) +
      (if (crows C j).xx < 0 then S (chel C j) (fun i => (zW C x X i : ℤ)) ^ 2 else 0) =
      if (preRows C).length ≤ (j : ℕ) then 1 else 0 := by
  have hδ : zW C x X (iδ C.m) = 1 := zW_iδ C x X
  have hδZ : (zW C x X (iδ C.m) : ℤ) = 1 := by exact_mod_cast hδ
  have hS := S_hel C x X j
  by_cases hj : (preRows C).length ≤ (j : ℕ)
  · rw [if_pos hj, (crows_unit C j hj).1, unitRow_val, hδZ]
    rw [if_neg (by simp [unitRow])]; ring
  · rw [if_neg hj]
    push Not at hj
    have hmem : (crows C j, chel C j) ∈ preRows C := by
      have := crows_mem C j
      unfold crows chel at this ⊢
      rw [allRows_getElem_pre C j j.isLt hj]
      exact List.getElem_mem _
    unfold preRows at hmem
    rw [List.mem_append] at hmem
    rcases hmem with hh | hl
    · unfold headRows at hh
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hh
      rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, seedRow_val, if_pos (by simp [seedRow]), hS]; ring
      · rw [h1, seedRow_val, if_pos (by simp [seedRow]), hS]; ring
      · rw [h1, revRow_val, if_neg (by simp [revRow]), S_cast90, SN_V0, hδZ]; ring
      · rw [h1, revRow_val, if_neg (by simp [revRow]), S_cast90, SN_V1, hδZ]; ring
    · unfold l1 at hl
      simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hl
      obtain ⟨R, hR', ⟨h1, _⟩ | ⟨h1, _⟩⟩ := hl
      · obtain ⟨_, _, hxx⟩ := paired_struct C R hR'
        rw [h1, hrowsW C x X hx hX hR R hR', if_neg (by omega)]; ring
      · obtain ⟨_, _, hxx⟩ := paired_struct C R hR'
        rw [h1, negRow_val, hrowsW C x X hx hX hR R hR', if_neg (by simp [negRow, hxx])]; ring

/-- The value shown by the window of a start `r` of row `j`: `1` at the unit rows, `0`
elsewhere. -/
theorem Gval (hx : 1 ≤ x) (hX : X C.inp = x) (hR : ∀ ρ ∈ C.rows, ρ.Holds X) (j : Fin (cs C))
    {r : ℕ} (hr : r ∈ starts (cs C) (crows C) j) :
    L90.a (crows C) (chel C) (cPX C) x (fun i => (zW C x X i : ℤ)) r +
      L90.a (crows C) (chel C) (cPX C) x (fun i => (zW C x X i : ℤ)) (r - 1) / BW C x X =
      if (preRows C).length ≤ (j : ℕ) then 1 else 0 := by
  have hLay := layoutOk C
  have hB := BW_ge_64 C x X
  have h2x := twox_lt_BW C x X
  have hcs := cs_eq C
  have htj := t_ge (nphys C.m) (cs C) j
  -- the value at `r`
  have hval : L90.a (crows C) (chel C) (cPX C) x (fun i => (zW C x X i : ℤ)) r =
      if (preRows C).length ≤ (j : ℕ) then 1 else 0 := by
    rcases (mem_starts (cs C) (crows C)).1 hr with heq | ⟨μ₀, hμ₀, heq⟩
    · rw [heq]
      show (D (cs C) (crows C) (chel C) (cPX C) * Cmain (x : ℤ) _ ^ 2).coeff _ = _
      rw [coeff_at_target (crows C) (chel C) (cPX C) x _ hLay j]
      exact crows_val C x X hx hX hR j
    · rcases card_of_mem_negs (hLay.rows_ok j) hμ₀ with hc | hc
      · rw [heq]
        show (D (cs C) (crows C) (chel C) (cPX C) * Cmain (x : ℤ) _ ^ 2).coeff _ = _
        rw [coeff_at_neg (crows C) (chel C) (cPX C) x _ hLay j hμ₀ hc, S_hel]
        -- a negative position belongs to a row before the unit rows
        have hj : ¬ (preRows C).length ≤ (j : ℕ) := by
          intro hj
          have := (crows_unit C j hj).1
          rw [this] at hμ₀
          simp [negs, terms, unitRow] at hμ₀
        rw [if_neg hj]; ring
      · rw [heq, hc, W_zero, Nat.sub_zero]
        show (D (cs C) (crows C) (chel C) (cPX C) * Cmain (x : ℤ) _ ^ 2).coeff _ = _
        rw [coeff_at_target (crows C) (chel C) (cPX C) x _ hLay j]
        exact crows_val C x X hx hX hR j
  -- the value at `r − 1`
  have hpad : L90.a (crows C) (chel C) (cPX C) x (fun i => (zW C x X i : ℤ)) (r - 1) / BW C x X = 0 := by
    obtain ⟨hb1, hb2⟩ := starts_bounds (crows C) hr
    by_cases hj : (j : ℕ) = cs C - 1
    · have hstart : r = tl (nphys C.m) (cs C) := by
        have hneg := (hLay.last j hj).1
        rcases (mem_starts (cs C) (crows C)).1 hr with h | ⟨μ, hμ, _⟩
        · rw [h]; unfold tl; rw [← hj]
        · rw [hneg] at hμ; simp at hμ
      rw [hstart]
      show (D (cs C) (crows C) (chel C) (cPX C) * Cmain (x : ℤ) _ ^ 2).coeff _ / _ = _
      rw [coeff_at_pad (crows C) (chel C) (cPX C) x _ hLay, ← Finset.mul_sum]
      have hsum : ∑ h ∈ cPX C, (zW C x X h : ℤ) = (SN (gP C.m C.inp) (zW C x X) : ℤ) := by
        unfold cPX; exact Iso.sum_image_group (gP C.m C.inp) (Iso.phys_injective _ _ _) _
      rw [hsum, SN_X C x X hX]
      apply Int.ediv_eq_zero_of_lt (by positivity)
      have : ((2 * x ^ 2 : ℕ) : ℤ) < BW C x X := by exact_mod_cast h2x
      push_cast at this; linarith
    · show (D (cs C) (crows C) (chel C) (cPX C) * Cmain (x : ℤ) _ ^ 2).coeff _ / _ = _
      rw [coeff_at_empty (crows C) (chel C) (cPX C) x _ hLay j hr (r - 1) (by omega) (by omega)
        (by omega) (by omega) (fun _ => hj), Int.zero_ediv]
  rw [hval, hpad, add_zero]

/-- Every digit of `σ` on the indicator support is binary. -/
theorem σW_digit_le_one (hx : 1 ≤ x) (hX : X C.inp = x) (hR : ∀ ρ ∈ C.rows, ρ.Holds X)
    (i : ℕ) (hi : i ∈ supp (crows C)) :
    σW C x X / BW C x X ^ i % BW C x X ≤ 1 := by
  rcases (mem_supp (crows C)).1 hi with ⟨i', rfl⟩ | ⟨r, hr, hir⟩
  · rw [σW_low_digit C x X _ (by
      have := v_le_M i'.isLt; have := t0_ge C; omega)]
    omega
  · obtain ⟨j, hj⟩ := (mem_Rset (cs C) (crows C)).1 hr
    have hres := σW_window C x X hx j hj
    rw [Gval C x X hx hX hR j hj] at hres
    have hB := BW_ge_64 C x X
    have hBZ : (64 : ℤ) ≤ BW C x X := by exact_mod_cast hB
    have hB3 : (1 : ℤ) < (BW C x X : ℤ) ^ 3 := by
      calc (1 : ℤ) < 64 := by norm_num
        _ ≤ BW C x X := hBZ
        _ ≤ (BW C x X : ℤ) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
    set G : ℤ := if (preRows C).length ≤ (j : ℕ) then 1 else 0 with hGdef
    have hG0 : 0 ≤ G := by rw [hGdef]; split_ifs <;> norm_num
    have hG1 : G ≤ 1 := by rw [hGdef]; split_ifs <;> norm_num
    have hGmod : G % (BW C x X : ℤ) ^ 3 = G := Int.emod_eq_of_lt hG0 (by linarith)
    rw [hGmod] at hres
    have hGB : G % (BW C x X : ℤ) = G := Int.emod_eq_of_lt hG0 (by linarith)
    have hGdiv : G / (BW C x X : ℤ) = 0 := Int.ediv_eq_zero_of_lt hG0 (by linarith)
    obtain ⟨c0, c1, c2⟩ := Iso.window_digits_cast (BW C x X) r (σW C x X)
    rw [hres] at c0 c1 c2
    rcases hir with h | h | h <;> rw [h]
    · have : ((σW C x X / BW C x X ^ r % BW C x X : ℕ) : ℤ) ≤ 1 := by
        rw [← c0, hGB]; exact hG1
      have : σW C x X / BW C x X ^ r % BW C x X ≤ 1 := by exact_mod_cast this
      omega
    · have : ((σW C x X / BW C x X ^ (r + 1) % BW C x X : ℕ) : ℤ) ≤ 1 := by
        rw [← c1, hGdiv]; norm_num
      have : σW C x X / BW C x X ^ (r + 1) % BW C x X ≤ 1 := by exact_mod_cast this
      omega
    · have : ((σW C x X / BW C x X ^ (r + 2) % BW C x X : ℕ) : ℤ) ≤ 1 := by
        rw [← c2, hGdiv]; norm_num
      have : σW C x X / BW C x X ^ (r + 2) % BW C x X ≤ 1 := by exact_mod_cast this
      omega

theorem θlW_lt_pow : (BW C x X - 2) * lW C x X < BW C x X ^ (2 * cL C) := by
  have h1 := lW_lt C x X
  have hB := BW_ge_64 C x X
  have h2 : (BW C x X - 2) * lW C x X < BW C x X * BW C x X ^ cK C :=
    Nat.mul_lt_mul_of_le_of_lt (by omega) h1 (by omega)
  have h3 : BW C x X * BW C x X ^ cK C = BW C x X ^ (cK C + 1) := (pow_succ' _ _).symm
  have h4 : BW C x X ^ (cK C + 1) ≤ BW C x X ^ (2 * cL C) :=
    Nat.pow_le_pow_right (by omega) (by have := cK_le_cL C; omega)
  omega

/-- The third mask. -/
theorem mask3W (hx : 1 ≤ x) (hX : X C.inp = x) (hR : ∀ ρ ∈ C.rows, ρ.Holds X) :
    τ 2 (σW C x X) ((BW C x X - 2) * lW C x X) = 0 := by
  obtain ⟨mB, hBm⟩ := BW_pow C x X
  have hB64 := BW_ge_64 C x X
  have hmB : 1 ≤ mB := by
    by_contra h; push Not at h
    interval_cases mB; simp at hBm; omega
  rw [τ_eq_zero_iff_digits _ _ mB (by omega)]
  intro i
  rw [Iso.digit_pow_two hBm, Iso.digit_pow_two hBm]
  by_cases hi2 : 2 * cL C ≤ i
  · have : (BW C x X - 2) * lW C x X / BW C x X ^ i = 0 :=
      Nat.div_eq_of_lt (lt_of_lt_of_le (θlW_lt_pow C x X) (Nat.pow_le_pow_right (by omega) hi2))
    rw [this, Nat.zero_mod, Nat.and_zero]
  · push Not at hi2
    rw [theta_mask_digit (crows C) (by omega) (hKL_W C) rfl (lW_sum C x X) hi2]
    by_cases hsupp : i ∈ supp (crows C)
    · rw [(ind_eq_one_iff (crows C) i).2 hsupp, mul_one]
      have hd := σW_digit_le_one C x X hx hX hR i hsupp
      rw [show BW C x X - 2 = 2 ^ mB - 2 by rw [hBm]]
      exact land_pow_sub_two_eq_zero hmB hd
    · rw [(ind_eq_zero_iff (crows C) i).2 hsupp, mul_zero, Nat.and_zero]

/-- `n² ∣ C(2r, r)`. -/
theorem centralW (hx : 1 ≤ x) (hX : X C.inp = x) (hR : ∀ ρ ∈ C.rows, ρ.Holds X) :
    nW C x X ^ 2 ∣ (2 * rW C x X).choose (rW C x X) := by
  obtain ⟨jq, _, hjq⟩ := qW_pow C x X
  have hq2 : 1 ≤ qW C x X ^ 2 := Nat.one_le_pow _ _ (by have := qW_ge C x X; omega)
  have hg : gW C x X < qW C x X ^ 2 :=
    lt_of_lt_of_le (gW_lt_qW C x X) (Nat.le_self_pow two_ne_zero _)
  have hT1 : qW C x X ^ 2 - 1 - bW C x X * lW C x X < qW C x X ^ 2 := by omega
  have hSl : gW C x X + qW C x X ^ 2 * (lW C x X + eW C x X * qW C x X + qW C x X ^ 2 * σW C x X) <
      qW C x X ^ 7 := by rw [← SW_eq]; exact SW_lt C x X
  have hr : rW C x X = (gW C x X + qW C x X ^ 2 *
      (lW C x X + eW C x X * qW C x X + qW C x X ^ 2 * σW C x X)) * (nW C x X ^ 2 - nW C x X) +
      ((qW C x X ^ 2 - 1 - bW C x X * lW C x X) + (BW C x X - 2) * lamW C x X * qW C x X ^ 2 +
        (BW C x X - 2) * lW C x X * qW C x X ^ 4 + 1) * (nW C x X ^ 2 - 1) := by
    rw [rW_eq, SW_eq, TW_eq]
  have key := masks_iff_central_core (g := gW C x X) (l := lW C x X) (e := eW C x X)
    (q := qW C x X) (σ := σW C x X) (θ := BW C x X - 2) (lam := lamW C x X) (b := bW C x X)
    (n := nW C x X) (r := rW C x X) (jq := jq) hjq (nW_eq C x X) hg hT1 (S2W_lt C x X)
    (θlamW_lt C x X) hSl (TW_lt C x X) (qW7_lt_nW C x X) hr
  exact key.1 ⟨mask1W C x X, mask2W C x X, mask3W C x X hx hX hR⟩

/-- The congruence `E45` with its positive quotient. -/
theorem E45W : ∃ tt : ℕ, 0 < tt ∧
    lW C x X + eW C x X * qW C x X = cV C + tt * (BW C x X - 2) := by
  have hB := BW_ge_64 C x X
  have hV : cV C = Nat.ofDigits 2 (ell0d (crows C) (cL C) ++ e0d (crows C) (chel C) (cPX C)) := by
    unfold cV; rfl
  have hS2 := code_eq C x X
  have hmod : BW C x X ≡ 2 [MOD BW C x X - 2] :=
    ((Nat.modEq_iff_dvd' (by omega)).2 dvd_rfl).symm
  have hcong := Nat.ofDigits_modEq' (BW C x X) 2 (BW C x X - 2) hmod
    (ell0d (crows C) (cL C) ++ e0d (crows C) (chel C) (cPX C))
  have hle : Nat.ofDigits 2 (ell0d (crows C) (cL C) ++ e0d (crows C) (chel C) (cPX C)) ≤
      Nat.ofDigits (BW C x X) (ell0d (crows C) (cL C) ++ e0d (crows C) (chel C) (cPX C)) :=
    Nat.ofDigits_monotone _ (by omega)
  obtain ⟨tt, htt⟩ := (Nat.modEq_iff_dvd' hle).1 hcong.symm
  have hlt : Nat.ofDigits 2 (ell0d (crows C) (cL C) ++ e0d (crows C) (chel C) (cPX C)) <
      Nat.ofDigits (BW C x X) (ell0d (crows C) (cL C) ++ e0d (crows C) (chel C) (cPX C)) := by
    rw [ofDigits_append_eq, ofDigits_append_eq, ell0d_length]
    have h1 : Nat.ofDigits 2 (ell0d (crows C) (cL C)) ≤
        Nat.ofDigits (BW C x X) (ell0d (crows C) (cL C)) :=
      Nat.ofDigits_monotone _ (by omega)
    have h2 : Nat.ofDigits 2 (e0d (crows C) (chel C) (cPX C)) ≤
        Nat.ofDigits (BW C x X) (e0d (crows C) (chel C) (cPX C)) :=
      Nat.ofDigits_monotone _ (by omega)
    have h3 : 1 ≤ Nat.ofDigits (BW C x X) (e0d (crows C) (chel C) (cPX C)) := by
      have := eW_pos C x X; unfold eW at this; exact this
    have h4 : 2 ^ cL C < BW C x X ^ cL C :=
      Nat.pow_lt_pow_left (by omega) (by have := cL_ge C; omega)
    have h5 : Nat.ofDigits 2 (e0d (crows C) (chel C) (cPX C)) * 2 ^ cL C ≤
        Nat.ofDigits (BW C x X) (e0d (crows C) (chel C) (cPX C)) * 2 ^ cL C :=
      Nat.mul_le_mul_right _ h2
    have h6 : Nat.ofDigits (BW C x X) (e0d (crows C) (chel C) (cPX C)) * 2 ^ cL C <
        Nat.ofDigits (BW C x X) (e0d (crows C) (chel C) (cPX C)) * BW C x X ^ cL C :=
      Nat.mul_lt_mul_of_pos_left h4 h3
    omega
  refine ⟨tt, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos tt with h0 | h0
    · rw [h0, mul_zero] at htt; omega
    · exact h0
  · rw [hS2, hV, mul_comm tt]; omega

end Masks

end

end L90

end Jones1980
