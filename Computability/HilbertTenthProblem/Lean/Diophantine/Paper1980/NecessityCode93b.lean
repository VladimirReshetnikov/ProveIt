import Diophantine.Paper1980.NecessityCode93a

/-!
# Necessity: the three masks of the constructed witnesses (Section 7, part 2)

At the constructed witnesses the three masks hold:

* `g & (q² − 1 − bl) = 0`: the digits of `g` vanish off the indicator
  support and have bit `j_H` clear on it, while the mask has digit
  `B − 1 − b = H₀ = 2^{j_H}` there;
* `(l + eq) & θλ = 0`: the canonical code has digits `≤ 3` (Lemma 2.9 of 1982);
* `σ & θl = 0`: below the least exponent of `D` the digits of `σ` vanish, and
  at every tested position the window shows `0` (paired rows) or `1` (unit
  rows), since `7x² < B` kills the padding carries.

Hence `n² ∣ C(2r, r)` (`centralW`).  The file also proves the positivity of
`l, e, g` and the congruence `E45` with its positive quotient `t`.
-/

namespace Jones1980

namespace Iso

open Layout Polynomial Finset
open Diophantine Pell
open Jones1982 (τ)

noncomputable section

/-- A digit `≤ 3` is disjoint from `2^m − 4`. -/
theorem land_pow_sub_four_eq_zero {x m : ℕ} (hm : 2 ≤ m) (hx : x ≤ 3) : x &&& (2 ^ m - 4) = 0 := by
  rw [Jones1982.land_eq_zero_iff]
  intro p hp
  have hp2 : p < 2 := by
    by_contra h
    push Not at h
    have : x.testBit p = false := Nat.testBit_lt_two_pow (lt_of_le_of_lt hx (by
      calc (3 : ℕ) < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) h))
    rw [this] at hp; exact absurd hp (by decide)
  have e : 2 ^ m - 4 = (2 ^ (m - 2) - 1) * 2 ^ 2 := by
    have : 2 ^ m = 2 ^ (m - 2) * 2 ^ 2 := by rw [← pow_add]; congr 1; omega
    rw [this, Nat.sub_mul, one_mul]; norm_num
  rw [e, Nat.testBit_mul_two_pow]
  simp [show ¬ (2 ≤ p) by omega]

/-- A number with bit `j` clear is disjoint from `2^j`. -/
theorem land_two_pow_eq_zero {x j : ℕ} (h : x.testBit j = false) : x &&& 2 ^ j = 0 := by
  rw [Jones1982.land_eq_zero_iff]
  intro p hp
  rw [Nat.testBit_two_pow, decide_eq_false_iff_not]
  intro hjp
  rw [← hjp, h] at hp
  exact absurd hp (by decide)

/-- Every coefficient of `D` below `t₀ − 2M` vanishes. -/
theorem coeff_D_eq_zero_of_lt {m s : ℕ} (rows : Fin s → Row m) (P5 P7 : Finset (Fin m)) (h : ℕ)
    (hh : h + 2 * M m < t m s 0) : (D m s rows P5 P7).coeff h = 0 := by
  rw [coeff_D]
  have hM : 6 ≤ M m := by
    unfold M; have := Nat.one_le_pow (m - 1) 3 (by norm_num); omega
  have h1 : ∑ j : Fin s, (rowPoly m s j (rows j)).coeff h = 0 := Finset.sum_eq_zero fun j _ => by
    by_contra hne
    have := (coeff_rowPoly_ne_zero j (rows j) h hne).2.1
    have := t_mono (m := m) (s := s) (Nat.zero_le (j : ℕ)); omega
  have h2 : ∑ j : Fin s, (resetPoly m s j).coeff h = 0 := Finset.sum_eq_zero fun j _ => by
    rw [coeff_resetPoly, if_neg]
    have := t_mono (m := m) (s := s) (Nat.zero_le (j : ℕ)); omega
  have h3 : ∀ (k : ℕ) (P : Finset (Fin m)), (padPoly m s k P).coeff h = 0 := fun k P => by
    by_contra hne
    have := (coeff_padPoly_ne_zero k P h hne).2.1
    have := t_mono (m := m) (s := s) (Nat.zero_le k); omega
  rw [h1, h2, h3, h3]; rfl

section Masks

variable (C : Gates.Circuit) (x : ℕ) (X : Fin C.m → ℕ)

theorem zW_eq : zW C x X = assign C.m X x (jH C) := by unfold zW; rfl

theorem zW_bit (i : Fin (nphys C.m)) : (zW C x X i).testBit (jH C) = false := by
  rw [zW_eq]; exact assign_bit _ _ _ _ (by have := jH_ge_ten C; omega) i

theorem zW_iδ : zW C x X (iδ C.m) = 1 := by rw [zW_eq]; exact assign_iδ _ _ _ _

theorem M_lt_t0 : 3 * M (nphys C.m) + 6 ≤ t (nphys C.m) (cs C) 0 := by
  have := t_zero_gt (nphys C.m) (cs C); have := d0_gt (nphys C.m); unfold d0 at *; omega

theorem hKL_W : K (nphys C.m) (cs C) ≤ cL C := by rw [← cK_eq]; have := cK_le_cL C; omega

theorem v_lt_cL (i : Fin (nphys C.m)) : v i < cL C := by
  have := v_le_M i.2; have := M_lt_t0 C
  have : t (nphys C.m) (cs C) 0 ≤ t (nphys C.m) (cs C) (cs C - 1) := t_mono (Nat.zero_le _)
  have := hKL_W C; unfold K at *; omega

/-- The digit function of `g`. -/
def gd (h : ℕ) : ℕ := ∑ i : Fin (nphys C.m), if h = v i then zW C x X i else 0

theorem gd_v (i : Fin (nphys C.m)) : gd C x X (v i) = zW C x X i := by
  unfold gd
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk; rw [if_neg]; intro h; exact hk (v_inj h).symm
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
  exact digit_sum (by have := BW_ge_64 C x X; omega) i _ (gd_lt C x X) (cL C)

theorem gW_lt_pow : gW C x X < BW C x X ^ cL C := by
  have := gW_lt C x X
  have := Nat.pow_le_pow_right (by have := BW_ge_64 C x X; omega : 1 ≤ BW C x X) (cK_le_cL C)
  have : BW C x X ^ cK C ≤ BW C x X ^ (cK C + 1) :=
    Nat.pow_le_pow_right (by have := BW_ge_64 C x X; omega) (by omega)
  omega

theorem maskW_lt : qW C x X ^ 2 - 1 - bW C x X * lW C x X < BW C x X ^ (2 * cL C) := by
  have : qW C x X ^ 2 = BW C x X ^ (2 * cL C) := by rw [qW_eq, ← pow_mul, mul_comm]
  have : 1 ≤ qW C x X ^ 2 := Nat.one_le_pow _ _ (by have := qW_ge C x X; omega)
  omega

theorem image_v_subset_supp {i : ℕ}
    (hi : i ∈ (Finset.univ : Finset (Fin (nphys C.m))).image (fun i : Fin (nphys C.m) => v i)) :
    i ∈ supp (nphys C.m) (cs C) := by
  obtain ⟨i', _, rfl⟩ := Finset.mem_image.1 hi
  unfold supp
  exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨i', Finset.mem_range.2 i'.isLt, rfl⟩)

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
  rw [digit_pow_two hBm, digit_pow_two hBm]
  by_cases hi2 : 2 * cL C ≤ i
  · have : (qW C x X ^ 2 - 1 - bW C x X * lW C x X) / BW C x X ^ i = 0 :=
      Nat.div_eq_of_lt (lt_of_lt_of_le (maskW_lt C x X) (Nat.pow_le_pow_right (by omega) hi2))
    rw [this, Nat.zero_mod, Nat.and_zero]
  · push Not at hi2
    rw [mask_digit (m := nphys C.m) (s := cs C) (by omega) (bW_lt_BW C x X) (hKL_W C)
      (lW_sum C x X) (qW_eq C x X) hi2]
    by_cases hiL : i < cL C
    · rw [gW_digit, if_pos hiL]
      by_cases hsupp : i ∈ supp (nphys C.m) (cs C)
      · rw [(ind_eq_one_iff i).2 hsupp, mul_one, BW_sub_bW]
        by_cases him : i ∈ (Finset.univ : Finset (Fin (nphys C.m))).image
            (fun i : Fin (nphys C.m) => v i)
        · obtain ⟨i', _, rfl⟩ := Finset.mem_image.1 him
          rw [gd_v]; exact land_two_pow_eq_zero (zW_bit C x X i')
        · rw [gd_of_not_mem C x X i him, Nat.zero_and]
      · rw [(ind_eq_zero_iff i).2 hsupp, mul_zero, Nat.sub_zero,
          gd_of_not_mem C x X i (fun him => hsupp (image_v_subset_supp C him)), Nat.zero_and]
    · rw [gW_digit, if_neg hiL, Nat.zero_and]

/-- The canonical code as a digit list. -/
theorem code_eq : lW C x X + eW C x X * qW C x X =
    Nat.ofDigits (BW C x X) (ell0d (nphys C.m) (cs C) (cL C) ++ e0d (nphys C.m) (cs C) (cD C)) := by
  rw [ofDigits_append_eq, ell0d_length, qW_eq]; unfold lW eW; rfl

theorem ys_digits : ∀ y ∈ ell0d (nphys C.m) (cs C) (cL C) ++ e0d (nphys C.m) (cs C) (cD C), y < 4 := by
  intro y hy
  rw [List.mem_append] at hy
  rcases hy with hy | hy
  · have := ell0d_mem_le (nphys C.m) (cs C) (cL C) y hy; omega
  · have := e0d_mem_le (nphys C.m) (cs C) (cD C) (cD_abs C) y hy; omega

theorem ys_length : (ell0d (nphys C.m) (cs C) (cL C) ++ e0d (nphys C.m) (cs C) (cD C)).length ≤
    2 * cL C := by
  rw [List.length_append, ell0d_length, e0d_length]; have := hKL_W C; omega

/-- The middle mask. -/
theorem mask2W : τ 2 (lW C x X + eW C x X * qW C x X) ((BW C x X - 4) * lamW C x X) = 0 := by
  obtain ⟨mB, hBm⟩ := BW_pow C x X
  have hB64 := BW_ge_64 C x X
  have hmB : 2 ≤ mB := by
    by_contra h; push Not at h
    interval_cases mB <;> simp at hBm <;> omega
  have hH := H0_ge_pow C
  have hHB := H0_le_BW C x X
  have key := Jones1982.lemma_2_9 (s := 2) (t := mB) (n := 2 * cL C) (m := 2 * cL C) (k := 2 * cL C)
    (by norm_num) hmB le_rfl le_rfl (by rw [← hBm]; norm_num; omega)
    (ys := ell0d (nphys C.m) (cs C) (cL C) ++ e0d (nphys C.m) (cs C) (cD C))
    (by have := ys_digits C; simpa using this) (by have := ys_length C; omega)
    (Nat.ofDigits (2 ^ mB) (ell0d (nphys C.m) (cs C) (cL C) ++ e0d (nphys C.m) (cs C) (cD C)))
  have hmask := (key.1 rfl).2.2
  rw [← hBm] at hmask
  rw [code_eq, θlamW_eq_mask]
  simpa using hmask

/-- Every paired row vanishes at the constructed digits. -/
theorem hrowsW (hx : 1 ≤ x) (hX : X C.inp = x) (hR : ∀ ρ ∈ C.rows, ρ.Holds X) :
    ∀ R ∈ pairedRows C, R.val (x : ℤ) (fun i => (zW C x X i : ℤ)) = 0 := by
  rw [zW_eq]; exact witness_rows hx hX hR (by have := jH_ge_ten C; omega)

theorem hC_W : ((x + gW C x X : ℕ) : ℤ) =
    (Cmain (nphys C.m) (x : ℤ) (fun i => (zW C x X i : ℤ)) +
      Cdum (nphys C.m) (cs C) (fun _ _ => 0)).eval (BW C x X : ℤ) := by
  rw [eval_Cmain_add_Cdum, gW_sum]
  push_cast
  simp

/-- The decomposition of `σ`. -/
theorem σW_decomp : ∃ High : ℤ, (σW C x X : ℤ) =
    ∑ p ∈ range (K (nphys C.m) (cs C)),
      (D (nphys C.m) (cs C) (crows C) (P5 C) (P7 C) *
        (Cmain (nphys C.m) (x : ℤ) (fun i => (zW C x X i : ℤ)) +
          Cdum (nphys C.m) (cs C) (fun _ _ => 0)) ^ 2).coeff p * (BW C x X : ℤ) ^ p +
      (BW C x X : ℤ) ^ (K (nphys C.m) (cs C)) * High :=
  sigma_decomp (crows C) (P5 C) (P7 C) (by have := three_le_cs C; omega)
    (by have := BW_ge_64 C x X; omega) (hKL_W C)
    (by rw [lamW_mul, qW_eq, ← pow_mul, mul_comm (cL C) 2]) (eW_cast C x X) (qW_eq C x X) _
    (hC_W C x X) (ESW C x X)

/-- The digits of `σ` below `t₀ − 2M` vanish. -/
theorem σW_low_digit (i : ℕ) (hi : i + 2 * M (nphys C.m) < t (nphys C.m) (cs C) 0) :
    σW C x X / BW C x X ^ i % BW C x X = 0 := by
  obtain ⟨High, hσ⟩ := σW_decomp C x X
  have hB := BW_ge_64 C x X
  set a : ℕ → ℤ := fun p => (D (nphys C.m) (cs C) (crows C) (P5 C) (P7 C) *
    (Cmain (nphys C.m) (x : ℤ) (fun i => (zW C x X i : ℤ)) +
      Cdum (nphys C.m) (cs C) (fun _ _ => 0)) ^ 2).coeff p with ha
  obtain ⟨u, hu⟩ : ∃ u, u = t (nphys C.m) (cs C) 0 - 2 * M (nphys C.m) := ⟨_, rfl⟩
  have huK : u ≤ K (nphys C.m) (cs C) := by
    have := t_mono (m := nphys C.m) (s := cs C) (Nat.zero_le (cs C - 1)); unfold K; omega
  have hzero : ∀ p, p < u → a p = 0 := fun p hp =>
    coeff_mul_eq_zero_of_lt (A := u) (B := 0)
      (fun i hi => coeff_D_eq_zero_of_lt _ _ _ i (by omega))
      (fun j hj => absurd hj (Nat.not_lt_zero _)) (by omega)
  rw [sum_range_split a _ huK, Finset.sum_eq_zero (fun p hp => by
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

/-- The residue of the window of target `j`. -/
theorem σW_window (hx : 1 ≤ x) (j : Fin (cs C)) :
    ((σW C x X / BW C x X ^ (t (nphys C.m) (cs C) j) : ℕ) : ℤ) % (BW C x X : ℤ) ^ 3 =
      ((crows C j).val x (fun i => (zW C x X i : ℤ)) +
        padVal (P5 C) (P7 C) x (fun i => (zW C x X i : ℤ)) j / BW C x X) % (BW C x X : ℤ) ^ 3 := by
  obtain ⟨High, hσ⟩ := σW_decomp C x X
  exact (window_residue (crows C) (P5 C) (P7 C) (three_le_cs C) (BW_ge_64 C x X) hx
    (x_lt_BW C x X) (fun i => (zW C x X i : ℤ)) (fun i => by positivity)
    (fun i => by exact_mod_cast (zW_lt_BW C x X i).le) (fun _ _ => 0) (hD1_W C x X) High hσ j
    (crows_valid C j).cross).1

theorem crows_mem_l1 (j : Fin (cs C)) (hj : (j : ℕ) + 3 < cs C) : crows C j ∈ l1 C := by
  unfold crows allRows
  have hlen := cs_eq C
  rw [List.getElem_append_left (by omega)]
  exact List.getElem_mem _

theorem paired_val_zero (hx : 1 ≤ x) (hX : X C.inp = x) (hR : ∀ ρ ∈ C.rows, ρ.Holds X)
    (j : Fin (cs C)) (hj : (j : ℕ) + 3 < cs C) :
    (crows C j).val x (fun i => (zW C x X i : ℤ)) = 0 := by
  have hmem := crows_mem_l1 C j hj
  unfold l1 at hmem
  rw [List.mem_flatMap] at hmem
  obtain ⟨R, hR', hmem⟩ := hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  have h0 := hrowsW C x X hx hX hR R hR'
  rcases hmem with h | h <;> rw [h]
  · exact h0
  · rw [negRow_val, h0, neg_zero]

/-- The value shown by the window of target `j`: `0` at a paired row, `1` at a unit row. -/
theorem Gval (hx : 1 ≤ x) (hX : X C.inp = x) (hR : ∀ ρ ∈ C.rows, ρ.Holds X) (j : Fin (cs C)) :
    (crows C j).val x (fun i => (zW C x X i : ℤ)) +
      padVal (P5 C) (P7 C) x (fun i => (zW C x X i : ℤ)) j / BW C x X =
      if cs C ≤ (j : ℕ) + 3 then 1 else 0 := by
  have hs3 := three_le_cs C
  have hB := BW_ge_64 C x X
  have h7 := sevenx_lt_BW C x X
  by_cases hj : cs C ≤ (j : ℕ) + 3
  · rw [if_pos hj, crows_unit C j hj, unitRow_val, zW_iδ]
    obtain ⟨hp5, hp7⟩ := decode_pads (hrowsW C x X hx hX hR)
    have h5 : (5 * (x : ℤ) ^ 2) / BW C x X = 0 :=
      Int.ediv_eq_zero_of_lt (by positivity) (by
        have : (5 * x ^ 2 : ℕ) < BW C x X := by omega
        exact_mod_cast this)
    have h7' : (7 * (x : ℤ) ^ 2) / BW C x X = 0 :=
      Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast h7)
    have hj3 : (j : ℕ) = cs C - 3 ∨ (j : ℕ) = cs C - 2 ∨ (j : ℕ) = cs C - 1 := by
      have := j.isLt; omega
    rcases hj3 with h | h | h
    · rw [padVal_of_lt (P5 C) (P7 C) _ _ j (by omega), Int.zero_ediv]
      all_goals (push_cast; try ring)
    · unfold padVal
      rw [if_pos (by omega), if_neg (by omega), ← Finset.mul_sum, hp5, add_zero,
        show (x : ℤ) ^ 2 + 2 * x * (2 * x) = 5 * (x : ℤ) ^ 2 by ring, h5]
      all_goals (push_cast; try ring)
    · unfold padVal
      rw [if_neg (by omega), if_pos (by omega), ← Finset.mul_sum, hp7, zero_add,
        show (x : ℤ) ^ 2 + 2 * x * (3 * x) = 7 * (x : ℤ) ^ 2 by ring, h7']
      all_goals (push_cast; try ring)
  · rw [if_neg hj, paired_val_zero C x X hx hX hR j (by omega),
      padVal_of_lt (P5 C) (P7 C) _ _ j (by omega), Int.zero_ediv, add_zero]

/-- Every digit of `σ` on the indicator support is at most three. -/
theorem σW_digit_le_three (hx : 1 ≤ x) (hX : X C.inp = x) (hR : ∀ ρ ∈ C.rows, ρ.Holds X)
    (i : ℕ) (hi : i ∈ supp (nphys C.m) (cs C)) :
    σW C x X / BW C x X ^ i % BW C x X ≤ 3 := by
  unfold supp at hi
  rw [Finset.mem_union] at hi
  rcases hi with hi | hi
  · rw [Finset.mem_image] at hi
    obtain ⟨i', hi', rfl⟩ := hi
    rw [σW_low_digit C x X _ (by
      have := v_le_M (Finset.mem_range.1 hi'); have := M_lt_t0 C; omega)]
    omega
  · rw [Finset.mem_biUnion] at hi
    obtain ⟨j, hj, hij⟩ := hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hij
    have hjs : j < cs C := Finset.mem_range.1 hj
    have hres := σW_window C x X hx ⟨j, hjs⟩
    rw [Gval C x X hx hX hR] at hres
    simp only [Fin.val_mk] at hres
    have hB := BW_ge_64 C x X
    have hBZ : (64 : ℤ) ≤ BW C x X := by exact_mod_cast hB
    have hB3 : (1 : ℤ) < (BW C x X : ℤ) ^ 3 := by
      calc (1 : ℤ) < 64 := by norm_num
        _ ≤ BW C x X := hBZ
        _ ≤ (BW C x X : ℤ) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
    set G : ℤ := if cs C ≤ j + 3 then 1 else 0 with hGdef
    have hG0 : 0 ≤ G := by rw [hGdef]; split_ifs <;> norm_num
    have hG1 : G ≤ 1 := by rw [hGdef]; split_ifs <;> norm_num
    have hGmod : G % (BW C x X : ℤ) ^ 3 = G := Int.emod_eq_of_lt hG0 (by linarith)
    rw [hGmod] at hres
    have hGB : G % (BW C x X : ℤ) = G := Int.emod_eq_of_lt hG0 (by linarith)
    have hGdiv : G / (BW C x X : ℤ) = 0 := Int.ediv_eq_zero_of_lt hG0 (by linarith)
    obtain ⟨c0, c1, c2⟩ := window_digits_cast (BW C x X) (t (nphys C.m) (cs C) j) (σW C x X)
    rw [hres] at c0 c1 c2
    rcases hij with rfl | rfl | rfl
    · have : ((σW C x X / BW C x X ^ (t (nphys C.m) (cs C) j) % BW C x X : ℕ) : ℤ) ≤ 1 := by
        rw [← c0, hGB]; exact hG1
      have : σW C x X / BW C x X ^ (t (nphys C.m) (cs C) j) % BW C x X ≤ 1 := by exact_mod_cast this
      omega
    · have : ((σW C x X / BW C x X ^ (t (nphys C.m) (cs C) j + 1) % BW C x X : ℕ) : ℤ) ≤ 1 := by
        rw [← c1, hGdiv]; norm_num
      have : σW C x X / BW C x X ^ (t (nphys C.m) (cs C) j + 1) % BW C x X ≤ 1 := by
        exact_mod_cast this
      omega
    · have : ((σW C x X / BW C x X ^ (t (nphys C.m) (cs C) j + 2) % BW C x X : ℕ) : ℤ) ≤ 1 := by
        rw [← c2, hGdiv]; norm_num
      have : σW C x X / BW C x X ^ (t (nphys C.m) (cs C) j + 2) % BW C x X ≤ 1 := by
        exact_mod_cast this
      omega

theorem θlW_lt_pow : (BW C x X - 4) * lW C x X < BW C x X ^ (2 * cL C) := by
  have h1 := lW_lt C x X
  have hB := BW_ge_64 C x X
  have h2 : (BW C x X - 4) * lW C x X < BW C x X * BW C x X ^ cK C :=
    Nat.mul_lt_mul_of_le_of_lt (by omega) h1 (by omega)
  have h3 : BW C x X * BW C x X ^ cK C = BW C x X ^ (cK C + 1) := (pow_succ' _ _).symm
  have h4 : BW C x X ^ (cK C + 1) ≤ BW C x X ^ (2 * cL C) :=
    Nat.pow_le_pow_right (by omega) (by have := cK_le_cL C; omega)
  omega

/-- The third mask. -/
theorem mask3W (hx : 1 ≤ x) (hX : X C.inp = x) (hR : ∀ ρ ∈ C.rows, ρ.Holds X) :
    τ 2 (σW C x X) ((BW C x X - 4) * lW C x X) = 0 := by
  obtain ⟨mB, hBm⟩ := BW_pow C x X
  have hB64 := BW_ge_64 C x X
  have hmB : 2 ≤ mB := by
    by_contra h; push Not at h
    interval_cases mB <;> simp at hBm <;> omega
  rw [τ_eq_zero_iff_digits _ _ mB (by omega)]
  intro i
  rw [digit_pow_two hBm, digit_pow_two hBm]
  by_cases hi2 : 2 * cL C ≤ i
  · have : (BW C x X - 4) * lW C x X / BW C x X ^ i = 0 :=
      Nat.div_eq_of_lt (lt_of_lt_of_le (θlW_lt_pow C x X) (Nat.pow_le_pow_right (by omega) hi2))
    rw [this, Nat.zero_mod, Nat.and_zero]
  · push Not at hi2
    rw [theta_mask_digit (m := nphys C.m) (s := cs C) (by omega) (hKL_W C) rfl (lW_sum C x X) hi2]
    by_cases hsupp : i ∈ supp (nphys C.m) (cs C)
    · rw [(ind_eq_one_iff i).2 hsupp, mul_one]
      have hd := σW_digit_le_three C x X hx hX hR i hsupp
      rw [show BW C x X - 4 = 2 ^ mB - 4 by rw [hBm]]
      exact land_pow_sub_four_eq_zero hmB hd
    · rw [(ind_eq_zero_iff i).2 hsupp, mul_zero, Nat.and_zero]

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
      ((qW C x X ^ 2 - 1 - bW C x X * lW C x X) + (BW C x X - 4) * lamW C x X * qW C x X ^ 2 +
        (BW C x X - 4) * lW C x X * qW C x X ^ 4 + 1) * (nW C x X ^ 2 - 1) := by
    rw [rW_eq, SW_eq, TW_eq]
  have key := masks_iff_central_core (g := gW C x X) (l := lW C x X) (e := eW C x X)
    (q := qW C x X) (σ := σW C x X) (θ := BW C x X - 4) (lam := lamW C x X) (b := bW C x X)
    (n := nW C x X) (r := rW C x X) (jq := jq) hjq (nW_eq C x X) hg hT1 (S2W_lt C x X)
    (θlamW_lt C x X) hSl (TW_lt C x X) (qW7_lt_nW C x X) hr
  exact key.1 ⟨mask1W C x X, mask2W C x X, mask3W C x X hx hX hR⟩

/-- `e > 0`: its unit digit is one. -/
theorem eW_pos : 0 < eW C x X := by
  have h := eW_cast C x X
  have hK : 0 < K (nphys C.m) (cs C) := by unfold K; omega
  have hD0 : (cD C).coeff 0 = 0 :=
    coeff_D_eq_zero_of_lt _ _ _ 0 (by have := M_lt_t0 C; omega)
  have : (1 : ℤ) ≤ eW C x X := by
    rw [h]
    calc (1 : ℤ) = (1 + (cD C).coeff 0) * (BW C x X : ℤ) ^ 0 := by rw [hD0]; simp
      _ ≤ ∑ h ∈ range (K (nphys C.m) (cs C)), (1 + (cD C).coeff h) * (BW C x X : ℤ) ^ h :=
        Finset.single_le_sum (f := fun h => (1 + (cD C).coeff h) * (BW C x X : ℤ) ^ h) (a := 0)
          (fun h _ => mul_nonneg (by linarith [abs_le.1 (cD_abs C h)]) (by positivity))
          (Finset.mem_range.2 hK)
  exact_mod_cast this

theorem v_iδ_mem_supp : v (iδ C.m) ∈ supp (nphys C.m) (cs C) :=
  image_v_subset_supp C (Finset.mem_image.2 ⟨iδ C.m, Finset.mem_univ _, rfl⟩)

theorem lW_pos : 0 < lW C x X := by
  rw [lW_sum]
  have hmem : v (iδ C.m) ∈ range (cL C) := Finset.mem_range.2 (v_lt_cL C _)
  have h := Finset.single_le_sum (f := fun h => ind (nphys C.m) (cs C) h * BW C x X ^ h)
    (fun _ _ => Nat.zero_le _) hmem
  rw [(ind_eq_one_iff _).2 (v_iδ_mem_supp C), one_mul] at h
  have : 0 < BW C x X ^ v (iδ C.m) := by have := BW_ge_64 C x X; positivity
  omega

theorem gW_pos : 0 < gW C x X := by
  rw [gW_sum]
  have h := Finset.single_le_sum (f := fun i : Fin (nphys C.m) => zW C x X i * BW C x X ^ (v i))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (iδ C.m))
  rw [zW_iδ, one_mul] at h
  have : 0 < BW C x X ^ v (iδ C.m) := by have := BW_ge_64 C x X; positivity
  omega

/-- The congruence `E45` with its positive quotient. -/
theorem E45W : ∃ tt : ℕ, 0 < tt ∧
    lW C x X + eW C x X * qW C x X = cV C + tt * (BW C x X - 4) := by
  have hB := BW_ge_64 C x X
  have hV : cV C = Nat.ofDigits 4 (ell0d (nphys C.m) (cs C) (cL C) ++ e0d (nphys C.m) (cs C) (cD C)) := by
    unfold cV; rfl
  have hS2 := code_eq C x X
  have hmod : BW C x X ≡ 4 [MOD BW C x X - 4] :=
    ((Nat.modEq_iff_dvd' (by omega)).2 dvd_rfl).symm
  have hcong := Nat.ofDigits_modEq' (BW C x X) 4 (BW C x X - 4) hmod
    (ell0d (nphys C.m) (cs C) (cL C) ++ e0d (nphys C.m) (cs C) (cD C))
  have hle : Nat.ofDigits 4 (ell0d (nphys C.m) (cs C) (cL C) ++ e0d (nphys C.m) (cs C) (cD C)) ≤
      Nat.ofDigits (BW C x X) (ell0d (nphys C.m) (cs C) (cL C) ++ e0d (nphys C.m) (cs C) (cD C)) :=
    Nat.ofDigits_monotone _ (by omega)
  obtain ⟨tt, htt⟩ := (Nat.modEq_iff_dvd' hle).1 hcong.symm
  have hlt : Nat.ofDigits 4 (ell0d (nphys C.m) (cs C) (cL C) ++ e0d (nphys C.m) (cs C) (cD C)) <
      Nat.ofDigits (BW C x X) (ell0d (nphys C.m) (cs C) (cL C) ++ e0d (nphys C.m) (cs C) (cD C)) := by
    rw [ofDigits_append_eq, ofDigits_append_eq, ell0d_length]
    have h1 : Nat.ofDigits 4 (ell0d (nphys C.m) (cs C) (cL C)) ≤
        Nat.ofDigits (BW C x X) (ell0d (nphys C.m) (cs C) (cL C)) :=
      Nat.ofDigits_monotone _ (by omega)
    have h2 : Nat.ofDigits 4 (e0d (nphys C.m) (cs C) (cD C)) ≤
        Nat.ofDigits (BW C x X) (e0d (nphys C.m) (cs C) (cD C)) :=
      Nat.ofDigits_monotone _ (by omega)
    have h3 : 1 ≤ Nat.ofDigits (BW C x X) (e0d (nphys C.m) (cs C) (cD C)) := by
      have := eW_pos C x X; unfold eW at this; exact this
    have h4 : 4 ^ cL C < BW C x X ^ cL C :=
      Nat.pow_lt_pow_left (by omega) (by have := cL_ge C; omega)
    have h5 : Nat.ofDigits 4 (e0d (nphys C.m) (cs C) (cD C)) * 4 ^ cL C ≤
        Nat.ofDigits (BW C x X) (e0d (nphys C.m) (cs C) (cD C)) * 4 ^ cL C :=
      Nat.mul_le_mul_right _ h2
    have h6 : Nat.ofDigits (BW C x X) (e0d (nphys C.m) (cs C) (cD C)) * 4 ^ cL C <
        Nat.ofDigits (BW C x X) (e0d (nphys C.m) (cs C) (cD C)) * BW C x X ^ cL C :=
      Nat.mul_lt_mul_of_pos_left h4 h3
    omega
  refine ⟨tt, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos tt with h0 | h0
    · rw [h0, mul_zero] at htt; omega
    · exact h0
  · rw [hS2, hV, mul_comm tt]; omega

end Masks

end

end Iso

end Jones1980
