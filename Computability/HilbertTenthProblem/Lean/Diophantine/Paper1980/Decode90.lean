import Diophantine.Paper1980.Compile90c
import Diophantine.Paper1980.Windows90
import Diophantine.Paper1980.Unit90
import Diophantine.Paper1980.Pell90
import Diophantine.Paper1980.Pack90

/-!
# Sufficiency: a positive solution of the 90-operation system decodes to an
accepting computation (Sections 4–6 of `BINARY_PRODUCT_90_PROOF.md`)

For a circuit `C` the layout is that of `Compile90b.lean`; the fixed index is
`K = t_last + 3`, `L = 3K + 3`, `H₀ = 2^{j_H}` a power of two exceeding
`2·2^{2L+1}`, `128 D₁ (m+1)²`, `3L + 3` and `1024`, `H = H₀ − 1`,
`V = ℓ₀(2) + e₀(2) 2^L`, `Tindex = ψ₂(L)`.

`sufficiency`: if the system has a positive solution at input `x > 0` then `C`
accepts `x`.  The proof runs through the Pell block, the three masks, the
canonical binary code, the digit reading of `g`, the decomposition of `σ`, the
windows of all targets, the seeds (`Vᵢ ≥ x`), the vanishing of the paired rows
(`δ > 0`), the reverses (`Vᵢ ≤ x`), the two binary unit tests forcing `δ = 1`,
and the decoding of the circuit rows.
-/

namespace Jones1980

namespace L90

open Layout (Row)
open Polynomial Finset
open Diophantine Pell
open Jones1982 (τ)
open Iso (absSum absSum_nonneg nphys gP gQ gR gU iδ iδ' SN S_cast negRow negRow_val unitRow
  unitRow_val)

noncomputable section

section LayoutOfCircuit

variable (C : Gates.Circuit)

/-- The fixed index. -/
@[irreducible] def cK : ℕ := K (nphys C.m) (cs C)
@[irreducible] def cL : ℕ := 3 * cK C + 3
def cD : ℤ[X] := D (cs C) (crows C) (chel C) (cPX C)
@[irreducible] def cD1 : ℕ := (absSum (cD C)).toNat
@[irreducible] def jH : ℕ :=
  2 * cL C + 2 + 128 * cD1 C * (nphys C.m + 1) ^ 2 + 3 * cL C + 3 + 10
@[irreducible] def H0 : ℕ := 2 ^ jH C
@[irreducible] def cH : ℕ := H0 C - 1
@[irreducible] def cV : ℕ :=
  Nat.ofDigits 2 (ell0d (crows C) (cL C) ++ e0d (crows C) (chel C) (cPX C))
@[irreducible] def cT : ℕ := yn Exp90.two_lt_one (cL C)

theorem jH_ge_pow : 2 * cL C + 2 ≤ jH C := by unfold jH; omega
theorem jH_ge_D1 : 128 * cD1 C * (nphys C.m + 1) ^ 2 ≤ jH C := by unfold jH; omega
theorem jH_ge_L : 3 * cL C + 3 ≤ jH C := by unfold jH; omega
theorem jH_ge_ten : 10 ≤ jH C := by unfold jH; omega

theorem H0_ge_pow : 2 * 2 ^ (2 * cL C + 1) ≤ H0 C := by
  have e : 2 * 2 ^ (2 * cL C + 1) = 2 ^ (2 * cL C + 2) := by rw [pow_succ]; ring
  rw [e]
  unfold H0
  exact Nat.pow_le_pow_right (by norm_num) (jH_ge_pow C)

theorem H0_gt_D1 : 128 * absSum (cD C) * ((nphys C.m : ℤ) + 1) ^ 2 < (H0 C : ℤ) := by
  have h1 : 128 * cD1 C * (nphys C.m + 1) ^ 2 < H0 C := by
    unfold H0
    calc 128 * cD1 C * (nphys C.m + 1) ^ 2 ≤ jH C := jH_ge_D1 C
      _ < 2 ^ jH C := Nat.lt_two_pow_self
  have h2 : absSum (cD C) = (cD1 C : ℤ) := by
    unfold cD1; rw [Int.toNat_of_nonneg (absSum_nonneg _)]
  rw [h2]; exact_mod_cast h1

theorem H0_ge_L : 3 * cL C + 3 ≤ H0 C := by
  unfold H0
  calc 3 * cL C + 3 ≤ jH C := jH_ge_L C
    _ ≤ 2 ^ jH C := Nat.lt_two_pow_self.le

theorem H0_ge_1024 : 1024 ≤ H0 C := by
  unfold H0
  calc 1024 = 2 ^ 10 := by norm_num
    _ ≤ 2 ^ jH C := Nat.pow_le_pow_right (by norm_num) (jH_ge_ten C)

theorem cK_eq : cK C = K (nphys C.m) (cs C) := by unfold cK; rfl

theorem cKL : K (nphys C.m) (cs C) ≤ cL C := by rw [← cK_eq]; unfold cL; omega

/-! ### Indices of the special rows -/

theorem cs_sub_two_lt : cs C - 2 < cs C := by have := six_le_cs C; omega
theorem cs_sub_one_lt : cs C - 1 < cs C := by have := six_le_cs C; omega
theorem head_lt (k : ℕ) (hk : k < 4) : k < cs C := by have := six_le_cs C; omega

theorem crows_head (k : ℕ) (hk : k < 4) :
    (allRows C)[k]'(head_lt C k hk) = (headRows C.m)[k]'(by simp [headRows]; omega) := by
  have hpre : k < (preRows C).length := by rw [preRows_length]; omega
  rw [allRows_getElem_pre C k (head_lt C k hk) hpre]
  unfold preRows
  rw [List.getElem_append_left (by simp [headRows]; omega)]

theorem crows_zero : crows C ⟨0, head_lt C 0 (by norm_num)⟩ = seedRow ∧
    chel C ⟨0, head_lt C 0 (by norm_num)⟩ = gV0 C.m := by
  unfold crows chel; rw [crows_head C 0 (by norm_num)]; exact ⟨rfl, rfl⟩

theorem crows_one : crows C ⟨1, head_lt C 1 (by norm_num)⟩ = seedRow ∧
    chel C ⟨1, head_lt C 1 (by norm_num)⟩ = gV1 C.m := by
  unfold crows chel; rw [crows_head C 1 (by norm_num)]; exact ⟨rfl, rfl⟩

theorem crows_two : crows C ⟨2, head_lt C 2 (by norm_num)⟩ = revRow (iδ C.m) (gV0 C.m) ∧
    chel C ⟨2, head_lt C 2 (by norm_num)⟩ = gV1 C.m := by
  unfold crows chel; rw [crows_head C 2 (by norm_num)]; exact ⟨rfl, rfl⟩

theorem crows_three : crows C ⟨3, head_lt C 3 (by norm_num)⟩ = revRow (iδ C.m) (gV1 C.m) ∧
    chel C ⟨3, head_lt C 3 (by norm_num)⟩ = gV0 C.m := by
  unfold crows chel; rw [crows_head C 3 (by norm_num)]; exact ⟨rfl, rfl⟩

/-- Every paired row and its negation occur among the rows before the unit rows. -/
theorem exists_pair_index (R : Row (nphys C.m)) (hR : R ∈ pairedRows90 C) :
    ∃ j j' : Fin (cs C), (j : ℕ) < (preRows C).length ∧ (j' : ℕ) < (preRows C).length ∧
      crows C j = R ∧ crows C j' = negRow R := by
  have h1 : (R, gV1 C.m) ∈ l1 C := List.mem_flatMap.2 ⟨R, hR, by simp⟩
  have h2 : (negRow R, gV1 C.m) ∈ l1 C := List.mem_flatMap.2 ⟨R, hR, by simp⟩
  obtain ⟨i, hi, hiR⟩ := List.mem_iff_getElem.1 h1
  obtain ⟨i', hi', hiR'⟩ := List.mem_iff_getElem.1 h2
  have hlen := cs_eq C
  have hpre : (preRows C).length = 4 + (l1 C).length := by
    unfold preRows; simp [headRows]; omega
  have hhead : (headRows C.m).length = 4 := by simp [headRows]
  have hj1 : 4 + i < cs C := by omega
  have hj2 : 4 + i' < cs C := by omega
  refine ⟨⟨4 + i, hj1⟩, ⟨4 + i', hj2⟩, ?_, ?_, ?_, ?_⟩
  · exact Nat.lt_of_lt_of_le (show 4 + i < (preRows C).length by omega) le_rfl
  · exact Nat.lt_of_lt_of_le (show 4 + i' < (preRows C).length by omega) le_rfl
  · unfold crows
    rw [allRows_getElem_pre C _ _ (by simp; omega)]
    unfold preRows
    rw [List.getElem_append_right (by rw [hhead]; exact Nat.le_add_right 4 _)]
    simp only [hhead, Nat.add_sub_cancel_left]
    rw [hiR]
  · unfold crows
    rw [allRows_getElem_pre C _ _ (by simp; omega)]
    unfold preRows
    rw [List.getElem_append_right (by rw [hhead]; exact Nat.le_add_right 4 _)]
    simp only [hhead, Nat.add_sub_cancel_left]
    rw [hiR']

theorem t_last_eq : t (nphys C.m) (cs C) (cs C - 1) = tl (nphys C.m) (cs C) := rfl

end LayoutOfCircuit

/-- The coordinate digits of `g`. -/
def zdig {m : ℕ} (g B : ℕ) (i : Fin m) : ℕ := g / B ^ (v i) % B

set_option maxHeartbeats 12000000 in
/-- Sufficiency: a positive solution of the system at the fixed index decodes to an
accepting computation of the circuit. -/
theorem sufficiency (C : Gates.Circuit) {x : ℕ} (hx : 0 < x)
    (hsolv : Solvable90 x (cV C) (cH C) (cT C)) : C.Accepts x := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l, n, o, q, r, s, t', w, α, γ, η, θ, lam, τ', φ, κ, μ,
    ρ, Δ, β, ζ, σ, y, pa, pb, pc, pd, pe, pf, pg, ph, pi, pj, pk, pl, pn, po, pq, pr, ps, pt, pw,
    pα, pγ, pη, pθ, plam, pτ, pφ, pκ, pμ, pρ, pΔ, pβ, pζ, pσ, py, hS⟩ := hsolv
  have hP : Pos90 x a b c d e f g h i j k l n o q r s t' w α γ η θ lam τ' φ κ μ ρ Δ β ζ σ y :=
    ⟨hx, pa, pb, pc, pd, pe, pf, pg, ph, pi, pj, pk, pl, pn, po, pq, pr, ps, pt, pw, pα, pγ, pη,
      pθ, plam, pτ, pφ, pκ, pμ, pρ, pΔ, pβ, pζ, pσ, py⟩
  have hLay := layoutOk C
  have hs6 := six_le_cs C
  have hKL : K (nphys C.m) (cs C) ≤ cL C := cKL C
  have hL1 : 1 ≤ cL C := by unfold cL; omega
  -- the index components
  have hH0 := H0_ge_1024 C
  have hH : cH C = H0 C - 1 := by unfold cH; rfl
  have hH64 : 64 ≤ cH C := by rw [hH]; omega
  have hLH : 3 * cL C ≤ cH C := by have := H0_ge_L C; rw [hH]; omega
  have hT : cT C = yn Exp90.two_lt_one (cL C) := by unfold cT; rfl
  -- the radix `B = cH C + b + 2`
  have hBH0 : cH C + b + 2 = H0 C + b + 1 := by rw [hH]; omega
  have hB64 : 64 ≤ cH C + b + 2 := by omega
  have hB2 : 2 ≤ cH C + b + 2 := by omega
  have hbB : b < cH C + b + 2 := by omega
  have hxb : x < b := by have := hS.E1b; omega
  have hxB : x < cH C + b + 2 := by omega
  -- the Pell block
  have hPp : 1 < 2 * (w * n ^ 2 * (s * n ^ 2) ^ 2) + 1 := by
    have : 0 < w * n ^ 2 * (s * n ^ 2) ^ 2 := by positivity
    omega
  have PB := pell_block90 hP hS hH64 hL1 hLH hT (by omega) hPp
  have hq : q = (cH C + b + 2) ^ cL C := PB.q_eq
  have hBq : cH C + b + 2 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) _
  have hbq : b < q := by omega
  obtain ⟨mB, hBm⟩ := PB.B_pow2
  have hmB6 : 6 ≤ mB := by
    by_contra hcon; push Not at hcon
    have : 2 ^ mB < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) hcon
    omega
  -- the three masks
  obtain ⟨mask1, mask2, mask3⟩ := (masks_iff_central90 hP hS hH64 hbq PB.q_pow2).2 PB.central
  -- bounds from the bootstrap
  have hlq := l_lt_q90 hP hS
  have hgq := g_lt_q90 hP hS
  have hS2 := S2_lt_sq90 hP hS
  have hlamB : lam * (cH C + b + 2 - 1) = (cH C + b + 2) ^ (2 * cL C) - 1 := by
    have := lam_mul_B_sub_one90 hP hS
    rw [show cH C + b + 2 - 1 = cH C + b + 1 by omega, this, hq, ← pow_mul, mul_comm (cL C) 2]
  -- the canonical code
  obtain ⟨ys, hys_def⟩ : ∃ ys : List ℕ,
      ys = ell0d (crows C) (cL C) ++ e0d (crows C) (chel C) (cPX C) := ⟨_, rfl⟩
  have hys : ∀ y' ∈ ys, y' < 2 := by
    intro y' hy
    rw [hys_def, List.mem_append] at hy
    rcases hy with hy | hy
    · have := ell0d_mem_le (crows C) (cL C) y' hy; omega
    · have := e0d_mem_le (crows C) (chel C) (cPX C) hLay y' hy; omega
  have hlen : ys.length ≤ 2 * cL C := by
    rw [hys_def, List.length_append, ell0d_length, e0d_length]; omega
  have hV : cV C = Nat.ofDigits 2 ys := by rw [hys_def]; unfold cV; rfl
  have hS2' : l + e * q < (cH C + b + 2) ^ (2 * cL C) := by
    rw [show 2 * cL C = cL C * 2 by ring, pow_mul, ← hq]; exact hS2
  have hcode : l + e * q = Nat.ofDigits (cH C + b + 2) ys :=
    S2_eq_ofDigits_two hBm ys hys hlen hV (by rw [hS.E3]) hlamB
      (le_trans (H0_ge_pow C) (by omega)) hS2' mask2 hS.E45
  rw [hys_def, ofDigits_append_eq, ell0d_length] at hcode
  have hl0 : Nat.ofDigits (cH C + b + 2) (ell0d (crows C) (cL C)) < (cH C + b + 2) ^ cL C := by
    have := Nat.ofDigits_lt_base_pow_length (l := ell0d (crows C) (cL C))
      (b := cH C + b + 2) (by omega)
      (fun y' hy => by have := ell0d_mem_le (crows C) (cL C) y' hy; omega)
    rwa [ell0d_length] at this
  obtain ⟨hl, he⟩ := split_code (q := q) (l' := Nat.ofDigits (cH C + b + 2)
    (ell0d (crows C) (cL C))) (e' := Nat.ofDigits (cH C + b + 2)
    (e0d (crows C) (chel C) (cPX C))) pq hlq (by rw [hq]; exact hl0)
    (by rw [← hq] at hcode; exact hcode)
  have hl' : l = ∑ hh ∈ range (cL C), ind (crows C) hh * (cH C + b + 2) ^ hh := by
    rw [hl, ofDigits_ell0d]
  -- the digits of `g`
  have hgdig := g_digits (crows C) (by omega) hBm hbB hKL hl' hq mask1
  have hgL : g < (cH C + b + 2) ^ cL C := by rw [← hq]; exact hgq
  obtain ⟨zN, hzN⟩ : ∃ zN : Fin (nphys C.m) → ℕ, zN = fun ii => zdig g (cH C + b + 2) ii :=
    ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : Fin (nphys C.m) → ℤ, z = fun ii => (zN ii : ℤ) := ⟨_, rfl⟩
  obtain ⟨dum, hdum⟩ : ∃ dum : ℕ → Fin 3 → ℤ,
      dum = fun rr (ee : Fin 3) => gdig g (cH C + b + 2) (rr + (ee : ℕ)) := ⟨_, rfl⟩
  have hC : ((x + g : ℕ) : ℤ) =
      (Cmain (x : ℤ) z + Cdum (cs C) (crows C) dum).eval ((cH C + b + 2 : ℕ) : ℤ) := by
    rw [hz, hzN, hdum]
    exact C_eq_eval (crows C) (by omega) hKL hgL (fun ii hi hi' => (hgdig ii hi).1 hi')
  have hz0 : ∀ ii, (0 : ℤ) ≤ z ii := fun ii => by rw [hz]; positivity
  have hzNB : ∀ ii, zN ii < cH C + b + 2 := fun ii => by
    rw [hzN]; exact Nat.mod_lt _ (by omega)
  have hzB : ∀ ii, z ii ≤ ((cH C + b + 2 : ℕ) : ℤ) := fun ii => by
    rw [hz]; show ((zN ii : ℕ) : ℤ) ≤ ((cH C + b + 2 : ℕ) : ℤ); exact_mod_cast (hzNB ii).le
  have hScast : ∀ P : Fin 3 → Fin (nphys C.m), S P z = (SN P zN : ℤ) := fun P => by
    rw [hz]; exact S_cast90 P zN
  -- the decomposition of `σ`
  obtain ⟨High, hσ⟩ := sigma_decomp (crows C) (chel C) (cPX C) hLay hKL he hl
    (Cmain (x : ℤ) z + Cdum (cs C) (crows C) dum) hC hS.ES
  -- the digits of `σ`
  have hσdig := sigma_digits_le_one (crows C) (by omega) hBm hKL
    (by rw [hS.E3]; omega) hl' mask3
  have hdig : ∀ jj : Fin (cs C),
      σ / (cH C + b + 2) ^ (t (nphys C.m) (cs C) jj) % (cH C + b + 2) ≤ 1 ∧
      σ / (cH C + b + 2) ^ (t (nphys C.m) (cs C) jj + 1) % (cH C + b + 2) ≤ 1 ∧
      σ / (cH C + b + 2) ^ (t (nphys C.m) (cs C) jj + 2) % (cH C + b + 2) ≤ 1 := by
    intro jj
    have hr := t_mem_Rset (cs C) (crows C) jj
    refine ⟨?_, ?_, ?_⟩
    · have := hσdig _ (mem_supp_of_mem_Rset_add (crows C) hr (show 0 < 3 by norm_num))
      rwa [add_zero] at this
    · exact hσdig _ (mem_supp_of_mem_Rset_add (crows C) hr (show 1 < 3 by norm_num))
    · exact hσdig _ (mem_supp_of_mem_Rset_add (crows C) hr (show 2 < 3 by norm_num))
  -- the windows of the targets
  have hD1 : 128 * absSum (cD C) * ((nphys C.m : ℤ) + 1) ^ 2 < ((cH C + b + 2 : ℕ) : ℤ) := by
    have := H0_gt_D1 C
    have : (H0 C : ℤ) ≤ ((cH C + b + 2 : ℕ) : ℤ) := by rw [hBH0]; push_cast; linarith
    linarith
  have hwin : ∀ jj : Fin (cs C),
      0 ≤ L90.a (crows C) (chel C) (cPX C) x z (t (nphys C.m) (cs C) jj) +
        L90.a (crows C) (chel C) (cPX C) x z (t (nphys C.m) (cs C) jj - 1) / (cH C + b + 2) ∧
      L90.a (crows C) (chel C) (cPX C) x z (t (nphys C.m) (cs C) jj) +
        L90.a (crows C) (chel C) (cPX C) x z (t (nphys C.m) (cs C) jj - 1) / (cH C + b + 2) =
        ((σ / (cH C + b + 2) ^ (t (nphys C.m) (cs C) jj) % (cH C + b + 2) : ℕ) : ℤ) +
          ((σ / (cH C + b + 2) ^ (t (nphys C.m) (cs C) jj + 1) % (cH C + b + 2) : ℕ) : ℤ) *
            (cH C + b + 2) +
          ((σ / (cH C + b + 2) ^ (t (nphys C.m) (cs C) jj + 2) % (cH C + b + 2) : ℕ) : ℤ) *
            (cH C + b + 2) ^ 2 := fun jj =>
    window_value (crows C) (chel C) (cPX C) hLay hB64 hx hxB z hz0 hzB dum hD1 High hσ jj
      (t_mem_starts (cs C) (crows C) jj) (hdig jj).1 (hdig jj).2.1 (hdig jj).2.2
  -- the raw values at the targets
  have hval : ∀ jj : Fin (cs C), L90.a (crows C) (chel C) (cPX C) x z (t (nphys C.m) (cs C) jj) =
      (crows C jj).val x z + (if (crows C jj).xx < 0 then S (chel C jj) z ^ 2 else 0) :=
    fun jj => coeff_at_target (crows C) (chel C) (cPX C) x z hLay jj
  have hpad0 : ∀ jj : Fin (cs C), (jj : ℕ) ≠ cs C - 1 →
      L90.a (crows C) (chel C) (cPX C) x z (t (nphys C.m) (cs C) jj - 1) = 0 := by
    intro jj hjj
    have := t_ge (nphys C.m) (cs C) jj
    exact coeff_at_empty (crows C) (chel C) (cPX C) x z hLay jj
      (t_mem_starts (cs C) (crows C) jj) (t (nphys C.m) (cs C) jj - 1) (by omega) (by omega)
      (by omega) (by omega) (fun _ => hjj)
  -- every paired row vanishes
  have hpaired : ∀ R ∈ pairedRows90 C, R.val (x : ℤ) (fun ii => (zN ii : ℤ)) = 0 := by
    intro R hR
    obtain ⟨j1, j2, hj1, hj2, e1, e2⟩ := exists_pair_index C R hR
    have hcs := cs_eq C
    have h1 := (hwin j1).1
    have h2 := (hwin j2).1
    rw [hpad0 j1 (by omega), Int.zero_ediv, add_zero, hval, e1] at h1
    rw [hpad0 j2 (by omega), Int.zero_ediv, add_zero, hval, e2, negRow_val] at h2
    obtain ⟨hS1, _, hxx1⟩ := paired_struct C R hR
    have hxxneg : ¬ (negRow R).xx < 0 := by simp [negRow, hxx1]
    rw [if_neg (by omega), add_zero] at h1
    rw [if_neg hxxneg, add_zero] at h2
    rw [← hz]
    linarith
  -- the seeds: `Vᵢ ≥ x`
  have hseed0 : (x : ℤ) ≤ SN (gV0 C.m) zN := by
    have h1 := (hwin ⟨0, head_lt C 0 (by norm_num)⟩).1
    rw [hpad0 _ (by simp; omega), Int.zero_ediv, add_zero, hval, (crows_zero C).1,
      (crows_zero C).2, seedRow_val, if_pos (by simp [seedRow]), hScast] at h1
    have hnn : (0 : ℤ) ≤ SN (gV0 C.m) zN := by positivity
    nlinarith
  have hseed1 : (x : ℤ) ≤ SN (gV1 C.m) zN := by
    have h1 := (hwin ⟨1, head_lt C 1 (by norm_num)⟩).1
    rw [hpad0 _ (by simp; omega), Int.zero_ediv, add_zero, hval, (crows_one C).1,
      (crows_one C).2, seedRow_val, if_pos (by simp [seedRow]), hScast] at h1
    have hnn : (0 : ℤ) ≤ SN (gV1 C.m) zN := by positivity
    nlinarith
  -- `δ ≥ 1`
  have hV0pos : 1 ≤ SN (gV0 C.m) zN := by
    have : (1 : ℤ) ≤ SN (gV0 C.m) zN := le_trans (by exact_mod_cast hx) hseed0
    exact_mod_cast this
  obtain ⟨hδ1, hδV0⟩ := decode_delta_bounds90 hpaired hV0pos
  -- the reverses: `Vᵢ ≤ x`
  have hrev0 : (SN (gV0 C.m) zN : ℤ) ≤ x := by
    have h1 := (hwin ⟨2, head_lt C 2 (by norm_num)⟩).1
    rw [hpad0 _ (by simp; omega), Int.zero_ediv, add_zero, hval, (crows_two C).1,
      revRow_val, if_neg (by simp [revRow]), add_zero, hScast, hz] at h1
    have hδZ : (1 : ℤ) ≤ (zN (iδ C.m) : ℤ) := by exact_mod_cast hδ1
    nlinarith
  have hV0 : SN (gV0 C.m) zN = x := by
    have : (SN (gV0 C.m) zN : ℤ) = x := le_antisymm hrev0 hseed0
    exact_mod_cast this
  have hδx : zN (iδ C.m) ≤ x := hV0 ▸ hδV0
  -- the two unit tests
  have hX : SN (gP C.m C.inp) zN = x := by rw [decode_X hpaired, hV0]
  have hunit : ∀ jj : Fin (cs C), (preRows C).length ≤ (jj : ℕ) →
      L90.a (crows C) (chel C) (cPX C) x z (t (nphys C.m) (cs C) jj) =
        ((zN (iδ C.m) ^ 2 : ℕ) : ℤ) := by
    intro jj hjj
    rw [hval, (crows_unit C jj hjj).1, unitRow_val, if_neg (by simp [unitRow]), add_zero, hz]
    push_cast; ring
  have hcs := cs_eq C
  -- the first unit test: `δ²`
  have t1 : ∃ d0 d1 d2, d0 ≤ 1 ∧ d1 ≤ 1 ∧ d2 ≤ 1 ∧
      zN (iδ C.m) ^ 2 = d0 + d1 * (cH C + b + 2) + d2 * (cH C + b + 2) ^ 2 := by
    obtain ⟨jj, hjj⟩ : ∃ jj : Fin (cs C), (jj : ℕ) = cs C - 2 := ⟨⟨cs C - 2, by omega⟩, rfl⟩
    have hw := (hwin jj).2
    rw [hpad0 jj (by omega), Int.zero_ediv, add_zero, hunit jj (by omega)] at hw
    refine ⟨σ / (cH C + b + 2) ^ (t (nphys C.m) (cs C) jj) % (cH C + b + 2),
      σ / (cH C + b + 2) ^ (t (nphys C.m) (cs C) jj + 1) % (cH C + b + 2),
      σ / (cH C + b + 2) ^ (t (nphys C.m) (cs C) jj + 2) % (cH C + b + 2),
      (hdig jj).1, (hdig jj).2.1, (hdig jj).2.2, ?_⟩
    exact_mod_cast hw
  -- the second unit test: `δ² + ⌊2x²/B⌋`
  have t2 : ∃ d0 d1 d2, d0 ≤ 1 ∧ d1 ≤ 1 ∧ d2 ≤ 1 ∧
      zN (iδ C.m) ^ 2 + 2 * x ^ 2 / (cH C + b + 2) =
        d0 + d1 * (cH C + b + 2) + d2 * (cH C + b + 2) ^ 2 := by
    obtain ⟨jj, hjj⟩ : ∃ jj : Fin (cs C), (jj : ℕ) = cs C - 1 := ⟨⟨cs C - 1, by omega⟩, rfl⟩
    have hw := (hwin jj).2
    have htl : t (nphys C.m) (cs C) jj = tl (nphys C.m) (cs C) := by
      unfold tl; rw [hjj]
    have hsum : ∑ hh ∈ cPX C, z hh = (SN (gP C.m C.inp) zN : ℤ) := by
      rw [hz]; exact decode_pad hpaired
    have hpadv : L90.a (crows C) (chel C) (cPX C) x z (t (nphys C.m) (cs C) jj - 1) =
        ((2 * x ^ 2 : ℕ) : ℤ) := by
      rw [htl]
      unfold L90.a
      rw [coeff_at_pad (crows C) (chel C) (cPX C) x z hLay, ← Finset.mul_sum, hsum, hX]
      push_cast; ring
    rw [hpadv, hunit jj (by omega)] at hw
    refine ⟨σ / (cH C + b + 2) ^ (t (nphys C.m) (cs C) jj) % (cH C + b + 2),
      σ / (cH C + b + 2) ^ (t (nphys C.m) (cs C) jj + 1) % (cH C + b + 2),
      σ / (cH C + b + 2) ^ (t (nphys C.m) (cs C) jj + 2) % (cH C + b + 2),
      (hdig jj).1, (hdig jj).2.1, (hdig jj).2.2, ?_⟩
    have hcast : ((zN (iδ C.m) ^ 2 + 2 * x ^ 2 / (cH C + b + 2) : ℕ) : ℤ) =
        ((zN (iδ C.m) ^ 2 : ℕ) : ℤ) + ((2 * x ^ 2 : ℕ) : ℤ) / ((cH C : ℤ) + b + 2) := by
      push_cast; ring
    rw [← hcast] at hw
    exact_mod_cast hw
  have hδ := unit_tests90 hB64 ⟨mB, hBm⟩ hδ1 hδx hxB t1 t2
  exact decode_accepts90 hpaired hδ hV0

end

end L90

end Jones1980
