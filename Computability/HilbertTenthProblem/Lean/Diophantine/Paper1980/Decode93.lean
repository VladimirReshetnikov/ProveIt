import Diophantine.Paper1980.Compile93b
import Diophantine.Paper1980.Windows93
import Diophantine.Paper1980.Unit93
import Diophantine.Paper1980.Pell93
import Diophantine.Paper1980.Pack93

/-!
# Sufficiency: a positive solution of the 93-operation system decodes to an
accepting computation (Sections 3–6)

For a circuit `C` the layout is: `m = 9 cm + 11` physical coordinates, the
rows `R, −R` for every paired row `R` followed by three unit rows `δ²`, the
padding sets `P₅, P₇`; the fixed index is `K = t_{s−1} + 3`, `L = 3K + 3`,
`H₀ = 2^{j_H}` a power of two exceeding `2·4^{2L+1}`, `128 D₁ (m+1)²`,
`3L + 3` and `1024`, `H = H₀ − 3`, `V = ℓ₀(4) + e₀(4) 4^L`, `Tindex = ψ₄(L)`.

`sufficiency`: if the system has a positive solution at input `x > 0` then
`C` accepts `x`.  The proof runs through the Pell block, the three masks,
the canonical code, the digit reading of `g`, the decomposition of `σ`,
the windows of all targets, the vanishing of the paired rows, the three
unit tests forcing `δ = 1`, and the decoding of the circuit rows.
-/

namespace Jones1980

namespace Iso

open Layout Polynomial Finset
open Diophantine Pell
open Jones1982 (τ)

noncomputable section

section LayoutOfCircuit

variable (C : Gates.Circuit)

/-- The paired rows with their negations. -/
def l1 : List (Row (nphys C.m)) := (pairedRows C).flatMap fun R => [R, negRow R]

/-- All rows: the paired rows with their negations, then three unit rows. -/
def allRows : List (Row (nphys C.m)) :=
  l1 C ++ [unitRow (iδ C.m), unitRow (iδ C.m), unitRow (iδ C.m)]

/-- The number of rows. -/
def cs : ℕ := (allRows C).length

/-- The rows, indexed. -/
def crows (j : Fin (cs C)) : Row (nphys C.m) := (allRows C)[(j : ℕ)]'j.isLt

theorem cs_eq : cs C = (l1 C).length + 3 := by
  unfold cs allRows; rw [List.length_append]; rfl

theorem three_le_cs : 3 ≤ cs C := by rw [cs_eq]; omega

theorem getElem_three {α : Type*} (u : α) (k : ℕ) (hk : k < 3) : [u, u, u][k] = u := by
  interval_cases k <;> rfl

theorem crows_unit (j : Fin (cs C)) (hj : cs C ≤ (j : ℕ) + 3) :
    crows C j = unitRow (iδ C.m) := by
  unfold crows allRows
  have hlen := cs_eq C
  rw [List.getElem_append_right (by omega)]
  exact getElem_three _ _ (by have := j.isLt; omega)

theorem exists_pair_index (R : Row (nphys C.m)) (hR : R ∈ pairedRows C) :
    ∃ j j' : Fin (cs C), (j : ℕ) + 3 ≤ cs C ∧ (j' : ℕ) + 3 ≤ cs C ∧
      crows C j = R ∧ crows C j' = negRow R := by
  have h1 : R ∈ l1 C := List.mem_flatMap.2 ⟨R, hR, by simp⟩
  have h2 : negRow R ∈ l1 C := List.mem_flatMap.2 ⟨R, hR, by simp⟩
  obtain ⟨i, hi, hiR⟩ := List.mem_iff_getElem.1 h1
  obtain ⟨i', hi', hiR'⟩ := List.mem_iff_getElem.1 h2
  have hlen := cs_eq C
  refine ⟨⟨i, by omega⟩, ⟨i', by omega⟩, by simp; omega, by simp; omega, ?_, ?_⟩
  · unfold crows allRows; simp only; rw [List.getElem_append_left hi]; exact hiR
  · unfold crows allRows; simp only; rw [List.getElem_append_left hi']; exact hiR'

theorem crows_valid (j : Fin (cs C)) : RowValid (crows C j) := by
  have hmem : crows C j ∈ allRows C := List.getElem_mem _
  unfold allRows l1 at hmem
  rw [List.mem_append, List.mem_flatMap] at hmem
  rcases hmem with ⟨R, hR, hmem⟩ | hmem
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h <;> rw [h]
    · exact (pairedRows_struct C R hR).valid
    · exact (negRow_struct (pairedRows_struct C R hR)).valid
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h <;> rw [h] <;> exact (unitRow_struct _).valid

/-- The fixed index. -/
@[irreducible] def cK : ℕ := K (nphys C.m) (cs C)
@[irreducible] def cL : ℕ := 3 * cK C + 3
def cD : ℤ[X] := D (nphys C.m) (cs C) (crows C) (P5 C) (P7 C)
@[irreducible] def cD1 : ℕ := (absSum (cD C)).toNat
@[irreducible] def jH : ℕ := 4 * cL C + 3 + 128 * cD1 C * (nphys C.m + 1) ^ 2 + 3 * cL C + 3 + 10
@[irreducible] def H0 : ℕ := 2 ^ jH C
@[irreducible] def cH : ℕ := H0 C - 3
@[irreducible] def cV : ℕ :=
  Nat.ofDigits 4 (ell0d (nphys C.m) (cs C) (cL C) ++ e0d (nphys C.m) (cs C) (cD C))
@[irreducible] def cT : ℕ := yn four_lt_one (cL C)

theorem cD_abs (h : ℕ) : |(cD C).coeff h| ≤ 1 :=
  abs_coeff_D_le_one (crows C) (P5 C) (P7 C) (three_le_cs C) (crows_valid C) h

theorem jH_ge_pow : 4 * cL C + 3 ≤ jH C := by unfold jH; omega
theorem jH_ge_D1 : 128 * cD1 C * (nphys C.m + 1) ^ 2 ≤ jH C := by unfold jH; omega
theorem jH_ge_L : 3 * cL C + 3 ≤ jH C := by unfold jH; omega
theorem jH_ge_ten : 10 ≤ jH C := by unfold jH; omega

theorem H0_ge_pow : 2 * 4 ^ (2 * cL C + 1) ≤ H0 C := by
  have e : 2 * 4 ^ (2 * cL C + 1) = 2 ^ (4 * cL C + 3) := by
    rw [show 4 * cL C + 3 = 2 * (2 * cL C + 1) + 1 by ring]
    conv_rhs => rw [pow_succ', pow_mul]
    norm_num
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

theorem mem_supp_t (j : Fin (cs C)) (e : Fin 3) :
    t (nphys C.m) (cs C) j + e ∈ supp (nphys C.m) (cs C) := by
  unfold supp
  apply Finset.mem_union_right
  rw [Finset.mem_biUnion]
  refine ⟨j, Finset.mem_range.2 j.isLt, ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton]
  have := e.isLt
  omega

end LayoutOfCircuit

/-- The coordinate digits of `g`. -/
def zdig {m : ℕ} (g B : ℕ) (i : Fin m) : ℕ := g / B ^ (v i) % B

set_option maxHeartbeats 4000000 in
/-- Sufficiency: a positive solution of the system at the fixed index decodes to an
accepting computation of the circuit. -/
theorem sufficiency (C : Gates.Circuit) {x : ℕ} (hx : 0 < x)
    (hsolv : Solvable93 x (cV C) (cH C) (cT C)) : C.Accepts x := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l, n, o, q, r, s, t, w, α, γ, η, θ, lam, τ', φ, κ, μ, ρ,
    Δ, β, ζ, σ, Ω, pa, pb, pc, pd, pe, pf, pg, ph, pi, pj, pk, pl, pn, po, pq, pr, ps, pt, pw,
    pα, pγ, pη, pθ, plam, pτ, pφ, pκ, pμ, pρ, pΔ, pβ, pζ, pσ, pΩ, hS⟩ := hsolv
  have hP : Pos93 x a b c d e f g h i j k l n o q r s t w α γ η θ lam τ' φ κ μ ρ Δ β ζ σ Ω :=
    ⟨hx, pa, pb, pc, pd, pe, pf, pg, ph, pi, pj, pk, pl, pn, po, pq, pr, ps, pt, pw, pα, pγ, pη,
      pθ, plam, pτ, pφ, pκ, pμ, pρ, pΔ, pβ, pζ, pσ, pΩ⟩
  have hs3 : 3 ≤ cs C := three_le_cs C
  have hKL : K (nphys C.m) (cs C) ≤ cL C := by unfold cL cK; omega
  have hL1 : 1 ≤ cL C := by unfold cL; omega
  -- the index components
  have hH0 := H0_ge_1024 C
  have hH : cH C = H0 C - 3 := by unfold cH; rfl
  have hH64 : 64 ≤ cH C := by rw [hH]; omega
  have hLH : 3 * cL C ≤ cH C := by have := H0_ge_L C; rw [hH]; omega
  have hT : cT C = yn four_lt_one (cL C) := by unfold cT; rfl
  -- the radix `B = cH C + b + 4`
  have hBH0 : cH C + b + 4 = H0 C + b + 1 := by rw [hH]; omega
  have hB64 : 64 ≤ cH C + b + 4 := by omega
  have hB2 : 2 ≤ cH C + b + 4 := by omega
  have hbB : b < cH C + b + 4 := by omega
  have hxb : x < b := by have := hS.E1b; omega
  have hxB : x < cH C + b + 4 := by omega
  -- the Pell block
  have hPp : 1 < 2 * (w * n ^ 2 * (s * n ^ 2) ^ 2) + 1 := by
    have : 0 < w * n ^ 2 * (s * n ^ 2) ^ 2 := by positivity
    omega
  have PB := pell_block hP hS hH64 hL1 hLH hT (by omega) hPp
  have hq : q = (cH C + b + 4) ^ cL C := PB.q_eq
  have hBq : cH C + b + 4 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) _
  have hbq : b < q := by omega
  obtain ⟨mB, hBm⟩ := PB.B_pow2
  have hmB6 : 6 ≤ mB := by
    by_contra hcon; push Not at hcon
    have : 2 ^ mB < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) hcon
    omega
  -- the three masks
  obtain ⟨mask1, mask2, mask3⟩ := (masks_iff_central hP hS hH64 hbq PB.q_pow2).2 PB.central
  -- bounds from the bootstrap
  have hlq := l_lt_q hP hS
  have hgq := g_lt_q hP hS
  have hS2 := S2_lt_sq hP hS
  have hlamB : lam * (cH C + b + 4 - 1) = (cH C + b + 4) ^ (2 * cL C) - 1 := by
    have := lam_mul_B_sub_one hP hS
    rw [show cH C + b + 4 - 1 = cH C + b + 3 by omega, this, hq, ← pow_mul, mul_comm (cL C) 2]
  -- the canonical code
  have hD : ∀ h, |(cD C).coeff h| ≤ 1 := cD_abs C
  obtain ⟨ys, hys_def⟩ : ∃ ys : List ℕ,
      ys = ell0d (nphys C.m) (cs C) (cL C) ++ e0d (nphys C.m) (cs C) (cD C) := ⟨_, rfl⟩
  have hys : ∀ y ∈ ys, y < 4 := by
    intro y hy
    rw [hys_def, List.mem_append] at hy
    rcases hy with hy | hy
    · have := ell0d_mem_le (nphys C.m) (cs C) (cL C) y hy; omega
    · have := e0d_mem_le (nphys C.m) (cs C) (cD C) hD y hy; omega
  have hlen : ys.length ≤ 2 * cL C := by
    rw [hys_def, List.length_append, ell0d_length, e0d_length]; omega
  have hV : cV C = Nat.ofDigits 4 ys := by rw [hys_def]; unfold cV; rfl
  have hS2' : l + e * q < (cH C + b + 4) ^ (2 * cL C) := by
    rw [show 2 * cL C = cL C * 2 by ring, pow_mul, ← hq]; exact hS2
  have hcode : l + e * q = Nat.ofDigits (cH C + b + 4) ys :=
    S2_eq_ofDigits hBm ys hys hlen hV (by rw [hS.E3]) hlamB
      (le_trans (H0_ge_pow C) (by omega)) hS2' mask2 hS.E45
  rw [hys_def, ofDigits_append_eq, ell0d_length] at hcode
  have hl0 : Nat.ofDigits (cH C + b + 4) (ell0d (nphys C.m) (cs C) (cL C)) <
      (cH C + b + 4) ^ cL C := by
    have := Nat.ofDigits_lt_base_pow_length (l := ell0d (nphys C.m) (cs C) (cL C))
      (b := cH C + b + 4) (by omega)
      (fun y hy => by have := ell0d_mem_le (nphys C.m) (cs C) (cL C) y hy; omega)
    rwa [ell0d_length] at this
  obtain ⟨hl, he⟩ := split_code (q := q) (l' := Nat.ofDigits (cH C + b + 4)
    (ell0d (nphys C.m) (cs C) (cL C))) (e' := Nat.ofDigits (cH C + b + 4)
    (e0d (nphys C.m) (cs C) (cD C))) pq hlq (by rw [hq]; exact hl0)
    (by rw [← hq] at hcode; exact hcode)
  have hl' : l = ∑ h ∈ range (cL C), ind (nphys C.m) (cs C) h * (cH C + b + 4) ^ h := by
    rw [hl, ofDigits_ell0d]
  have he' : (e : ℤ) = ∑ h ∈ range (K (nphys C.m) (cs C)),
      (1 + (cD C).coeff h) * ((cH C + b + 4 : ℕ) : ℤ) ^ h := by
    rw [he]; exact ofDigits_e0d (nphys C.m) (cs C) (cH C + b + 4) (cD C) hD
  -- the digits of `g`
  have hgdig := g_digits (m := nphys C.m) (s := cs C) (by omega) hBm hbB hKL hl' hq mask1
  have hgL : g < (cH C + b + 4) ^ cL C := by rw [← hq]; exact hgq
  have hC : ((x + g : ℕ) : ℤ) = (Cmain (nphys C.m) (x : ℤ)
      (fun i => (zdig g (cH C + b + 4) i : ℤ)) +
      Cdum (nphys C.m) (cs C) (fun jj e => gdig g (cH C + b + 4) (Layout.t (nphys C.m) (cs C) jj + e))).eval
        ((cH C + b + 4 : ℕ) : ℤ) :=
    C_eq_eval (m := nphys C.m) (s := cs C) (by omega) hKL hgL
      (fun i hi hi' => (hgdig i hi).1 hi')
  have hz0 : ∀ i : Fin (nphys C.m), (0 : ℤ) ≤ (zdig g (cH C + b + 4) i : ℤ) :=
    fun i => by positivity
  have hzNB : ∀ i : Fin (nphys C.m), zdig g (cH C + b + 4) i < cH C + b + 4 :=
    fun i => Nat.mod_lt _ (by omega)
  have hzB : ∀ i : Fin (nphys C.m), (zdig g (cH C + b + 4) i : ℤ) ≤ ((cH C + b + 4 : ℕ) : ℤ) :=
    fun i => by exact_mod_cast (hzNB i).le
  -- the decomposition of `σ`
  obtain ⟨High, hσ⟩ := sigma_decomp (crows C) (P5 C) (P7 C) (by omega) hB2 hKL hlamB he' hq
    (Cmain (nphys C.m) (x : ℤ) (fun i => (zdig g (cH C + b + 4) i : ℤ)) +
      Cdum (nphys C.m) (cs C) (fun jj e => gdig g (cH C + b + 4) (Layout.t (nphys C.m) (cs C) jj + e)))
    hC hS.ES
  -- the digits of `σ`
  have hσdig := sigma_digits_le_three (m := nphys C.m) (s := cs C) (by omega) hBm hKL
    (by rw [hS.E3]; omega) hl' mask3
  -- the windows
  have hD1 : 128 * absSum (cD C) * ((nphys C.m : ℤ) + 1) ^ 2 < ((cH C + b + 4 : ℕ) : ℤ) := by
    have := H0_gt_D1 C
    have : (H0 C : ℤ) ≤ ((cH C + b + 4 : ℕ) : ℤ) := by rw [hBH0]; push_cast; linarith
    linarith
  have hwin : ∀ jj : Fin (cs C),
      0 ≤ (crows C jj).val x (fun i => (zdig g (cH C + b + 4) i : ℤ)) +
        padVal (P5 C) (P7 C) x (fun i => (zdig g (cH C + b + 4) i : ℤ)) jj / (cH C + b + 4) ∧
      (crows C jj).val x (fun i => (zdig g (cH C + b + 4) i : ℤ)) +
        padVal (P5 C) (P7 C) x (fun i => (zdig g (cH C + b + 4) i : ℤ)) jj / (cH C + b + 4) =
        ((σ / (cH C + b + 4) ^ (Layout.t (nphys C.m) (cs C) jj) % (cH C + b + 4) : ℕ) : ℤ) +
          ((σ / (cH C + b + 4) ^ (Layout.t (nphys C.m) (cs C) jj + 1) % (cH C + b + 4) : ℕ) : ℤ) *
            (cH C + b + 4) +
          ((σ / (cH C + b + 4) ^ (Layout.t (nphys C.m) (cs C) jj + 2) % (cH C + b + 4) : ℕ) : ℤ) *
            (cH C + b + 4) ^ 2 := fun jj =>
    window_value (crows C) (P5 C) (P7 C) hs3 hB64 hx hxB _ hz0 hzB _ hD1 High hσ jj
      (crows_valid C jj).cross
      (by have := hσdig _ (mem_supp_t C jj 0); rwa [Fin.val_zero, add_zero] at this)
      (hσdig _ (mem_supp_t C jj 1)) (hσdig _ (mem_supp_t C jj 2))
  -- every paired row vanishes
  have hpaired : ∀ R ∈ pairedRows C,
      R.val (x : ℤ) (fun i => (zdig g (cH C + b + 4) i : ℤ)) = 0 := by
    intro R hR
    obtain ⟨j1, j2, hj1, hj2, e1, e2⟩ := exists_pair_index C R hR
    have h1 := (hwin j1).1
    have h2 := (hwin j2).1
    rw [padVal_of_lt (P5 C) (P7 C) _ _ j1 (by omega), Int.zero_ediv, add_zero, e1] at h1
    rw [padVal_of_lt (P5 C) (P7 C) _ _ j2 (by omega), Int.zero_ediv, add_zero, e2, negRow_val] at h2
    linarith
  -- `1 ≤ δ ≤ x`
  obtain ⟨hδ1, hδx⟩ := decode_delta_bounds hpaired (by omega)
  obtain ⟨hpad5, hpad7⟩ := decode_pads hpaired
  -- the three unit tests
  have hunit : ∀ jj : Fin (cs C), cs C ≤ (jj : ℕ) + 3 →
      (crows C jj).val x (fun i => (zdig g (cH C + b + 4) i : ℤ)) =
        ((zdig g (cH C + b + 4) (iδ C.m) ^ 2 : ℕ) : ℤ) := by
    intro jj hjj
    rw [crows_unit C jj hjj, unitRow_val]
    push_cast; ring
  have test : ∀ jj : Fin (cs C), cs C ≤ (jj : ℕ) + 3 → ∀ (P : ℕ),
      padVal (P5 C) (P7 C) x (fun i => (zdig g (cH C + b + 4) i : ℤ)) jj = (P : ℤ) →
      ∃ d0 d1 d2, d0 ≤ 3 ∧ d1 ≤ 3 ∧ d2 ≤ 3 ∧
        zdig g (cH C + b + 4) (iδ C.m) ^ 2 + P / (cH C + b + 4) =
          d0 + d1 * (cH C + b + 4) + d2 * (cH C + b + 4) ^ 2 := by
    intro jj hjj P hPv
    have hw := (hwin jj).2
    rw [hunit jj hjj, hPv] at hw
    refine ⟨σ / (cH C + b + 4) ^ (Layout.t (nphys C.m) (cs C) jj) % (cH C + b + 4),
      σ / (cH C + b + 4) ^ (Layout.t (nphys C.m) (cs C) jj + 1) % (cH C + b + 4),
      σ / (cH C + b + 4) ^ (Layout.t (nphys C.m) (cs C) jj + 2) % (cH C + b + 4),
      by have := hσdig _ (mem_supp_t C jj 0); rwa [Fin.val_zero, add_zero] at this,
      hσdig _ (mem_supp_t C jj 1), hσdig _ (mem_supp_t C jj 2), ?_⟩
    exact_mod_cast hw
  have hp1 : padVal (P5 C) (P7 C) x (fun i => (zdig g (cH C + b + 4) i : ℤ))
      (⟨cs C - 3, by omega⟩ : Fin (cs C)) = ((0 : ℕ) : ℤ) := by
    rw [padVal_of_lt (P5 C) (P7 C) _ _ (⟨cs C - 3, by omega⟩ : Fin (cs C))
      (by simp only [Fin.val_mk]; omega)]; rfl
  have hp2 : padVal (P5 C) (P7 C) x (fun i => (zdig g (cH C + b + 4) i : ℤ))
      (⟨cs C - 2, by omega⟩ : Fin (cs C)) = ((5 * x ^ 2 : ℕ) : ℤ) := by
    unfold padVal
    rw [if_pos (by simp only [Fin.val_mk]), if_neg (by simp only [Fin.val_mk]; omega),
      ← Finset.mul_sum, hpad5]
    push_cast; ring
  have hp3 : padVal (P5 C) (P7 C) x (fun i => (zdig g (cH C + b + 4) i : ℤ))
      (⟨cs C - 1, by omega⟩ : Fin (cs C)) = ((7 * x ^ 2 : ℕ) : ℤ) := by
    unfold padVal
    rw [if_neg (by simp only [Fin.val_mk]; omega), if_pos (by simp only [Fin.val_mk]),
      ← Finset.mul_sum, hpad7]
    push_cast; ring
  have t1 := test ⟨cs C - 3, by omega⟩ (by simp only [Fin.val_mk]; omega) 0 hp1
  have t5 := test ⟨cs C - 2, by omega⟩ (by simp only [Fin.val_mk]; omega) _ hp2
  have t7 := test ⟨cs C - 1, by omega⟩ (by simp only [Fin.val_mk]; omega) _ hp3
  simp only [Nat.zero_div, add_zero] at t1
  have hδ := unit_tests hB64 ⟨mB, hBm⟩ hδ1 hδx hxB t1 t5 t7
  exact decode_accepts hpaired hδ

end

end Iso

end Jones1980
