import Diophantine.Paper1982.Master1

/-!
# Jones 1982, §4: the three `τ`-conditions of the universal systems

* `tau3_iff`: (4.10)–(4.11), `τ₂(S₃, T₃) = 0 ⟺ P(z₀, …, z_ν) = 0` for the code
  `c = 1 + xB + g(B)` of `z₀ = x, z₁, …, z_ν < b`;
* `msList`: the mask `M₁ = q³ − 1 − (b − 1)l` (U9) as the digit list `mⱼ = B − b` at
  `j = 5ⁱ` (`1 ≤ i ≤ ν`), `mⱼ = B − 1` otherwise (`j < 3L`);
* `code_of_tau1`, `tau1_of_code`: (4.8) with Lemmas 2.7, 2.11 — `τ₂(g, M₁) = 0` (with `g < q`)
  iff `g = Σ_{i=1}^ν zᵢ B^(5^i)` with `zᵢ < b`;
* `transfer_iff`: Lemma 2.9 for `e` (from `y`) and `l` (from `u`), with the mask
  `θλ = mask29 B (2z) (4L)` split in two halves.
-/

namespace Jones1982

open Polynomial Finset

section Tau3

variable {ν : ℕ} {P : MvPolynomial (Fin (ν + 1)) ℤ} {z u y : ℕ}

/-- `λ (1 + q⁴) = Σ_{i<8L} Bⁱ` for `λ = Σ_{i<4L} Bⁱ`, `q = B^L`. -/
theorem lam_mul_one_add (B : ℤ) (L : ℕ) :
    (∑ i ∈ range (4 * L), B ^ i) * (1 + (B ^ L) ^ 4) = ∑ i ∈ range (8 * L), B ^ i := by
  rw [show 8 * L = 4 * L + 4 * L by ring, Finset.sum_range_add, mul_add, mul_one, ← pow_mul,
    Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_add]; ring

/-- The bound `|hⱼ| < B/2` for the coefficients of `−c⁴D₀` (the paper's
`z(ν+2)⁴b⁴ < (y/2)b⁴ < B/2`). -/
theorem coeff_Hpoly_lt (hI : Index ν P z u y) (hν : 1 ≤ ν) {b : ℕ} (hyb : y < b)
    (zs : Fin (ν + 1) → ℕ) (hzs : ∀ i, zs i < b) (i : ℕ) :
    2 * |(Hpoly ν 4 P z zs).coeff i| < (b : ℤ) ^ 5 := by
  have h1 := abs_coeff_Hpoly_le ν 4 P (fun k hk => hI.Pcoef_le hk) zs i
  have hsum : ∑ j, (zs j : ℤ) ≤ (ν + 1) * (b : ℤ) - (ν + 1) := by
    have : ∑ j : Fin (ν + 1), (zs j : ℤ) ≤ ∑ j : Fin (ν + 1), ((b : ℤ) - 1) :=
      Finset.sum_le_sum fun j _ => by
        have := hzs j
        have : (zs j : ℤ) + 1 ≤ b := by exact_mod_cast this
        linarith
    simpa using this
  have hb1 : (1 : ℤ) ≤ b := by
    have := hI.y_pos; have : 0 < b := by omega
    exact_mod_cast this
  have h2 : 1 + ∑ j, (zs j : ℤ) < (ν + 2) * b := by
    have : (0 : ℤ) ≤ ν := by positivity
    nlinarith
  have h3 : (1 + ∑ j, (zs j : ℤ)) ^ 4 < ((ν + 2) * (b : ℤ)) ^ 4 := by
    apply pow_lt_pow_left₀ h2 (by positivity) (by norm_num)
  have h4 : 2 * (z : ℤ) * (ν + 2) ^ 4 < y := by
    have := hI.y_big hν; exact_mod_cast this
  have h5 : (y : ℤ) ≤ b - 1 := by
    have : (y : ℤ) + 1 ≤ b := by exact_mod_cast hyb
    linarith
  have hz0 : (0 : ℤ) ≤ z := by positivity
  have hb4 : (0 : ℤ) < (b : ℤ) ^ 4 := by positivity
  calc 2 * |(Hpoly ν 4 P z zs).coeff i| ≤ 2 * ((z : ℤ) * (1 + ∑ j, (zs j : ℤ)) ^ 4) := by linarith
    _ ≤ 2 * ((z : ℤ) * ((ν + 2) * (b : ℤ)) ^ 4) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_left h3.le hz0
    _ = (2 * (z : ℤ) * (ν + 2) ^ 4) * (b : ℤ) ^ 4 := by ring
    _ < (y : ℤ) * (b : ℤ) ^ 4 := mul_lt_mul_of_pos_right h4 hb4
    _ ≤ ((b : ℤ) - 1) * (b : ℤ) ^ 4 := mul_le_mul_of_nonneg_right h5 hb4.le
    _ < (b : ℤ) ^ 5 := by nlinarith

/-- The identity (4.9)–(4.11): `S₃ = 2(e − zλ)c⁴ + Bλ(1 + q⁴) = 2 Σ_{i<8L} (hᵢ + B/2) Bⁱ`,
`hᵢ` the coefficients of `−c⁴D₀`, for `B = b⁵ = 2ᵗ`. -/
theorem S3_eq {P : MvPolynomial (Fin (ν + 1)) ℤ} {b w x e g lam q : ℕ} (hb : b = 2 ^ w)
    (hw : 1 ≤ w) (z : ℕ) (zs : Fin (ν + 1) → ℕ) (he : (e : ℤ) = (epoly ν 4 P z).eval ((b : ℤ) ^ 5))
    (hlam : (lam : ℤ) = (lampoly ν 4).eval ((b : ℤ) ^ 5)) (hq : q = (b ^ 5) ^ L4 ν)
    (hg : (1 + (x : ℤ) * b ^ 5 + g) = (cpoly ν 4 zs).eval ((b : ℤ) ^ 5)) :
    2 * ((e : ℤ) - z * lam) * (1 + x * b ^ 5 + g) ^ 4 + b ^ 5 * lam * (1 + q ^ 4) =
      2 * ∑ i ∈ range (8 * L4 ν),
        ((Hpoly ν 4 P z zs).coeff i + 2 ^ (5 * w - 1)) * (2 ^ (5 * w) : ℤ) ^ i := by
  obtain ⟨t, ht⟩ : ∃ t, t = 5 * w := ⟨_, rfl⟩
  rw [← ht]
  have hB : b ^ 5 = 2 ^ t := by rw [hb, ← pow_mul, ht, mul_comm]
  have hBZ : (b : ℤ) ^ 5 = 2 ^ t := by exact_mod_cast hB
  have h2tZ : (2 : ℤ) ^ t = 2 * 2 ^ (t - 1) := by
    have h2t : 2 ^ t = 2 * 2 ^ (t - 1) := by
      rw [← pow_succ']; congr 1; omega
    exact_mod_cast h2t
  have hH : (Hpoly ν 4 P z zs).eval ((b : ℤ) ^ 5) =
      ∑ i ∈ range (8 * L4 ν), (Hpoly ν 4 P z zs).coeff i * ((b : ℤ) ^ 5) ^ i :=
    eval_eq_sum_range' (natDegree_Hpoly_lt ν 4 P z zs) _
  have hH' := eval_Hpoly ν 4 P z zs ((b : ℤ) ^ 5)
  rw [← he, ← hlam] at hH'
  rw [hg]
  have hq' : (q : ℤ) ^ 4 = ((b : ℤ) ^ 5) ^ (L4 ν * 4) := by
    rw [hq]; push_cast; rw [← pow_mul]
  have hlam' : (lam : ℤ) = ∑ i ∈ range (4 * L4 ν), ((b : ℤ) ^ 5) ^ i := by
    rw [hlam, eval_lampoly]
  have e1 : 2 * ((e : ℤ) - z * lam) * (cpoly ν 4 zs).eval ((b : ℤ) ^ 5) ^ 4 =
      2 * (Hpoly ν 4 P z zs).eval ((b : ℤ) ^ 5) := by
    rw [hH']; ring
  rw [e1, hH]
  have e2 : (b : ℤ) ^ 5 * lam * (1 + q ^ 4) = 2 * ∑ i ∈ range (8 * L4 ν), 2 ^ (t - 1) * (2 ^ t : ℤ) ^ i := by
    rw [hq', hlam', show ((b : ℤ) ^ 5) ^ (L4 ν * 4) = (((b : ℤ) ^ 5) ^ L4 ν) ^ 4 from pow_mul _ _ _]
    rw [mul_assoc, lam_mul_one_add ((b : ℤ) ^ 5) (L4 ν), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hBZ, h2tZ]; ring
  rw [e2, hBZ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `S₃ ≥ 0` for a code of `z₀ = x, z₁, …, z_ν < b` (the article's "`0 ≤ S₃` is
established"). -/
theorem S3_nonneg (hI : Index ν P z u y) (hν : 1 ≤ ν) {b w x e g lam q : ℕ} (hb : b = 2 ^ w)
    (hw : 1 ≤ w) (zs : Fin (ν + 1) → ℕ) (hzs : ∀ i, zs i < b) (hyb : y < b)
    (he : (e : ℤ) = (epoly ν 4 P z).eval ((b : ℤ) ^ 5))
    (hlam : (lam : ℤ) = (lampoly ν 4).eval ((b : ℤ) ^ 5)) (hq : q = (b ^ 5) ^ L4 ν)
    (hg : (1 + (x : ℤ) * b ^ 5 + g) = (cpoly ν 4 zs).eval ((b : ℤ) ^ 5)) :
    0 ≤ 2 * ((e : ℤ) - z * lam) * (1 + x * b ^ 5 + g) ^ 4 + b ^ 5 * lam * (1 + q ^ 4) := by
  rw [S3_eq hb hw z zs he hlam hq hg]
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg _ (by positivity)
  have := coeff_Hpoly_lt hI hν hyb zs hzs i
  have hBZ : (b : ℤ) ^ 5 = 2 ^ (5 * w) := by rw [hb]; push_cast; rw [← pow_mul, mul_comm]
  have h2tZ : (2 : ℤ) ^ (5 * w) = 2 * 2 ^ (5 * w - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hBZ, h2tZ] at this
  have := (abs_lt.1 (show |(Hpoly ν 4 P z zs).coeff i| < 2 ^ (5 * w - 1) by linarith)).1
  linarith

/-- (4.10)–(4.11): for the code `1 + xB + g` of `z₀ = x, z₁, …, z_ν < b` (`B = b⁵`, `b = 2ʷ`),
with `e = e(B)`, `λ = λ(B)`, `q = B^L`: `τ₂(S₃, T₃) = 0 ⟺ P(z₀, …, z_ν) = 0`. -/
theorem tau3_iff (hI : Index ν P z u y) (hν : 1 ≤ ν) (hP : P.totalDegree ≤ 4)
    {b w x e g lam q : ℕ} (hb : b = 2 ^ w) (hw : 1 ≤ w) (zs : Fin (ν + 1) → ℕ)
    (hzs : ∀ i, zs i < b) (hzs0 : zs 0 = x) (hyb : y < b)
    (he : (e : ℤ) = (epoly ν 4 P z).eval ((b : ℤ) ^ 5))
    (hlam : (lam : ℤ) = (lampoly ν 4).eval ((b : ℤ) ^ 5))
    (hq : q = (b ^ 5) ^ L4 ν)
    (hg : (1 + (x : ℤ) * b ^ 5 + g) = (cpoly ν 4 zs).eval ((b : ℤ) ^ 5)) :
    τ 2 (2 * ((e : ℤ) - z * lam) * (1 + x * b ^ 5 + g) ^ 4 + b ^ 5 * lam * (1 + q ^ 4)).toNat
        ((b ^ 5 - 2) * q) = 0 ↔
      MvPolynomial.eval (fun j => (zs j : ℤ)) P = 0 := by
  obtain ⟨t, ht⟩ : ∃ t, t = 5 * w := ⟨_, rfl⟩
  have hB : b ^ 5 = 2 ^ t := by rw [hb, ← pow_mul, ht, mul_comm]
  have hBZ : (b : ℤ) ^ 5 = 2 ^ t := by exact_mod_cast hB
  have ht1 : 1 ≤ t := by omega
  have h2t : 2 ^ t = 2 * 2 ^ (t - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h2tZ : (2 : ℤ) ^ t = 2 * 2 ^ (t - 1) := by exact_mod_cast h2t
  -- the coefficients `hᵢ`
  obtain ⟨h, hh⟩ : ∃ h : ℕ → ℤ, h = (Hpoly ν 4 P z zs).coeff := ⟨_, rfl⟩
  have hbound : ∀ i < 8 * L4 ν, |h i| < 2 ^ (t - 1) := by
    intro i _
    have := coeff_Hpoly_lt hI hν hyb zs hzs i
    rw [hBZ, h2tZ] at this
    rw [hh]; linarith
  have hL : L4 ν < 8 * L4 ν := by
    have : 0 < L4 ν := by positivity
    omega
  have hS := S3_eq hb hw z zs he hlam hq hg
  rw [← ht, ← hh] at hS
  -- `T₃ = 2 (B/2 − 1) B^L`
  have hT : (b ^ 5 - 2) * q = 2 * ((2 ^ (t - 1) - 1) * (2 ^ t) ^ L4 ν) := by
    rw [hq, hB]
    have : 1 ≤ 2 ^ (t - 1) := Nat.one_le_two_pow
    rw [show 2 ^ t - 2 = 2 * (2 ^ (t - 1) - 1) by omega]
    ring
  rw [hS, hT, tau_shifted_iff ht1 hL h hbound, hh, coeff_Hpoly_Lexp ν 4 P hP z zs]
  constructor
  · intro h0
    have : (Nat.factorial 4 : ℤ) ≠ 0 := by positivity
    exact (mul_eq_zero.1 h0).resolve_left this
  · intro h0; rw [h0, mul_zero]

end Tau3

/-! ### The mask `M₁ = q³ − 1 − (b − 1) l` -/

section Mask

variable (ν : ℕ)

/-- The digits of `M₁`: `B − 1 − (b − 1) cⱼ`, `cⱼ` the coefficients of `lpoly` (`j < 3L`). -/
noncomputable def msList (b : ℕ) : List ℕ :=
  (List.range (3 * L4 ν)).map fun j => b ^ 5 - 1 - (b - 1) * ((lpoly ν 4).coeff j).toNat

theorem msList_length (b : ℕ) : (msList ν b).length = 3 * L4 ν := by simp [msList]

theorem msList_getD (b : ℕ) {j : ℕ} (hj : j < 3 * L4 ν) :
    (msList ν b).getD j 0 = b ^ 5 - 1 - (b - 1) * ((lpoly ν 4).coeff j).toNat := by
  unfold msList
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

theorem msList_getD_of_mem {b : ℕ} (hb : 1 ≤ b) {i : ℕ} (hi : i ∈ Finset.Icc 1 ν)
    (hj : 5 ^ i < 3 * L4 ν) : (msList ν b).getD (5 ^ i) 0 = b ^ 5 - b := by
  rw [msList_getD ν b hj, coeff_lpoly_of_mem ν hi]
  simp only [Int.toNat_one, mul_one]
  have : b ≤ b ^ 5 := Nat.le_self_pow (by norm_num) b
  omega

theorem msList_getD_of_not (b : ℕ) {j : ℕ} (hj : j < 3 * L4 ν)
    (h : ¬ ∃ i ∈ Finset.Icc 1 ν, 5 ^ i = j) : (msList ν b).getD j 0 = b ^ 5 - 1 := by
  rw [msList_getD ν b hj, coeff_lpoly_of_not ν h]; simp

theorem five_pow_lt_three_L4 {i : ℕ} (hi : i ≤ ν) : 5 ^ i < 3 * L4 ν := by
  have : 5 ^ i ≤ 5 ^ ν := Nat.pow_le_pow_right (by norm_num) hi
  have : 5 ^ ν ≤ L4 ν := five_pow_le_L4 ν
  have : 0 < L4 ν := by positivity
  omega

theorem mem_msList {b x : ℕ} (hb : 1 ≤ b) (hx : x ∈ msList ν b) : x < b ^ 5 := by
  unfold msList at hx
  rw [List.mem_map] at hx
  obtain ⟨j, -, rfl⟩ := hx
  have : 1 ≤ b ^ 5 := Nat.one_le_pow _ _ hb
  omega

/-- `l = Σ_{j<3L} cⱼ Bʲ` (as natural numbers). -/
theorem l_eq_sum {b l : ℕ} (hl : (l : ℤ) = (lpoly ν 4).eval ((b : ℤ) ^ 5)) :
    l = ∑ j ∈ range (3 * L4 ν), ((lpoly ν 4).coeff j).toNat * (b ^ 5) ^ j := by
  have h1 := ofDigits_coeffList_eq_eval (lpoly ν 4) (fun i => (coeff_lpoly_bounds ν i).1) (b ^ 5)
    (n := 3 * L4 ν) (lt_of_le_of_lt (natDegree_lpoly_le ν) (five_pow_lt_three_L4 ν le_rfl))
  push_cast at h1
  rw [← hl] at h1
  have h2 : l = Nat.ofDigits (b ^ 5) (coeffList (lpoly ν 4) (3 * L4 ν)) := by exact_mod_cast h1.symm
  rw [h2]
  unfold coeffList
  rw [ofDigits_map_range]

/-- `ofDigits B (msList) = q³ − 1 − (b − 1) l` (U9). -/
theorem ofDigits_msList {b l : ℕ} (hb : 1 ≤ b) (hl : (l : ℤ) = (lpoly ν 4).eval ((b : ℤ) ^ 5)) :
    Nat.ofDigits (b ^ 5) (msList ν b) = (b ^ 5) ^ (3 * L4 ν) - 1 - (b - 1) * l := by
  unfold msList
  rw [ofDigits_map_range]
  have hB : 1 ≤ b ^ 5 := Nat.one_le_pow _ _ hb
  have hbB : b ≤ b ^ 5 := Nat.le_self_pow (by norm_num) b
  have hgeom := geom_sum_mul_add (b ^ 5 - 1) (3 * L4 ν)
  rw [Nat.sub_add_cancel hB] at hgeom
  have hsum : ∑ j ∈ range (3 * L4 ν), (b ^ 5 - 1 - (b - 1) * ((lpoly ν 4).coeff j).toNat) * (b ^ 5) ^ j
      + (b - 1) * l = (∑ j ∈ range (3 * L4 ν), (b ^ 5) ^ j) * (b ^ 5 - 1) := by
    rw [l_eq_sum ν hl, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hc := coeff_lpoly_bounds ν j
    have hc1 : ((lpoly ν 4).coeff j).toNat ≤ 1 := by
      rw [Int.toNat_le]; exact_mod_cast hc.2
    have : (b - 1) * ((lpoly ν 4).coeff j).toNat ≤ b ^ 5 - 1 := by
      calc (b - 1) * ((lpoly ν 4).coeff j).toNat ≤ (b - 1) * 1 := Nat.mul_le_mul_left _ hc1
        _ ≤ b ^ 5 - 1 := by omega
    have e : (b ^ 5 - 1 - (b - 1) * ((lpoly ν 4).coeff j).toNat) +
        (b - 1) * ((lpoly ν 4).coeff j).toNat = b ^ 5 - 1 := by omega
    calc (b ^ 5 - 1 - (b - 1) * ((lpoly ν 4).coeff j).toNat) * (b ^ 5) ^ j +
          (b - 1) * (((lpoly ν 4).coeff j).toNat * (b ^ 5) ^ j)
        = ((b ^ 5 - 1 - (b - 1) * ((lpoly ν 4).coeff j).toNat) +
            (b - 1) * ((lpoly ν 4).coeff j).toNat) * (b ^ 5) ^ j := by ring
      _ = (b ^ 5) ^ j * (b ^ 5 - 1) := by rw [e]; ring
  omega

end Mask

/-! ### Recovering the digits of the code from `τ₂(g, M₁) = 0` -/

section Code

variable {ν : ℕ}

/-- `ofDigits b L = Σ_{j < |L|} L.getD j 0 · bʲ`. -/
theorem ofDigits_eq_sum_getD (b : ℕ) :
    ∀ L : List ℕ, Nat.ofDigits b L = ∑ j ∈ Finset.range L.length, (L.getD j 0 : ℕ) * b ^ j
  | [] => by simp [Nat.ofDigits]
  | h :: t => by
    rw [Nat.ofDigits_cons, ofDigits_eq_sum_getD b t, List.length_cons, Finset.sum_range_succ',
      Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    refine congrArg₂ (· + ·) ?_ rfl
    exact Finset.sum_congr rfl fun j _ => by ring

/-- The digit list of a number `g < B^n` (base-`B` digits padded with zeros to length `n`). -/
noncomputable def digitsPad (B g n : ℕ) : List ℕ :=
  B.digits g ++ List.replicate (n - (B.digits g).length) 0

theorem digitsPad_length {B g n : ℕ} (hB : 1 < B) (hg : g < B ^ n) : (digitsPad B g n).length = n := by
  unfold digitsPad
  have := (Nat.digits_length_le_iff hB g).2 hg
  simp; omega

theorem digitsPad_lt {B g n : ℕ} (hB : 1 < B) {x : ℕ} (hx : x ∈ digitsPad B g n) : x < B := by
  unfold digitsPad at hx
  rw [List.mem_append] at hx
  rcases hx with hx | hx
  · exact Nat.digits_lt_base hB hx
  · rw [List.mem_replicate] at hx; rw [hx.2]; omega

theorem ofDigits_digitsPad (B g n : ℕ) : Nat.ofDigits B (digitsPad B g n) = g := by
  unfold digitsPad
  rw [Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]

/-- Lemma 2.11 pointwise: for digit lists of length `n` with digits `< 2ᵗ`,
`τ₂(ofDigits, ofDigits) = 0 ⟺ ∀ j < n, τ₂(Lⱼ, Mⱼ) = 0`. -/
theorem tau_ofDigits_iff {B t n : ℕ} (hB : B = 2 ^ t) {L M : List ℕ} (hL : ∀ x ∈ L, x < B)
    (hM : ∀ x ∈ M, x < B) (hLn : L.length = n) (hMn : M.length = n) :
    τ 2 (Nat.ofDigits B L) (Nat.ofDigits B M) = 0 ↔
      ∀ j < n, τ 2 (L.getD j 0) (M.getD j 0) = 0 := by
  subst hB
  rw [lemma_2_11 L M hL hM (by omega), List.forall₂_iff_get]
  constructor
  · rintro ⟨-, h⟩ j hj
    have := h j (by omega) (by omega)
    rwa [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  · intro h
    refine ⟨by omega, fun j h₁ h₂ => ?_⟩
    have := h j (by omega)
    rwa [List.getD_eq_getElem _ _ h₁, List.getD_eq_getElem _ _ h₂] at this

set_option maxHeartbeats 1000000 in
/-- (4.8): from `τ₂(g, M₁) = 0` and `g < q = B^L`, the code is `g = Σ_{i=1}^ν zᵢ B^(5^i)` with
`zᵢ < b` (`b = 2ʷ`, `B = b⁵`). -/
theorem code_of_tau1 {b w g l x : ℕ} (hb : b = 2 ^ w) (hw : 1 ≤ w) (hxb : x < b)
    (hl : (l : ℤ) = (lpoly ν 4).eval ((b : ℤ) ^ 5)) (hg : g < (b ^ 5) ^ L4 ν)
    (hτ : τ 2 g ((b ^ 5) ^ (3 * L4 ν) - 1 - (b - 1) * l) = 0) :
    ∃ zs : Fin (ν + 1) → ℕ, zs 0 = x ∧ (∀ i, zs i < b) ∧
      (g : ℤ) = (gpoly ν zs).eval ((b : ℤ) ^ 5) := by
  have hb1 : 1 ≤ b := by rw [hb]; exact Nat.one_le_two_pow
  have hB : b ^ 5 = 2 ^ (5 * w) := by rw [hb, ← pow_mul, mul_comm]
  have hB1 : 1 < b ^ 5 := by rw [hB]; exact Nat.one_lt_two_pow (by omega)
  have hg3 : g < (b ^ 5) ^ (3 * L4 ν) :=
    lt_of_lt_of_le hg (Nat.pow_le_pow_right (by omega) (by omega))
  rw [← ofDigits_msList ν hb1 hl, ← ofDigits_digitsPad (b ^ 5) g (3 * L4 ν)] at hτ
  rw [tau_ofDigits_iff hB (n := 3 * L4 ν) (fun x hx => digitsPad_lt hB1 hx)
    (fun x hx => mem_msList ν hb1 hx) (digitsPad_length hB1 hg3) (msList_length ν b)] at hτ
  -- the digits at `5^i` are `< b`, the other digits vanish
  have hdig : ∀ j < 3 * L4 ν, (digitsPad (b ^ 5) g (3 * L4 ν)).getD j 0 < 2 ^ (5 * w) := by
    intro j hj
    rw [List.getD_eq_getElem _ _ (by rw [digitsPad_length hB1 hg3]; exact hj), ← hB]
    exact digitsPad_lt hB1 (List.getElem_mem _)
  have hpos : ∀ i ∈ Finset.Icc 1 ν, (digitsPad (b ^ 5) g (3 * L4 ν)).getD (5 ^ i) 0 < b := by
    intro i hi
    have hj : 5 ^ i < 3 * L4 ν := five_pow_lt_three_L4 ν (Finset.mem_Icc.1 hi).2
    have := hτ (5 ^ i) hj
    have e : b ^ 5 - b = 2 ^ (5 * w) - 2 ^ w := by rw [hB, hb]
    rw [msList_getD_of_mem ν hb1 hi hj, e, τ_comm] at this
    have h := (lemma_2_7 (k := w) (K := 5 * w) (by omega) (hdig _ hj)).2 this
    rwa [← hb] at h
  have hzero : ∀ j < 3 * L4 ν, (¬ ∃ i ∈ Finset.Icc 1 ν, 5 ^ i = j) →
      (digitsPad (b ^ 5) g (3 * L4 ν)).getD j 0 = 0 := by
    intro j hj hne
    have := hτ j hj
    have e : b ^ 5 - 1 = 2 ^ (5 * w) - 1 := by rw [hB]
    rw [msList_getD_of_not ν b hj hne, e, τ_comm] at this
    exact (lemma_2_7' (hdig _ hj)).2 this
  -- the solution
  refine ⟨fun i => if i = 0 then x else (digitsPad (b ^ 5) g (3 * L4 ν)).getD (5 ^ (i : ℕ)) 0,
    by simp, fun i => ?_, ?_⟩
  · dsimp only
    by_cases hi : i = 0
    · rw [if_pos hi]; exact hxb
    · rw [if_neg hi]
      have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
      exact hpos i (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  · -- both sides have the digit list `digitsPad`
    have h1 : (g : ℤ) = ((Nat.ofDigits (b ^ 5) (digitsPad (b ^ 5) g (3 * L4 ν)) : ℕ) : ℤ) := by
      rw [ofDigits_digitsPad]
    have h2 := ofDigits_coeffList_eq_eval (gpoly ν fun i =>
        if i = 0 then x else (digitsPad (b ^ 5) g (3 * L4 ν)).getD (5 ^ (i : ℕ)) 0)
      (coeff_gpoly_nonneg ν _) (b ^ 5) (n := 3 * L4 ν)
      (lt_of_le_of_lt (natDegree_gpoly_le ν _) (five_pow_lt_three_L4 ν le_rfl))
    rw [Nat.cast_pow] at h2
    rw [h1, ← h2]
    congr 2
    apply List.ext_getElem
    · rw [digitsPad_length hB1 hg3, coeffList_length]
    · intro j hj₁ hj₂
      rw [← List.getD_eq_getElem _ 0 hj₁, ← List.getD_eq_getElem _ 0 hj₂]
      rw [digitsPad_length hB1 hg3] at hj₁
      rw [coeffList_getD _ _ _ hj₁]
      by_cases h : ∃ i' : Fin (ν + 1), i' ≠ 0 ∧ 5 ^ (i' : ℕ) = j
      · obtain ⟨i', hi', rfl⟩ := h
        rw [coeff_gpoly_of_ne ν _ hi', if_neg hi', Int.toNat_natCast]
      · rw [coeff_gpoly_of_not ν _ h, Int.toNat_zero, hzero j hj₁]
        rw [exists_Icc_iff]; exact h

set_option maxHeartbeats 1000000 in
/-- Conversely, `g = Σ_{i=1}^ν zᵢ B^(5^i)` with `zᵢ < b` satisfies `τ₂(g, M₁) = 0` and `g < q`. -/
theorem tau1_of_code {b w l : ℕ} (hb : b = 2 ^ w) (hw : 1 ≤ w)
    (hl : (l : ℤ) = (lpoly ν 4).eval ((b : ℤ) ^ 5)) (zs : Fin (ν + 1) → ℕ) (hzs : ∀ i, zs i < b)
    {g : ℕ} (hg : (g : ℤ) = (gpoly ν zs).eval ((b : ℤ) ^ 5)) :
    τ 2 g ((b ^ 5) ^ (3 * L4 ν) - 1 - (b - 1) * l) = 0 ∧ g < b * (b ^ 5) ^ (5 ^ ν) := by
  have hb1 : 1 ≤ b := by rw [hb]; exact Nat.one_le_two_pow
  have hB : b ^ 5 = 2 ^ (5 * w) := by rw [hb, ← pow_mul, mul_comm]
  have hB1 : 1 < b ^ 5 := by rw [hB]; exact Nat.one_lt_two_pow (by omega)
  have hgL : g = Nat.ofDigits (b ^ 5) (coeffList (gpoly ν zs) (3 * L4 ν)) := by
    have := ofDigits_coeffList_eq_eval (gpoly ν zs) (coeff_gpoly_nonneg ν zs) (b ^ 5)
      (n := 3 * L4 ν) (lt_of_le_of_lt (natDegree_gpoly_le ν _) (five_pow_lt_three_L4 ν le_rfl))
    push_cast at this
    rw [← hg] at this
    exact_mod_cast this.symm
  have hcoeff : ∀ j, ((gpoly ν zs).coeff j).toNat < b := by
    intro j
    by_cases h : ∃ i' : Fin (ν + 1), i' ≠ 0 ∧ 5 ^ (i' : ℕ) = j
    · obtain ⟨i', hi', rfl⟩ := h
      rw [coeff_gpoly_of_ne ν _ hi', Int.toNat_natCast]; exact hzs i'
    · rw [coeff_gpoly_of_not ν _ h]; simp; omega
  constructor
  · rw [← ofDigits_msList ν hb1 hl, hgL]
    rw [tau_ofDigits_iff hB (n := 3 * L4 ν)
      (fun x hx => by
        obtain ⟨i, -, rfl⟩ := mem_coeffList hx
        exact lt_of_lt_of_le (hcoeff i) (Nat.le_self_pow (by norm_num) b))
      (fun x hx => mem_msList ν hb1 hx) (coeffList_length _ _) (msList_length ν b)]
    intro j hj
    rw [coeffList_getD _ _ _ hj]
    by_cases h : ∃ i ∈ Finset.Icc 1 ν, 5 ^ i = j
    · obtain ⟨i, hi, rfl⟩ := h
      rw [msList_getD_of_mem ν hb1 hi hj, hB, hb]
      have hi' : ∃ i' : Fin (ν + 1), i' ≠ 0 ∧ 5 ^ (i' : ℕ) = 5 ^ i := (exists_Icc_iff ν _).1 ⟨i, hi, rfl⟩
      obtain ⟨i', hi'0, hii'⟩ := hi'
      rw [← hii', coeff_gpoly_of_ne ν _ hi'0, Int.toNat_natCast]
      have hzi : zs i' < 2 ^ w := by rw [← hb]; exact hzs i'
      have hzi' : zs i' < 2 ^ (5 * w) :=
        lt_of_lt_of_le hzi (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [τ_comm]
      exact (lemma_2_7 (by omega) hzi').1 hzi
    · rw [coeff_gpoly_of_not ν _ (by rw [← exists_Icc_iff]; exact h)]
      simp only [Int.toNat_zero]
      exact τ_zero_left _
  · -- `g < b B^(5^ν)`
    have hgL' : g = Nat.ofDigits (b ^ 5) (coeffList (gpoly ν zs) (5 ^ ν + 1)) := by
      have := ofDigits_coeffList_eq_eval (gpoly ν zs) (coeff_gpoly_nonneg ν zs) (b ^ 5)
        (n := 5 ^ ν + 1) (lt_of_le_of_lt (natDegree_gpoly_le ν _) (Nat.lt_succ_self _))
      push_cast at this
      rw [← hg] at this
      exact_mod_cast this.symm
    rw [hgL']
    have := ofDigits_lt_mul_pow (B := b ^ 5) (z := b) hB1 (Nat.le_self_pow (by norm_num) b)
      (coeffList (gpoly ν zs) (5 ^ ν + 1))
      (fun x hx => by obtain ⟨i, -, rfl⟩ := mem_coeffList hx; exact hcoeff i)
      (by simp [coeffList])
    rwa [coeffList_length, Nat.add_sub_cancel] at this

end Code

/-! ### Lemma 2.9 for `e` and `l` -/

section Transfer

variable {ν : ℕ} {P : MvPolynomial (Fin (ν + 1)) ℤ} {z u y : ℕ}

/-- `2(2z)^(2L+1) ≤ B` for `B = b⁵`, `y < b`, `2(2z)^L ≤ y`. -/
theorem two_pow_le_B (hI : Index ν P z u y) {b : ℕ} (hyb : y < b) :
    2 * (2 * z) ^ (2 * L4 ν + 1) ≤ b ^ 5 := by
  have h1 := hI.y_ge
  have h2 := hI.two_z_le_y
  have hz := hI.two_le
  have h3 : (2 * z) ^ (2 * L4 ν + 1) = (2 * z) ^ L4 ν * (2 * z) ^ L4 ν * (2 * z) := by
    rw [← pow_add, ← pow_succ]; congr 1; ring
  have h4 : 2 * (2 * z) ^ (2 * L4 ν + 1) ≤ y * y * y := by
    rw [h3]
    calc 2 * ((2 * z) ^ L4 ν * (2 * z) ^ L4 ν * (2 * z))
        ≤ 2 * (2 * z) ^ L4 ν * (2 * (2 * z) ^ L4 ν) * (2 * z) := by ring_nf; omega
      _ ≤ y * y * y := Nat.mul_le_mul (Nat.mul_le_mul h1 h1) h2
  have h5 : y * y * y ≤ b ^ 5 := by
    have : y ≤ b := hyb.le
    have : y * y * y ≤ b * b * b := Nat.mul_le_mul (Nat.mul_le_mul this this) this
    have : b * b * b ≤ b ^ 5 := by
      rw [show b * b * b = b ^ 3 by ring]
      exact Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  omega

/-- Lemma 2.9 packaged for the digit polynomials (coefficients in `[0, 2z)`, degree `≤ L`):
for `V ≥ 0` and `v = p(2z)`,
`V = p(B) ⟺ V ≡ v (mod B − 2z) ∧ V < B^(2L) ∧ τ₂(V, mask29 B (2z) (2L)) = 0`. -/
theorem transfer_iff (hI : Index ν P z u y) {b w : ℕ} (hb : b = 2 ^ w) (hw : 1 ≤ w) (hyb : y < b)
    (p : ℤ[X]) (hp0 : ∀ i, 0 ≤ p.coeff i) (hp1 : ∀ i, p.coeff i < 2 * z)
    (hdeg : p.natDegree ≤ L4 ν) {v V : ℕ} (hv : (v : ℤ) = p.eval (2 * z : ℤ)) :
    (V : ℤ) = p.eval ((b : ℤ) ^ 5) ↔
      (V ≡ v [MOD b ^ 5 - 2 * z] ∧ V < (b ^ 5) ^ (2 * L4 ν) ∧
        τ 2 V (mask29 (b ^ 5) (2 * z) (2 * L4 ν)) = 0) := by
  obtain ⟨s, hs⟩ := hI.pow2
  have hz := hI.two_le
  have h2z : 2 * z = 2 ^ (s + 1) := by rw [hs, pow_succ]; ring
  have hB : b ^ 5 = 2 ^ (5 * w) := by rw [hb, ← pow_mul, mul_comm]
  have hs1 : 1 ≤ s + 1 := by omega
  have hst : s + 1 ≤ 5 * w := by
    have : 2 ^ (s + 1) ≤ 2 ^ (5 * w) := by
      rw [← h2z, ← hB]
      have := hI.two_z_le_y
      have : y ≤ b ^ 5 := hyb.le.trans (Nat.le_self_pow (by norm_num) b)
      omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  have hzB := two_pow_le_B hI hyb
  rw [h2z, hB] at hzB
  -- the digit list of `v`
  obtain ⟨ys, hys⟩ : ∃ ys, ys = coeffList p (L4 ν + 1) := ⟨_, rfl⟩
  have hysz : ∀ x ∈ ys, x < 2 ^ (s + 1) := by
    intro x hx
    rw [hys] at hx
    obtain ⟨i, -, rfl⟩ := mem_coeffList hx
    rw [← h2z, Int.toNat_lt (hp0 i)]; push_cast; exact hp1 i
  have hlen : ys.length ≤ L4 ν + 1 := by rw [hys, coeffList_length]
  have hvy : v = Nat.ofDigits (2 ^ (s + 1)) ys := by
    have := ofDigits_coeffList_eq_eval p hp0 (2 * z) (n := L4 ν + 1) (by omega)
    rw [← hys] at this
    have h' : ((Nat.ofDigits (2 * z) ys : ℕ) : ℤ) = (v : ℤ) := by
      rw [this, hv]; push_cast; rfl
    have h'' : v = Nat.ofDigits (2 * z) ys := by exact_mod_cast h'.symm
    rw [h2z] at h''
    exact h''
  have hVB : (V : ℤ) = p.eval ((b : ℤ) ^ 5) ↔ V = Nat.ofDigits (2 ^ (5 * w)) ys := by
    have := ofDigits_coeffList_eq_eval p hp0 (b ^ 5) (n := L4 ν + 1) (by omega)
    rw [← hys, Nat.cast_pow] at this
    rw [← hB]
    constructor
    · intro h
      have h' : (V : ℤ) = ((Nat.ofDigits (b ^ 5) ys : ℕ) : ℤ) := h.trans this.symm
      exact_mod_cast h'
    · intro h; rw [h]; exact this
  have h29 := lemma_2_9 (s := s + 1) (t := 5 * w) (n := L4 ν) (m := 2 * L4 ν) (k := 2 * L4 ν)
    hs1 hst (by omega) le_rfl hzB hysz hlen V
  rw [hVB, h29, ← hvy, ← h2z, ← hB]
  -- adjust (ii)
  have hpB : p.eval ((b : ℤ) ^ 5) < ((b ^ 5) ^ (2 * L4 ν) : ℕ) := by
    have h1 := ofDigits_coeffList_eq_eval p hp0 (b ^ 5) (n := L4 ν + 1) (by omega)
    rw [← hys, Nat.cast_pow] at h1
    rw [← h1]
    have h2 := Nat.ofDigits_lt_base_pow_length (b := b ^ 5) (l := ys)
      (by rw [hB]; exact Nat.one_lt_two_pow (by omega))
      (fun x hx => lt_of_lt_of_le (b := 2 * z) (by rw [h2z]; exact hysz x hx) (by
        rw [h2z, hB]; exact Nat.pow_le_pow_right (by norm_num) hst))
    rw [hys, coeffList_length] at h2
    have h3 : (b ^ 5) ^ (L4 ν + 1) ≤ (b ^ 5) ^ (2 * L4 ν) :=
      Nat.pow_le_pow_right (by rw [hB]; positivity)
        (by have : 1 ≤ L4 ν := Nat.one_le_pow _ _ (by norm_num); omega)
    have h4 : Nat.ofDigits (b ^ 5) ys < (b ^ 5) ^ (2 * L4 ν) := by
      rw [hys]; exact lt_of_lt_of_le h2 h3
    exact_mod_cast h4
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, h3⟩
    have hV : (V : ℤ) = p.eval ((b : ℤ) ^ 5) := by
      rw [hVB]
      rw [h29, ← hvy, ← h2z, ← hB]
      exact ⟨h1, h2, h3⟩
    rw [← hV] at hpB
    exact_mod_cast hpB
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, h3⟩
    calc V < (b ^ 5) ^ (2 * L4 ν) := h2
      _ ≤ 2 * z * (b ^ 5) ^ (2 * L4 ν) := Nat.le_mul_of_pos_left _ (by omega)

end Transfer

end Jones1982
