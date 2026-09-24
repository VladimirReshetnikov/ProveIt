import Diophantine.Paper1982.Theorem2

/-!
# Jones 1982, §3: membership through two unknowns and one central binomial coefficient

The first step of the reduction to nine unknowns.  Fix the index `⟨z, u, y⟩` of a normalized
quartic.  The ceiling is `b = xy + 1 + ε`, the radix `B = b⁵`, and every other quantity of the
§4 system — `q = B^L`, `λ`, `θ = B − 2z`, `e = e(B)`, `l = l(B)` — is a fixed function of `b`.
Then, for `x ≥ 1`, `x ∈ W` iff for some `ε` and `g ≥ 1`:

* `b` is a power of two,
* `g < 4b·B^(5^ν)` (necessity even gives `g < b·B^(5^ν)`), and
* `N² ∣ C(2R, R)` for `N = q¹⁶` and the packed code `R` of Theorem 2.

This replaces the §3 coding of the article (base `β b^δ`) by the §4 coding with the index
constants, which has the same effect: the eliminated quantities are polynomials in `ε` and `g`.
-/

namespace Jones1982.Nine

open Polynomial Finset

variable {ν : ℕ} {P : MvPolynomial (Fin (ν + 1)) ℤ} {z u y : ℕ}

/-- The ceiling. -/
def bN (x y ε : ℕ) : ℕ := x * y + 1 + ε

/-- `q = B^L`. -/
def qN (ν b : ℕ) : ℕ := (b ^ 5) ^ L4 ν

/-- `λ = Σ_{i<4L} Bⁱ`. -/
def lamN (ν b : ℕ) : ℕ := ∑ i ∈ range (4 * L4 ν), (b ^ 5) ^ i

/-- `θ = B − 2z`. -/
def θN (z b : ℕ) : ℕ := b ^ 5 - 2 * z

/-- `e = e(B)`. -/
noncomputable def eN (ν : ℕ) (P : MvPolynomial (Fin (ν + 1)) ℤ) (z b : ℕ) : ℕ :=
  Nat.ofDigits (b ^ 5) (coeffList (epoly ν 4 P z) (L4 ν + 1))

/-- `l = l(B)`. -/
noncomputable def lN (ν b : ℕ) : ℕ :=
  Nat.ofDigits (b ^ 5) (coeffList (lpoly ν 4) (L4 ν + 1))

/-- The packed code `R` of Theorem 2. -/
noncomputable def RN (ν : ℕ) (P : MvPolynomial (Fin (ν + 1)) ℤ) (x z b g : ℕ) : ℕ :=
  centralCode (qN ν b ^ 16) (packedS x z b (eN ν P z b) g (lN ν b) (qN ν b) (lamN ν b))
    (packedT b (lN ν b) (qN ν b) (θN z b) (lamN ν b))

theorem eN_eq (hI : Index ν P z u y) (b : ℕ) :
    (eN ν P z b : ℤ) = (epoly ν 4 P z).eval ((b : ℤ) ^ 5) := by
  have := ofDigits_coeffList_eq_eval (epoly ν 4 P z) (fun i => (hI.coeff_epoly_bounds i).1) (b ^ 5)
    (n := L4 ν + 1) (lt_of_le_of_lt (natDegree_epoly_le ν 4 P z) (Nat.lt_succ_self _))
  rw [Nat.cast_pow] at this
  rw [eN, this]

theorem lN_eq (ν b : ℕ) : (lN ν b : ℤ) = (lpoly ν 4).eval ((b : ℤ) ^ 5) := by
  have := ofDigits_coeffList_eq_eval (lpoly ν 4) (fun i => (coeff_lpoly_bounds ν i).1) (b ^ 5)
    (n := L4 ν + 1) (lt_of_le_of_lt ((natDegree_lpoly_le ν).trans (five_pow_le_L4 ν))
      (Nat.lt_succ_self _))
  rw [Nat.cast_pow] at this
  rw [lN, this]

theorem lamN_eq (ν b : ℕ) : (lamN ν b : ℤ) = (lampoly ν 4).eval ((b : ℤ) ^ 5) := by
  rw [eval_lampoly, lamN]; push_cast; rfl

theorem eN_lt (hI : Index ν P z u y) {b : ℕ} (hB1 : 1 < b ^ 5) (h2zB : 2 * z ≤ b ^ 5) :
    eN ν P z b < 2 * z * (b ^ 5) ^ L4 ν := by
  rw [eN]
  have := ofDigits_lt_mul_pow (B := b ^ 5) (z := 2 * z) hB1 h2zB
    (coeffList (epoly ν 4 P z) (L4 ν + 1))
    (fun x hx => by
      obtain ⟨i, -, rfl⟩ := mem_coeffList hx
      have := hI.coeff_epoly_bounds i
      rw [Int.toNat_lt this.1]; push_cast; exact this.2)
    (by simp [coeffList])
  rwa [coeffList_length, Nat.add_sub_cancel] at this

theorem lN_lt (ν : ℕ) {b : ℕ} (hB1 : 1 < b ^ 5) : lN ν b < 2 * (b ^ 5) ^ (5 ^ ν) := by
  have hl' : lN ν b = Nat.ofDigits (b ^ 5) (coeffList (lpoly ν 4) (5 ^ ν + 1)) := by
    have := ofDigits_coeffList_eq_eval (lpoly ν 4) (fun i => (coeff_lpoly_bounds ν i).1) (b ^ 5)
      (n := 5 ^ ν + 1) (lt_of_le_of_lt (natDegree_lpoly_le ν) (Nat.lt_succ_self _))
    rw [Nat.cast_pow, ← lN_eq] at this
    exact_mod_cast this.symm
  rw [hl']
  have := ofDigits_lt_mul_pow (B := b ^ 5) (z := 2) hB1 (by omega)
    (coeffList (lpoly ν 4) (5 ^ ν + 1))
    (fun x hx => by
      obtain ⟨i, -, rfl⟩ := mem_coeffList hx
      have := coeff_lpoly_bounds ν i
      rw [Int.toNat_lt this.1]; push_cast; linarith)
    (by simp [coeffList])
  rwa [coeffList_length, Nat.add_sub_cancel] at this

/-- `e > y` and `l > u` once `2z < B`. -/
theorem y_lt_eN (hI : Index ν P z u y) {b : ℕ} (h2zB : 2 * z < b ^ 5) : y < eN ν P z b := by
  have h2zB' : (2 * (z : ℤ)) < (b : ℤ) ^ 5 := by exact_mod_cast h2zB
  obtain ⟨k₀, hk₀, hexp⟩ : ∃ k₀ ∈ star ν 4, expo ν 4 k₀ = 0 :=
    ⟨(fun _ => 0 : Fin (ν + 2) → ℕ) + Pi.single 0 4, by rw [mem_star]; simp, by simp [expo]⟩
  have h1 := eval_lt_eval_of_pos (p := epoly ν 4 P z) (fun i => (hI.coeff_epoly_bounds i).1)
    (n := L4 ν - expo ν 4 k₀) (by rw [hexp]; exact Nat.one_le_pow _ _ (by norm_num))
    (by
      rw [coeff_epoly_of_mem ν 4 P z hk₀]
      have := hI.big k₀ hk₀
      have := abs_lt.1 (show |Pcoef ν P k₀| < z by omega)
      push_cast; linarith)
    (a := 2 * (z : ℤ)) (by positivity) h2zB'
  rw [← hI.hy, ← eN_eq hI] at h1
  exact_mod_cast h1

theorem u_lt_lN (hI : Index ν P z u y) (hν : 1 ≤ ν) {b : ℕ} (h2zB : 2 * z < b ^ 5) :
    u < lN ν b := by
  have h2zB' : (2 * (z : ℤ)) < (b : ℤ) ^ 5 := by exact_mod_cast h2zB
  have h1 := eval_lt_eval_of_pos (p := lpoly ν 4) (fun i => (coeff_lpoly_bounds ν i).1)
    (n := 5 ^ 1) (by norm_num)
    (by rw [coeff_lpoly_of_mem ν (Finset.mem_Icc.2 ⟨le_rfl, hν⟩)]; norm_num)
    (a := 2 * (z : ℤ)) (by positivity) h2zB'
  rw [← hI.hu, ← lN_eq] at h1
  exact_mod_cast h1

theorem two_z_lt (hI : Index ν P z u y) {x : ℕ} (hx : 0 < x) (ε : ℕ) : 2 * z < bN x y ε ^ 5 := by
  have h2zy := hI.two_z_le_y
  have hyx : y ≤ x * y := Nat.le_mul_of_pos_left _ hx
  have hbB : bN x y ε ≤ bN x y ε ^ 5 := Nat.le_self_pow (by norm_num) _
  rw [bN] at hbB ⊢
  omega

/-- The common equations of §4, with every eliminated quantity a function of `b`, for any
`g < 4b·B^(5^ν)`. -/
theorem uEqs_of_bound (hν : 1 ≤ ν) (hI : Index ν P z u y) {x : ℕ} (hx : 0 < x) {ε g : ℕ}
    (hgb : g < 4 * bN x y ε * (bN x y ε ^ 5) ^ (5 ^ ν)) :
    ∃ m t α : ℕ, 0 < m ∧ 0 < t ∧ 0 < α ∧
      UEqs ν x z u y (bN x y ε) (eN ν P z (bN x y ε)) g (lN ν (bN x y ε)) m (qN ν (bN x y ε)) t
        (θN z (bN x y ε)) (lamN ν (bN x y ε)) α := by
  set b := bN x y ε with hbdef
  have hy1 := hI.y_pos
  have hz2 := hI.two_le
  have hxy1 : 1 ≤ x * y := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hbxy : x * y < b := by rw [hbdef, bN]; omega
  have hb2 : 2 ≤ b := by omega
  have hyb : y < b := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hx) hbxy
  have hB1 : 1 < b ^ 5 := lt_of_lt_of_le (by omega) (Nat.le_self_pow (by norm_num) b)
  have hbB : b ≤ b ^ 5 := Nat.le_self_pow (by norm_num) b
  have h2zy := hI.two_z_le_y
  have h2zB : 2 * z < b ^ 5 := by omega
  -- `λ`, `θ`, `q`
  have U4 : lamN ν b + qN ν b ^ 4 = 1 + lamN ν b * b ^ 5 := by
    have hg := geom_sum_mul_add (b ^ 5 - 1) (4 * L4 ν)
    rw [Nat.sub_add_cancel (by omega)] at hg
    rw [qN, ← pow_mul, mul_comm (L4 ν) 4, ← hg, lamN, Nat.mul_sub, mul_one]
    have : (∑ i ∈ range (4 * L4 ν), (b ^ 5) ^ i) ≤ (∑ i ∈ range (4 * L4 ν), (b ^ 5) ^ i) * b ^ 5 :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  have U5 : θN z b + 2 * z = b ^ 5 := by rw [θN]; omega
  -- `m`, `t`: `B − 2z` divides `p(B) − p(2z)`
  have hθZ : (θN z b : ℤ) = (b : ℤ) ^ 5 - 2 * z := by
    rw [θN]; push_cast [h2zB.le]; ring
  have hq2 : qN ν b ^ 2 = (b ^ 5) ^ (2 * L4 ν) := by rw [qN, ← pow_mul, mul_comm]
  have hey := y_lt_eN hI h2zB
  have hlu := u_lt_lN hI hν h2zB
  have hey' : θN z b ∣ eN ν P z b - y := by
    have h1 : (θN z b : ℤ) ∣ (eN ν P z b : ℤ) - y := by
      rw [hθZ, eN_eq hI, hI.hy]; exact Polynomial.sub_dvd_eval_sub _ _ _
    rw [← Int.natCast_dvd_natCast]; push_cast [hey.le]; exact h1
  have hlu' : θN z b ∣ lN ν b - u := by
    have h1 : (θN z b : ℤ) ∣ (lN ν b : ℤ) - u := by
      rw [hθZ, lN_eq, hI.hu]; exact Polynomial.sub_dvd_eval_sub _ _ _
    rw [← Int.natCast_dvd_natCast]; push_cast [hlu.le]; exact h1
  obtain ⟨m, hm⟩ := hey'
  have hm1 : 1 ≤ m := by
    by_contra h0; push Not at h0
    have : m = 0 := by omega
    rw [this, mul_zero] at hm; omega
  obtain ⟨t, ht⟩ := hlu'
  have ht1 : 1 ≤ t := by
    by_contra h0; push Not at h0
    have : t = 0 := by omega
    rw [this, mul_zero] at ht; omega
  -- (U6')
  have he_lt := eN_lt hI hB1 h2zB.le
  have hl_lt := lN_lt ν hB1 (b := b)
  have hbig : eN ν P z b * lN ν b * g ^ 2 < qN ν b ^ 2 := by
    have h1 : eN ν P z b * lN ν b * g ^ 2 <
        (2 * z * (b ^ 5) ^ L4 ν) * (2 * (b ^ 5) ^ (5 ^ ν)) * (4 * b * (b ^ 5) ^ (5 ^ ν)) ^ 2 :=
      Nat.mul_lt_mul'' (Nat.mul_lt_mul'' he_lt hl_lt) (Nat.pow_lt_pow_left hgb two_ne_zero)
    have h2 : (2 * z * (b ^ 5) ^ L4 ν) * (2 * (b ^ 5) ^ (5 ^ ν)) * (4 * b * (b ^ 5) ^ (5 ^ ν)) ^ 2 =
        (64 * z * b ^ 2) * (b ^ 5) ^ (L4 ν + 3 * 5 ^ ν) := by
      rw [pow_add, pow_mul]; ring
    have h3 : 64 * z * b ^ 2 ≤ b ^ 5 := by
      have hyb' := hI.y_big hν
      have h81 : 81 ≤ (ν + 2) ^ 4 := by
        calc 81 = 3 ^ 4 := by norm_num
          _ ≤ (ν + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      have h64 : 64 * z ≤ b := by nlinarith
      calc 64 * z * b ^ 2 ≤ b * b ^ 2 := Nat.mul_le_mul_right _ h64
        _ = b ^ 3 := by ring
        _ ≤ b ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h4 : (b ^ 5) ^ (L4 ν + 3 * 5 ^ ν + 1) ≤ (b ^ 5) ^ (2 * L4 ν) := by
      apply Nat.pow_le_pow_right (by omega)
      rw [L4_eq, pow_succ]
      have : 0 < 5 ^ ν := by positivity
      omega
    calc eN ν P z b * lN ν b * g ^ 2 < (64 * z * b ^ 2) * (b ^ 5) ^ (L4 ν + 3 * 5 ^ ν) := by
          rw [← h2]; exact h1
      _ ≤ b ^ 5 * (b ^ 5) ^ (L4 ν + 3 * 5 ^ ν) := Nat.mul_le_mul_right _ h3
      _ = (b ^ 5) ^ (L4 ν + 3 * 5 ^ ν + 1) := by ring
      _ ≤ (b ^ 5) ^ (2 * L4 ν) := h4
      _ = qN ν b ^ 2 := hq2.symm
  have hlt : eN ν P z b * lN ν b * g ^ 2 < (b - x * y) * qN ν b ^ 2 :=
    lt_of_lt_of_le hbig (Nat.le_mul_of_pos_left _ (by omega))
  refine ⟨m, t, (b - x * y) * qN ν b ^ 2 - eN ν P z b * lN ν b * g ^ 2, hm1, ht1, by omega,
    ?_, by rw [qN, q_eq], U4, U5, by rw [Nat.mul_comm t]; omega, by rw [Nat.mul_comm m]; omega⟩
  have h1 : ((b - x * y) * qN ν b ^ 2 : ℕ) =
      eN ν P z b * lN ν b * g ^ 2 + ((b - x * y) * qN ν b ^ 2 - eN ν P z b * lN ν b * g ^ 2) := by
    omega
  have h2 := congrArg (fun n : ℕ => (n : ℤ)) h1
  push_cast [Nat.cast_sub hbxy.le] at h2
  push_cast
  linarith

/-- **Sufficiency.** -/
theorem mem_of_reduced (hν : 1 ≤ ν) (hP : P.totalDegree ≤ 4) (hI : Index ν P z u y) {x : ℕ}
    (hx : 0 < x) {ε g k : ℕ} (hg : 0 < g) (hb : bN x y ε = 2 ^ k)
    (hgb : g < 4 * bN x y ε * (bN x y ε ^ 5) ^ (5 ^ ν))
    (hdvd : (qN ν (bN x y ε) ^ 16) ^ 2 ∣
      (2 * RN ν P x z (bN x y ε) g).choose (RN ν P x z (bN x y ε) g)) :
    Wset P x := by
  obtain ⟨m, t, α, hm, ht, hα, hU⟩ := uEqs_of_bound hν hI hx hgb
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rw [pow_zero, bN] at hb
      have := Nat.mul_pos hx hI.y_pos
      omega
    · exact h
  have hy1 := hI.y_pos
  have hz2 := hI.two_le
  have hl : 0 < lN ν (bN x y ε) := by
    have := u_lt_lN hI hν (two_z_lt hI hx ε)
    omega
  have hUS := (hU.usys_iff_central hI hx hb hk hg hl hm ht hα).2 hdvd
  exact mem_of_USys hν hP hI hx hb hk hg hl hm ht hα hUS

/-- The size facts needed for Lemma 2.25. -/
theorem sizes_of_reduced (hν : 1 ≤ ν) (hI : Index ν P z u y) {x : ℕ}
    (hx : 0 < x) {ε g : ℕ} (hg : 0 < g)
    (hgb : g < 4 * bN x y ε * (bN x y ε ^ 5) ^ (5 ^ ν)) :
    8 ≤ qN ν (bN x y ε) ^ 16 ∧ 8 ≤ RN ν P x z (bN x y ε) g ∧
      bN x y ε ≤ qN ν (bN x y ε) ^ 16 ∧ bN x y ε ≤ RN ν P x z (bN x y ε) g ∧
      (RN ν P x z (bN x y ε) g : ℤ) = rPolynomial x z (bN x y ε) (eN ν P z (bN x y ε)) g
        (lN ν (bN x y ε)) (qN ν (bN x y ε) ^ 16) (qN ν (bN x y ε)) (θN z (bN x y ε))
        (lamN ν (bN x y ε)) := by
  obtain ⟨m, t, α, hm, ht, hα, hU⟩ := uEqs_of_bound hν hI hx hgb
  have hb2 : 2 ≤ bN x y ε := by
    have := Nat.mul_pos hx hI.y_pos
    rw [bN]; omega
  have hl : 0 < lN ν (bN x y ε) := by
    obtain ⟨-, -, -, -, -, -, -, hlb, -⟩ := hU.sizes hI hx hb2 hg (by
      have := u_lt_lN hI hν (two_z_lt hI hx ε)
      omega) hm ht hα
    omega
  obtain ⟨_, _, _, hlq, _, hbq, _⟩ := hU.sizes hI hx hb2 hg hl hm ht hα
  have hM := M1_bounds hb2 hbq hlq
  have hS := hU.S3_nonneg hI hx hb2 hg hl hm ht hα
  have hr := centralCode_eq_rPolynomial (θ := θN z (bN x y ε)) hb2 hM
    (n := qN ν (bN x y ε) ^ 16) (Nat.one_le_pow _ _ (by rw [qN]; positivity)) hS
  obtain ⟨h1, -, h3, h4, h5⟩ := hU.packing_sizes hI hx hb2 hg hl hm ht hα rfl hr
  exact ⟨h1, h4, h3, h5, hr⟩

set_option maxHeartbeats 1000000 in
/-- **Necessity**, with the stronger bound `g < b·B^(5^ν)`. -/
theorem reduced_of_mem (hν : 1 ≤ ν) (hP : P.totalDegree ≤ 4) (hnorm : Normalized P)
    (hI : Index ν P z u y) {x : ℕ} (hx : 0 < x) (hW : Wset P x) :
    ∃ ε g k : ℕ, 0 < g ∧ bN x y ε = 2 ^ k ∧ g < bN x y ε * (bN x y ε ^ 5) ^ (5 ^ ν) ∧
      (qN ν (bN x y ε) ^ 16) ^ 2 ∣
        (2 * RN ν P x z (bN x y ε) g).choose (RN ν P x z (bN x y ε) g) := by
  obtain ⟨b, e, g, l, m, q, t, θ, lam, α, w, he0, hg0, hl0, hm, hq0, ht, hθ0, hlam0, hα, hw, hb,
    hU, -⟩ := USys_of_mem hν hP hnorm hI hx hW
  have hb2 : 2 ≤ b := by rw [hb]; exact Nat.one_lt_two_pow (by omega)
  obtain ⟨hbxy, h2zB, heq, hlq, hgq, hbq, heb, hlb, hlam⟩ :=
    hU.toUEqs.sizes hI hx hb2 hg0 hl0 hm ht hα
  have hdvd := (hU.toUEqs.usys_iff_central hI hx hb hw hg0 hl0 hm ht hα).1 hU
  obtain ⟨⟨U6, U3, U4, U5, U7, U8⟩, τ1, τ2, τ3⟩ := hU
  have hq : q = (b ^ 5) ^ L4 ν := by rw [U3, q_eq]
  have hy1 := hI.y_pos
  have hz2 := hI.two_le
  have hxb : x < b := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hy1) hbxy
  have hyb : y < b := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hx) hbxy
  have hθ : θ = b ^ 5 - 2 * z := by omega
  have hq2 : q ^ 2 = (b ^ 5) ^ (2 * L4 ν) := by rw [hq, ← pow_mul, mul_comm]
  rw [hq] at τ2
  obtain ⟨hτe, hτl⟩ := (tau2_iff hb hw (by omega) h2zB U5 hlam (by rw [← hq2]; exact heq)).1 τ2
  have he : (e : ℤ) = (epoly ν 4 P z).eval ((b : ℤ) ^ 5) := by
    rw [transfer_iff hI hb hw hyb (epoly ν 4 P z) (fun i => (hI.coeff_epoly_bounds i).1)
      (fun i => (hI.coeff_epoly_bounds i).2) (natDegree_epoly_le ν 4 P z) hI.hy]
    refine ⟨?_, by rw [← hq2]; exact heq, hτe⟩
    rw [← hθ, U8]
    exact ((Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).2
      ⟨m, by rw [Nat.add_sub_cancel_left, mul_comm]⟩).symm
  have hl : (l : ℤ) = (lpoly ν 4).eval ((b : ℤ) ^ 5) := by
    rw [transfer_iff hI hb hw hyb (lpoly ν 4) (fun i => (coeff_lpoly_bounds ν i).1)
      (fun i => by have := (coeff_lpoly_bounds ν i).2; push_cast; linarith)
      ((natDegree_lpoly_le ν).trans (five_pow_le_L4 ν)) hI.hu]
    refine ⟨?_, by rw [← hq2]; exact hlq, hτl⟩
    rw [← hθ, U7]
    exact ((Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).2
      ⟨t, by rw [Nat.add_sub_cancel_left, mul_comm]⟩).symm
  have hq3 : q ^ 3 = (b ^ 5) ^ (3 * L4 ν) := by rw [hq, ← pow_mul, mul_comm]
  rw [hq3] at τ1
  obtain ⟨zs, -, hzs, hgZ⟩ := code_of_tau1 hb hw hxb hl (by rw [← hq]; exact hgq) τ1
  have hgb := (tau1_of_code hb hw hl zs hzs hgZ).2
  obtain ⟨ε, rfl⟩ : ∃ ε, b = x * y + 1 + ε := ⟨b - x * y - 1, by omega⟩
  have heN : e = eN ν P z (x * y + 1 + ε) := by
    have := (eN_eq hI (x * y + 1 + ε)).trans he.symm; exact_mod_cast this.symm
  have hlN : l = lN ν (x * y + 1 + ε) := by
    have := (lN_eq ν (x * y + 1 + ε)).trans hl.symm; exact_mod_cast this.symm
  refine ⟨ε, g, w, hg0, hb, hgb, ?_⟩
  have hlamN : lam = lamN ν (x * y + 1 + ε) := hlam
  have hθN : θ = θN z (x * y + 1 + ε) := hθ
  have hqN : q = qN ν (x * y + 1 + ε) := hq
  rw [heN, hlN, hlamN, hθN, hqN] at hdvd
  exact hdvd

end Jones1982.Nine
