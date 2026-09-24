import Diophantine.Paper1982.Master2

/-!
# Jones 1982, §4: the master equivalence behind Theorems 1–3

> `x ∈ W_{⟨z,u,y⟩}` iff conditions (U2)–(U5), (U6'), (U7)–(U17) hold together with `b pow 2`
> and `τ₂(Sᵢ, Tᵢ) = 0` (`i = 1, 2, 3`).

`USys` collects (with `B = b⁵` and `q = B^L` eliminated): (U6') `elg² + α = (b − xy)q²`
(the article's `elg² < q²(b − xy)`, with `α ≥ 1`), (U3) `q = b^(5^(ν+2))`,
(U4) `λ + q⁴ = 1 + λb⁵`, (U5) `θ + 2z = b⁵`, (U7) `l = u + tθ`, (U8) `e = y + mθ`, and the
three `τ`-conditions (4.8), (4.4), (4.11) with `S₁ = g`, `T₁ = M₁ = q³ − 1 − (b−1)l`,
`S₂ = e + lq²`, `T₂ = θλ`, `S₃ = 2(e − zλ)(1 + xb⁵ + g)⁴ + b⁵λ(1 + q⁴)`, `T₃ = (b⁵ − 2)q`.
All unknowns are positive integers; `g ≥ 1` uses the normalization `P(x, 0, …, 0) ≠ 0`.

`master`: for `ν ≥ 1`, `P` of degree `≤ 4`, normalized, with index `⟨z, u, y⟩` (4.1) and
`x ≥ 1`: `x ∈ W_{⟨z,u,y⟩}` iff `USys` is solvable in positive integers with `b = 2ʷ`.
-/

namespace Jones1982

open Polynomial Finset

/-- The equations (U6'), (U3), (U4), (U5), (U7), (U8) common to Theorems 1–3. -/
structure UEqs (ν : ℕ) (x z u y b e g l m q t θ lam α : ℕ) : Prop where
  U6 : (e : ℤ) * l * g ^ 2 + α = ((b : ℤ) - x * y) * q ^ 2
  U3 : q = b ^ (5 ^ (ν + 2))
  U4 : lam + q ^ 4 = 1 + lam * b ^ 5
  U5 : θ + 2 * z = b ^ 5
  U7 : l = u + t * θ
  U8 : e = y + m * θ

/-- The conditions of §4 common to Theorems 1–3: the equations and the three `τ`-conditions. -/
structure USys (ν : ℕ) (x z u y b e g l m q t θ lam α : ℕ) : Prop
    extends UEqs ν x z u y b e g l m q t θ lam α where
  τ1 : τ 2 g (q ^ 3 - 1 - (b - 1) * l) = 0
  τ2 : τ 2 (e + l * q ^ 2) (θ * lam) = 0
  τ3 : τ 2 (2 * ((e : ℤ) - z * lam) * (1 + x * b ^ 5 + g) ^ 4 + b ^ 5 * lam * (1 + q ^ 4)).toNat
        ((b ^ 5 - 2) * q) = 0

section Master

variable {ν : ℕ} {P : MvPolynomial (Fin (ν + 1)) ℤ} {z u y : ℕ}

theorem q_eq (ν b : ℕ) : b ^ (5 ^ (ν + 2)) = (b ^ 5) ^ L4 ν := by
  rw [← pow_mul, L4_eq, ← pow_succ']

/-- The mask `θλ` of (4.4) is `mask29 B (2z) (4L)`, and it splits into two halves. -/
theorem theta_lam_eq {b lam θ : ℕ} (hz : 2 * z ≤ b ^ 5) (hθ : θ + 2 * z = b ^ 5)
    (hlam : lam = ∑ i ∈ range (4 * L4 ν), (b ^ 5) ^ i) :
    θ * lam = mask29 (b ^ 5) (2 * z) (2 * L4 ν) + mask29 (b ^ 5) (2 * z) (2 * L4 ν) * (b ^ 5) ^ (2 * L4 ν) := by
  rw [← mask29_add, show 2 * L4 ν + 2 * L4 ν = 4 * L4 ν by ring, mask29_eq, hlam]
  congr 1; omega

theorem mask29_lt {b w : ℕ} (hb : b = 2 ^ w) (hw : 1 ≤ w) (hz0 : 0 < z) (hz : 2 * z ≤ b ^ 5)
    (k : ℕ) : mask29 (b ^ 5) (2 * z) k < (b ^ 5) ^ k := by
  have hB1 : 1 < b ^ 5 := by
    rw [hb, ← pow_mul]; exact Nat.one_lt_two_pow (by omega)
  unfold mask29
  have := Nat.ofDigits_lt_base_pow_length (b := b ^ 5) (l := List.replicate k (b ^ 5 - 2 * z)) hB1
    (fun x hx => by rw [List.mem_replicate] at hx; rw [hx.2]; omega)
  simpa using this

/-- (4.4) split by Lemma 2.10: `τ₂(e + lq², θλ) = 0 ⟺ τ₂(e, mask) = 0 ∧ τ₂(l, mask) = 0`
(`e < q²`). -/
theorem tau2_iff {b w e l lam θ : ℕ} (hb : b = 2 ^ w) (hw : 1 ≤ w) (hz0 : 0 < z) (hz : 2 * z ≤ b ^ 5)
    (hθ : θ + 2 * z = b ^ 5) (hlam : lam = ∑ i ∈ range (4 * L4 ν), (b ^ 5) ^ i)
    (he : e < (b ^ 5) ^ (2 * L4 ν)) :
    τ 2 (e + l * ((b ^ 5) ^ L4 ν) ^ 2) (θ * lam) = 0 ↔
      τ 2 e (mask29 (b ^ 5) (2 * z) (2 * L4 ν)) = 0 ∧
        τ 2 l (mask29 (b ^ 5) (2 * z) (2 * L4 ν)) = 0 := by
  rw [theta_lam_eq hz hθ hlam, ← pow_mul, mul_comm (L4 ν) 2]
  have hB : (b ^ 5) ^ (2 * L4 ν) = 2 ^ (5 * w * (2 * L4 ν)) := by
    rw [hb, ← pow_mul, ← pow_mul]; ring_nf
  rw [hB] at he ⊢
  have hm := mask29_lt (z := z) hb hw hz0 hz (2 * L4 ν)
  rw [hB] at hm
  exact (lemma_2_10 he hm).symm

/-! ### Sufficiency -/

/-- The size facts implied by the system: `xy < b`, `e, l < q²`, `g < q`, `b ≤ q`
(the article's "(U7) and (U8) imply `e ≥ b`, `l ≥ b`, so that (U6') implies
`e < q²`, `l < q²`, `g < q`"). -/
theorem UEqs.sizes (hI : Index ν P z u y) {x : ℕ} (hx : 0 < x)
    {b e g l m q t θ lam α : ℕ} (hb2 : 2 ≤ b)
    (hg0 : 0 < g) (hl0 : 0 < l) (hm : 0 < m) (ht : 0 < t) (hα : 0 < α)
    (hU : UEqs ν x z u y b e g l m q t θ lam α) :
    x * y < b ∧ 2 * z ≤ b ^ 5 ∧ e < q ^ 2 ∧ l < q ^ 2 ∧ g < q ∧ b ≤ q ∧ b ≤ e ∧ b ≤ l ∧
      lam = ∑ i ∈ range (4 * L4 ν), (b ^ 5) ^ i := by
  obtain ⟨U6, U3, U4, U5, U7, U8⟩ := hU
  have hq : q = (b ^ 5) ^ L4 ν := by rw [U3, q_eq]
  have hy1 := hI.y_pos
  have hz2 := hI.two_le
  have h2zy := hI.two_z_le_y
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ (by positivity)
  have hbxy : x * y < b := by
    have h1 : (0 : ℤ) < ((b : ℤ) - x * y) * q ^ 2 := by
      rw [← U6]; positivity
    have h2 : (0 : ℤ) < (b : ℤ) - x * y := by
      by_contra hcon
      push Not at hcon
      have : ((b : ℤ) - x * y) * q ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon (by positivity)
      linarith
    have : (x : ℤ) * y < b := by linarith
    exact_mod_cast this
  have hbB : 2 * b ≤ b ^ 5 := by
    have : 2 ≤ b ^ 4 := le_trans (by norm_num) (Nat.pow_le_pow_left hb2 4)
    calc 2 * b ≤ b ^ 4 * b := Nat.mul_le_mul_right _ this
      _ = b ^ 5 := by ring
  have hyb : y < b := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hx) hbxy
  have h2zB : 2 * z ≤ b ^ 5 := by omega
  have hq4 : q ^ 4 = (b ^ 5) ^ (4 * L4 ν) := by rw [hq, ← pow_mul, mul_comm]
  have hlam : lam = ∑ i ∈ range (4 * L4 ν), (b ^ 5) ^ i :=
    geom_of_eq (by omega) (by rw [← hq4]; exact U4)
  have hθb : b ≤ θ := by omega
  have heb : b ≤ e := by rw [U8]; nlinarith
  have hlb : b ≤ l := by rw [U7]; nlinarith
  have hlt : e * l * g ^ 2 < (b - x * y) * q ^ 2 := by
    have h1 : ((e * l * g ^ 2 : ℕ) : ℤ) < (((b - x * y) * q ^ 2 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hbxy.le]
      have : (0 : ℤ) < α := by exact_mod_cast hα
      linarith
    exact_mod_cast h1
  have hD1 : 1 ≤ b - x * y := by omega
  have hxy1 : 1 ≤ x * y := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hlg : l * g ^ 2 < q ^ 2 := by
    by_contra hcon
    push Not at hcon
    have h1 : (b - x * y + 1) * (l * g ^ 2) ≤ e * (l * g ^ 2) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (b - x * y) * q ^ 2 ≤ (b - x * y) * (l * g ^ 2) := Nat.mul_le_mul_left _ hcon
    have h3 : (b - x * y + 1) * (l * g ^ 2) = (b - x * y) * (l * g ^ 2) + l * g ^ 2 := by ring
    have h4 : e * (l * g ^ 2) = e * l * g ^ 2 := by ring
    omega
  have heg : e * g ^ 2 < q ^ 2 := by
    by_contra hcon
    push Not at hcon
    have h1 : (b - x * y + 1) * (e * g ^ 2) ≤ l * (e * g ^ 2) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (b - x * y) * q ^ 2 ≤ (b - x * y) * (e * g ^ 2) := Nat.mul_le_mul_left _ hcon
    have h3 : (b - x * y + 1) * (e * g ^ 2) = (b - x * y) * (e * g ^ 2) + e * g ^ 2 := by ring
    have h4 : l * (e * g ^ 2) = e * l * g ^ 2 := by ring
    omega
  have hg2 : 1 ≤ g ^ 2 := Nat.one_le_pow _ _ hg0
  have hgq : g < q := by
    have : g ^ 2 < q ^ 2 := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hl0) hlg
    exact (Nat.pow_lt_pow_iff_left two_ne_zero).1 this
  have hlq : l < q ^ 2 := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hg2) hlg
  have heq : e < q ^ 2 := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hg2) heg
  have hbq : b ≤ q := by
    rw [hq]
    calc b ≤ b ^ 5 := Nat.le_self_pow (by norm_num) b
      _ = (b ^ 5) ^ 1 := (pow_one _).symm
      _ ≤ (b ^ 5) ^ L4 ν := Nat.pow_le_pow_right (by omega) (Nat.one_le_pow _ _ (by norm_num))
  exact ⟨hbxy, h2zB, heq, hlq, hgq, hbq, heb, hlb, hlam⟩

/-- `(b − 1) l ≤ q³ − 2`: the mask `M₁ = q³ − 1 − (b − 1) l` is a positive integer. -/
theorem M1_bounds {b l q : ℕ} (hb2 : 2 ≤ b) (hbq : b ≤ q) (hlq : l < q ^ 2) :
    (b - 1) * l + 2 ≤ q ^ 3 := by
  have h1 : (b - 1) * l ≤ (q - 1) * (q ^ 2 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hq2 : 2 ≤ q := by omega
  have h2 : (q - 1) * (q ^ 2 - 1) + q ^ 2 + q = q ^ 3 + 1 := by
    have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [hq1, (by omega : 1 ≤ q)]
    ring
  have : 3 ≤ q ^ 2 + q := by nlinarith
  omega

/-- `0 ≤ S₃` follows from the equations alone (the article's "to derive `0 ≤ S₃` we use
`1 + g ≤ q` and `D₀ < zλ`"). -/
theorem UEqs.S3_nonneg (hI : Index ν P z u y) {x : ℕ} (hx : 0 < x)
    {b e g l m q t θ lam α : ℕ} (hb2 : 2 ≤ b)
    (hg0 : 0 < g) (hl0 : 0 < l) (hm : 0 < m) (ht : 0 < t) (hα : 0 < α)
    (hU : UEqs ν x z u y b e g l m q t θ lam α) :
    0 ≤ 2 * ((e : ℤ) - z * lam) * (1 + x * b ^ 5 + g) ^ 4 + b ^ 5 * lam * (1 + q ^ 4) := by
  obtain ⟨hbxy, h2zB, heq, hlq, hgq, hbq, heb, hlb, hlam⟩ :=
    hU.sizes hI hx hb2 hg0 hl0 hm ht hα
  have hq : q = (b ^ 5) ^ L4 ν := by rw [hU.U3, q_eq]
  have hy1 := hI.y_pos
  have hz2 := hI.two_le
  have hyb : y < b := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hx) hbxy
  have hxb : x < b := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hy1) hbxy
  -- `c = 1 + xB + g ≤ 2q` (as `xB < B² ≤ q`)
  have hL2 : 2 ≤ L4 ν := by
    rw [L4_eq]; exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 1 ≤ ν + 1))
  have hB2q : (b ^ 5) ^ 2 ≤ q := by rw [hq]; exact Nat.pow_le_pow_right (by positivity) hL2
  have hc : 1 + x * b ^ 5 + g ≤ 2 * q := by
    have h1 : x * b ^ 5 ≤ (b - 1) * b ^ 5 := Nat.mul_le_mul_right _ (by omega)
    have h2 : (b - 1) * b ^ 5 + b ^ 5 = b ^ 5 * b := by
      rw [Nat.sub_one_mul]
      have : b ^ 5 ≤ b * b ^ 5 := Nat.le_mul_of_pos_left _ (by omega)
      rw [mul_comm (b ^ 5) b]; omega
    have h3 : b ^ 5 * b ≤ (b ^ 5) ^ 2 := by
      rw [sq]; exact Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) b)
    omega
  -- `32 z ≤ B`
  have h32 : 32 * z ≤ b ^ 5 := by
    have h1 : 2 * z ≤ y := hI.two_z_le_y
    have h2 : y ^ 5 ≤ b ^ 5 := Nat.pow_le_pow_left hyb.le 5
    have h3 : (2 * z) ^ 5 ≤ y ^ 5 := Nat.pow_le_pow_left h1 5
    have h4 : 32 * z ≤ (2 * z) ^ 5 := by
      have : z ≤ z ^ 5 := Nat.le_self_pow (by norm_num) z
      calc 32 * z ≤ 32 * z ^ 5 := Nat.mul_le_mul_left _ this
        _ = (2 * z) ^ 5 := by ring
    omega
  -- in `ℤ`
  have hcZ : (1 + (x : ℤ) * b ^ 5 + g) ≤ 2 * q := by exact_mod_cast hc
  have hc0 : (0 : ℤ) ≤ 1 + (x : ℤ) * b ^ 5 + g := by positivity
  have hc4 : (1 + (x : ℤ) * b ^ 5 + g) ^ 4 ≤ (2 * (q : ℤ)) ^ 4 := pow_le_pow_left₀ hc0 hcZ 4
  have h32Z : 32 * (z : ℤ) ≤ (b : ℤ) ^ 5 := by exact_mod_cast h32
  have hlam0 : (0 : ℤ) ≤ lam := by positivity
  have hq0 : (0 : ℤ) ≤ q := by positivity
  have hB0 : (0 : ℤ) ≤ (b : ℤ) ^ 5 := by positivity
  have hz0 : (0 : ℤ) ≤ z := by positivity
  have he0 : (0 : ℤ) ≤ e := by positivity
  -- `2c⁴(zλ − e) ≤ 2c⁴ zλ ≤ 32 q⁴ zλ ≤ B q⁴ λ ≤ Bλ(1 + q⁴)`
  have h1 : 2 * (1 + (x : ℤ) * b ^ 5 + g) ^ 4 * ((z : ℤ) * lam - e) ≤
      2 * (2 * (q : ℤ)) ^ 4 * ((z : ℤ) * lam) := by
    have ha : 2 * (1 + (x : ℤ) * b ^ 5 + g) ^ 4 * ((z : ℤ) * lam - e) ≤
        2 * (1 + (x : ℤ) * b ^ 5 + g) ^ 4 * ((z : ℤ) * lam) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hb' : 2 * (1 + (x : ℤ) * b ^ 5 + g) ^ 4 * ((z : ℤ) * lam) ≤
        2 * (2 * (q : ℤ)) ^ 4 * ((z : ℤ) * lam) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc4 (by norm_num)) (by positivity)
    linarith
  have h2 : 2 * (2 * (q : ℤ)) ^ 4 * ((z : ℤ) * lam) ≤ (b : ℤ) ^ 5 * lam * q ^ 4 := by
    have : 2 * (2 * (q : ℤ)) ^ 4 * ((z : ℤ) * lam) = (32 * (z : ℤ)) * (lam * q ^ 4) := by ring
    rw [this, mul_assoc ((b : ℤ) ^ 5)]
    exact mul_le_mul_of_nonneg_right h32Z (by positivity)
  have h3 : (b : ℤ) ^ 5 * lam * q ^ 4 ≤ (b : ℤ) ^ 5 * lam * (1 + q ^ 4) := by
    apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have e0 : 2 * ((e : ℤ) - z * lam) * (1 + x * b ^ 5 + g) ^ 4 + b ^ 5 * lam * (1 + q ^ 4) =
      (b : ℤ) ^ 5 * lam * (1 + q ^ 4) - 2 * (1 + (x : ℤ) * b ^ 5 + g) ^ 4 * ((z : ℤ) * lam - e) := by
    ring
  rw [e0]
  linarith

set_option maxHeartbeats 1000000 in
/-- The solvability of the system gives `x ∈ W_{⟨z,u,y⟩}`. -/
theorem mem_of_USys (hν : 1 ≤ ν) (hP : P.totalDegree ≤ 4) (hI : Index ν P z u y) {x : ℕ}
    (hx : 0 < x) {b e g l m q t θ lam α w : ℕ} (hb : b = 2 ^ w) (hw : 1 ≤ w)
    (hg0 : 0 < g) (hl0 : 0 < l) (hm : 0 < m) (ht : 0 < t) (hα : 0 < α)
    (hU : USys ν x z u y b e g l m q t θ lam α) : Wset P x := by
  have hb2 : 2 ≤ b := by rw [hb]; exact Nat.one_lt_two_pow (by omega)
  obtain ⟨hbxy, h2zB, heq, hlq, hgq, hbq, heb, hlb, hlam⟩ :=
    hU.toUEqs.sizes hI hx hb2 hg0 hl0 hm ht hα
  obtain ⟨⟨U6, U3, U4, U5, U7, U8⟩, τ1, τ2, τ3⟩ := hU
  have hq : q = (b ^ 5) ^ L4 ν := by rw [U3, q_eq]
  have hy1 := hI.y_pos
  have hz2 := hI.two_le
  have hxb : x < b := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hy1) hbxy
  have hyb : y < b := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hx) hbxy
  have hθ : θ = b ^ 5 - 2 * z := by omega
  have hlamZ : (lam : ℤ) = (lampoly ν 4).eval ((b : ℤ) ^ 5) := by
    rw [eval_lampoly, hlam]; push_cast; rfl
  have hq2 : q ^ 2 = (b ^ 5) ^ (2 * L4 ν) := by rw [hq, ← pow_mul, mul_comm]
  -- (4.4) split
  rw [hq] at τ2
  obtain ⟨hτe, hτl⟩ := (tau2_iff hb hw (by omega) h2zB U5 hlam (by rw [← hq2]; exact heq)).1 τ2
  -- Lemma 2.9 for `e` and `l`
  have he : (e : ℤ) = (epoly ν 4 P z).eval ((b : ℤ) ^ 5) := by
    rw [transfer_iff hI hb hw hyb (epoly ν 4 P z) (fun i => (hI.coeff_epoly_bounds i).1)
      (fun i => (hI.coeff_epoly_bounds i).2) (natDegree_epoly_le ν 4 P z) hI.hy]
    refine ⟨?_, by rw [← hq2]; exact heq, hτe⟩
    rw [← hθ, U8]
    exact ((Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).2 ⟨m, by rw [Nat.add_sub_cancel_left, mul_comm]⟩).symm
  have hl : (l : ℤ) = (lpoly ν 4).eval ((b : ℤ) ^ 5) := by
    rw [transfer_iff hI hb hw hyb (lpoly ν 4) (fun i => (coeff_lpoly_bounds ν i).1)
      (fun i => by have := (coeff_lpoly_bounds ν i).2; push_cast; linarith)
      ((natDegree_lpoly_le ν).trans (five_pow_le_L4 ν)) hI.hu]
    refine ⟨?_, by rw [← hq2]; exact hlq, hτl⟩
    rw [← hθ, U7]
    exact ((Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).2 ⟨t, by rw [Nat.add_sub_cancel_left, mul_comm]⟩).symm
  -- the code
  have hq3 : q ^ 3 = (b ^ 5) ^ (3 * L4 ν) := by rw [hq, ← pow_mul, mul_comm]
  rw [hq3] at τ1
  obtain ⟨zs, hzs0, hzs, hgZ⟩ := code_of_tau1 hb hw hxb hl (by rw [← hq]; exact hgq) τ1
  refine ⟨zs, hzs0, ?_⟩
  rw [← tau3_iff hI hν hP hb hw zs hzs hzs0 hyb he hlamZ hq
    (by rw [eval_cpoly_eq, hzs0, ← hgZ])]
  exact τ3

/-! ### Necessity -/

/-- `p(B) > p(2z)` for a digit polynomial with nonnegative coefficients, a positive
coefficient of `X^n` with `n ≥ 1`, and `2z < B`. -/
theorem eval_lt_eval_of_pos {p : ℤ[X]} (hp0 : ∀ i, 0 ≤ p.coeff i) {n : ℕ} (hn : 1 ≤ n)
    (hpn : 0 < p.coeff n) {a B : ℤ} (ha : 0 ≤ a) (haB : a < B) : p.eval a < p.eval B := by
  have hN : p.natDegree < p.natDegree + 1 := Nat.lt_succ_self _
  rw [eval_eq_sum_range' hN, eval_eq_sum_range' hN]
  have hnmem : n ∈ range (p.natDegree + 1) := by
    rw [Finset.mem_range]
    have : n ≤ p.natDegree := le_natDegree_of_ne_zero hpn.ne'
    omega
  apply Finset.sum_lt_sum
  · intro i _
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha haB.le i) (hp0 i)
  · exact ⟨n, hnmem, mul_lt_mul_of_pos_left (pow_lt_pow_left₀ haB ha (by omega)) hpn⟩

set_option maxHeartbeats 1000000 in
/-- `x ∈ W_{⟨z,u,y⟩}` gives a solution of the system in positive integers. -/
theorem USys_of_mem (hν : 1 ≤ ν) (hP : P.totalDegree ≤ 4) (hnorm : Normalized P)
    (hI : Index ν P z u y) {x : ℕ} (hx : 0 < x) (hW : Wset P x) :
    ∃ b e g l m q t θ lam α w : ℕ, 0 < e ∧ 0 < g ∧ 0 < l ∧ 0 < m ∧ 0 < q ∧ 0 < t ∧ 0 < θ ∧
      0 < lam ∧ 0 < α ∧ 0 < w ∧ b = 2 ^ w ∧ USys ν x z u y b e g l m q t θ lam α ∧
      0 ≤ 2 * ((e : ℤ) - z * lam) * (1 + x * b ^ 5 + g) ^ 4 + b ^ 5 * lam * (1 + q ^ 4) := by
  obtain ⟨zs, hzs0, hPz⟩ := hW
  have hy1 := hI.y_pos
  have hz2 := hI.two_le
  have h2zy := hI.two_z_le_y
  -- the bound `b`
  obtain ⟨w, hw⟩ : ∃ w, w = x * y + ∑ i, zs i + 1 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = 2 ^ w := ⟨_, rfl⟩
  have hw1 : 1 ≤ w := by omega
  have hwb : w < b := by rw [hb]; exact Nat.lt_two_pow_self
  have hbxy : x * y < b := by omega
  have hzs : ∀ i, zs i < b := fun i => by
    have := Finset.single_le_sum (f := fun i => zs i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hxb : x < b := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hy1) hbxy
  have hyb : y < b := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hx) hbxy
  have hb2 : 2 ≤ b := by rw [hb]; exact Nat.one_lt_two_pow (by omega)
  have hB1 : 1 < b ^ 5 := by rw [hb, ← pow_mul]; exact Nat.one_lt_two_pow (by omega)
  have hbB : 2 * b ≤ b ^ 5 := by
    have : 2 ≤ b ^ 4 := le_trans (by norm_num) (Nat.pow_le_pow_left hb2 4)
    calc 2 * b ≤ b ^ 4 * b := Nat.mul_le_mul_right _ this
      _ = b ^ 5 := by ring
  have h2zB : 2 * z ≤ b ^ 5 := by omega
  have hL1 : 1 ≤ L4 ν := Nat.one_le_pow _ _ (by norm_num)
  -- `q`, `λ`, `θ`
  obtain ⟨q, hq⟩ : ∃ q, q = (b ^ 5) ^ L4 ν := ⟨_, rfl⟩
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ (by omega)
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = ∑ i ∈ range (4 * L4 ν), (b ^ 5) ^ i := ⟨_, rfl⟩
  have hlam1 : 1 ≤ lam := by
    rw [hlam]
    have := Finset.single_le_sum (f := fun i => (b ^ 5) ^ i) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (show 0 < 4 * L4 ν by omega))
    simpa using this
  have hlamZ : (lam : ℤ) = (lampoly ν 4).eval ((b : ℤ) ^ 5) := by
    rw [eval_lampoly, hlam]; push_cast; rfl
  have U4 : lam + q ^ 4 = 1 + lam * b ^ 5 := by
    have hg := geom_sum_mul_add (b ^ 5 - 1) (4 * L4 ν)
    rw [Nat.sub_add_cancel (by omega)] at hg
    rw [hq, ← pow_mul, mul_comm (L4 ν) 4, ← hg, ← hlam, Nat.mul_sub, mul_one]
    have : lam ≤ lam * b ^ 5 := Nat.le_mul_of_pos_right _ (by omega)
    omega
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = b ^ 5 - 2 * z := ⟨_, rfl⟩
  have hθ1 : 1 ≤ θ := by omega
  have U5 : θ + 2 * z = b ^ 5 := by omega
  -- `e`, `l`, `g`
  obtain ⟨e, he⟩ : ∃ e, e = Nat.ofDigits (b ^ 5) (coeffList (epoly ν 4 P z) (L4 ν + 1)) := ⟨_, rfl⟩
  have heZ : (e : ℤ) = (epoly ν 4 P z).eval ((b : ℤ) ^ 5) := by
    have := ofDigits_coeffList_eq_eval (epoly ν 4 P z) (fun i => (hI.coeff_epoly_bounds i).1) (b ^ 5)
      (n := L4 ν + 1) (lt_of_le_of_lt (natDegree_epoly_le ν 4 P z) (Nat.lt_succ_self _))
    rw [Nat.cast_pow] at this
    rw [he, this]
  obtain ⟨l, hl⟩ : ∃ l, l = Nat.ofDigits (b ^ 5) (coeffList (lpoly ν 4) (L4 ν + 1)) := ⟨_, rfl⟩
  have hlZ : (l : ℤ) = (lpoly ν 4).eval ((b : ℤ) ^ 5) := by
    have := ofDigits_coeffList_eq_eval (lpoly ν 4) (fun i => (coeff_lpoly_bounds ν i).1) (b ^ 5)
      (n := L4 ν + 1) (lt_of_le_of_lt ((natDegree_lpoly_le ν).trans (five_pow_le_L4 ν)) (Nat.lt_succ_self _))
    rw [Nat.cast_pow] at this
    rw [hl, this]
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.ofDigits (b ^ 5) (coeffList (gpoly ν zs) (3 * L4 ν)) := ⟨_, rfl⟩
  have hgZ : (g : ℤ) = (gpoly ν zs).eval ((b : ℤ) ^ 5) := by
    have := ofDigits_coeffList_eq_eval (gpoly ν zs) (coeff_gpoly_nonneg ν zs) (b ^ 5)
      (n := 3 * L4 ν) (lt_of_le_of_lt (natDegree_gpoly_le ν zs) (five_pow_lt_three_L4 ν le_rfl))
    rw [Nat.cast_pow] at this
    rw [hg, this]
  -- `e > y`, `l > u`
  have h2zB' : (2 * (z : ℤ)) < (b : ℤ) ^ 5 := by
    have : 2 * z < b ^ 5 := by omega
    exact_mod_cast this
  have hey : y < e := by
    obtain ⟨k₀, hk₀, hexp⟩ : ∃ k₀ ∈ star ν 4, expo ν 4 k₀ = 0 :=
      ⟨(fun _ => 0 : Fin (ν + 2) → ℕ) + Pi.single 0 4, by rw [mem_star]; simp, by simp [expo]⟩
    have h1 := eval_lt_eval_of_pos (p := epoly ν 4 P z) (fun i => (hI.coeff_epoly_bounds i).1)
      (n := L4 ν - expo ν 4 k₀) (by rw [hexp]; omega)
      (by
        rw [coeff_epoly_of_mem ν 4 P z hk₀]
        have := hI.big k₀ hk₀
        have := abs_lt.1 (show |Pcoef ν P k₀| < z by omega)
        push_cast; linarith)
      (a := 2 * (z : ℤ)) (by positivity) h2zB'
    rw [← hI.hy, ← heZ] at h1
    exact_mod_cast h1
  have hlu : u < l := by
    have h1 := eval_lt_eval_of_pos (p := lpoly ν 4) (fun i => (coeff_lpoly_bounds ν i).1)
      (n := 5 ^ 1) (by norm_num)
      (by rw [coeff_lpoly_of_mem ν (Finset.mem_Icc.2 ⟨le_rfl, hν⟩)]; norm_num)
      (a := 2 * (z : ℤ)) (by positivity) h2zB'
    rw [← hI.hu, ← hlZ] at h1
    exact_mod_cast h1
  -- Lemma 2.9 for `e` and `l`
  have hq2 : q ^ 2 = (b ^ 5) ^ (2 * L4 ν) := by rw [hq, ← pow_mul, mul_comm]
  obtain ⟨hey', hey2, hτe⟩ := (transfer_iff hI hb hw1 hyb (epoly ν 4 P z)
    (fun i => (hI.coeff_epoly_bounds i).1) (fun i => (hI.coeff_epoly_bounds i).2)
    (natDegree_epoly_le ν 4 P z) hI.hy).1 heZ
  obtain ⟨hlu', hlu2, hτl⟩ := (transfer_iff hI hb hw1 hyb (lpoly ν 4)
    (fun i => (coeff_lpoly_bounds ν i).1)
    (fun i => by have := (coeff_lpoly_bounds ν i).2; push_cast; linarith)
    ((natDegree_lpoly_le ν).trans (five_pow_le_L4 ν)) hI.hu).1 hlZ
  rw [← hθ] at hey' hlu'
  -- `m` and `t`
  obtain ⟨m, hm⟩ := (Nat.modEq_iff_dvd' hey.le).1 hey'.symm
  have hm1 : 1 ≤ m := by
    by_contra h0; push Not at h0
    have : m = 0 := by omega
    rw [this, mul_zero] at hm; omega
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hlu.le).1 hlu'.symm
  have ht1 : 1 ≤ t := by
    by_contra h0; push Not at h0
    have : t = 0 := by omega
    rw [this, mul_zero] at ht; omega
  -- `g ≥ 1` by the normalization
  have hg1 : 1 ≤ g := by
    by_contra h0
    push Not at h0
    have hg0 : g = 0 := by omega
    apply hnorm x
    have hzero : ∀ i : Fin (ν + 1), i ≠ 0 → zs i = 0 := by
      intro i hi
      have hsum : (gpoly ν zs).eval ((b : ℤ) ^ 5) = 0 := by rw [← hgZ, hg0]; simp
      unfold gpoly at hsum
      rw [eval_finset_sum] at hsum
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by
        split_ifs
        · simp
        · simp only [eval_mul, eval_C, eval_pow, eval_X]; positivity)).1 hsum i (Finset.mem_univ i)
      rw [if_neg hi] at hterm
      simp only [eval_mul, eval_C, eval_pow, eval_X] at hterm
      have hBpos : (0 : ℤ) < ((b : ℤ) ^ 5) ^ (5 ^ (i : ℕ)) := by
        have : (0 : ℤ) < b := by exact_mod_cast (by omega : 0 < b)
        positivity
      have := (mul_eq_zero.1 hterm).resolve_right hBpos.ne'
      exact_mod_cast this
    have : (fun j : Fin (ν + 1) => if j = 0 then (x : ℤ) else 0) = fun j => (zs j : ℤ) := by
      funext j
      by_cases hj : j = 0
      · rw [if_pos hj, hj, hzs0]
      · rw [if_neg hj, hzero j hj]; rfl
    rw [this]; exact hPz
  -- the estimates for (U6')
  obtain ⟨hτ1, hgb⟩ := tau1_of_code hb hw1 hlZ zs hzs hgZ
  have he_lt : e < 2 * z * (b ^ 5) ^ L4 ν := by
    rw [he]
    have := ofDigits_lt_mul_pow (B := b ^ 5) (z := 2 * z) hB1 h2zB
      (coeffList (epoly ν 4 P z) (L4 ν + 1))
      (fun x hx => by
        obtain ⟨i, -, rfl⟩ := mem_coeffList hx
        have := hI.coeff_epoly_bounds i
        rw [Int.toNat_lt this.1]; push_cast; exact this.2)
      (by simp [coeffList])
    rwa [coeffList_length, Nat.add_sub_cancel] at this
  have hl_lt : l < 2 * (b ^ 5) ^ (5 ^ ν) := by
    have hl' : l = Nat.ofDigits (b ^ 5) (coeffList (lpoly ν 4) (5 ^ ν + 1)) := by
      have := ofDigits_coeffList_eq_eval (lpoly ν 4) (fun i => (coeff_lpoly_bounds ν i).1) (b ^ 5)
        (n := 5 ^ ν + 1) (lt_of_le_of_lt (natDegree_lpoly_le ν) (Nat.lt_succ_self _))
      rw [Nat.cast_pow, ← hlZ] at this
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
  have hbig : e * l * g ^ 2 < q ^ 2 := by
    have h1 : e * l * g ^ 2 < (2 * z * (b ^ 5) ^ L4 ν) * (2 * (b ^ 5) ^ (5 ^ ν)) * (b * (b ^ 5) ^ (5 ^ ν)) ^ 2 :=
      Nat.mul_lt_mul'' (Nat.mul_lt_mul'' he_lt hl_lt) (Nat.pow_lt_pow_left hgb two_ne_zero)
    have h2 : (2 * z * (b ^ 5) ^ L4 ν) * (2 * (b ^ 5) ^ (5 ^ ν)) * (b * (b ^ 5) ^ (5 ^ ν)) ^ 2 =
        (4 * z * b ^ 2) * (b ^ 5) ^ (L4 ν + 3 * 5 ^ ν) := by
      rw [pow_add, pow_mul]; ring
    have h3 : 4 * z * b ^ 2 ≤ b ^ 5 := by
      have h4z : 4 * z ≤ b ^ 3 := by
        have : 4 * z ≤ 2 * y := by omega
        have : 2 * y ≤ 2 * b := by omega
        have : 2 * b ≤ b ^ 3 := by
          calc 2 * b ≤ b ^ 2 * b := Nat.mul_le_mul_right _ (by nlinarith)
            _ = b ^ 3 := by ring
        omega
      calc 4 * z * b ^ 2 ≤ b ^ 3 * b ^ 2 := Nat.mul_le_mul_right _ h4z
        _ = b ^ 5 := by ring
    have h4 : (b ^ 5) ^ (L4 ν + 3 * 5 ^ ν + 1) ≤ (b ^ 5) ^ (2 * L4 ν) := by
      apply Nat.pow_le_pow_right (by omega)
      rw [L4_eq, pow_succ]
      have : 0 < 5 ^ ν := by positivity
      omega
    calc e * l * g ^ 2 < (4 * z * b ^ 2) * (b ^ 5) ^ (L4 ν + 3 * 5 ^ ν) := by rw [← h2]; exact h1
      _ ≤ b ^ 5 * (b ^ 5) ^ (L4 ν + 3 * 5 ^ ν) := Nat.mul_le_mul_right _ h3
      _ = (b ^ 5) ^ (L4 ν + 3 * 5 ^ ν + 1) := by ring
      _ ≤ (b ^ 5) ^ (2 * L4 ν) := h4
      _ = q ^ 2 := hq2.symm
  have hlt : e * l * g ^ 2 < (b - x * y) * q ^ 2 :=
    lt_of_lt_of_le hbig (Nat.le_mul_of_pos_left _ (by omega))
  obtain ⟨α, hα⟩ : ∃ α, α = (b - x * y) * q ^ 2 - e * l * g ^ 2 := ⟨_, rfl⟩
  have hα1 : 1 ≤ α := by omega
  -- the three `τ`-conditions
  have hq3 : q ^ 3 = (b ^ 5) ^ (3 * L4 ν) := by rw [hq, ← pow_mul, mul_comm]
  have hτ2 : τ 2 (e + l * q ^ 2) (θ * lam) = 0 := by
    rw [hq]
    exact (tau2_iff hb hw1 (by omega) h2zB U5 hlam hey2).2 ⟨hτe, hτl⟩
  have hτ3 := (tau3_iff hI hν hP hb hw1 zs hzs hzs0 hyb heZ hlamZ hq
    (by rw [eval_cpoly_eq, hzs0, ← hgZ])).2 hPz
  have hS3 := S3_nonneg hI hν hb hw1 zs hzs hyb heZ hlamZ hq (by rw [eval_cpoly_eq, hzs0, ← hgZ])
  refine ⟨b, e, g, l, m, q, t, θ, lam, α, w, by omega, hg1, by omega, hm1, hq1, ht1, hθ1, hlam1,
    hα1, hw1, hb, ⟨⟨?_, by rw [hq, q_eq], U4, U5, by rw [mul_comm]; omega, by rw [mul_comm]; omega⟩,
    by rw [hq3]; exact hτ1, hτ2, hτ3⟩, hS3⟩
  -- (U6')
  have h1 : ((b - x * y) * q ^ 2 : ℕ) = e * l * g ^ 2 + α := by omega
  have h2 : (((b - x * y) * q ^ 2 : ℕ) : ℤ) = ((e * l * g ^ 2 + α : ℕ) : ℤ) := by rw [h1]
  push_cast [Nat.cast_sub hbxy.le] at h2
  linarith

/-- The master equivalence of §4: `x ∈ W_{⟨z,u,y⟩}` iff `USys` is solvable in positive integers
with `b = 2ʷ`. -/
theorem master (hν : 1 ≤ ν) (hP : P.totalDegree ≤ 4) (hnorm : Normalized P)
    (hI : Index ν P z u y) {x : ℕ} (hx : 0 < x) :
    Wset P x ↔ ∃ b e g l m q t θ lam α w : ℕ, 0 < e ∧ 0 < g ∧ 0 < l ∧ 0 < m ∧ 0 < q ∧ 0 < t ∧
      0 < θ ∧ 0 < lam ∧ 0 < α ∧ 0 < w ∧ b = 2 ^ w ∧ USys ν x z u y b e g l m q t θ lam α := by
  constructor
  · intro hW
    obtain ⟨b, e, g, l, m, q, t, θ, lam, α, w, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hb, hU, -⟩ :=
      USys_of_mem hν hP hnorm hI hx hW
    exact ⟨b, e, g, l, m, q, t, θ, lam, α, w, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hb, hU⟩
  · rintro ⟨b, e, g, l, m, q, t, θ, lam, α, w, -, hg, hl, hm, -, ht, -, -, hα, hw, hb, hU⟩
    exact mem_of_USys hν hP hI hx hb hw hg hl hm ht hα hU

end Master

end Jones1982
