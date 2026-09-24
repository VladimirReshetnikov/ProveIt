import Diophantine.Paper1978.Godel

/-!
# Jones 1978, Theorems 1 and 2

> **Theorem 1.** The sets `Ŵ₁, Ŵ₂, …` (the nonnegative-witness enumeration) may be
> represented, for `x, n > 0`, in the form
> `x ∈ Ŵₙ ⟺ ∃ a b ∀ i ≤ n ∃ s w p q ∀ j v ∃ e g {(s+w)² + 3w + s = 2i ∧`
> `([j = w ∧ v = q] ∨ [j = 3i ∧ v = p + q] ∨ [j = s ∧ (v = p ∨ (i = n ∧ v = q + x))] ∨`
> `[j = 3i + 1 ∧ v = pq]) → (a = v + e + ejb ∧ v + g = jb)}`.

> **Theorem 2.** The same sets are represented, for `x, n > 0`, by
> `∃ a b ∀ i ∃ s w p q ∀ j v ∃ e g` of the single polynomial equation displayed in the
> article (`F2 = 0` below), whose matrix is a polynomial equation over `ℤ` with the
> unknowns ranging over `ℕ`.

Theorem 1 is (3.3) with the repeated term `j = s` distributed; the residue condition
`a = v + e + ejb ∧ v + g = jb` says `v = S₊(a, b, j) = a mod (1 + jb)`.  Theorem 2 follows
from Theorem 1 by the elementary principles `A = 0 ∧ B = 0 ⟺ A² + B² = 0`,
`A = 0 ∨ B = 0 ⟺ AB = 0`, `(A = 0 → ∃ e B = 0) ⟺ ∃ e (A = e + 1 ∨ B = 0)` for a nonnegative
`A`, and `(∀ i ≤ n)(∃ s) C = 0 ⟺ (∀ i)(∃ s)(n + s + 1 − i) C = 0`.
-/

namespace Jones1978

/-- `Pₖ(X) ≥ 0` for a nonnegative assignment. -/
theorem P_nonneg {X : ℕ → ℤ} (hX : ∀ i, 0 ≤ X i) : ∀ k, 0 ≤ P k X := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [P_zero]
    have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hmod with h | h | h
    · obtain ⟨i, rfl⟩ : ∃ i, k = 3 * i := ⟨k / 3, by omega⟩
      rw [P_add (by omega)]
      have := ih (K i) (by have := K_le i; omega)
      have := ih (L i) (by have := L_le i; omega)
      linarith
    · obtain ⟨i, rfl⟩ : ∃ i, k = 3 * i + 1 := ⟨k / 3, by omega⟩
      rw [P_mul]
      exact mul_nonneg (ih (K i) (by have := K_le i; omega)) (ih (L i) (by have := L_le i; omega))
    · obtain ⟨i, rfl⟩ : ∃ i, k = 3 * i + 2 := ⟨k / 3, by omega⟩
      rw [P_var]; exact hX i

/-! ### Theorem 1 -/

/-- The disjunction in the antecedent of Theorem 1. -/
def Cond1 (x n i s w p q j v : ℕ) : Prop :=
  (j = w ∧ v = q) ∨ (j = 3 * i ∧ v = p + q) ∨ (j = s ∧ (v = p ∨ (i = n ∧ v = q + x))) ∨
    (j = 3 * i + 1 ∧ v = p * q)

/-- The formula `F(x, n)` of Theorem 1. -/
def Thm1 (x n : ℕ) : Prop :=
  ∃ a b : ℕ, ∀ i, i ≤ n → ∃ s w p q : ℕ, ∀ j v : ℕ, ∃ e g : ℕ,
    (s + w) ^ 2 + 3 * w + s = 2 * i ∧
    (Cond1 x n i s w p q j v → (a = v + e + e * j * b ∧ v + g = j * b))

/-- **Theorem 1.** -/
theorem theorem_1 {x n : ℕ} (hn : 0 < n) : x ∈ Wh n ↔ Thm1 x n := by
  constructor
  · rintro ⟨X, hX⟩
    -- code the values `Pₖ(X)`, `k ≤ 3n + 1`, by least nonnegative residues
    set X' : ℕ → ℤ := fun i => (X i : ℤ) with hX'
    have hnn : ∀ k, 0 ≤ P k X' := P_nonneg (fun i => by simp [hX'])
    obtain ⟨a, b, -, -, hab⟩ := exists_residues (fun k => (P k X').toNat) (3 * n + 1)
    have hSp : ∀ k ≤ 3 * n + 1, (Sp a b k : ℤ) = P k X' := by
      intro k hk
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · rw [Sp_zero, P_zero]; rfl
      · unfold Sp
        rw [hab k hkpos hk]
        exact Int.toNat_of_nonneg (hnn k)
    refine ⟨a, b, fun i hi => ⟨K i, L i, Sp a b (K i), Sp a b (L i), fun j v => ?_⟩⟩
    have hpair : (K i + L i) ^ 2 + 3 * L i + K i = 2 * i := by
      rw [← two_J, J_K_L]
    -- if the antecedent holds then `v = S₊(a, b, j)`
    by_cases hc : Cond1 x n i (K i) (L i) (Sp a b (K i)) (Sp a b (L i)) j v
    · have hv : v = Sp a b j := by
        have hKi : K i ≤ 3 * n + 1 := by have := K_le i; omega
        have hLi : L i ≤ 3 * n + 1 := by have := L_le i; omega
        rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hv⟩ | ⟨rfl, rfl⟩
        · rfl
        · have h1 := hSp (3 * i) (by omega)
          rw [P_add', ← hSp (K i) hKi, ← hSp (L i) hLi] at h1
          exact_mod_cast h1.symm
        · rcases hv with rfl | ⟨hin, rfl⟩
          · rfl
          · rw [hin] at hKi hLi ⊢
            have h1 := hSp (K n) hKi
            rw [hX, ← hSp (L n) hLi] at h1
            exact_mod_cast h1.symm
        · have h1 := hSp (3 * i + 1) (by omega)
          rw [P_mul, ← hSp (K i) hKi, ← hSp (L i) hLi] at h1
          exact_mod_cast h1.symm
      obtain ⟨e, g, he, hg⟩ := (Sp_iff a b j v).1 hv
      exact ⟨e, g, hpair, fun _ => ⟨he, hg⟩⟩
    · exact ⟨0, 0, hpair, fun h => absurd h hc⟩
  · rintro ⟨a, b, H⟩
    -- the recursions for `S₊` up to `n`, and `S₊(K n) = S₊(L n) + x`
    have hrec : ∀ i ≤ n, Sp a b (3 * i) = Sp a b (K i) + Sp a b (L i) ∧
        Sp a b (3 * i + 1) = Sp a b (K i) * Sp a b (L i) := by
      intro i hi
      obtain ⟨s, w, p, q, hsw⟩ := H i hi
      have hpair := (hsw 0 0).choose_spec.choose_spec.1
      have hJ : J s w = i := (pairing_eq_iff s w i).1 hpair
      obtain ⟨rfl, rfl⟩ := J_eq_iff.1 hJ
      have hq : q = Sp a b (L i) := by
        obtain ⟨e, g, -, h⟩ := hsw (L i) q
        exact (Sp_iff a b (L i) q).2 ⟨e, g, h (Or.inl ⟨rfl, rfl⟩)⟩
      have hp : p = Sp a b (K i) := by
        obtain ⟨e, g, -, h⟩ := hsw (K i) p
        exact (Sp_iff a b (K i) p).2 ⟨e, g, h (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)))⟩
      have hpq : p + q = Sp a b (3 * i) := by
        obtain ⟨e, g, -, h⟩ := hsw (3 * i) (p + q)
        exact (Sp_iff a b (3 * i) (p + q)).2 ⟨e, g, h (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
      have hpq' : p * q = Sp a b (3 * i + 1) := by
        obtain ⟨e, g, -, h⟩ := hsw (3 * i + 1) (p * q)
        exact (Sp_iff a b (3 * i + 1) (p * q)).2 ⟨e, g, h (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))⟩
      rw [← hpq, ← hpq', hp, hq]
      exact ⟨rfl, rfl⟩
    have hx : Sp a b (K n) = Sp a b (L n) + x := by
      obtain ⟨s, w, p, q, hsw⟩ := H n le_rfl
      have hpair := (hsw 0 0).choose_spec.choose_spec.1
      have hJ : J s w = n := (pairing_eq_iff s w n).1 hpair
      obtain ⟨rfl, rfl⟩ := J_eq_iff.1 hJ
      have hq : q = Sp a b (L n) := by
        obtain ⟨e, g, -, h⟩ := hsw (L n) q
        exact (Sp_iff a b (L n) q).2 ⟨e, g, h (Or.inl ⟨rfl, rfl⟩)⟩
      have hqx : q + x = Sp a b (K n) := by
        obtain ⟨e, g, -, h⟩ := hsw (K n) (q + x)
        exact (Sp_iff a b (K n) (q + x)).2
          ⟨e, g, h (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩)))⟩
      omega
    have key := Sp_eq_P hrec
    refine ⟨fun j => Sp a b (3 * j + 2), ?_⟩
    rw [← key (K n) (by have := K_le n; omega), ← key (L n) (by have := L_le n; omega), hx]
    push_cast; ring

/-! ### Theorem 2 -/

/-- The product of the four "case" polynomials. -/
def Prod2 (x n i s w p q j v : ℕ) : ℤ :=
  (((j : ℤ) - w) ^ 2 + ((v : ℤ) - q) ^ 2) *
    (((j : ℤ) - s) ^ 2 + ((v : ℤ) - p) ^ 2 * (((i : ℤ) - n) ^ 2 + ((v : ℤ) - q - x) ^ 2)) *
    (((j : ℤ) - 3 * i) ^ 2 + ((v : ℤ) - p - q) ^ 2) *
    (((j : ℤ) - 3 * i - 1) ^ 2 + ((v : ℤ) - p * q) ^ 2)

/-- The matrix of Theorem 2. -/
def F2 (x n i s w p q j v e g a b : ℕ) : ℤ :=
  ((n : ℤ) + s + 1 - i) *
    ((((s : ℤ) + w) ^ 2 + 3 * w + s - 2 * i) ^ 2 +
      (Prod2 x n i s w p q j v - e - 1) ^ 2 *
        (((v : ℤ) + e + e * j * b - a) ^ 2 + ((v : ℤ) + g - j * b) ^ 2))

/-- The formula of Theorem 2. -/
def Thm2 (x n : ℕ) : Prop :=
  ∃ a b : ℕ, ∀ i : ℕ, ∃ s w p q : ℕ, ∀ j v : ℕ, ∃ e g : ℕ, F2 x n i s w p q j v e g a b = 0

theorem sq_eq_zero {a : ℤ} : a ^ 2 = 0 ↔ a = 0 := pow_eq_zero_iff two_ne_zero

theorem sq_add_sq_eq_zero {a b : ℤ} : a ^ 2 + b ^ 2 = 0 ↔ a = 0 ∧ b = 0 := by
  rw [add_eq_zero_iff_of_nonneg (sq_nonneg a) (sq_nonneg b), sq_eq_zero, sq_eq_zero]

theorem Prod2_nonneg (x n i s w p q j v : ℕ) : 0 ≤ Prod2 x n i s w p q j v := by
  unfold Prod2; positivity

/-- `Prod2 = 0` iff the antecedent of Theorem 1 holds. -/
theorem Prod2_eq_zero_iff (x n i s w p q j v : ℕ) :
    Prod2 x n i s w p q j v = 0 ↔ Cond1 x n i s w p q j v := by
  unfold Prod2 Cond1
  rw [mul_eq_zero, mul_eq_zero, mul_eq_zero, sq_add_sq_eq_zero, sq_add_sq_eq_zero,
    sq_add_sq_eq_zero]
  have h3 : ((j : ℤ) - s) ^ 2 + ((v : ℤ) - p) ^ 2 * (((i : ℤ) - n) ^ 2 + ((v : ℤ) - q - x) ^ 2) = 0
      ↔ (j = s ∧ (v = p ∨ (i = n ∧ v = q + x))) := by
    rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) (by positivity), sq_eq_zero, mul_eq_zero,
      sq_eq_zero, sq_add_sq_eq_zero]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by omega, ?_⟩
      rcases h2 with h2 | ⟨h2, h3⟩
      · left; omega
      · right; omega
    · rintro ⟨h1, h2⟩
      refine ⟨by omega, ?_⟩
      rcases h2 with h2 | ⟨h2, h3⟩
      · left; omega
      · right; exact ⟨by omega, by omega⟩
  rw [h3]
  constructor
  · rintro (((⟨h1, h2⟩ | h) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
    · left; exact ⟨by omega, by omega⟩
    · right; right; left; exact h
    · right; left; exact ⟨by omega, by omega⟩
    · right; right; right
      refine ⟨by omega, ?_⟩
      have : (v : ℤ) = p * q := by linarith
      exact_mod_cast this
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | h | ⟨h1, h2⟩)
    · left; left; left; exact ⟨by omega, by omega⟩
    · left; right; exact ⟨by omega, by omega⟩
    · left; left; right; exact h
    · right
      refine ⟨by omega, ?_⟩
      subst h2; push_cast; ring

/-- Theorem 1 and Theorem 2 are equivalent formulas. -/
theorem thm1_iff_thm2 (x n : ℕ) : Thm1 x n ↔ Thm2 x n := by
  constructor
  · rintro ⟨a, b, H⟩
    refine ⟨a, b, fun i => ?_⟩
    by_cases hi : i ≤ n
    · obtain ⟨s, w, p, q, hsw⟩ := H i hi
      refine ⟨s, w, p, q, fun j v => ?_⟩
      obtain ⟨e, g, hpair, himp⟩ := hsw j v
      have hpairZ : ((s : ℤ) + w) ^ 2 + 3 * w + s - 2 * i = 0 := by
        have : (((s + w) ^ 2 + 3 * w + s : ℕ) : ℤ) = ((2 * i : ℕ) : ℤ) := by rw [hpair]
        push_cast at this; linarith
      by_cases hc : Cond1 x n i s w p q j v
      · obtain ⟨h1, h2⟩ := himp hc
        refine ⟨e, g, ?_⟩
        unfold F2
        have e1 : ((v : ℤ) + e + e * j * b - a) = 0 := by
          have : ((v + e + e * j * b : ℕ) : ℤ) = a := by rw [← h1]
          push_cast at this; linarith
        have e2 : ((v : ℤ) + g - j * b) = 0 := by
          have : ((v + g : ℕ) : ℤ) = ((j * b : ℕ) : ℤ) := by rw [h2]
          push_cast at this; linarith
        rw [hpairZ, e1, e2]; ring
      · -- `Prod2 ≥ 1`: take `e = Prod2 − 1`
        have hP0 : Prod2 x n i s w p q j v ≠ 0 := fun h => hc ((Prod2_eq_zero_iff _ _ _ _ _ _ _ _ _).1 h)
        have hP1 : 1 ≤ Prod2 x n i s w p q j v := by
          have := Prod2_nonneg x n i s w p q j v
          omega
        refine ⟨(Prod2 x n i s w p q j v - 1).toNat, 0, ?_⟩
        unfold F2
        rw [Int.toNat_of_nonneg (by omega), hpairZ]
        ring
    · -- `i > n`: the factor `n + s + 1 − i` vanishes for `s = i − n − 1`
      refine ⟨i - n - 1, 0, 0, 0, fun j v => ⟨0, 0, ?_⟩⟩
      unfold F2
      have : (n : ℤ) + ((i - n - 1 : ℕ) : ℤ) + 1 - i = 0 := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      rw [this]; ring
  · rintro ⟨a, b, H⟩
    refine ⟨a, b, fun i hi => ?_⟩
    obtain ⟨s, w, p, q, hsw⟩ := H i
    refine ⟨s, w, p, q, fun j v => ?_⟩
    obtain ⟨e, g, hF⟩ := hsw j v
    unfold F2 at hF
    have hfac : (0 : ℤ) < (n : ℤ) + s + 1 - i := by
      have : (i : ℤ) ≤ n := by exact_mod_cast hi
      linarith
    have hsum : (((s : ℤ) + w) ^ 2 + 3 * w + s - 2 * i) ^ 2 +
        (Prod2 x n i s w p q j v - e - 1) ^ 2 *
          (((v : ℤ) + e + e * j * b - a) ^ 2 + ((v : ℤ) + g - j * b) ^ 2) = 0 :=
      (mul_eq_zero.1 hF).resolve_left hfac.ne'
    have h1 : (((s : ℤ) + w) ^ 2 + 3 * w + s - 2 * i) ^ 2 = 0 := by
      have := sq_nonneg (((s : ℤ) + w) ^ 2 + 3 * w + s - 2 * i)
      have : 0 ≤ (Prod2 x n i s w p q j v - e - 1) ^ 2 *
          (((v : ℤ) + e + e * j * b - a) ^ 2 + ((v : ℤ) + g - j * b) ^ 2) := by positivity
      linarith
    have h2 : (Prod2 x n i s w p q j v - e - 1) ^ 2 *
        (((v : ℤ) + e + e * j * b - a) ^ 2 + ((v : ℤ) + g - j * b) ^ 2) = 0 := by
      have := sq_nonneg (((s : ℤ) + w) ^ 2 + 3 * w + s - 2 * i)
      linarith
    refine ⟨e, g, ?_, fun hc => ?_⟩
    · have h1' : ((s : ℤ) + w) ^ 2 + 3 * w + s - 2 * i = 0 := sq_eq_zero.1 h1
      have : (((s + w) ^ 2 + 3 * w + s : ℕ) : ℤ) = ((2 * i : ℕ) : ℤ) := by push_cast; linarith
      exact_mod_cast this
    · have hP : Prod2 x n i s w p q j v = 0 := (Prod2_eq_zero_iff _ _ _ _ _ _ _ _ _).2 hc
      rw [hP] at h2
      have hne : (0 - (e : ℤ) - 1) ^ 2 ≠ 0 := by
        apply pow_ne_zero 2
        have : (0 : ℤ) ≤ e := by positivity
        intro h0
        linarith
      have h3 := (mul_eq_zero.1 h2).resolve_left hne
      obtain ⟨h4, h5⟩ := sq_add_sq_eq_zero.1 h3
      constructor
      · have : ((v + e + e * j * b : ℕ) : ℤ) = a := by push_cast; linarith
        exact_mod_cast this.symm
      · have : ((v + g : ℕ) : ℤ) = ((j * b : ℕ) : ℤ) := by push_cast; linarith
        exact_mod_cast this

/-- **Theorem 2.** -/
theorem theorem_2 {x n : ℕ} (hn : 0 < n) : x ∈ Wh n ↔ Thm2 x n :=
  (theorem_1 hn).trans (thm1_iff_thm2 x n)

end Jones1978
