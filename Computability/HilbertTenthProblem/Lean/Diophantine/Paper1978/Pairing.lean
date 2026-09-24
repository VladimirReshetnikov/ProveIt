import Mathlib.Tactic

/-!
# Jones 1978, §2: the Cantor pairing functions `J`, `K`, `L`

`2 J(s, w) = (s + w)² + 3w + s`, `J(K(y), L(y)) = y`, `J` is a bijection `ℕ × ℕ → ℕ`,
and `K(y) ≤ y`, `L(y) ≤ y`.
-/

namespace Jones1978

/-- The triangular number `T m = m (m+1) / 2`. -/
def T (m : ℕ) : ℕ := m * (m + 1) / 2

theorem two_T (m : ℕ) : 2 * T m = m * (m + 1) := by
  unfold T
  have : 2 ∣ m * (m + 1) := (Nat.even_mul_succ_self m).two_dvd
  omega

theorem T_succ (m : ℕ) : T (m + 1) = T m + (m + 1) := by
  have h1 := two_T m
  have h2 := two_T (m + 1)
  nlinarith

/-- The Cantor pairing function `J(s, w) = T(s + w) + w`. -/
def J (s w : ℕ) : ℕ := T (s + w) + w

/-- The article's definition `2 J(s, w) = (s + w)² + 3w + s`. -/
theorem two_J (s w : ℕ) : 2 * J s w = (s + w) ^ 2 + 3 * w + s := by
  unfold J
  have := two_T (s + w)
  nlinarith

theorem T_le_J (s w : ℕ) : T (s + w) ≤ J s w := Nat.le_add_right _ _

theorem J_lt_T_succ (s w : ℕ) : J s w < T (s + w + 1) := by
  unfold J; rw [T_succ]; omega

theorem T_mono {a b : ℕ} (h : a ≤ b) : T a ≤ T b := by
  have h1 := two_T a
  have h2 := two_T b
  have : a * (a + 1) ≤ b * (b + 1) := Nat.mul_le_mul h (by omega)
  omega

theorem T_strictMono {a b : ℕ} (h : a < b) : T a < T b := by
  calc T a < T (a + 1) := by rw [T_succ]; omega
    _ ≤ T b := T_mono h

theorem le_T (m : ℕ) : m ≤ T m := by
  have := two_T m
  nlinarith

/-- `J` is injective. -/
theorem J_injective {s w s' w' : ℕ} (h : J s w = J s' w') : s = s' ∧ w = w' := by
  have hsum : s + w = s' + w' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := J_lt_T_succ s w
      have h2 := T_le_J s' w'
      have h3 := T_mono (show s + w + 1 ≤ s' + w' by omega)
      omega
    · have h1 := J_lt_T_succ s' w'
      have h2 := T_le_J s w
      have h3 := T_mono (show s' + w' + 1 ≤ s + w by omega)
      omega
  unfold J at h
  rw [hsum] at h
  omega

/-- The inverses, defined by the successor rule `J(s, w) + 1 = J(s - 1, w + 1)` for
`s ≥ 1` and `J(0, w) + 1 = J(w + 1, 0)`. -/
def KL : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | y + 1 =>
    let p := KL y
    if p.1 = 0 then (p.2 + 1, 0) else (p.1 - 1, p.2 + 1)

def K (y : ℕ) : ℕ := (KL y).1
def L (y : ℕ) : ℕ := (KL y).2

theorem J_succ_of_pos (s w : ℕ) : J (s + 1) w + 1 = J s (w + 1) := by
  unfold J
  rw [show s + 1 + w = s + (w + 1) by ring]
  ring

theorem J_zero_succ (w : ℕ) : J 0 w + 1 = J (w + 1) 0 := by
  unfold J
  simp only [zero_add, add_zero]
  rw [T_succ]; ring

/-- `J(K(y), L(y)) = y`. -/
theorem J_K_L (y : ℕ) : J (K y) (L y) = y := by
  induction y with
  | zero => rfl
  | succ y ih =>
    unfold K L at ih ⊢
    simp only [KL]
    by_cases h : (KL y).1 = 0
    · rw [if_pos h]
      rw [h] at ih
      simp only
      rw [← J_zero_succ, ih]
    · rw [if_neg h]
      simp only
      obtain ⟨s, hs⟩ : ∃ s, (KL y).1 = s + 1 := ⟨(KL y).1 - 1, by omega⟩
      rw [hs] at ih
      rw [hs, Nat.add_sub_cancel, ← J_succ_of_pos, ih]

theorem K_J (s w : ℕ) : K (J s w) = s := by
  have := J_injective (J_K_L (J s w))
  exact this.1

theorem L_J (s w : ℕ) : L (J s w) = w := by
  have := J_injective (J_K_L (J s w))
  exact this.2

theorem J_eq_iff {s w y : ℕ} : J s w = y ↔ s = K y ∧ w = L y := by
  constructor
  · rintro rfl; exact ⟨(K_J s w).symm, (L_J s w).symm⟩
  · rintro ⟨rfl, rfl⟩; exact J_K_L y

theorem K_le (y : ℕ) : K y ≤ y := by
  conv_rhs => rw [← J_K_L y]
  unfold J
  have := le_T (K y + L y)
  omega

theorem L_le (y : ℕ) : L y ≤ y := by
  conv_rhs => rw [← J_K_L y]
  unfold J
  omega

theorem le_J_left (s w : ℕ) : s ≤ J s w := by
  unfold J; have := le_T (s + w); omega

theorem le_J_right (s w : ℕ) : w ≤ J s w := by
  unfold J; omega

/-- The paper's form of the pairing equation: `(s+w)² + 3w + s = 2 i ↔ J(s, w) = i`. -/
theorem pairing_eq_iff (s w i : ℕ) : (s + w) ^ 2 + 3 * w + s = 2 * i ↔ J s w = i := by
  rw [← two_J]; omega

end Jones1978
