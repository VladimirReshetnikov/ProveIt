import Diophantine.Paper1982.Master3

/-!
# Jones 1982, (U18)–(U24): packing three carry conditions

The three blocks have lengths `q³`, `q⁴`, `q⁹`. Packing them gives two integers
below `q¹⁶`. Lemma 2.16 turns their carry-free addition into divisibility of a
single central binomial coefficient. The integer identity at the end verifies
the expanded equation for `r` printed in Theorems 2 and 3.
-/

namespace Jones1982

/-- Three blocks in mixed bases, as in (U21) and (U22). -/
def pack3 (N₁ N₂ a₁ a₂ a₃ : ℕ) : ℕ := a₁ + a₂ * N₁ + a₃ * N₁ * N₂

theorem pack3_lt {N₁ N₂ N₃ a₁ a₂ a₃ : ℕ}
    (h₁ : a₁ < N₁) (h₂ : a₂ < N₂) (h₃ : a₃ < N₃) :
    pack3 N₁ N₂ a₁ a₂ a₃ < N₁ * N₂ * N₃ := by
  have h₁₂ : a₁ + a₂ * N₁ < N₁ * N₂ := by
    calc a₁ + a₂ * N₁ < N₁ + a₂ * N₁ := Nat.add_lt_add_right h₁ _
      _ = (a₂ + 1) * N₁ := by ring
      _ ≤ N₂ * N₁ := Nat.mul_le_mul_right _ h₂
      _ = N₁ * N₂ := by ring
  unfold pack3
  calc a₁ + a₂ * N₁ + a₃ * N₁ * N₂ < N₁ * N₂ + a₃ * N₁ * N₂ :=
      Nat.add_lt_add_right h₁₂ _
    _ = (a₃ + 1) * (N₁ * N₂) := by ring
    _ ≤ N₃ * (N₁ * N₂) := Nat.mul_le_mul_right _ h₃
    _ = N₁ * N₂ * N₃ := by ring

/-- The central-binomial code (U24). -/
def centralCode (N S T : ℕ) : ℕ := S * (N ^ 2 - N) + (T + 1) * (N ^ 2 - 1)

theorem centralCode_pos {N S T : ℕ} (hN : 2 ≤ N) : 0 < centralCode N S T := by
  have hsq : 1 < N ^ 2 := by nlinarith
  have : 0 < (T + 1) * (N ^ 2 - 1) := Nat.mul_pos (by omega) (by omega)
  unfold centralCode
  omega

/-- The code is at least its base, a size fact used when applying Lemma 2.25
to the output of the packing construction. -/
theorem centralCode_ge_base {N S T : ℕ} (hN : 2 ≤ N) : N ≤ centralCode N S T := by
  have hsq : N + 1 ≤ N ^ 2 := by nlinarith
  have hterm : N ^ 2 - 1 ≤ (T + 1) * (N ^ 2 - 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  unfold centralCode
  omega

/-- Three bounded blocks can be tested by one central-binomial divisibility condition. -/
theorem pack3_carries_iff_dvd {q k S₁ T₁ S₂ T₂ S₃ T₃ : ℕ} (hq : q = 2 ^ k)
    (hS₁ : S₁ < q ^ 3) (hT₁ : T₁ < q ^ 3)
    (hS₂ : S₂ < q ^ 4) (hT₂ : T₂ < q ^ 4)
    (hS₃ : S₃ < q ^ 9) (hT₃ : T₃ < q ^ 9) :
    (τ 2 S₁ T₁ = 0 ∧ τ 2 S₂ T₂ = 0 ∧ τ 2 S₃ T₃ = 0) ↔
      (q ^ 16) ^ 2 ∣ (2 * centralCode (q ^ 16)
        (pack3 (q ^ 3) (q ^ 4) S₁ S₂ S₃) (pack3 (q ^ 3) (q ^ 4) T₁ T₂ T₃)).choose
          (centralCode (q ^ 16) (pack3 (q ^ 3) (q ^ 4) S₁ S₂ S₃)
            (pack3 (q ^ 3) (q ^ 4) T₁ T₂ T₃)) := by
  have hq3 : q ^ 3 = 2 ^ (k * 3) := by rw [hq, ← pow_mul]
  have hq4 : q ^ 4 = 2 ^ (k * 4) := by rw [hq, ← pow_mul]
  have hq16 : q ^ 16 = 2 ^ (k * 16) := by rw [hq, ← pow_mul]
  have hprod : q ^ 3 * q ^ 4 * q ^ 9 = q ^ 16 := by ring
  have hS := pack3_lt hS₁ hS₂ hS₃
  have hT := pack3_lt hT₁ hT₂ hT₃
  rw [hprod] at hS hT
  have hτ := lemma_2_11_three (by rwa [← hq3] : S₁ < 2 ^ (k * 3))
    (by rwa [← hq3] : T₁ < 2 ^ (k * 3))
    (by rwa [← hq4] : S₂ < 2 ^ (k * 4)) (by rwa [← hq4] : T₂ < 2 ^ (k * 4))
    (S₃ := S₃) (T₃ := T₃)
  rw [← hq3, ← hq4] at hτ
  change _ ↔ τ 2 (pack3 (q ^ 3) (q ^ 4) S₁ S₂ S₃)
    (pack3 (q ^ 3) (q ^ 4) T₁ T₂ T₃) = 0 at hτ
  refine hτ.trans ?_
  have hdvd := lemma_2_16 (by rwa [← hq16] : pack3 (q ^ 3) (q ^ 4) S₁ S₂ S₃ < 2 ^ (k * 16))
    (by rwa [← hq16] : pack3 (q ^ 3) (q ^ 4) T₁ T₂ T₃ < 2 ^ (k * 16))
    (R := centralCode (q ^ 16) (pack3 (q ^ 3) (q ^ 4) S₁ S₂ S₃)
      (pack3 (q ^ 3) (q ^ 4) T₁ T₂ T₃)) (by rw [← hq16]; rfl)
  rwa [← hq16] at hdvd

/-- The signed third block (U16). -/
def thirdBlock (x z b e g q lam : ℕ) : ℤ :=
  2 * ((e : ℤ) - z * lam) * (1 + x * b ^ 5 + g) ^ 4 + b ^ 5 * lam * (1 + q ^ 4)

/-- The packed left operand (U21). -/
def packedS (x z b e g l q lam : ℕ) : ℕ :=
  pack3 (q ^ 3) (q ^ 4) g (e + l * q ^ 2) (thirdBlock x z b e g q lam).toNat

/-- The packed right operand (U22). -/
def packedT (b l q θ lam : ℕ) : ℕ :=
  pack3 (q ^ 3) (q ^ 4) (q ^ 3 - 1 - (b - 1) * l) (θ * lam) ((b ^ 5 - 2) * q)

/-- The polynomial expression for `r` printed in Theorems 2 and 3.
Subtractions in this expression are integer subtractions. -/
def rPolynomial (x z b e g l n q θ lam : ℕ) : ℤ :=
  ((g : ℤ) + e * q ^ 3 + l * q ^ 5 +
    (2 * ((e : ℤ) - z * lam) * (1 + x * b ^ 5 + g) ^ 4 +
      lam * b ^ 5 + lam * b ^ 5 * q ^ 4) * q ^ 7) * ((n : ℤ) ^ 2 - n) +
  ((q : ℤ) ^ 3 - b * l + l + θ * lam * q ^ 3 + ((b : ℤ) ^ 5 - 2) * q ^ 8) *
    ((n : ℤ) ^ 2 - 1)

/-- Expanding (U21)–(U24) yields exactly the displayed equation for `r`. -/
theorem centralCode_eq_rPolynomial {x z b e g l n q θ lam : ℕ} (hb : 2 ≤ b)
    (hM : (b - 1) * l + 2 ≤ q ^ 3) (hn : 1 ≤ n)
    (hS : 0 ≤ thirdBlock x z b e g q lam) :
    (centralCode n (packedS x z b e g l q lam) (packedT b l q θ lam) : ℤ) =
      rPolynomial x z b e g l n q θ lam := by
  have hb5 : 2 ≤ b ^ 5 := le_trans hb (Nat.le_self_pow (by norm_num) b)
  have hn2 : n ≤ n ^ 2 := Nat.le_self_pow (by norm_num) n
  unfold centralCode packedS packedT pack3 rPolynomial
  push_cast [Nat.cast_sub (by omega : 1 ≤ q ^ 3),
    Nat.cast_sub (by omega : (b - 1) * l ≤ q ^ 3 - 1), Nat.cast_sub (by omega : 1 ≤ b),
    Nat.cast_sub hb5, Nat.cast_sub hn2, Nat.cast_sub (by omega : 1 ≤ n ^ 2)]
  rw [Int.toNat_of_nonneg hS]
  unfold thirdBlock
  ring

end Jones1982
