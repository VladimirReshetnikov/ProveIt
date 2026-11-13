import DiophantineConsistency.ModelCarries
import DiophantineConsistency.ModelDifferenceRing
import DiophantineConsistency.JonesSyntaxCore

/-! # Jones 1982, (U18)–(U24) in every model of `𝗜𝚺₁`: packing three carry tests

The internal counterpart of `Jones1982.pack3_carries_iff_dvd` and
`Jones1982.centralCode_eq_rPolynomial` (`Diophantine/Paper1982/Packing.lean`).

* `pack3 N₁ N₂ a₁ a₂ a₃ = a₁ + a₂ N₁ + a₃ N₁ N₂` and `centralCode N S T = S(N² − N) + (T + 1)(N² − 1)`
  are model functions (truncated subtraction, harmless since `N ≤ N²`);
* `pack3_carries_iff_dvd`: for `q = 2^κ` and blocks below `q³`, `q⁴`, `q⁹`, the three
  no-carry tests hold iff `(q¹⁶)² ∣ binom (2R) R` for the packed code `R`;
* `ι_centralCode_eq_rankCode`: in the ring of differences, the packed code is the rank
  coding polynomial `NinePolynomial.rankCode` of the executable syntax, once the three
  signed quantities `S₃`, `M₁ = q³ − 1 − (b − 1) l` and `b⁵ − 2` are supplied by their
  ring values. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ModelPacking
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticBinaryCarry ArithmeticBinomPascal ModelCarries ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Three blocks in mixed bases, (U21), (U22). -/
def pack3 (N₁ N₂ a₁ a₂ a₃ : V) : V := a₁ + a₂ * N₁ + a₃ * N₁ * N₂

/-- The central-binomial code (U24). -/
def centralCode (N S T : V) : V := S * (N ^ 2 - N) + (T + 1) * (N ^ 2 - 1)

theorem pack3_lt {N₁ N₂ N₃ a₁ a₂ a₃ : V} (h₁ : a₁ < N₁) (h₂ : a₂ < N₂) (h₃ : a₃ < N₃) :
    pack3 N₁ N₂ a₁ a₂ a₃ < N₁ * N₂ * N₃ := by
  have h₁₂ : a₁ + a₂ * N₁ < N₁ * N₂ := by
    calc a₁ + a₂ * N₁ < N₁ + a₂ * N₁ := add_lt_add_of_lt_of_le h₁ le_rfl
      _ = (a₂ + 1) * N₁ := by ring
      _ ≤ N₂ * N₁ := mul_le_mul_of_nonneg_right (lt_iff_succ_le.mp h₂) (Arithmetic.zero_le _)
      _ = N₁ * N₂ := mul_comm _ _
  unfold pack3
  calc a₁ + a₂ * N₁ + a₃ * N₁ * N₂ < N₁ * N₂ + a₃ * N₁ * N₂ := add_lt_add_of_lt_of_le h₁₂ le_rfl
    _ = (a₃ + 1) * (N₁ * N₂) := by ring
    _ ≤ N₃ * (N₁ * N₂) :=
        mul_le_mul_of_nonneg_right (lt_iff_succ_le.mp h₃) (Arithmetic.zero_le _)
    _ = N₁ * N₂ * N₃ := by ring

theorem le_sq_sub_one {N : V} (hN : 2 ≤ N) : N ≤ N ^ 2 - 1 := by
  apply le_tsub_of_add_le_right
  have h1 : (1 : V) ≤ N := le_trans one_le_two hN
  calc N + 1 ≤ N + N := add_le_add (le_refl N) h1
    _ = 2 * N := (two_mul N).symm
    _ ≤ N * N := mul_le_mul_of_nonneg_right hN (Arithmetic.zero_le _)
    _ = N ^ 2 := (sq N).symm

/-- The code is at least its base. -/
theorem centralCode_ge_base {N S T : V} (hN : 2 ≤ N) : N ≤ centralCode N S T := by
  unfold centralCode
  calc N ≤ N ^ 2 - 1 := le_sq_sub_one hN
    _ ≤ (T + 1) * (N ^ 2 - 1) :=
        le_mul_of_one_le_left (Arithmetic.zero_le _) (le_add_of_nonneg_left (Arithmetic.zero_le T))
    _ ≤ S * (N ^ 2 - N) + (T + 1) * (N ^ 2 - 1) := le_add_left le_rfl

theorem centralCode_pos {N S T : V} (hN : 2 ≤ N) : 0 < centralCode N S T :=
  lt_of_lt_of_le (lt_of_lt_of_le zero_lt_two hN) (centralCode_ge_base hN)

/-- **(U18)–(U24).** Three bounded blocks are tested by one central-binomial divisibility. -/
theorem pack3_carries_iff_dvd {κ S₁ T₁ S₂ T₂ S₃ T₃ : V}
    (hS₁ : S₁ < Exp.exp κ ^ 3) (hT₁ : T₁ < Exp.exp κ ^ 3)
    (hS₂ : S₂ < Exp.exp κ ^ 4) (hT₂ : T₂ < Exp.exp κ ^ 4)
    (hS₃ : S₃ < Exp.exp κ ^ 9) (hT₃ : T₃ < Exp.exp κ ^ 9) :
    (NoCarry S₁ T₁ ∧ NoCarry S₂ T₂ ∧ NoCarry S₃ T₃) ↔
      (Exp.exp κ ^ 16) ^ 2 ∣
        binom (2 * centralCode (Exp.exp κ ^ 16)
            (pack3 (Exp.exp κ ^ 3) (Exp.exp κ ^ 4) S₁ S₂ S₃)
            (pack3 (Exp.exp κ ^ 3) (Exp.exp κ ^ 4) T₁ T₂ T₃))
          (centralCode (Exp.exp κ ^ 16)
            (pack3 (Exp.exp κ ^ 3) (Exp.exp κ ^ 4) S₁ S₂ S₃)
            (pack3 (Exp.exp κ ^ 3) (Exp.exp κ ^ 4) T₁ T₂ T₃)) := by
  obtain ⟨k3, h3⟩ := pow_exp_exists κ 3
  obtain ⟨k4, h4⟩ := pow_exp_exists κ 4
  obtain ⟨k16, h16⟩ := pow_exp_exists κ 16
  have hprod : Exp.exp κ ^ 3 * Exp.exp κ ^ 4 * Exp.exp κ ^ 9 = Exp.exp κ ^ 16 := by ring
  have hS := pack3_lt hS₁ hS₂ hS₃
  have hT := pack3_lt hT₁ hT₂ hT₃
  rw [hprod, h16] at hS hT
  have hτ : (NoCarry S₁ T₁ ∧ NoCarry S₂ T₂ ∧ NoCarry S₃ T₃) ↔
      NoCarry (pack3 (Exp.exp κ ^ 3) (Exp.exp κ ^ 4) S₁ S₂ S₃)
        (pack3 (Exp.exp κ ^ 3) (Exp.exp κ ^ 4) T₁ T₂ T₃) := by
    unfold pack3
    rw [h3, h4]
    rw [h3] at hS₁ hT₁
    rw [h4] at hS₂ hT₂
    exact noCarry_three hS₁ hT₁ hS₂ hT₂
  rw [hτ, h16]
  exact noCarry_iff_sq_dvd_central hS hT rfl

/-! ### The code in the ring of differences -/

theorem ι_tsub {a b : V} (h : b ≤ a) : ι (a - b) = ι a - ι b := by
  have e : a = b + (a - b) := (add_tsub_cancel_of_le h).symm
  have h1 : ι a = ι b + ι (a - b) := by
    rw [← map_add]
    exact congrArg ι e
  rw [h1]
  ring

/-- **(U21)–(U24) expanded.** With `S₃`, `M₁ = q³ − 1 − (b − 1) l` and `D = b⁵ − 2` given by
their ring values, the packed code is `NinePolynomial.rankCode` of the ring values. -/
theorem ι_centralCode_eq_rankCode {x z b e g l n q θ lam S₃ M₁ D : V} (hn : 1 ≤ n)
    (hS₃ : ι S₃ = 2 * (ι e - ι z * ι lam) * (1 + ι x * ι b ^ 5 + ι g) ^ 4 +
      ι lam * ι b ^ 5 + ι lam * ι b ^ 5 * ι q ^ 4)
    (hM₁ : ι M₁ = ι q ^ 3 - 1 - (ι b - 1) * ι l)
    (hD : ι D = ι b ^ 5 - 2) :
    ι (centralCode n (pack3 (q ^ 3) (q ^ 4) g (e + l * q ^ 2) S₃)
        (pack3 (q ^ 3) (q ^ 4) M₁ (θ * lam) (D * q))) =
      NinePolynomial.rankCode (ι x) (ι z) (ι b) (ι e) (ι g) (ι l) (ι n) (ι q) (ι θ) (ι lam) := by
  have hn2 : n ≤ n ^ 2 := by
    calc n = n * 1 := (mul_one n).symm
      _ ≤ n * n := mul_le_mul_of_nonneg_left hn (Arithmetic.zero_le _)
      _ = n ^ 2 := (sq n).symm
  have hn1 : 1 ≤ n ^ 2 := le_trans hn hn2
  have e1 : ι (n ^ 2 - n) = ι n ^ 2 - ι n := by rw [ι_tsub hn2, map_pow]
  have e2 : ι (n ^ 2 - 1) = ι n ^ 2 - 1 := by rw [ι_tsub hn1, map_pow, map_one]
  unfold centralCode pack3
  simp only [map_add, map_mul, map_pow, map_one, e1, e2, hS₃, hM₁, hD]
  unfold NinePolynomial.rankCode
  ring

end DiophantineConsistency.ModelPacking
