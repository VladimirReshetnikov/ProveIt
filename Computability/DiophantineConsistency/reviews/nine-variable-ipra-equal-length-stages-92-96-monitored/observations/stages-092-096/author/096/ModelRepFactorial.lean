import DiophantineConsistency.ModelRepInterfaces
import DiophantineConsistency.ArithmeticBinomFactorial

/-! # Internal correctness of the ceiling-quotient factorial graph

`FactorialRepresentation.factorialCoordinates` computes
`((r+1)^n + (C-1)) / C` with `r = (n+2)^(n+2)` and `C = binom (r+n) n`.
Inside every model of `𝗜𝚺₁` this is `ArithmeticBinomFactorial.fact n`
(`factorial_formula`). The argument is the one of
`FactorialRepresentation.factorial_formula`, with the ascending product
`asc r n = n! · binom (r+n) n = (r+1)(r+2)…(r+n)`:

* `asc_succ`: `asc r (n+1) = (r+n+1) · asc r n` (from `binom_mul_fact`);
* `pow_le_asc`: `(r+1)^n ≤ asc r n`;
* `asc_key`: `(r+1) · asc r m ≤ (r+1)^(m+1) + m² · asc r m`;
* `n² · n! ≤ (n+2)! ≤ (n+2)^(n+2)`, so `asc r n < (r+1)^n + C`, and the
  ceiling quotient is exactly `n!`.

`factCase_of` turns this into `ModelRepInterfaces.FactCase`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelRepFactorial
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelRep ModelScalarPR ModelRepBasic ModelRepArith ModelRepInterfaces
open ArithmeticPow ArithmeticBinomPascal ArithmeticBinomFactorial

section Formula
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The ascending product `(r+1)(r+2)…(r+n)`, as `n! · binom (r+n) n`. -/
def asc (r n : V) : V := fact n * binom (r + n) n

theorem asc_mul_fact (r n : V) : asc r n * fact r = fact (r + n) := by
  have h := binom_mul_fact n r
  rw [add_comm n r] at h
  unfold asc
  rw [← h]
  ring

theorem asc_zero (r : V) : asc r 0 = 1 := by
  unfold asc
  simp

theorem asc_succ (r n : V) : asc r (n + 1) = (r + n + 1) * asc r n := by
  apply mul_right_cancel₀ (fact_pos r).ne'
  rw [asc_mul_fact, mul_assoc, asc_mul_fact, ← add_assoc, fact_succ]

theorem pow_le_asc (r n : V) : power (r + 1) n ≤ asc r n := by
  induction n using ISigma1.sigma1_succ_induction
  · unfold asc
    definability
  case zero => simp [asc_zero]
  case succ n ih =>
    rw [power_succ, asc_succ]
    exact mul_le_mul ((add_le_add_iff_right 1).mpr le_self_add) ih (Arithmetic.zero_le _) (Arithmetic.zero_le _)

/-- The ascending-product estimate of `FactorialRepresentation.factorial_formula`. -/
theorem asc_key (r m : V) :
    (r + 1) * asc r m ≤ power (r + 1) (m + 1) + m * m * asc r m := by
  induction m using ISigma1.sigma1_succ_induction
  · unfold asc
    definability
  case zero => simp [asc_zero]
  case succ m ih =>
    have hP : power (r + 1) (m + 1) ≤ (r + m + 1) * asc r m := by
      rw [power_succ]
      exact mul_le_mul ((add_le_add_iff_right 1).mpr le_self_add) (pow_le_asc r m)
        (Arithmetic.zero_le _) (Arithmetic.zero_le _)
    have hm : m + m * m ≤ (m + 1) * (m + 1) := by
      calc m + m * m ≤ (m + m * m) + (m + 1) := le_self_add
        _ = (m + 1) * (m + 1) := by ring
    rw [asc_succ, power_succ (r + 1) (m + 1)]
    calc (r + 1) * ((r + m + 1) * asc r m)
        = (r + m + 1) * ((r + 1) * asc r m) := by ring
      _ ≤ (r + m + 1) * (power (r + 1) (m + 1) + m * m * asc r m) :=
          mul_le_mul_of_nonneg_left ih (Arithmetic.zero_le _)
      _ = (r + 1) * power (r + 1) (m + 1) +
            (m * power (r + 1) (m + 1) + m * m * ((r + m + 1) * asc r m)) := by ring
      _ ≤ (r + 1) * power (r + 1) (m + 1) +
            (m * ((r + m + 1) * asc r m) + m * m * ((r + m + 1) * asc r m)) :=
          _root_.add_le_add le_rfl
            (_root_.add_le_add (mul_le_mul_of_nonneg_left hP (Arithmetic.zero_le _)) le_rfl)
      _ = (r + 1) * power (r + 1) (m + 1) + (m + m * m) * ((r + m + 1) * asc r m) := by ring
      _ ≤ (r + 1) * power (r + 1) (m + 1) + (m + 1) * (m + 1) * ((r + m + 1) * asc r m) :=
          _root_.add_le_add le_rfl (mul_le_mul_of_nonneg_right hm (Arithmetic.zero_le _))

theorem fact_le_power (m : V) : fact m ≤ power m m := by
  induction m using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ m ih =>
    rw [fact_succ, power_succ]
    exact mul_le_mul_of_nonneg_left (le_trans ih (power_mono_base m (m + 1) m le_self_add))
      (Arithmetic.zero_le _)

theorem small_factor (n : V) : n * n * fact n ≤ power (n + 2) (n + 2) := by
  have h1 : fact (n + 2) = (n + 2) * (n + 1) * fact n := by
    rw [show n + 2 = n + 1 + 1 by ring, fact_succ, fact_succ]
    ring
  have h2 : n * n ≤ (n + 2) * (n + 1) := by
    calc n * n ≤ n * n + (3 * n + 2) := le_self_add
      _ = (n + 2) * (n + 1) := by ring
  calc n * n * fact n ≤ (n + 2) * (n + 1) * fact n :=
        mul_le_mul_of_nonneg_right h2 (Arithmetic.zero_le _)
    _ = fact (n + 2) := h1.symm
    _ ≤ power (n + 2) (n + 2) := fact_le_power (n + 2)

/-- The ceiling quotient computes the factorial once `n² · n! ≤ r`. -/
theorem ceil_formula (n r : V) (hr : n * n * fact n ≤ r) :
    (power (r + 1) n + (binom (r + n) n - 1)) / binom (r + n) n = fact n := by
  obtain ⟨C, hCdef⟩ : ∃ C : V, C = binom (r + n) n := ⟨_, rfl⟩
  rw [← hCdef]
  have hC : 0 < C := by rw [hCdef]; exact binom_pos (r + n) n le_add_self
  have hasc : asc r n = fact n * C := by
    unfold asc
    rw [hCdef]
  have hlow : power (r + 1) n ≤ fact n * C := by
    rw [← hasc]
    exact pow_le_asc r n
  have hkey : (r + 1) * (fact n * C) ≤ power (r + 1) (n + 1) + n * n * (fact n * C) := by
    rw [← hasc]
    exact asc_key r n
  have hlt : fact n * C < power (r + 1) n + C := by
    rcases lt_or_ge (fact n * C) (power (r + 1) n + C) with h | h
    · exact h
    · exfalso
      have e1 : (r + 1) * (power (r + 1) n + C) ≤
          power (r + 1) (n + 1) + n * n * (fact n * C) :=
        le_trans (mul_le_mul_of_nonneg_left h (Arithmetic.zero_le _)) hkey
      have e2 : power (r + 1) (n + 1) + (r + 1) * C ≤
          power (r + 1) (n + 1) + (n * n * fact n) * C := by
        calc power (r + 1) (n + 1) + (r + 1) * C = (r + 1) * (power (r + 1) n + C) := by
              rw [power_succ]; ring
          _ ≤ power (r + 1) (n + 1) + n * n * (fact n * C) := e1
          _ = power (r + 1) (n + 1) + (n * n * fact n) * C := by ring
      have e3 : (r + 1) * C ≤ (n * n * fact n) * C := (add_le_add_iff_left _).mp e2
      have e4 : r + 1 ≤ n * n * fact n := le_of_mul_le_mul_right e3 hC
      exact absurd (lt_of_lt_of_le (lt_add_one r) e4) (not_lt.mpr hr)
  have hC1 : C - 1 + 1 = C := tsub_add_cancel_of_le (pos_iff_one_le.mp hC)
  have hb : C * fact n ≤ power (r + 1) n + (C - 1) := by
    have h' : fact n * C < power (r + 1) n + (C - 1) + 1 := by
      rw [add_assoc, hC1]
      exact hlt
    rw [mul_comm]
    exact LO.FirstOrder.Arithmetic.lt_succ_iff_le.mp h'
  have hCm : C - 1 < C := by
    calc C - 1 < C - 1 + 1 := lt_add_one _
      _ = C := hC1
  have ha : power (r + 1) n + (C - 1) < C * (fact n + 1) := by
    calc power (r + 1) n + (C - 1) < fact n * C + C := add_lt_add_of_le_of_lt hlow hCm
      _ = C * (fact n + 1) := by ring
  exact div_eq_of hb ha

/-- The arithmetic value of `factorialCoordinates` is the internal factorial. -/
theorem factorial_formula (n : V) :
    (power (power (n + ((2 : ℕ) : V)) (n + ((2 : ℕ) : V)) + 1) n +
        (binom (power (n + ((2 : ℕ) : V)) (n + ((2 : ℕ) : V)) + n) n - 1)) /
      binom (power (n + ((2 : ℕ) : V)) (n + ((2 : ℕ) : V)) + n) n = fact n := by
  have h2 : ((2 : ℕ) : V) = 2 := Nat.cast_ofNat
  rw [h2]
  exact ceil_formula n _ (small_factor n)

end Formula

/-- Internal correctness of the factorial graph, given the power and binomial graphs. -/
theorem factCase_of (hp : PowCase) (hb : BinomCase) : FactCase := by
  have hn := graphHolds_coordinate (σ := Fin 1) 0
  have hs := graphHolds_add hn (graphHolds_constant (σ := Fin 1) 2)
  have hR := graphHolds_pow hp hs hs
  have hC := graphHolds_binomial hb (graphHolds_add hR hn) hn
  have hnum := graphHolds_add
    (graphHolds_pow hp (graphHolds_add hR (graphHolds_constant 1)) hn)
    (graphHolds_sub hC (graphHolds_constant 1))
  refine holds_congr _ ?_ (graphHolds_div hnum hC)
  intro V _ _ v
  show v none =
      (power (power (v (some 0) + ((2 : ℕ) : V)) (v (some 0) + ((2 : ℕ) : V)) + ((1 : ℕ) : V))
          (v (some 0)) +
        (binom (power (v (some 0) + ((2 : ℕ) : V)) (v (some 0) + ((2 : ℕ) : V)) + v (some 0))
          (v (some 0)) - ((1 : ℕ) : V))) /
        binom (power (v (some 0) + ((2 : ℕ) : V)) (v (some 0) + ((2 : ℕ) : V)) + v (some 0))
          (v (some 0)) ↔
    v none = fact (v (some 0))
  rw [Nat.cast_one, factorial_formula]

end DiophantineConsistency.ModelRepFactorial
