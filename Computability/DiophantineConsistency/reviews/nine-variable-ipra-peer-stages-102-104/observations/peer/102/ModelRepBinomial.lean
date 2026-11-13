import DiophantineConsistency.ModelRepInterfaces
import DiophantineConsistency.ArithmeticBinomExpansion

/-! # Internal correctness of the digit-extraction binomial graph

`FactorialRepresentation.binomialCoordinates` computes
`((2^n+2)^n / (2^n+1)^k) % (2^n+1)`. Inside every model of `𝗜𝚺₁` this equals
the represented binomial coefficient `ArithmeticBinomPascal.binom n k`, also for
`k > n` (`digit_formula`):

* the internal binomial theorem `power (q+1) n = bsum q n (n+1)`;
* for `2^n < q`, every partial sum satisfies `bsum q n j < q^j`
  (`bsum_lt_power`, from `bsum_scaled_le` and `bsum_one_le`);
* splitting the sum at degree `k` (`bsum_split`), division by `q^k` discards the
  low part, and reduction modulo `q` keeps exactly the digit `binom n k ≤ 2^n`.

`binomCase_of` turns this into `ModelRepInterfaces.BinomCase`, given the
internal power graph `PowCase`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelRepBinomial
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelRep ModelScalarPR ModelRepBasic ModelRepArith ModelRepInterfaces
open ArithmeticPow ArithmeticBinomPascal ArithmeticBinomExpansion

section Digits
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Every binomial coefficient of row `n` is at most `2^n`. -/
theorem binom_le_exp (n k : V) : binom n k ≤ Exp.exp n := by
  have h := bsum_one_le n (k + 1)
  rw [bsum_succ, one_power, mul_one] at h
  exact le_trans le_add_self h

/-- Partial sums in a radix exceeding `2^n` stay below the next power. -/
theorem bsum_lt_power (q n j : V) (hq : Exp.exp n < q) : bsum q n j < power q j := by
  have hq1 : 1 ≤ q := le_trans (one_le_exp n) hq.le
  have hpos : 0 < power q j := power_pos q j (lt_of_lt_of_le _root_.zero_lt_one hq1)
  have h1 : q * bsum q n j ≤ Exp.exp n * power q j :=
    le_trans (bsum_scaled_le q n j hq1)
      (mul_le_mul_of_nonneg_right (bsum_one_le n j) (Arithmetic.zero_le _))
  have h2 : q * bsum q n j < q * power q j :=
    lt_of_le_of_lt h1 (mul_lt_mul_of_pos_right hq hpos)
  exact lt_of_mul_lt_mul_left h2 (Arithmetic.zero_le _)

/-- Digit extraction in a radix `q > 2^n`. -/
theorem digit_extract (q n k : V) (hq : Exp.exp n < q) :
    power (q + 1) n / power q k % q = binom n k := by
  have hq0 : 0 < q := lt_of_le_of_lt (Arithmetic.zero_le _) hq
  rw [binomial_theorem]
  rcases le_or_gt k n with hkn | hkn
  · obtain ⟨w, hw⟩ := bsum_split q n k (n - k)
    have hidx : k + (n - k) + 1 = n + 1 := by rw [add_tsub_cancel_of_le hkn]
    rw [hidx] at hw
    rw [hw, add_comm (bsum q n k), div_mul_add' _ _ (bsum_lt_power q n k hq),
      mod_add_mul' _ _ hq0, mod_eq_self_of_lt (lt_of_le_of_lt (binom_le_exp n k) hq)]
  · have hst : bsum q n k = bsum q n (n + 1) := by
      have h := bsum_stable q n (k - (n + 1))
      rwa [add_tsub_cancel_of_le (LO.FirstOrder.Arithmetic.succ_le_iff_lt.mpr hkn)] at h
    rw [← hst, div_eq_zero_of_lt _ (bsum_lt_power q n k hq), zero_mod,
      binom_eq_zero_of_lt n k hkn]

/-- The arithmetic value of `binomialCoordinates` is the internal binomial. -/
theorem digit_formula (n k : V) :
    power (power ((2 : ℕ) : V) n + 1 + 1) n / power (power ((2 : ℕ) : V) n + 1) k %
      (power ((2 : ℕ) : V) n + 1) = binom n k := by
  have h2 : ((2 : ℕ) : V) = 2 := Nat.cast_ofNat
  rw [h2]
  exact digit_extract (power 2 n + 1) n k (by rw [power_two]; exact lt_add_one _)

end Digits

/-- Internal correctness of the binomial graph, given the internal power graph. -/
theorem binomCase_of (hp : PowCase) : BinomCase := by
  have hn := graphHolds_coordinate (σ := Fin 2) 0
  have hk := graphHolds_coordinate (σ := Fin 2) 1
  have hq := graphHolds_add (graphHolds_pow hp (graphHolds_constant (σ := Fin 2) 2) hn)
    (graphHolds_constant (σ := Fin 2) 1)
  have hr := graphHolds_mod (graphHolds_div
    (graphHolds_pow hp (graphHolds_add hq (graphHolds_constant 1)) hn)
    (graphHolds_pow hp hq hk)) hq
  refine holds_congr _ ?_ hr
  intro V _ _ v
  show v none =
      power (power ((2 : ℕ) : V) (v (some 0)) + ((1 : ℕ) : V) + ((1 : ℕ) : V)) (v (some 0)) /
        power (power ((2 : ℕ) : V) (v (some 0)) + ((1 : ℕ) : V)) (v (some 1)) %
        (power ((2 : ℕ) : V) (v (some 0)) + ((1 : ℕ) : V)) ↔
    v none = binom (v (some 0)) (v (some 1))
  rw [Nat.cast_one, digit_formula]

end DiophantineConsistency.ModelRepBinomial
