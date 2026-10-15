import GowersSzemeredi.Proofs05WeylConstantBounds
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The Weyl budget in every degree, and the Schmidt formula with symbolic
exponents (Notes L.6, E6).

`Proofs05WeylConstantBounds` bounds the Weyl budget numerically for `j ≤ 2`.
Route (II) in every dimension needs it for all `j`:
* `weylNextBudget_le`: `weylNextBudget k B K ≤ 2^(k+18)·B⁴·K³` for `B, K ≥ 1`;
* `weylBudget_le_gen`: `weylBudget j B ≤ 2^(weylBudgetLog j)·B^(weylBudgetDeg j)` for `B ≥ 1`, with
  `weylBudgetDeg (j+1) = 6·weylBudgetDeg j + 4` and `weylBudgetLog (j+1) = 3·weylBudgetLog j + 9·weylBudgetDeg j + j + 19`;
* `weylBudgetDeg_succ_le`: `weylBudgetDeg j + 1 ≤ 6^(j+1)`, and `weylBudgetLog_le`: `weylBudgetLog j ≤ (j+10)·6^(j+2)`;
* `weylBudgetPolynomial_eval_one_le_gen` and
  `weylBudgetPolynomial_natDegree_le_gen`: `A_j ≤ 2^(weylBudgetLog j)` and
  `natDegree ≤ weylBudgetLog j + weylBudgetDeg j`, through `two_pow_natDegree_le_eval_two`;
* `schmidt_base_formula_le_gen`: the Schmidt base formula at `C ≤ 2^c` is at
  most `2^(c + 3e + 35)`, for every `e`.

All of this is stated without the port's Schmidt names, so it is checked
locally; the heavy bridge only unfolds definitions. -/
set_option autoImplicit false
namespace LeanProofs.GowersSzemeredi

open Polynomial

/-! ### One Weyl step -/

theorem weylNextBudget_le (k B K : Nat) (hB : 1 ≤ B) (hK : 1 ≤ K) :
    OAI.Erdos3.weylNextBudget k B K ≤ 2 ^ (k + 18) * B ^ 4 * K ^ 3 := by
  unfold OAI.Erdos3.weylNextBudget
  have hk : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  have hA : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hB2 : B ^ 2 ≤ B ^ 4 := Nat.pow_le_pow_right hB (by norm_num)
  have hK1 : K ≤ K ^ 3 := by
    calc K = K ^ 1 := (pow_one K).symm
      _ ≤ K ^ 3 := Nat.pow_le_pow_right hK (by norm_num)
  have hK2 : K ^ 2 ≤ K ^ 3 := Nat.pow_le_pow_right hK (by norm_num)
  have hB1 : 1 ≤ B ^ 2 := Nat.one_le_pow _ _ hB
  have hK3 : 1 ≤ K ^ 3 := Nat.one_le_pow _ _ hK
  have h18 : 2 ^ (k + 18) = 2 ^ k * 262144 := by rw [pow_add]; norm_num
  rw [h18]
  set X := 2 ^ k * B ^ 4 * K ^ 3 with hX
  have hX1 : K ≤ X := by
    calc K ≤ K ^ 3 := hK1
      _ = 1 * 1 * K ^ 3 := by ring
      _ ≤ 2 ^ k * B ^ 4 * K ^ 3 := Nat.mul_le_mul (Nat.mul_le_mul hA (le_trans hB1 hB2)) le_rfl
  have hX2 : B ^ 2 ≤ X := by
    calc B ^ 2 ≤ B ^ 4 := hB2
      _ = 1 * B ^ 4 * 1 := by ring
      _ ≤ 2 ^ k * B ^ 4 * K ^ 3 := Nat.mul_le_mul (Nat.mul_le_mul hA le_rfl) hK3
  have hX3 : B ^ 2 * K ≤ X := by
    calc B ^ 2 * K ≤ B ^ 4 * K ^ 3 := Nat.mul_le_mul hB2 hK1
      _ = 1 * B ^ 4 * K ^ 3 := by ring
      _ ≤ 2 ^ k * B ^ 4 * K ^ 3 := Nat.mul_le_mul (Nat.mul_le_mul hA le_rfl) le_rfl
  have hX4 : (k + 1) * B ^ 2 * K ^ 2 ≤ X := by
    calc (k + 1) * B ^ 2 * K ^ 2 ≤ 2 ^ k * B ^ 4 * K ^ 3 :=
          Nat.mul_le_mul (Nat.mul_le_mul hk hB2) hK2
      _ = X := rfl
  have e1 : 128 * B ^ 2 * K = 128 * (B ^ 2 * K) := by ring
  have e2 : 65536 * 2 ^ k * B ^ 4 * K ^ 3 = 65536 * X := by rw [hX]; ring
  have e3 : 128 * (k + 1) * B ^ 2 * K ^ 2 = 128 * ((k + 1) * B ^ 2 * K ^ 2) := by ring
  have e4 : 98304 * 2 ^ k * B ^ 4 * K ^ 3 = 98304 * X := by rw [hX]; ring
  have e5 : 2 ^ k * 262144 * B ^ 4 * K ^ 3 = 262144 * X := by rw [hX]; ring
  rw [e1, e2, e3, e4, e5]
  omega

/-! ### Every degree -/

/-- The `B`-exponent of the Weyl budget bound. -/
def weylBudgetDeg : Nat → Nat
  | 0 => 1
  | j + 1 => 6 * weylBudgetDeg j + 4

/-- The constant exponent of the Weyl budget bound. -/
def weylBudgetLog : Nat → Nat
  | 0 => 0
  | j + 1 => 3 * weylBudgetLog j + 9 * weylBudgetDeg j + j + 19

/-- **The Weyl budget in every degree.** -/
theorem weylBudget_le_gen : ∀ (j : Nat) {B : Nat}, 1 ≤ B →
    OAI.Erdos3.weylBudget j B ≤ 2 ^ weylBudgetLog j * B ^ weylBudgetDeg j
  | 0, B, _ => by simp [OAI.Erdos3.weylBudget, weylBudgetLog, weylBudgetDeg]
  | j + 1, B, hB => by
    have hB8 : 1 ≤ 8 * B ^ 2 := le_trans hB (by nlinarith [Nat.one_le_pow 2 B hB])
    have ih := weylBudget_le_gen j hB8
    have hK : 1 ≤ OAI.Erdos3.weylBudget j (8 * B ^ 2) := OAI.Erdos3.weylBudget_pos j (by omega)
    have hstep := weylNextBudget_le (j + 1) B _ hB hK
    show OAI.Erdos3.weylNextBudget (j + 1) B (OAI.Erdos3.weylBudget j (8 * B ^ 2)) ≤ _
    refine hstep.trans ?_
    have hK' : OAI.Erdos3.weylBudget j (8 * B ^ 2) ≤ 2 ^ (weylBudgetLog j + 3 * weylBudgetDeg j) * B ^ (2 * weylBudgetDeg j) := by
      refine ih.trans (le_of_eq ?_)
      rw [mul_pow, show (8 : Nat) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_mul, pow_add]
      ring
    have h3 := Nat.pow_le_pow_left hK' 3
    calc 2 ^ (j + 1 + 18) * B ^ 4 * OAI.Erdos3.weylBudget j (8 * B ^ 2) ^ 3
        ≤ 2 ^ (j + 1 + 18) * B ^ 4 * (2 ^ (weylBudgetLog j + 3 * weylBudgetDeg j) * B ^ (2 * weylBudgetDeg j)) ^ 3 :=
          Nat.mul_le_mul_left _ h3
      _ = 2 ^ weylBudgetLog (j + 1) * B ^ weylBudgetDeg (j + 1) := by
          simp only [weylBudgetLog, weylBudgetDeg]
          rw [mul_pow, ← pow_mul, ← pow_mul]
          rw [show 3 * weylBudgetLog j + 9 * weylBudgetDeg j + j + 19 = (j + 1 + 18) + (weylBudgetLog j + 3 * weylBudgetDeg j) * 3 by ring,
            show 6 * weylBudgetDeg j + 4 = 4 + 2 * weylBudgetDeg j * 3 by ring, pow_add, pow_add]
          ring

theorem weylBudgetDeg_succ_le : ∀ j : Nat, weylBudgetDeg j + 1 ≤ 6 ^ (j + 1)
  | 0 => by simp [weylBudgetDeg]
  | j + 1 => by
    have ih := weylBudgetDeg_succ_le j
    show 6 * weylBudgetDeg j + 4 + 1 ≤ 6 ^ (j + 1 + 1)
    rw [pow_succ]
    omega

theorem weylBudgetLog_le : ∀ j : Nat, weylBudgetLog j ≤ (j + 10) * 6 ^ (j + 2)
  | 0 => by simp [weylBudgetLog]
  | j + 1 => by
    have ih := weylBudgetLog_le j
    have hE := weylBudgetDeg_succ_le j
    show 3 * weylBudgetLog j + 9 * weylBudgetDeg j + j + 19 ≤ (j + 1 + 10) * 6 ^ (j + 1 + 2)
    have h6 : 6 ^ (j + 1 + 2) = 6 ^ (j + 2) * 6 := by rw [show j + 1 + 2 = (j + 2) + 1 by ring, pow_succ]
    have h6' : 6 ^ (j + 2) = 6 ^ (j + 1) * 6 := by rw [pow_succ]
    have hpos : 36 ≤ 6 ^ (j + 2) := by
      calc 36 = 6 ^ 2 := by norm_num
        _ ≤ 6 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [h6]
    nlinarith

/-! ### The Weyl constants -/

theorem weylBudgetPolynomial_eval_one_le_gen (j : Nat) :
    (OAI.Erdos3.weylBudgetPolynomial j).eval 1 ≤ 2 ^ weylBudgetLog j := by
  rw [OAI.Erdos3.weylBudgetPolynomial_eval]
  have h := weylBudget_le_gen j (B := 1) le_rfl
  simpa using h

theorem weylBudgetPolynomial_natDegree_le_gen (j : Nat) :
    (OAI.Erdos3.weylBudgetPolynomial j).natDegree ≤ weylBudgetLog j + weylBudgetDeg j := by
  have hne : OAI.Erdos3.weylBudgetPolynomial j ≠ 0 := by
    intro h
    have hpos := OAI.Erdos3.weylBudget_pos j (B := 1) (by norm_num)
    rw [← OAI.Erdos3.weylBudgetPolynomial_eval, h] at hpos
    simp at hpos
  have h1 := two_pow_natDegree_le_eval_two _ hne
  rw [OAI.Erdos3.weylBudgetPolynomial_eval] at h1
  have h2 := weylBudget_le_gen j (B := 2) (by norm_num)
  rw [← pow_add] at h2
  have h3 := h1.trans h2
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h3

/-! ### The Schmidt base formula -/

/-- **The Schmidt base formula at `C ≤ 2^c` is at most `2^(c + 3e + 35)`.** -/
theorem schmidt_base_formula_le_gen (C e c : Nat) (hC : (C : Real) ≤ 2 ^ c) :
    2 + 121 * Real.exp 10 + (10 + 8 * Real.exp (4 * Real.pi + 1)) *
        (1 + 2 * Real.exp Real.pi * (C : Real) * (8 : Real) ^ e) +
      ((15 * (e + 1) + 23 : Nat) : Real) ≤ 2 ^ (c + 3 * e + 35) := by
  have he1 : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have hexp : ∀ n : Nat, Real.exp n ≤ 3 ^ n := fun n => by
    rw [← Real.exp_one_rpow, Real.rpow_natCast]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le he1 n
  have h10 : Real.exp 10 ≤ 3 ^ 10 := by exact_mod_cast hexp 10
  have h14 : Real.exp (4 * Real.pi + 1) ≤ 3 ^ 14 := by
    have hpi := Real.pi_lt_d2
    calc Real.exp (4 * Real.pi + 1) ≤ Real.exp 14 := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 3 ^ 14 := by exact_mod_cast hexp 14
  have h4 : Real.exp Real.pi ≤ 81 := by
    have hpi := Real.pi_lt_d2
    calc Real.exp Real.pi ≤ Real.exp 4 := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 3 ^ 4 := by exact_mod_cast hexp 4
      _ = 81 := by norm_num
  set X : Real := (2 : Real) ^ (c + 3 * e) with hXdef
  have hX1 : 1 ≤ X := one_le_pow₀ (by norm_num)
  have h8e : (8 : Real) ^ e = 2 ^ (3 * e) := by
    rw [show (8 : Real) = 2 ^ 3 by norm_num, ← pow_mul]
  have hCe : (C : Real) * 8 ^ e ≤ X := by
    rw [h8e, hXdef, pow_add]
    exact mul_le_mul_of_nonneg_right hC (by positivity)
  have hEe : ((15 * (e + 1) + 23 : Nat) : Real) ≤ 64 * X := by
    have hlin : 15 * (e + 1) + 23 ≤ 64 * 2 ^ e := by
      have : e < 2 ^ e := Nat.lt_two_pow_self
      omega
    have hc1 : ((15 * (e + 1) + 23 : Nat) : Real) ≤ 64 * (2 : Real) ^ e := by exact_mod_cast hlin
    have hc2 : (2 : Real) ^ e ≤ X := by
      rw [hXdef]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hinner : 1 + 2 * Real.exp Real.pi * (C : Real) * (8 : Real) ^ e ≤ 256 * X := by
    have : 2 * Real.exp Real.pi * (C : Real) * (8 : Real) ^ e ≤ 162 * X := by
      calc 2 * Real.exp Real.pi * (C : Real) * (8 : Real) ^ e
          = 2 * Real.exp Real.pi * ((C : Real) * 8 ^ e) := by ring
        _ ≤ 2 * 81 * X := mul_le_mul (by linarith) hCe (by positivity) (by norm_num)
        _ = 162 * X := by ring
    linarith
  have houter : 10 + 8 * Real.exp (4 * Real.pi + 1) ≤ 2 ^ 26 := by
    have : (10 : Real) + 8 * 3 ^ 14 ≤ 2 ^ 26 := by norm_num
    linarith
  have hprod : (10 + 8 * Real.exp (4 * Real.pi + 1)) *
      (1 + 2 * Real.exp Real.pi * (C : Real) * (8 : Real) ^ e) ≤ 2 ^ 26 * (256 * X) :=
    mul_le_mul houter hinner (by positivity) (by positivity)
  have hgoal : (2 : Real) ^ (c + 3 * e + 35) = X * 2 ^ 35 := by rw [hXdef, pow_add]
  rw [hgoal]
  nlinarith


/-! ### The family-lemma constants -/

/-- The exponent bounding the Schmidt base constant in degree `j + 1`. -/
def schmidtKExp (j : Nat) : Nat := weylBudgetLog j + 5 * (weylBudgetLog j + weylBudgetDeg j + 1) + 35

/-- The bound on the Schmidt exponent constant in degree `j + 1`. -/
def schmidtPBnd (j : Nat) : Nat := 15 * (weylBudgetLog j + weylBudgetDeg j + 2) + 23

theorem weylBudgetDeg_mono : Monotone weylBudgetDeg := by
  refine monotone_nat_of_le_succ fun j => ?_
  show weylBudgetDeg j ≤ 6 * weylBudgetDeg j + 4
  omega

theorem weylBudgetLog_mono : Monotone weylBudgetLog := by
  refine monotone_nat_of_le_succ fun j => ?_
  show weylBudgetLog j ≤ 3 * weylBudgetLog j + 9 * weylBudgetDeg j + j + 19
  omega

theorem schmidtKExp_mono : Monotone schmidtKExp := fun a b h => by
  unfold schmidtKExp
  have h1 := weylBudgetLog_mono h
  have h2 := weylBudgetDeg_mono h
  omega

theorem schmidtPBnd_mono : Monotone schmidtPBnd := fun a b h => by
  unfold schmidtPBnd
  have h1 := weylBudgetLog_mono h
  have h2 := weylBudgetDeg_mono h
  omega

theorem six_pow_le (n : Nat) : 6 ^ n ≤ 2 ^ (3 * n) := by
  rw [pow_mul]; exact Nat.pow_le_pow_left (by norm_num) n

theorem weylBudgetDegLog_le (k : Nat) : weylBudgetLog k + weylBudgetDeg k + 2 ≤ 2 ^ (4 * k + 11) := by
  have hF := weylBudgetLog_le k
  have hE := weylBudgetDeg_succ_le k
  have h1 : 6 ^ (k + 2) ≤ 2 ^ (3 * k + 6) := by
    have := six_pow_le (k + 2); rwa [show 3 * (k + 2) = 3 * k + 6 by ring] at this
  have h2 : 6 ^ (k + 1) ≤ 2 ^ (3 * k + 3) := by
    have := six_pow_le (k + 1); rwa [show 3 * (k + 1) = 3 * k + 3 by ring] at this
  have h3 : k + 10 ≤ 2 ^ (k + 4) := by
    have : k < 2 ^ k := Nat.lt_two_pow_self
    have h16 : 2 ^ (k + 4) = 2 ^ k * 16 := by rw [pow_add]; norm_num
    omega
  have h4 : (k + 10) * 6 ^ (k + 2) ≤ 2 ^ (4 * k + 10) := by
    calc (k + 10) * 6 ^ (k + 2) ≤ 2 ^ (k + 4) * 2 ^ (3 * k + 6) := Nat.mul_le_mul h3 h1
      _ = 2 ^ (4 * k + 10) := by rw [← pow_add]; ring_nf
  have h5 : 2 ^ (3 * k + 3) < 2 ^ (4 * k + 10) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h6 : 2 ^ (4 * k + 11) = 2 ^ (4 * k + 10) * 2 := by rw [pow_succ]
  have hFa : weylBudgetLog k ≤ 2 ^ (4 * k + 10) := hF.trans h4
  have hEa : weylBudgetDeg k + 1 ≤ 2 ^ (3 * k + 3) := hE.trans h2
  rw [h6]
  omega

theorem schmidtKExp_le (k : Nat) : schmidtKExp k ≤ 2 ^ (4 * k + 14) := by
  have h := weylBudgetDegLog_le k
  unfold schmidtKExp
  have h14 : 2 ^ (4 * k + 14) = 2 ^ (4 * k + 11) * 8 := by
    rw [show 4 * k + 14 = (4 * k + 11) + 3 by ring, pow_add]; norm_num
  have h11 : 2 ^ 11 ≤ 2 ^ (4 * k + 11) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem schmidtPBnd_le (k : Nat) : schmidtPBnd k ≤ 2 ^ (4 * k + 16) := by
  have h := weylBudgetDegLog_le k
  unfold schmidtPBnd
  have h16 : 2 ^ (4 * k + 16) = 2 ^ (4 * k + 11) * 32 := by
    rw [show 4 * k + 16 = (4 * k + 11) + 5 by ring, pow_add]; norm_num
  have h11 : 2 ^ 11 ≤ 2 ^ (4 * k + 11) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- A base constant dominating `1 + (k+1)·2^E`. -/
theorem uniform_base_le (k E : Nat) :
    (1 : Real) + (k + 1) * 2 ^ E ≤ 2 ^ (E + k + 2) ∧ (2 : Real) ≤ 2 ^ (E + k + 2) := by
  have hk : ((k + 1 : Nat) : Real) ≤ 2 ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k))
  push_cast at hk
  have hE1 : (1 : Real) ≤ 2 ^ E := one_le_pow₀ (by norm_num)
  have hsplit : (2 : Real) ^ (E + k + 2) = 2 ^ E * 2 ^ k * 4 := by rw [pow_add, pow_add]; norm_num
  rw [hsplit]
  constructor <;> nlinarith

/-- **The family-lemma constants are at most `2^(2^(4k+16))`**, given the
shapes the Schmidt layer produces (the estimates of
`family_constants_tower_le`, without the final tower). -/
theorem family_constants_poly_le (k : Nat) {MK : Real} {MP Pu : Nat}
    (hMK : MK ≤ 2 ^ (schmidtKExp k + k + 2)) (hPu : Pu ≤ 1 + (k + 1) * schmidtPBnd k)
    (hMP : MP ≤ (2 * (k + 1 + 1) * Pu + 4) ^ (2 ^ (k + 1))) :
    ((⌈MK⌉₊ : Nat) : Real) + (((k + 1) * MP : Nat) : Real) ≤
      2 ^ ((2 : Nat) ^ (4 * k + 16)) := by
  set E := schmidtKExp k
  have hE := schmidtKExp_le k
  have hPB := schmidtPBnd_le k
  have hkA : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  have hKc : ⌈MK⌉₊ ≤ 2 ^ (E + k + 2) := by
    have : MK ≤ ((2 ^ (E + k + 2) : Nat) : Real) := by push_cast; exact hMK
    exact (Nat.ceil_le).mpr this
  have hPu' : Pu ≤ 2 ^ (5 * k + 17) := by
    have h1 : (k + 1) * schmidtPBnd k ≤ 2 ^ k * 2 ^ (4 * k + 16) := Nat.mul_le_mul hkA hPB
    have h2 : 2 ^ k * 2 ^ (4 * k + 16) = 2 ^ (5 * k + 16) := by rw [← pow_add]; ring_nf
    have h3 : 2 ^ (5 * k + 17) = 2 ^ (5 * k + 16) * 2 := by rw [pow_succ]
    have h4 : 1 ≤ 2 ^ (5 * k + 16) := Nat.one_le_two_pow
    omega
  have hinner : 2 * (k + 1 + 1) * Pu + 4 ≤ 2 ^ (6 * k + 20) := by
    have h1 : 2 * (k + 1 + 1) ≤ 2 ^ (k + 2) := by
      have h := Nat.lt_two_pow_self (n := k + 1)
      rw [show k + 2 = (k + 1) + 1 by ring, pow_succ]; omega
    have h2 : 2 * (k + 1 + 1) * Pu ≤ 2 ^ (k + 2) * 2 ^ (5 * k + 17) := Nat.mul_le_mul h1 hPu'
    have h3 : 2 ^ (k + 2) * 2 ^ (5 * k + 17) = 2 ^ (6 * k + 19) := by rw [← pow_add]; ring_nf
    have h4 : 2 ^ (6 * k + 20) = 2 ^ (6 * k + 19) * 2 := by rw [pow_succ]
    have h5 : 4 ≤ 2 ^ (6 * k + 19) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (6 * k + 19) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hMP' : (k + 1) * MP ≤ 2 ^ (k + (6 * k + 20) * 2 ^ (k + 1)) := by
    have h1 : MP ≤ 2 ^ ((6 * k + 20) * 2 ^ (k + 1)) :=
      hMP.trans ((Nat.pow_le_pow_left hinner _).trans (le_of_eq (by rw [← pow_mul])))
    calc (k + 1) * MP ≤ 2 ^ k * 2 ^ ((6 * k + 20) * 2 ^ (k + 1)) := Nat.mul_le_mul hkA h1
      _ = 2 ^ (k + (6 * k + 20) * 2 ^ (k + 1)) := by rw [← pow_add]
  have hP14 : k + 2 ≤ 2 ^ (4 * k + 14) := by
    have h1 : k + 2 < 2 ^ (k + 2) := Nat.lt_two_pow_self
    have h2 : 2 ^ (k + 2) ≤ 2 ^ (4 * k + 14) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hexp1 : E + k + 2 ≤ 2 ^ (4 * k + 14) + 2 ^ (4 * k + 14) := by omega
  have hexp2 : k + (6 * k + 20) * 2 ^ (k + 1) ≤ 2 ^ (4 * k + 14) + 2 ^ (4 * k + 14) := by
    have h1 : 6 * k + 20 ≤ 2 ^ (k + 5) := by
      have : k < 2 ^ k := Nat.lt_two_pow_self
      have h32 : 2 ^ (k + 5) = 2 ^ k * 32 := by rw [pow_add]; norm_num
      omega
    have h2 : (6 * k + 20) * 2 ^ (k + 1) ≤ 2 ^ (k + 5) * 2 ^ (k + 1) := Nat.mul_le_mul_right _ h1
    have h3 : 2 ^ (k + 5) * 2 ^ (k + 1) = 2 ^ (2 * k + 6) := by rw [← pow_add]; ring_nf
    have h4 : 2 ^ (2 * k + 6) ≤ 2 ^ (4 * k + 14) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h5 : k ≤ 2 ^ (4 * k + 14) := by omega
    calc k + (6 * k + 20) * 2 ^ (k + 1) ≤ 2 ^ (4 * k + 14) + 2 ^ (2 * k + 6) := by
          rw [← h3]; exact Nat.add_le_add h5 h2
      _ ≤ 2 ^ (4 * k + 14) + 2 ^ (4 * k + 14) := Nat.add_le_add_left h4 _
  have hsum : ⌈MK⌉₊ + (k + 1) * MP ≤ 2 ^ (2 ^ (4 * k + 14) + 2 ^ (4 * k + 14) + 1) := by
    have hA := hKc.trans (Nat.pow_le_pow_right (by norm_num) hexp1)
    have hB := hMP'.trans (Nat.pow_le_pow_right (by norm_num) hexp2)
    rw [pow_succ]
    omega
  have hfin : 2 ^ (2 ^ (4 * k + 14) + 2 ^ (4 * k + 14) + 1) ≤ 2 ^ (2 ^ (4 * k + 16)) := by
    apply Nat.pow_le_pow_right (by norm_num)
    have h1 : 2 ^ (4 * k + 16) = 4 * 2 ^ (4 * k + 14) := by
      rw [show 4 * k + 16 = (4 * k + 14) + 2 by ring, pow_add]; ring
    have h2 : 1 ≤ 2 ^ (4 * k + 14) := Nat.one_le_two_pow
    omega
  have hcast : ((⌈MK⌉₊ + (k + 1) * MP : Nat) : Real) ≤ ((2 ^ (2 ^ (4 * k + 16)) : Nat) : Real) := by
    exact_mod_cast hsum.trans hfin
  push_cast at hcast ⊢
  exact hcast

/-- **The family-lemma constants are at most `2^(2^(2^(k+5)))`**, given the
shapes the Schmidt layer produces. -/
theorem family_constants_tower_le (k : Nat) {MK : Real} {MP Pu : Nat}
    (hMK : MK ≤ 2 ^ (schmidtKExp k + k + 2)) (hPu : Pu ≤ 1 + (k + 1) * schmidtPBnd k)
    (hMP : MP ≤ (2 * (k + 1 + 1) * Pu + 4) ^ (2 ^ (k + 1))) :
    ((⌈MK⌉₊ : Nat) : Real) + (((k + 1) * MP : Nat) : Real) ≤
      2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))) := by
  refine (family_constants_poly_le k hMK hPu hMP).trans ?_
  apply pow_le_pow_right₀ (by norm_num)
  apply Nat.pow_le_pow_right (by norm_num)
  have hk : k < 2 ^ k := Nat.lt_two_pow_self
  have h32 : 2 ^ (k + 5) = 2 ^ k * 32 := by rw [pow_add]; norm_num
  omega

end LeanProofs.GowersSzemeredi
