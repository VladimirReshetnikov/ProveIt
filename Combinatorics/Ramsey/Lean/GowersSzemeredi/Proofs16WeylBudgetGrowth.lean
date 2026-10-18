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
  simpa using weylBudget_le_gen j (B := 1) le_rfl

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
  have hexp (x : Real) (n : Nat) (h : x ≤ n) : Real.exp x ≤ 3 ^ n :=
    (Real.exp_le_exp.mpr h).trans ((Real.exp_one_pow n).symm.trans_le
      (pow_le_pow_left₀ (Real.exp_pos 1).le (Real.exp_one_lt_d9.le.trans (by norm_num)) n))
  have hpi := Real.pi_lt_d2
  have h10 := hexp 10 10 (by norm_num)
  have h14 := hexp (4 * Real.pi + 1) 14 (by push_cast; linarith)
  set X : Real := (2 : Real) ^ (c + 3 * e) with hXdef
  have hX1 : 1 ≤ X := one_le_pow₀ (by norm_num)
  have hCe : (C : Real) * 8 ^ e ≤ X := by
    rw [hXdef, pow_add, pow_mul]
    exact mul_le_mul hC (by norm_num) (by positivity) (by positivity)
  have he : ((e + 1 : Nat) : Real) ≤ 2 ^ e := by exact_mod_cast Nat.lt_two_pow_self (n := e)
  have he' : (2 : Real) ^ e ≤ X := by
    rw [hXdef]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hin := mul_le_mul (hexp Real.pi 4 (by push_cast; linarith)) hCe (by positivity)
    (by positivity)
  have hprod := mul_le_mul (show 10 + 8 * Real.exp (4 * Real.pi + 1) ≤ 2 ^ 26 by linarith)
    (show 1 + 2 * Real.exp Real.pi * (C : Real) * 8 ^ e ≤ 1 + 2 * 81 * X by linarith)
    (by positivity) (by positivity)
  rw [pow_add, ← hXdef]
  push_cast at he ⊢
  linarith

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
  have hp {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right Nat.zero_lt_two h
  have hk (n : Nat) : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have hin : 2 * (k + 1 + 1) * Pu + 4 ≤ 2 ^ (6 * k + 20) := by
    have h1 := Nat.mul_le_mul (Nat.mul_le_mul_left 2 (hk (k + 1)))
      (hPu.trans (Nat.add_le_add_left (Nat.mul_le_mul (hk k) (schmidtPBnd_le k)) 1))
    have h2 : 2 * 2 ^ (k + 1) * (1 + 2 ^ k * 2 ^ (4 * k + 16)) =
        4 * 2 ^ k + 2 ^ (6 * k + 18) := by ring
    have h3 : 2 ^ (6 * k + 20) = 4 * 2 ^ (6 * k + 18) := by ring
    have h4 : 8 * 2 ^ k ≤ 2 ^ (6 * k + 18) :=
      (by ring : 8 * 2 ^ k = 2 ^ (k + 3)).trans_le (hp (by omega))
    have := hk k
    omega
  have hMP' : (k + 1) * MP ≤ 2 ^ (k + (6 * k + 20) * 2 ^ (k + 1)) := by
    rw [pow_add, pow_mul]
    exact Nat.mul_le_mul (hk k) (hMP.trans (Nat.pow_le_pow_left hin _))
  have hT := hk (4 * k + 14)
  have hexp : k + (6 * k + 20) * 2 ^ (k + 1) ≤ 2 * 2 ^ (4 * k + 14) := by
    have h1 : 6 * k + 20 ≤ 2 ^ (k + 5) := by
      have : 2 ^ (k + 5) = 32 * 2 ^ k := by ring
      have := hk k
      omega
    have h2 := Nat.mul_le_mul_right (2 ^ (k + 1)) h1
    have h3 : 2 ^ (k + 5) * 2 ^ (k + 1) = 2 ^ (2 * k + 6) := by ring
    have h4 := hp (show 2 * k + 6 ≤ 4 * k + 14 by omega)
    omega
  have hE : schmidtKExp k + k + 2 ≤ 2 * 2 ^ (4 * k + 14) := by have := schmidtKExp_le k; omega
  have hKc : ⌈MK⌉₊ ≤ 2 ^ (schmidtKExp k + k + 2) := Nat.ceil_le.mpr (by exact_mod_cast hMK)
  have hsum := Nat.add_le_add (hKc.trans (hp hE)) (hMP'.trans (hp hexp))
  rw [← two_mul, ← pow_succ'] at hsum
  have h16 : 2 ^ (4 * k + 16) = 4 * 2 ^ (4 * k + 14) := by ring
  exact_mod_cast hsum.trans (hp (show 2 * 2 ^ (4 * k + 14) + 1 ≤ 2 ^ (4 * k + 16) by omega))

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
