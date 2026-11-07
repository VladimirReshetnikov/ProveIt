import DiophantineConsistency.Mixed121.Mixed121ControllerData
import Mathlib.Tactic.ReduceModChar

/-! Conditional controller-unit proof at the source34 constants: `Γ` is a unit
modulo `d·λ^(m+1)`, given the kernel residue `K ≡ 2050743806 (mod C0)`.

This is `Mixed121ConstructionUnit` with the source34 residues. The kernel
residue changes (`Source34KernelResidue.kernel_mod`), so `Γ ≡ 1150455639`
modulo `C0`, whose exact order is the full Carmichael exponent `334620` of
`C0 = 11²·13·677·2341` (`gamma_order_nat`). The lift to `d·λ^(m+1)` is the
same LTE step. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Source34ConstructionUnit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPow ArithmeticControllerLift Mixed121ControllerData

/-! ## Standard residues modulo `L = 2492980061` -/

theorem nat_mod_of_zmod {m : ℕ} [NeZero m] (a b : ℕ) (h : (a : ZMod m) = b) (hb : b < m) :
    a % m = b := by
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hb] using congrArg ZMod.val h

theorem B_nat : 2 ^ 1064921 % 2492980061 = 1114334487 := by
  apply nat_mod_of_zmod _ _ _ (by norm_num)
  rw [Nat.cast_pow, Nat.cast_ofNat]
  reduce_mod_char

theorem rho_nat : 2 ^ (121 * 1063) % 2492980061 = 2402499162 := by
  apply nat_mod_of_zmod _ _ _ (by norm_num)
  rw [Nat.cast_pow, Nat.cast_ofNat]
  change (2 : ZMod 2492980061) ^ 128623 = 2402499162
  reduce_mod_char

theorem frob_nat : 1114334487 ^ 2341 % 2492980061 = 1114334487 := by
  apply nat_mod_of_zmod _ _ _ (by norm_num)
  rw [Nat.cast_pow, Nat.cast_ofNat]
  reduce_mod_char

theorem gamma_order_nat : 1150455639 ^ 334620 % 2492980061 = 1 := by
  apply nat_mod_of_zmod _ _ _ (by norm_num)
  rw [Nat.cast_pow, Nat.cast_ofNat]
  reduce_mod_char

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem L_pos : (0 : V) < 2492980061 := by norm_num

theorem cast_mod_eq {a b r : ℕ} (h : a % b = r) : (a : V) % (b : V) = (r : V) := by
  rw [← cast_mod, h]

theorem power_natCast (x : V) (k : ℕ) : power x (k : V) = x ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_add, Nat.cast_one, power_succ, ih, pow_succ, mul_comm]

theorem pow_cong {M : V} (hM : 0 < M) (a b : V) (h : a % M = b % M) :
    ∀ n, power a n % M = power b n % M := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => rw [power_succ, power_succ, mod_mul hM, ih, h, ← mod_mul hM]

/-- Product and sum of numeral residues. -/
theorem mul_res {a b : V} {x y : ℕ} (ha : a % 2492980061 = (x : V))
    (hb : b % 2492980061 = (y : V)) :
    (a * b) % 2492980061 = ((x * y % 2492980061 : ℕ) : V) := by
  rw [mod_mul L_pos, ha, hb, ← Nat.cast_mul,
    show (2492980061 : V) = ((2492980061 : ℕ) : V) by simp, ← cast_mod]

theorem add_res {a b : V} {x y : ℕ} (ha : a % 2492980061 = (x : V))
    (hb : b % 2492980061 = (y : V)) :
    (a + b) % 2492980061 = ((x + y) % 2492980061 : ℕ) := by
  rw [mod_add L_pos, ha, hb, ← Nat.cast_add,
    show (2492980061 : V) = ((2492980061 : ℕ) : V) by simp, ← cast_mod]

theorem sub_one_res {a : V} {x : ℕ} (hx : 1 ≤ x) (hxL : x < 2492980061)
    (ha : a % 2492980061 = (x : V)) : (a - 1) % 2492980061 = ((x - 1 : ℕ) : V) := by
  have hd := div_add_mod a 2492980061
  rw [ha] at hd
  have hx1 : (1 : V) ≤ (x : V) := by exact_mod_cast hx
  have hsub : ((x - 1 : ℕ) : V) = (x : V) - 1 := by
    have h1 : ((x - 1 : ℕ) : V) + 1 = (x : V) := by
      exact_mod_cast Nat.sub_add_cancel hx
    exact eq_tsub_of_add_eq h1
  rw [← hd, add_tsub_assoc_of_le hx1, ← hsub, mod_mul_add' _ _ L_pos,
    mod_eq_self_of_lt (by exact_mod_cast (lt_of_le_of_lt (Nat.sub_le x 1) hxL))]

theorem one_res : (1 : V) % 2492980061 = ((1 : ℕ) : V) := by
  rw [Nat.cast_one]; exact mod_eq_self_of_lt (by norm_num)

/-! ## `B = 2^d` modulo `L`, and its Frobenius fixed point -/

theorem exp_eq_power (x : V) : Exp.exp (1064921 * x) = power (Exp.exp 1064921) x := by
  rw [← power_two, ← power_two, power_iterate]

theorem B_res : Exp.exp (1064921 : V) % 2492980061 = ((1114334487 : ℕ) : V) := by
  have h := cast_exp (V := V) 1064921
  rw [Nat.cast_ofNat] at h
  rw [h, show (2492980061 : V) = ((2492980061 : ℕ) : V) by simp, cast_mod_eq B_nat]

theorem B_frob : power (Exp.exp (1064921 : V)) 2341 % 2492980061 =
    Exp.exp (1064921 : V) % 2492980061 := by
  have h1 := pow_cong L_pos (Exp.exp (1064921 : V)) ((1114334487 : ℕ) : V)
    (by rw [B_res, mod_eq_self_of_lt (by norm_num)]) 2341
  rw [h1, B_res, show (2341 : V) = ((2341 : ℕ) : V) by simp, power_natCast, ← Nat.cast_pow,
    show (2492980061 : V) = ((2492980061 : ℕ) : V) by simp, cast_mod_eq frob_nat]

theorem B_frob_iter : ∀ n, power (Exp.exp (1064921 : V)) (power 2341 n) % 2492980061 =
    Exp.exp (1064921 : V) % 2492980061 := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    rw [power_succ, ← power_iterate]
    rw [pow_cong L_pos _ _ B_frob, ih]

theorem exp_p_res (n : V) :
    Exp.exp (1064921 * power 2341 n) % 2492980061 = ((1114334487 : ℕ) : V) := by
  rw [exp_eq_power, B_frob_iter, B_res]

/-! ## The unit -/

/-- `Γ = ρ^1063 (q² − 1)(1 + q(K + B^s))`. -/
def Gamma (K N s : V) : V :=
  Exp.exp (121 * 1063) * (Exp.exp (1064921 * N) ^ 2 - 1) *
    (1 + Exp.exp (1064921 * N) * (K + Exp.exp (1064921 * s)))

theorem rho_res : Exp.exp (121 * 1063 : V) % 2492980061 = ((2402499162 : ℕ) : V) := by
  have h := cast_exp (V := V) (121 * 1063)
  rw [show ((121 * 1063 : ℕ) : V) = 121 * 1063 by push_cast; ring] at h
  rw [h, show (2492980061 : V) = ((2492980061 : ℕ) : V) by simp, cast_mod_eq rho_nat]

theorem Gamma_res (K : V) (hK : K % 2492980061 = 2050743806) (m e : V) :
    Gamma K (power 2341 (m + 1)) (power 2341 e) % 2492980061 = ((1150455639 : ℕ) : V) := by
  have hq := exp_p_res (V := V) (m + 1)
  have hs := exp_p_res (V := V) e
  have hq2 : (Exp.exp (1064921 * power (2341 : V) (m + 1)) ^ 2) % 2492980061 =
      ((1683307311 : ℕ) : V) := by
    rw [pow_two, mul_res hq hq]
  have hq21 := sub_one_res (by norm_num) (by norm_num) hq2
  have hKs := add_res hK hs
  have hqK := mul_res hq hKs
  have h1 := add_res one_res hqK
  have hr := mul_res (mul_res rho_res hq21) h1
  exact hr

/-- `Γ` is a unit modulo `d·N`, conditional on the stated kernel residue. -/
theorem gamma_unit (K : V) (hK : K % 2492980061 = 2050743806) (m e : V) :
    ∃ Γi, (Gamma K (power 2341 (m + 1)) (power 2341 e) * Γi) %
        (1064921 * power 2341 (m + 1)) = 1 % (1064921 * power 2341 (m + 1)) := by
  set G := Gamma K (power (2341 : V) (m + 1)) (power 2341 e) with hG
  have hGr := Gamma_res K hK m e
  rw [← hG] at hGr
  -- G^λ ≡ 1 (mod L)
  have hpow : power G 334620 % 2492980061 = 1 := by
    rw [pow_cong L_pos G ((1150455639 : ℕ) : V) (by rw [hGr, mod_eq_self_of_lt (by norm_num)]),
      show (334620 : V) = ((334620 : ℕ) : V) by simp, power_natCast, ← Nat.cast_pow,
      show (2492980061 : V) = ((2492980061 : ℕ) : V) by simp, cast_mod_eq gamma_order_nat]
    simp
  obtain ⟨v1, hd⟩ : ∃ v1, power G 334620 = 1 + 1064921 * 2341 * v1 :=
    ⟨_, by simpa only [show (1064921 : V) * 2341 = 2492980061 by norm_num, hpow, add_comm]
      using (div_add_mod (power G 334620) (1064921 * 2341)).symm⟩
  obtain ⟨w, _, hw⟩ := lte (c := (1064921 : V)) (v := v1) p_odd m
  refine ⟨power G (334620 * power 2341 m - 1), ?_⟩
  have hpos : 1 ≤ 334620 * power (2341 : V) m :=
    one_le_mul (by norm_num) (pos_iff_one_le.mp (power_pos _ _ p_pos))
  have hmul : G * power G (334620 * power 2341 m - 1) = power G (334620 * power 2341 m) := by
    conv_rhs => rw [← tsub_add_cancel_of_le hpos]
    rw [power_succ]
  rw [hmul, ← power_iterate, hd, hw, power_succ,
    show (1064921 : V) * (2341 * power 2341 m) = 1064921 * 2341 * power 2341 m by ring,
    mod_add_mul' _ _ (mul_pos C0_pos (power_pos _ _ p_pos))]

/-- The residue premise can be supplied by a standard natural-number calculation. -/
theorem gamma_unit_nat (k : ℕ) (hk : k % 2492980061 = 2050743806) (m e : V) :
    ∃ Γi, (Gamma (k : V) (power 2341 (m + 1)) (power 2341 e) * Γi) %
        (1064921 * power 2341 (m + 1)) = 1 % (1064921 * power 2341 (m + 1)) := by
  exact gamma_unit (k : V) (cast_mod_eq hk) m e

#print axioms gamma_unit
#print axioms gamma_unit_nat

end DiophantineConsistency.Source34ConstructionUnit
