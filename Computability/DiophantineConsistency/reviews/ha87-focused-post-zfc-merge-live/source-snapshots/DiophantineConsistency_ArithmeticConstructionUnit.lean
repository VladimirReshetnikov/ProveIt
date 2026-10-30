import DiophantineConsistency.ArithmeticControllerData
import DiophantineConsistency.ArithmeticConstructionKernel

/-! **K7b — the rank-variation factor `Γ` is a unit modulo `d·N`** (construction
spec §7 K2), in every model of IΣ1.

`Γ = ρ^977·(q² − 1)·(1 + q·(K + B^s))` with `ρ = 2^47`, `B = 2^d`, `d = 94517`,
`q = 2^(d·N)`, `N = p^(m+1)`, `s = p^e`, `p = 120199`. All residues are taken
modulo the single standard number `L = 47·2011·p = d·p = 11360848883`:

* `B^p ≡ B (mod L)` (one modular exponentiation), hence `B^(p^n) ≡ B` by Σ1
  induction, so `q ≡ B^s ≡ B`;
* `K ≡ 1491904576 (mod L)` (`ArithmeticConstructionKernel.K_cast_common`);
* so `Γ ≡ 706142772 (mod L)` and `706142772^600990 ≡ 1 (mod L)`
  (`600990 = lcm(46, 2010, 120198)`);
* `Γ^600990 = 1 + d·p·v`, and lifting the exponent
  (`ArithmeticControllerLift.lte`) gives `Γ^(600990·p^m) ≡ 1 (mod d·p^(m+1))`.

No Chinese remainder argument or Bezout inverse is needed: the inverse is the
explicit power `Γ^(600990·p^m − 1)`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ArithmeticConstructionUnit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPow ArithmeticControllerLift ArithmeticControllerData
attribute [local irreducible] CurrentKernel2011.K

/-! ## Standard residues modulo `L = 11360848883` -/

theorem nat_mod_of_zmod {m : ℕ} [NeZero m] (a b : ℕ) (h : (a : ZMod m) = b) (hb : b < m) :
    a % m = b := by
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hb] using congrArg ZMod.val h

theorem B_nat : 2 ^ 94517 % 11360848883 = 10287028452 := by
  apply nat_mod_of_zmod _ _ _ (by norm_num)
  rw [Nat.cast_pow, Nat.cast_ofNat]
  reduce_mod_char

theorem rho_nat : 2 ^ (47 * 977) % 11360848883 = 9930929229 := by
  apply nat_mod_of_zmod _ _ _ (by norm_num)
  rw [Nat.cast_pow, Nat.cast_ofNat]
  change (2 : ZMod 11360848883) ^ 45919 = 9930929229
  reduce_mod_char

theorem frob_nat : 10287028452 ^ 120199 % 11360848883 = 10287028452 := by
  apply nat_mod_of_zmod _ _ _ (by norm_num)
  rw [Nat.cast_pow, Nat.cast_ofNat]
  reduce_mod_char

theorem gamma_order_nat : 706142772 ^ 600990 % 11360848883 = 1 := by
  apply nat_mod_of_zmod _ _ _ (by norm_num)
  rw [Nat.cast_pow, Nat.cast_ofNat]
  reduce_mod_char

theorem K_nat : CurrentKernel2011.K % 11360848883 = 1491904576 :=
  nat_mod_of_zmod _ _ ArithmeticConstructionKernel.K_cast_common (by norm_num)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem L_pos : (0 : V) < 11360848883 := by norm_num

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
theorem mul_res {a b : V} {x y : ℕ} (ha : a % 11360848883 = (x : V))
    (hb : b % 11360848883 = (y : V)) :
    (a * b) % 11360848883 = ((x * y % 11360848883 : ℕ) : V) := by
  rw [mod_mul L_pos, ha, hb, ← Nat.cast_mul,
    show (11360848883 : V) = ((11360848883 : ℕ) : V) by simp, ← cast_mod]

theorem add_res {a b : V} {x y : ℕ} (ha : a % 11360848883 = (x : V))
    (hb : b % 11360848883 = (y : V)) :
    (a + b) % 11360848883 = ((x + y) % 11360848883 : ℕ) := by
  rw [mod_add L_pos, ha, hb, ← Nat.cast_add,
    show (11360848883 : V) = ((11360848883 : ℕ) : V) by simp, ← cast_mod]

theorem sub_one_res {a : V} {x : ℕ} (hx : 1 ≤ x) (hxL : x < 11360848883)
    (ha : a % 11360848883 = (x : V)) : (a - 1) % 11360848883 = ((x - 1 : ℕ) : V) := by
  have hd := div_add_mod a 11360848883
  rw [ha] at hd
  have hx1 : (1 : V) ≤ (x : V) := by exact_mod_cast hx
  have hsub : ((x - 1 : ℕ) : V) = (x : V) - 1 := by
    have h1 : ((x - 1 : ℕ) : V) + 1 = (x : V) := by
      exact_mod_cast Nat.sub_add_cancel hx
    exact eq_tsub_of_add_eq h1
  rw [← hd, add_tsub_assoc_of_le hx1, ← hsub, mod_mul_add' _ _ L_pos,
    mod_eq_self_of_lt (by exact_mod_cast (lt_of_le_of_lt (Nat.sub_le x 1) hxL))]

theorem one_res : (1 : V) % 11360848883 = ((1 : ℕ) : V) := by
  rw [Nat.cast_one]; exact mod_eq_self_of_lt (by norm_num)

/-! ## `B = 2^d` modulo `L`, and its Frobenius fixed point -/

theorem exp_eq_power (x : V) : Exp.exp (94517 * x) = power (Exp.exp 94517) x := by
  rw [← power_two, ← power_two, power_iterate]

theorem B_res : Exp.exp (94517 : V) % 11360848883 = ((10287028452 : ℕ) : V) := by
  have h := cast_exp (V := V) 94517
  rw [Nat.cast_ofNat] at h
  rw [h, show (11360848883 : V) = ((11360848883 : ℕ) : V) by simp, cast_mod_eq B_nat]

theorem B_frob : power (Exp.exp (94517 : V)) 120199 % 11360848883 =
    Exp.exp (94517 : V) % 11360848883 := by
  have h1 := pow_cong L_pos (Exp.exp (94517 : V)) ((10287028452 : ℕ) : V)
    (by rw [B_res, mod_eq_self_of_lt (by norm_num)]) 120199
  rw [h1, B_res, show (120199 : V) = ((120199 : ℕ) : V) by simp, power_natCast, ← Nat.cast_pow,
    show (11360848883 : V) = ((11360848883 : ℕ) : V) by simp, cast_mod_eq frob_nat]

theorem B_frob_iter : ∀ n, power (Exp.exp (94517 : V)) (power 120199 n) % 11360848883 =
    Exp.exp (94517 : V) % 11360848883 := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    rw [power_succ, ← power_iterate]
    rw [pow_cong L_pos _ _ B_frob, ih]

theorem exp_p_res (n : V) :
    Exp.exp (94517 * power 120199 n) % 11360848883 = ((10287028452 : ℕ) : V) := by
  rw [exp_eq_power, B_frob_iter, B_res]

/-! ## The unit -/

/-- `Γ = ρ^977 (q² − 1)(1 + q(K + B^s))`. -/
def Gamma (N s : V) : V :=
  Exp.exp (47 * 977) * (Exp.exp (94517 * N) ^ 2 - 1) *
    (1 + Exp.exp (94517 * N) * ((CurrentKernel2011.K : V) + Exp.exp (94517 * s)))

theorem rho_res : Exp.exp (47 * 977 : V) % 11360848883 = ((9930929229 : ℕ) : V) := by
  have h := cast_exp (V := V) (47 * 977)
  rw [show ((47 * 977 : ℕ) : V) = 47 * 977 by push_cast; ring] at h
  rw [h, show (11360848883 : V) = ((11360848883 : ℕ) : V) by simp, cast_mod_eq rho_nat]

theorem K_res : (CurrentKernel2011.K : V) % 11360848883 = ((1491904576 : ℕ) : V) := by
  rw [show (11360848883 : V) = ((11360848883 : ℕ) : V) by simp, cast_mod_eq K_nat]

theorem Gamma_res (m e : V) :
    Gamma (power 120199 (m + 1)) (power 120199 e) % 11360848883 = ((706142772 : ℕ) : V) := by
  have hq := exp_p_res (V := V) (m + 1)
  have hs := exp_p_res (V := V) e
  have hq2 : (Exp.exp (94517 * power (120199 : V) (m + 1)) ^ 2) % 11360848883 =
      ((11247600509 : ℕ) : V) := by
    rw [pow_two, mul_res hq hq]
  have hq21 := sub_one_res (by norm_num) (by norm_num) hq2
  have hKs := add_res K_res hs
  have hqK := mul_res hq hKs
  have h1 := add_res one_res hqK
  have hr := mul_res (mul_res rho_res hq21) h1
  exact hr

/-- **Γ is a unit modulo `d·N`**, with an explicit inverse. -/
theorem gamma_unit (m e : V) :
    ∃ Γi, (Gamma (power 120199 (m + 1)) (power 120199 e) * Γi) %
        (94517 * power 120199 (m + 1)) = 1 % (94517 * power 120199 (m + 1)) := by
  set G := Gamma (power (120199 : V) (m + 1)) (power 120199 e) with hG
  have hGr := Gamma_res (V := V) m e
  rw [← hG] at hGr
  -- G^λ ≡ 1 (mod L)
  have hpow : power G 600990 % 11360848883 = 1 := by
    rw [pow_cong L_pos G ((706142772 : ℕ) : V) (by rw [hGr, mod_eq_self_of_lt (by norm_num)]),
      show (600990 : V) = ((600990 : ℕ) : V) by simp, power_natCast, ← Nat.cast_pow,
      show (11360848883 : V) = ((11360848883 : ℕ) : V) by simp, cast_mod_eq gamma_order_nat]
    simp
  obtain ⟨v1, hd⟩ : ∃ v1, power G 600990 = 1 + 94517 * 120199 * v1 :=
    ⟨_, by simpa only [show (94517 : V) * 120199 = 11360848883 by norm_num, hpow, add_comm]
      using (div_add_mod (power G 600990) (94517 * 120199)).symm⟩
  obtain ⟨w, _, hw⟩ := lte (c := (94517 : V)) (v := v1) p_odd m
  refine ⟨power G (600990 * power 120199 m - 1), ?_⟩
  have hpos : 1 ≤ 600990 * power (120199 : V) m :=
    one_le_mul (by norm_num) (pos_iff_one_le.mp (power_pos _ _ p_pos))
  have hmul : G * power G (600990 * power 120199 m - 1) = power G (600990 * power 120199 m) := by
    conv_rhs => rw [← tsub_add_cancel_of_le hpos]
    rw [power_succ]
  rw [hmul, ← power_iterate, hd, hw, power_succ,
    show (94517 : V) * (120199 * power 120199 m) = 94517 * 120199 * power 120199 m by ring,
    mod_add_mul' _ _ (mul_pos C0_pos (power_pos _ _ p_pos))]

end DiophantineConsistency.ArithmeticConstructionUnit
