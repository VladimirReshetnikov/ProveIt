import DiophantineConsistency.Bm2963.Bm2963ControllerData
import DiophantineConsistency.Bm2963.Bm2963KernelResidue

/-! **The rank-variation factor `Γ` is a unit modulo `d·N`** at the
block-mask2963 constants (`PROOF.md` (4) and §11), in every model of IΣ1:
`ArithmeticConstructionUnit` transcribed with the block-mask2963 residues.

`Γ = ρ^977·(q² − 1)·(1 + q·(K + B^s))` with `ρ = 2^47`, `B = 2^d`, `d = 139261`,
`q = 2^(d·N)`, `N = p^(m+1)`, `s = p^e`, `p = λ = 1362521`. All residues are
taken modulo the single standard number `C0 = 47·2963·λ = d·λ = 189746036981`:

* `B^λ ≡ B (mod C0)` (one modular exponentiation), hence `B^(λ^n) ≡ B` by Σ1
  induction, so `q ≡ B^s ≡ B`;
* `K ≡ 25047958135 (mod C0)` (`Bm2963KernelResidue.K_mod`);
* so `Γ ≡ 109671521435 (mod C0)` and `109671521435^1362520 ≡ 1 (mod C0)`
  (`ord_C0 Γ = lcm(46, 2962, 1362520) = 1362520 = λ − 1`, so here the unit
  exponent is `λ − 1` itself; admissible942 needed the lcm exponent 740784);
* `Γ^1362520 = 1 + d·λ·v`, and lifting the exponent
  (`ArithmeticControllerLift.lte`) gives `Γ^(1362520·λ^m) ≡ 1 (mod d·λ^(m+1))`.

The inverse is the explicit power `Γ^(1362520·λ^m − 1)`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace Bm2963ConstructionUnit
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPow ArithmeticControllerLift Bm2963ControllerData
open ArithmeticControllerData (cast_exp cast_mod)
attribute [local irreducible] Bm2963Kernel.K

/-! ## Standard residues modulo `L = 189746036981` -/

theorem nat_mod_of_zmod {m : ℕ} [NeZero m] (a b : ℕ) (h : (a : ZMod m) = b) (hb : b < m) :
    a % m = b := by
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hb] using congrArg ZMod.val h

theorem B_nat : 2 ^ 139261 % 189746036981 = 112210659107 := by
  apply nat_mod_of_zmod _ _ _ (by norm_num)
  rw [Nat.cast_pow, Nat.cast_ofNat]
  reduce_mod_char

theorem rho_nat : 2 ^ (47 * 977) % 189746036981 = 64935804024 := by
  apply nat_mod_of_zmod _ _ _ (by norm_num)
  rw [Nat.cast_pow, Nat.cast_ofNat]
  change (2 : ZMod 189746036981) ^ 45919 = 64935804024
  reduce_mod_char

theorem frob_nat : 112210659107 ^ 1362521 % 189746036981 = 112210659107 := by
  apply nat_mod_of_zmod _ _ _ (by norm_num)
  rw [Nat.cast_pow, Nat.cast_ofNat]
  reduce_mod_char

theorem gamma_order_nat : 109671521435 ^ 1362520 % 189746036981 = 1 := by
  apply nat_mod_of_zmod _ _ _ (by norm_num)
  rw [Nat.cast_pow, Nat.cast_ofNat]
  reduce_mod_char

theorem K_nat : Bm2963Kernel.K % 189746036981 = 25047958135 :=
  Bm2963KernelResidue.K_mod

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem L_pos : (0 : V) < 189746036981 := by norm_num

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
theorem mul_res {a b : V} {x y : ℕ} (ha : a % 189746036981 = (x : V))
    (hb : b % 189746036981 = (y : V)) :
    (a * b) % 189746036981 = ((x * y % 189746036981 : ℕ) : V) := by
  rw [mod_mul L_pos, ha, hb, ← Nat.cast_mul,
    show (189746036981 : V) = ((189746036981 : ℕ) : V) by simp, ← cast_mod]

theorem add_res {a b : V} {x y : ℕ} (ha : a % 189746036981 = (x : V))
    (hb : b % 189746036981 = (y : V)) :
    (a + b) % 189746036981 = ((x + y) % 189746036981 : ℕ) := by
  rw [mod_add L_pos, ha, hb, ← Nat.cast_add,
    show (189746036981 : V) = ((189746036981 : ℕ) : V) by simp, ← cast_mod]

theorem sub_one_res {a : V} {x : ℕ} (hx : 1 ≤ x) (hxL : x < 189746036981)
    (ha : a % 189746036981 = (x : V)) : (a - 1) % 189746036981 = ((x - 1 : ℕ) : V) := by
  have hd := div_add_mod a 189746036981
  rw [ha] at hd
  have hx1 : (1 : V) ≤ (x : V) := by exact_mod_cast hx
  have hsub : ((x - 1 : ℕ) : V) = (x : V) - 1 := by
    have h1 : ((x - 1 : ℕ) : V) + 1 = (x : V) := by
      exact_mod_cast Nat.sub_add_cancel hx
    exact eq_tsub_of_add_eq h1
  rw [← hd, add_tsub_assoc_of_le hx1, ← hsub, mod_mul_add' _ _ L_pos,
    mod_eq_self_of_lt (by exact_mod_cast (lt_of_le_of_lt (Nat.sub_le x 1) hxL))]

theorem one_res : (1 : V) % 189746036981 = ((1 : ℕ) : V) := by
  rw [Nat.cast_one]; exact mod_eq_self_of_lt (by norm_num)

/-! ## `B = 2^d` modulo `L`, and its Frobenius fixed point -/

theorem exp_eq_power (x : V) : Exp.exp (139261 * x) = power (Exp.exp 139261) x := by
  rw [← power_two, ← power_two, power_iterate]

theorem B_res : Exp.exp (139261 : V) % 189746036981 = ((112210659107 : ℕ) : V) := by
  have h := cast_exp (V := V) 139261
  rw [Nat.cast_ofNat] at h
  rw [h, show (189746036981 : V) = ((189746036981 : ℕ) : V) by simp, cast_mod_eq B_nat]

theorem B_frob : power (Exp.exp (139261 : V)) 1362521 % 189746036981 =
    Exp.exp (139261 : V) % 189746036981 := by
  have h1 := pow_cong L_pos (Exp.exp (139261 : V)) ((112210659107 : ℕ) : V)
    (by rw [B_res, mod_eq_self_of_lt (by norm_num)]) 1362521
  rw [h1, B_res, show (1362521 : V) = ((1362521 : ℕ) : V) by simp, power_natCast, ← Nat.cast_pow,
    show (189746036981 : V) = ((189746036981 : ℕ) : V) by simp, cast_mod_eq frob_nat]

theorem B_frob_iter : ∀ n, power (Exp.exp (139261 : V)) (power 1362521 n) % 189746036981 =
    Exp.exp (139261 : V) % 189746036981 := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    rw [power_succ, ← power_iterate]
    rw [pow_cong L_pos _ _ B_frob, ih]

theorem exp_p_res (n : V) :
    Exp.exp (139261 * power 1362521 n) % 189746036981 = ((112210659107 : ℕ) : V) := by
  rw [exp_eq_power, B_frob_iter, B_res]

/-! ## The unit -/

/-- `Γ = ρ^977 (q² − 1)(1 + q(K + B^s))`. -/
def Gamma (N s : V) : V :=
  Exp.exp (47 * 977) * (Exp.exp (139261 * N) ^ 2 - 1) *
    (1 + Exp.exp (139261 * N) * ((Bm2963Kernel.K : V) + Exp.exp (139261 * s)))

theorem rho_res : Exp.exp (47 * 977 : V) % 189746036981 = ((64935804024 : ℕ) : V) := by
  have h := cast_exp (V := V) (47 * 977)
  rw [show ((47 * 977 : ℕ) : V) = 47 * 977 by push_cast; ring] at h
  rw [h, show (189746036981 : V) = ((189746036981 : ℕ) : V) by simp, cast_mod_eq rho_nat]

theorem K_res : (Bm2963Kernel.K : V) % 189746036981 = ((25047958135 : ℕ) : V) := by
  rw [show (189746036981 : V) = ((189746036981 : ℕ) : V) by simp, cast_mod_eq K_nat]

theorem Gamma_res (m e : V) :
    Gamma (power 1362521 (m + 1)) (power 1362521 e) % 189746036981 = ((109671521435 : ℕ) : V) := by
  have hq := exp_p_res (V := V) (m + 1)
  have hs := exp_p_res (V := V) e
  have hq2 : (Exp.exp (139261 * power (1362521 : V) (m + 1)) ^ 2) % 189746036981 =
      ((184702121587 : ℕ) : V) := by
    rw [pow_two, mul_res hq hq]
  have hq21 := sub_one_res (by norm_num) (by norm_num) hq2
  have hKs := add_res K_res hs
  have hqK := mul_res hq hKs
  have h1 := add_res one_res hqK
  have hr := mul_res (mul_res rho_res hq21) h1
  exact hr

/-- **Γ is a unit modulo `d·N`**, with an explicit inverse. -/
theorem gamma_unit (m e : V) :
    ∃ Γi, (Gamma (power 1362521 (m + 1)) (power 1362521 e) * Γi) %
        (139261 * power 1362521 (m + 1)) = 1 % (139261 * power 1362521 (m + 1)) := by
  set G := Gamma (power (1362521 : V) (m + 1)) (power 1362521 e) with hG
  have hGr := Gamma_res (V := V) m e
  rw [← hG] at hGr
  -- G^λ ≡ 1 (mod L)
  have hpow : power G 1362520 % 189746036981 = 1 := by
    rw [pow_cong L_pos G ((109671521435 : ℕ) : V) (by rw [hGr, mod_eq_self_of_lt (by norm_num)]),
      show (1362520 : V) = ((1362520 : ℕ) : V) by simp, power_natCast, ← Nat.cast_pow,
      show (189746036981 : V) = ((189746036981 : ℕ) : V) by simp, cast_mod_eq gamma_order_nat]
    simp
  obtain ⟨v1, hd⟩ : ∃ v1, power G 1362520 = 1 + 139261 * 1362521 * v1 :=
    ⟨_, by simpa only [show (139261 : V) * 1362521 = 189746036981 by norm_num, hpow, add_comm]
      using (div_add_mod (power G 1362520) (139261 * 1362521)).symm⟩
  obtain ⟨w, _, hw⟩ := lte (c := (139261 : V)) (v := v1) p_odd m
  refine ⟨power G (1362520 * power 1362521 m - 1), ?_⟩
  have hpos : 1 ≤ 1362520 * power (1362521 : V) m :=
    one_le_mul (by norm_num) (pos_iff_one_le.mp (power_pos _ _ p_pos))
  have hmul : G * power G (1362520 * power 1362521 m - 1) = power G (1362520 * power 1362521 m) := by
    conv_rhs => rw [← tsub_add_cancel_of_le hpos]
    rw [power_succ]
  rw [hmul, ← power_iterate, hd, hw, power_succ,
    show (139261 : V) * (1362521 * power 1362521 m) = 139261 * 1362521 * power 1362521 m by ring,
    mod_add_mul' _ _ (mul_pos C0_pos (power_pos _ _ p_pos))]

end Bm2963ConstructionUnit

#print axioms Bm2963ConstructionUnit.Gamma_res
#print axioms Bm2963ConstructionUnit.gamma_unit
