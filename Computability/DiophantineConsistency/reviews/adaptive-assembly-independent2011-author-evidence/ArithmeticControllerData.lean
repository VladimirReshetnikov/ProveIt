import DiophantineConsistency.ArithmeticStandardCasts
import DiophantineConsistency.ArithmeticControllerLift
import DiophantineConsistency.ArithmeticPackingBlocks
import Mathlib.Tactic.ReduceModChar

/-! **K5b — controller data at the actual constants** (construction spec §2,
§7 K3, §8), in every model of IΣ1.

Constants: `d = 94517` (block width, `B = 2^d`), the auxiliary prime
`p = 120199 = 2·60099+1`, `C0 = d·p`, and `g = B^(p-1) = 2^(d·120198)`.

* `g_eq` — `g = 1 + C0·v` with `v ≡ 5394 (mod p)` and `5394·66027 ≡ 1 (mod p)`:
  the single standard residue `g mod C0·p = 61280418874903`, checked in ℕ by
  modular exponentiation (`reduce_mod_char`) and transported through
  `Nat.cast` (the huge power is never evaluated).
* `zc P e = (g^e mod C0·P) / C0` — the discrete-log coordinate at level
  `P = p^m`; `zc_spec`, `zc_surj` (Hensel), `zc_inj`.
* `exp_pos_eq` — at a dummy position `2 + 120198·e`,
  `B^(2+120198 e) = B²·g^e`.
* `pt q` — the indicator of `j = q`; `bsum_pt`, `bsum_add_pt`: adding one
  dummy bit at block `q` adds exactly `B^q` to the block sum. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ArithmeticControllerData
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPow ArithmeticControllerLift ArithmeticPackingBlocks
attribute [local instance] Classical.propDecidable

/-! ## The standard residue of `g` -/

theorem g_mod_nat : 2 ^ (94517 * 120198) % (94517 * 120199 * 120199) = 61280418874903 := by
  have h : ((2 ^ (94517 * 120198) : ℕ) : ZMod 1365562674887717) = 61280418874903 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    change (2 : ZMod 1365562674887717) ^ 11360754366 = 61280418874903
    reduce_mod_char
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast] at hv
  rw [show 94517 * 120199 * 120199 = 1365562674887717 by norm_num, hv]
  rfl

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem cast_exp (n : ℕ) : Exp.exp (n : V) = ((2 ^ n : ℕ) : V) := by
  exact ArithmeticStandardCasts.cast_exp n

theorem cast_mod (a b : ℕ) : ((a % b : ℕ) : V) = (a : V) % (b : V) := by
  exact ArithmeticStandardCasts.cast_mod a b

/-- `g = B^(p-1) = 2^(94517·120198)`. -/
def gV : V := Exp.exp (94517 * 120198)

/-- The unit cofactor of `g - 1 = C0·v`. -/
def vV : V := 120199 * (gV / (94517 * 120199 * 120199)) + 5394

theorem g_mod : (gV : V) % (94517 * 120199 * 120199) = 61280418874903 := by
  have h := cast_mod (V := V) (2 ^ (94517 * 120198)) (94517 * 120199 * 120199)
  rw [g_mod_nat, ← cast_exp] at h
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h
  unfold gV
  rw [← h]

theorem g_eq : (gV : V) = 1 + 94517 * 120199 * vV := by
  have hd := div_add_mod (gV : V) (94517 * 120199 * 120199)
  rw [g_mod] at hd
  unfold vV
  calc (gV : V) = 94517 * 120199 * 120199 * (gV / (94517 * 120199 * 120199)) +
        61280418874903 := hd.symm
    _ = 94517 * 120199 * 120199 * (gV / (94517 * 120199 * 120199)) +
        (1 + 94517 * 120199 * 5394) := by norm_num
    _ = _ := by ring

theorem p_odd : (120199 : V) = 2 * 60099 + 1 := by norm_num

theorem p_pos : (0 : V) < 120199 := by norm_num

theorem v_inv : (vV * 66027 : V) % 120199 = 1 := by
  unfold vV
  rw [← mod_mul_mod_left _ _ p_pos, add_comm, mod_add_mul' _ _ p_pos,
    mod_mul_mod_left _ _ p_pos]
  have h := cast_mod (V := V) (5394 * 66027) 120199
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h
  rw [← h]
  norm_num

/-! ## Discrete-log coordinates at level `P = p^m` -/

theorem C0_gt : (1 : V) < 94517 * 120199 := by norm_num

theorem C0_pos : (0 : V) < 94517 * 120199 := lt_trans _root_.zero_lt_one C0_gt

private theorem coordinate_lt {P z : V} (hz : z < P) :
    1 + 94517 * 120199 * z < 94517 * 120199 * P := by
  calc 1 + 94517 * 120199 * z < 94517 * 120199 + 94517 * 120199 * z :=
        add_lt_add_of_lt_of_le C0_gt le_rfl
    _ = 94517 * 120199 * (z + 1) := by ring
    _ ≤ 94517 * 120199 * P :=
      mul_le_mul_of_nonneg_left (lt_iff_succ_le.mp hz) (Arithmetic.zero_le _)

/-- The coordinate `zc P e = (g^e mod C0·P) / C0`. -/
def zc (P e : V) : V := (power gV e % (94517 * 120199 * P)) / (94517 * 120199)

instance zc_definable (P : V) : 𝚺₁-Function₁ (zc P) := by unfold zc; definability

theorem power_gV (e : V) : ∃ t, power (gV : V) e = 1 + 94517 * 120199 * t := by
  rw [g_eq]; exact power_g e

/-- `g^e ≡ 1 + C0·zc(e) (mod C0·P)` with `zc(e) < P`. -/
theorem zc_spec {P : V} (hP : 0 < P) (e : V) :
    power (gV : V) e % (94517 * 120199 * P) = 1 + 94517 * 120199 * zc P e ∧ zc P e < P := by
  obtain ⟨t, ht⟩ := power_gV (V := V) e
  have hr : t % P < P := mod_lt t hP
  have hlt := coordinate_lt hr
  have hm : power (gV : V) e % (94517 * 120199 * P) = 1 + 94517 * 120199 * (t % P) := by
    rw [ht]
    have he : 1 + 94517 * 120199 * t =
        (1 + 94517 * 120199 * (t % P)) + 94517 * 120199 * P * (t / P) := by
      calc 1 + 94517 * 120199 * t = 1 + 94517 * 120199 * (P * (t / P) + t % P) := by
            rw [div_add_mod]
        _ = _ := by ring
    rw [he, mod_add_mul' _ _ (mul_pos C0_pos (lt_of_le_of_lt (Arithmetic.zero_le _) hr)),
      mod_eq_self_of_lt hlt]
  have hz : zc P e = t % P := by
    unfold zc
    rw [hm, add_comm]
    exact div_mul_add' _ _ C0_gt
  rw [hz]
  exact ⟨hm, hr⟩

theorem zc_surj (m z : V) (hz : z < power 120199 m) :
    ∃ e < power 120199 m, zc (power 120199 m) e = z := by
  have hP : (0 : V) < power 120199 m := power_pos _ m p_pos
  obtain ⟨e, he, Q, hQ⟩ := coordinates_surj (c := (94517 : V)) (v := vV) (vinv := 66027)
    p_odd v_inv m z hz
  refine ⟨e, he, ?_⟩
  have h1 := (zc_spec hP e).1
  rw [← g_eq] at hQ
  have hlt := coordinate_lt hz
  rw [hQ, show (94517 : V) * 120199 * power 120199 m * Q + 1 + 94517 * 120199 * z =
      (1 + 94517 * 120199 * z) + 94517 * 120199 * power 120199 m * Q by ring,
    mod_add_mul' _ _ (mul_pos C0_pos hP), mod_eq_self_of_lt hlt] at h1
  have h2 := add_left_cancel h1
  exact (mul_cancel_left C0_pos h2).symm

theorem zc_inj (m e e' : V) (he : e < power 120199 m) (he' : e' < power 120199 m)
    (h : zc (power 120199 m) e = zc (power 120199 m) e') : e = e' := by
  have hP : (0 : V) < power 120199 m := power_pos _ m p_pos
  have h1 := (zc_spec hP e).1
  have h2 := (zc_spec hP e').1
  have hinj := coordinates_inj (c := (94517 : V)) (v := vV) (vinv := 66027)
    p_odd (by norm_num) v_inv m e he e' he'
  rw [← g_eq] at hinj
  exact hinj (by rw [h1, h2, h])

/-! ## Dummy positions -/

/-- The dummy position of coordinate index `e`. -/
def pos (e : V) : V := 2 + 120198 * e

theorem exp_pos_eq (e : V) :
    Exp.exp (94517 * pos e) = Exp.exp (94517 * 2) * power (gV : V) e := by
  have h : Exp.exp ((94517 : V) * (120198 * e)) = power (Exp.exp (94517 * 120198)) e := by
    rw [← power_two, ← power_two, power_iterate, mul_assoc]
  unfold pos gV
  rw [mul_add, exp_add, h]

/-! ## One dummy bit in a block sum -/

theorem fun1_of_rel {f : V → V} {R : V → V → Prop}
    (hR : 𝚺₁.Definable (fun v : Fin 2 → V => R (v 0) (v 1)))
    (h : ∀ y a, R y a ↔ y = f a) : 𝚺₁-Function₁ f :=
  hR.of_iff fun v => (h (v 0) (v 1)).symm

/-- The indicator of block `q`. -/
def pt (q j : V) : V := if j = q then 1 else 0

instance pt_definable (q : V) : 𝚺₁-Function₁ (pt q) :=
  fun1_of_rel (R := fun y j => (j = q ∧ y = 1) ∨ (j ≠ q ∧ y = 0)) (by definability)
    (fun y j => by by_cases h : j = q <;> simp [pt, h])

theorem pt_le (q j : V) : pt q j ≤ 1 := by unfold pt; split <;> simp

theorem one_lt_exp {w : V} (hw : 0 < w) : (1 : V) < Exp.exp w := by
  have h := exp_succ (w - 1)
  rw [tsub_add_cancel_of_le (pos_iff_one_le.mp hw)] at h
  rw [h]
  calc (1 : V) < 2 := by norm_num
    _ ≤ 2 * Exp.exp (w - 1) := le_mul_of_one_le_right (by norm_num) (one_le_exp _)

theorem bsum_pt {w : V} (hw : 0 < w) (q : V) :
    ∀ n, (q < n ∧ bsum w (pt q) n = Exp.exp (w * q)) ∨ (n ≤ q ∧ bsum w (pt q) n = 0) := by
  have hb : ∀ j, pt q j < Exp.exp w := fun j => lt_of_le_of_lt (pt_le q j) (one_lt_exp hw)
  haveI := bsum_definable w (pt q) hb
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact Or.inr ⟨Arithmetic.zero_le _, by simp⟩
  case succ n ih =>
    rw [bsum_succ (fun j _ => hb j)]
    rcases ih with ⟨hq, hs⟩ | ⟨hq, hs⟩
    · have hne : n ≠ q := ne_of_gt hq
      exact Or.inl ⟨lt_trans hq (lt_add_one n), by simp [hs, pt, hne]⟩
    · rcases lt_or_eq_of_le hq with hlt | rfl
      · have hne : n ≠ q := ne_of_lt hlt
        exact Or.inr ⟨lt_iff_succ_le.mp hlt, by simp [hs, pt, hne]⟩
      · exact Or.inl ⟨lt_add_one n, by simp [hs, pt]⟩

/-- Adding one dummy bit at an empty block `q < n` adds `B^q`. -/
theorem bsum_add_pt {w : V} (hw : 0 < w) {f f' : V → V} [𝚺₁-Function₁ f] [𝚺₁-Function₁ f']
    {n q : V} (hq : q < n) (hf : ∀ j < n, f j ≤ 1) (hfq : f q = 0)
    (hf' : ∀ j < n, f' j = f j + pt q j) :
    bsum w f' n = bsum w f n + Exp.exp (w * q) := by
  have hsum : ∀ j < n, f j + pt q j < Exp.exp w := by
    intro j hj
    by_cases hjq : j = q
    · rw [hjq, hfq, zero_add]; exact lt_of_le_of_lt (pt_le q q) (one_lt_exp hw)
    · simp only [pt, hjq, if_false, add_zero]; exact lt_of_le_of_lt (hf j hj) (one_lt_exp hw)
  rw [bsum_add hsum hf']
  rcases bsum_pt hw q n with ⟨_, h⟩ | ⟨h, _⟩
  · rw [h]
  · exact absurd hq (not_lt.mpr h)

end DiophantineConsistency.ArithmeticControllerData
