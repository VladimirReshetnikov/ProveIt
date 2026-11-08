import DiophantineConsistency.ArithmeticControllerData
import DiophantineConsistency.ArithmeticControllerLift
import DiophantineConsistency.ArithmeticPackingBlocks
import Mathlib.Tactic.ReduceModChar

/-! # Controller data at the block-mask2963 constants

The block-mask2963 counterpart of `ArithmeticControllerData`
(`research/low-padding-independent/PROOF.md` §11), transcribed by exact
constant substitution; the argument is unchanged. In every model of IΣ1.

Constants: `d = 47·2963 = 139261` (block width, `B = 2^d`), the auxiliary
prime `p = λ = 1362521 = 2·681260+1` of the block-mask2963 controller, `C0 = d·p = 189746036981`, and
`g = B^(p-1) = 2^(d·1362520)`.

* `g_eq` — `g = 1 + C0·v` with `v ≡ 667106 (mod p)` and `667106·919674 ≡ 1 (mod p)`:
  the single standard residue `g mod C0·p = 126580719746246987`, checked in ℕ by
  modular exponentiation (`reduce_mod_char`) and transported through
  `Nat.cast` (the huge power is never evaluated).
* `zc P e = (g^e mod C0·P) / C0` — the discrete-log coordinate at level
  `P = p^m`; `zc_spec`, `zc_surj` (Hensel), `zc_inj`.
* `exp_pos_eq` — at a dummy position `2 + 1362520·e`,
  `B^(2+1362520 e) = B²·g^e`.

`B` is not primitive modulo `λ` (its order is 681260); only `g ≡ 1 (mod C0)` and
the unit cofactor `v` are used. The constant-free one-bit block-sum lemmas
(`pt`, `bsum_add_pt`, `one_lt_exp`) are reused from `ArithmeticControllerData`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace Bm2963ControllerData
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPow ArithmeticControllerLift ArithmeticPackingBlocks
open ArithmeticControllerData (cast_exp cast_mod)
attribute [local instance] Classical.propDecidable

/-! ## The standard residue of `g` -/

theorem g_mod_nat : 2 ^ (139261 * 1362520) % (139261 * 1362521 * 1362521) = 126580719746246987 := by
  have h : ((2 ^ (139261 * 1362520) : ℕ) : ZMod 258532960053389101) = 126580719746246987 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    change (2 : ZMod 258532960053389101) ^ 189745897720 = 126580719746246987
    reduce_mod_char
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast] at hv
  rw [show 139261 * 1362521 * 1362521 = 258532960053389101 by norm_num, hv]
  rfl

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `g = B^(p-1) = 2^(139261·1362520)`. -/
def gV : V := Exp.exp (139261 * 1362520)

/-- The unit cofactor of `g - 1 = C0·v`. -/
def vV : V := 1362521 * (gV / (139261 * 1362521 * 1362521)) + 667106

theorem g_mod : (gV : V) % (139261 * 1362521 * 1362521) = 126580719746246987 := by
  have h := cast_mod (V := V) (2 ^ (139261 * 1362520)) (139261 * 1362521 * 1362521)
  rw [g_mod_nat, ← cast_exp] at h
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h
  unfold gV
  rw [← h]

theorem g_eq : (gV : V) = 1 + 139261 * 1362521 * vV := by
  have hd := div_add_mod (gV : V) (139261 * 1362521 * 1362521)
  rw [g_mod] at hd
  unfold vV
  calc (gV : V) = 139261 * 1362521 * 1362521 * (gV / (139261 * 1362521 * 1362521)) +
        126580719746246987 := hd.symm
    _ = 139261 * 1362521 * 1362521 * (gV / (139261 * 1362521 * 1362521)) +
        (1 + 139261 * 1362521 * 667106) := by norm_num
    _ = _ := by ring

theorem p_odd : (1362521 : V) = 2 * 681260 + 1 := by norm_num

theorem p_pos : (0 : V) < 1362521 := by norm_num

theorem v_inv : (vV * 919674 : V) % 1362521 = 1 := by
  unfold vV
  rw [← mod_mul_mod_left _ _ p_pos, add_comm, mod_add_mul' _ _ p_pos,
    mod_mul_mod_left _ _ p_pos]
  have h := cast_mod (V := V) (667106 * 919674) 1362521
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h
  rw [← h]
  norm_num

/-! ## Discrete-log coordinates at level `P = p^m` -/

theorem C0_gt : (1 : V) < 139261 * 1362521 := by norm_num

theorem C0_pos : (0 : V) < 139261 * 1362521 := lt_trans _root_.zero_lt_one C0_gt

private theorem coordinate_lt {P z : V} (hz : z < P) :
    1 + 139261 * 1362521 * z < 139261 * 1362521 * P := by
  calc 1 + 139261 * 1362521 * z < 139261 * 1362521 + 139261 * 1362521 * z :=
        add_lt_add_of_lt_of_le C0_gt le_rfl
    _ = 139261 * 1362521 * (z + 1) := by ring
    _ ≤ 139261 * 1362521 * P :=
      mul_le_mul_of_nonneg_left (lt_iff_succ_le.mp hz) (Arithmetic.zero_le _)

/-- The coordinate `zc P e = (g^e mod C0·P) / C0`. -/
def zc (P e : V) : V := (power gV e % (139261 * 1362521 * P)) / (139261 * 1362521)

instance zc_definable (P : V) : 𝚺₁-Function₁ (zc P) := by unfold zc; definability

theorem power_gV (e : V) : ∃ t, power (gV : V) e = 1 + 139261 * 1362521 * t := by
  rw [g_eq]; exact power_g e

/-- `g^e ≡ 1 + C0·zc(e) (mod C0·P)` with `zc(e) < P`. -/
theorem zc_spec {P : V} (hP : 0 < P) (e : V) :
    power (gV : V) e % (139261 * 1362521 * P) = 1 + 139261 * 1362521 * zc P e ∧ zc P e < P := by
  obtain ⟨t, ht⟩ := power_gV (V := V) e
  have hr : t % P < P := mod_lt t hP
  have hlt := coordinate_lt hr
  have hm : power (gV : V) e % (139261 * 1362521 * P) = 1 + 139261 * 1362521 * (t % P) := by
    rw [ht]
    have he : 1 + 139261 * 1362521 * t =
        (1 + 139261 * 1362521 * (t % P)) + 139261 * 1362521 * P * (t / P) := by
      calc 1 + 139261 * 1362521 * t = 1 + 139261 * 1362521 * (P * (t / P) + t % P) := by
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

theorem zc_surj (m z : V) (hz : z < power 1362521 m) :
    ∃ e < power 1362521 m, zc (power 1362521 m) e = z := by
  have hP : (0 : V) < power 1362521 m := power_pos _ m p_pos
  obtain ⟨e, he, Q, hQ⟩ := coordinates_surj (c := (139261 : V)) (v := vV) (vinv := 919674)
    p_odd v_inv m z hz
  refine ⟨e, he, ?_⟩
  have h1 := (zc_spec hP e).1
  rw [← g_eq] at hQ
  have hlt := coordinate_lt hz
  rw [hQ, show (139261 : V) * 1362521 * power 1362521 m * Q + 1 + 139261 * 1362521 * z =
      (1 + 139261 * 1362521 * z) + 139261 * 1362521 * power 1362521 m * Q by ring,
    mod_add_mul' _ _ (mul_pos C0_pos hP), mod_eq_self_of_lt hlt] at h1
  have h2 := add_left_cancel h1
  exact (mul_cancel_left C0_pos h2).symm

theorem zc_inj (m e e' : V) (he : e < power 1362521 m) (he' : e' < power 1362521 m)
    (h : zc (power 1362521 m) e = zc (power 1362521 m) e') : e = e' := by
  have hP : (0 : V) < power 1362521 m := power_pos _ m p_pos
  have h1 := (zc_spec hP e).1
  have h2 := (zc_spec hP e').1
  have hinj := coordinates_inj (c := (139261 : V)) (v := vV) (vinv := 919674)
    p_odd (by norm_num) v_inv m e he e' he'
  rw [← g_eq] at hinj
  exact hinj (by rw [h1, h2, h])

/-! ## Dummy positions -/

/-- The dummy position of coordinate index `e`. -/
def pos (e : V) : V := 2 + 1362520 * e

theorem exp_pos_eq (e : V) :
    Exp.exp (139261 * pos e) = Exp.exp (139261 * 2) * power (gV : V) e := by
  have h : Exp.exp ((139261 : V) * (1362520 * e)) = power (Exp.exp (139261 * 1362520)) e := by
    rw [← power_two, ← power_two, power_iterate, mul_assoc]
  unfold pos gV
  rw [mul_add, exp_add, h]

end Bm2963ControllerData

#print axioms Bm2963ControllerData.g_eq
#print axioms Bm2963ControllerData.v_inv
#print axioms Bm2963ControllerData.zc_surj
#print axioms Bm2963ControllerData.zc_inj
#print axioms Bm2963ControllerData.exp_pos_eq
