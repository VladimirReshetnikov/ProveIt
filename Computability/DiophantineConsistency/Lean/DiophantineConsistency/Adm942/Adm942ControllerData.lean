import DiophantineConsistency.ArithmeticControllerData
import DiophantineConsistency.ArithmeticControllerLift
import DiophantineConsistency.ArithmeticPackingBlocks
import Mathlib.Tactic.ReduceModChar

/-! # Controller data at the admissible942 constants

The admissible942 counterpart of `ArithmeticControllerData`
(`research/admissible942-independent/PROOF.md` §11), transcribed by exact
constant substitution; the argument is unchanged. In every model of IΣ1.

Constants: `d = 47·4027 = 189269` (block width, `B = 2^d`), the auxiliary
prime `p = λ = 246929 = 2·123464+1` of Pca942, `C0 = d·p = 46736004901`, and
`g = B^(p-1) = 2^(d·246928)`.

* `g_eq` — `g = 1 + C0·v` with `v ≡ 154321 (mod p)` and `154321·96206 ≡ 1 (mod p)`:
  the single standard residue `g mod C0·p = 7212347012327222`, checked in ℕ by
  modular exponentiation (`reduce_mod_char`) and transported through
  `Nat.cast` (the huge power is never evaluated).
* `zc P e = (g^e mod C0·P) / C0` — the discrete-log coordinate at level
  `P = p^m`; `zc_spec`, `zc_surj` (Hensel), `zc_inj`.
* `exp_pos_eq` — at a dummy position `2 + 246928·e`,
  `B^(2+246928 e) = B²·g^e`.

`B` is not primitive modulo `λ` (its order is 15433); only `g ≡ 1 (mod C0)` and
the unit cofactor `v` are used. The constant-free one-bit block-sum lemmas
(`pt`, `bsum_add_pt`, `one_lt_exp`) are reused from `ArithmeticControllerData`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace Adm942ControllerData
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPow ArithmeticControllerLift ArithmeticPackingBlocks
open ArithmeticControllerData (cast_exp cast_mod)
attribute [local instance] Classical.propDecidable

/-! ## The standard residue of `g` -/

theorem g_mod_nat : 2 ^ (189269 * 246928) % (189269 * 246929 * 246929) = 7212347012327222 := by
  have h : ((2 ^ (189269 * 246928) : ℕ) : ZMod 11540474954199029) = 7212347012327222 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    change (2 : ZMod 11540474954199029) ^ 46735815632 = 7212347012327222
    reduce_mod_char
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast] at hv
  rw [show 189269 * 246929 * 246929 = 11540474954199029 by norm_num, hv]
  rfl

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `g = B^(p-1) = 2^(189269·246928)`. -/
def gV : V := Exp.exp (189269 * 246928)

/-- The unit cofactor of `g - 1 = C0·v`. -/
def vV : V := 246929 * (gV / (189269 * 246929 * 246929)) + 154321

theorem g_mod : (gV : V) % (189269 * 246929 * 246929) = 7212347012327222 := by
  have h := cast_mod (V := V) (2 ^ (189269 * 246928)) (189269 * 246929 * 246929)
  rw [g_mod_nat, ← cast_exp] at h
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h
  unfold gV
  rw [← h]

theorem g_eq : (gV : V) = 1 + 189269 * 246929 * vV := by
  have hd := div_add_mod (gV : V) (189269 * 246929 * 246929)
  rw [g_mod] at hd
  unfold vV
  calc (gV : V) = 189269 * 246929 * 246929 * (gV / (189269 * 246929 * 246929)) +
        7212347012327222 := hd.symm
    _ = 189269 * 246929 * 246929 * (gV / (189269 * 246929 * 246929)) +
        (1 + 189269 * 246929 * 154321) := by norm_num
    _ = _ := by ring

theorem p_odd : (246929 : V) = 2 * 123464 + 1 := by norm_num

theorem p_pos : (0 : V) < 246929 := by norm_num

theorem v_inv : (vV * 96206 : V) % 246929 = 1 := by
  unfold vV
  rw [← mod_mul_mod_left _ _ p_pos, add_comm, mod_add_mul' _ _ p_pos,
    mod_mul_mod_left _ _ p_pos]
  have h := cast_mod (V := V) (154321 * 96206) 246929
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h
  rw [← h]
  norm_num

/-! ## Discrete-log coordinates at level `P = p^m` -/

theorem C0_gt : (1 : V) < 189269 * 246929 := by norm_num

theorem C0_pos : (0 : V) < 189269 * 246929 := lt_trans _root_.zero_lt_one C0_gt

private theorem coordinate_lt {P z : V} (hz : z < P) :
    1 + 189269 * 246929 * z < 189269 * 246929 * P := by
  calc 1 + 189269 * 246929 * z < 189269 * 246929 + 189269 * 246929 * z :=
        add_lt_add_of_lt_of_le C0_gt le_rfl
    _ = 189269 * 246929 * (z + 1) := by ring
    _ ≤ 189269 * 246929 * P :=
      mul_le_mul_of_nonneg_left (lt_iff_succ_le.mp hz) (Arithmetic.zero_le _)

/-- The coordinate `zc P e = (g^e mod C0·P) / C0`. -/
def zc (P e : V) : V := (power gV e % (189269 * 246929 * P)) / (189269 * 246929)

instance zc_definable (P : V) : 𝚺₁-Function₁ (zc P) := by unfold zc; definability

theorem power_gV (e : V) : ∃ t, power (gV : V) e = 1 + 189269 * 246929 * t := by
  rw [g_eq]; exact power_g e

/-- `g^e ≡ 1 + C0·zc(e) (mod C0·P)` with `zc(e) < P`. -/
theorem zc_spec {P : V} (hP : 0 < P) (e : V) :
    power (gV : V) e % (189269 * 246929 * P) = 1 + 189269 * 246929 * zc P e ∧ zc P e < P := by
  obtain ⟨t, ht⟩ := power_gV (V := V) e
  have hr : t % P < P := mod_lt t hP
  have hlt := coordinate_lt hr
  have hm : power (gV : V) e % (189269 * 246929 * P) = 1 + 189269 * 246929 * (t % P) := by
    rw [ht]
    have he : 1 + 189269 * 246929 * t =
        (1 + 189269 * 246929 * (t % P)) + 189269 * 246929 * P * (t / P) := by
      calc 1 + 189269 * 246929 * t = 1 + 189269 * 246929 * (P * (t / P) + t % P) := by
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

theorem zc_surj (m z : V) (hz : z < power 246929 m) :
    ∃ e < power 246929 m, zc (power 246929 m) e = z := by
  have hP : (0 : V) < power 246929 m := power_pos _ m p_pos
  obtain ⟨e, he, Q, hQ⟩ := coordinates_surj (c := (189269 : V)) (v := vV) (vinv := 96206)
    p_odd v_inv m z hz
  refine ⟨e, he, ?_⟩
  have h1 := (zc_spec hP e).1
  rw [← g_eq] at hQ
  have hlt := coordinate_lt hz
  rw [hQ, show (189269 : V) * 246929 * power 246929 m * Q + 1 + 189269 * 246929 * z =
      (1 + 189269 * 246929 * z) + 189269 * 246929 * power 246929 m * Q by ring,
    mod_add_mul' _ _ (mul_pos C0_pos hP), mod_eq_self_of_lt hlt] at h1
  have h2 := add_left_cancel h1
  exact (mul_cancel_left C0_pos h2).symm

theorem zc_inj (m e e' : V) (he : e < power 246929 m) (he' : e' < power 246929 m)
    (h : zc (power 246929 m) e = zc (power 246929 m) e') : e = e' := by
  have hP : (0 : V) < power 246929 m := power_pos _ m p_pos
  have h1 := (zc_spec hP e).1
  have h2 := (zc_spec hP e').1
  have hinj := coordinates_inj (c := (189269 : V)) (v := vV) (vinv := 96206)
    p_odd (by norm_num) v_inv m e he e' he'
  rw [← g_eq] at hinj
  exact hinj (by rw [h1, h2, h])

/-! ## Dummy positions -/

/-- The dummy position of coordinate index `e`. -/
def pos (e : V) : V := 2 + 246928 * e

theorem exp_pos_eq (e : V) :
    Exp.exp (189269 * pos e) = Exp.exp (189269 * 2) * power (gV : V) e := by
  have h : Exp.exp ((189269 : V) * (246928 * e)) = power (Exp.exp (189269 * 246928)) e := by
    rw [← power_two, ← power_two, power_iterate, mul_assoc]
  unfold pos gV
  rw [mul_add, exp_add, h]

end Adm942ControllerData

#print axioms Adm942ControllerData.g_eq
#print axioms Adm942ControllerData.v_inv
#print axioms Adm942ControllerData.zc_surj
#print axioms Adm942ControllerData.zc_inj
#print axioms Adm942ControllerData.exp_pos_eq
