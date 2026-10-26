import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace ControllerCastReview

theorem exists_coordinate {C0 T : ℕ} [NeZero C0] [NeZero T]
    (z : ZMod (C0*T)) (a : ℕ) (ha : a < C0)
    (hz : ZMod.castHom (dvd_mul_right C0 T) (ZMod C0) z = (a : ZMod C0)) :
    ∃ u : ZMod T,
      z = (a : ZMod (C0*T))+(C0 : ZMod (C0*T))*(u.val : ZMod (C0*T)) := by
  have hm : z.val%C0 = a := by
    simpa only [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast,
      Nat.mod_eq_of_lt ha] using congrArg ZMod.val hz
  have hq : z.val/C0 < T :=
    (Nat.div_lt_iff_lt_mul (NeZero.pos C0)).mpr (by
      simpa only [Nat.mul_comm] using ZMod.val_lt z)
  refine ⟨((z.val/C0 : ℕ) : ZMod T),?_⟩
  rw [ZMod.val_natCast_of_lt hq,← Nat.cast_mul,← Nat.cast_add]
  rw [← hm,Nat.mod_add_div,ZMod.natCast_zmod_val]

theorem exists_boolean_sub_ne_zero {A : Type*} [AddGroup A]
    (t b : A) (hb : b ≠ 0) : ∃ e : ℕ, e ≤ 1 ∧ t-e • b ≠ 0 := by
  by_cases ht : t = 0
  · refine ⟨1,by omega,?_⟩
    simpa only [one_nsmul,ht,zero_sub,neg_ne_zero] using hb
  · exact ⟨0,by omega,by simpa only [zero_nsmul,sub_zero] using ht⟩

theorem exists_coprime_cardinality {p C0 : ℕ} [NeZero C0]
    (hp : Nat.Prime p) (hdiv : p ∣ C0) (t b : ZMod C0)
    (hb : ZMod.castHom hdiv (ZMod p) b ≠ 0) (n : ℕ) :
    ∃ e a : ℕ, e ≤ 1 ∧ 0 < a ∧ a < C0 ∧
      (a : ZMod C0) = t-(e : ZMod C0)*b ∧ Nat.Coprime a (p^n) := by
  let phi : ZMod C0 →+* ZMod p := ZMod.castHom hdiv (ZMod p)
  obtain ⟨e,he,hne⟩ := exists_boolean_sub_ne_zero (phi t) (phi b) hb
  let r : ZMod C0 := t-(e : ZMod C0)*b
  have hr : phi r ≠ 0 := by
    simpa only [r,map_sub,map_mul,map_natCast,nsmul_eq_mul] using hne
  have hnd : ¬ p ∣ r.val := by
    apply (ZMod.natCast_eq_zero_iff r.val p).not.mp
    simpa only [phi, ZMod.castHom_apply, ZMod.cast_eq_val] using hr
  have hpos : 0 < r.val :=
    ZMod.val_pos.mpr (fun hz => hr (by rw [hz, map_zero]))
  exact ⟨e,r.val,he,hpos,ZMod.val_lt r,ZMod.natCast_zmod_val r,
    hp.coprime_pow_of_not_dvd hnd⟩

example : ∃ u : ZMod 5, (13 : ZMod (5*5)) = 3 + 5*(u.val : ZMod (5*5)) :=
  exists_coordinate 13 3 (by decide) (by decide)

example : ∃ u : ZMod 1, (3 : ZMod (5*1)) = 3 + 5*(u.val : ZMod (5*1)) :=
  exists_coordinate 3 3 (by decide) (by decide)

#print axioms exists_coordinate
#print axioms exists_coprime_cardinality

end ControllerCastReview
