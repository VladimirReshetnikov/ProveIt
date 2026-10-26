import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
namespace ControllerCastBaseline
theorem exists_coordinate {C0 T : ℕ} [NeZero C0] [NeZero T]
    (z : ZMod (C0*T)) (a : ℕ) (ha : a < C0)
    (hz : ZMod.castHom (dvd_mul_right C0 T) (ZMod C0) z = (a : ZMod C0)) :
    ∃ u : ZMod T,
      z = (a : ZMod (C0*T))+(C0 : ZMod (C0*T))*(u.val : ZMod (C0*T)) := by
  let phi : ZMod (C0*T) →+* ZMod C0 := ZMod.castHom (dvd_mul_right C0 T) (ZMod C0)
  have hc : phi z = (z.val : ZMod C0) := by
    calc
      phi z = phi (z.val : ZMod (C0*T)) := congrArg phi (ZMod.natCast_zmod_val z).symm
      _ = (z.val : ZMod C0) := map_natCast phi z.val
  have hm : z.val%C0 = a := by
    have he := congrArg ZMod.val (hc.symm.trans hz)
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt ha] using he
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
  have hc : (r.val : ZMod p) = phi r := by
    rw [← map_natCast phi r.val,ZMod.natCast_zmod_val]
  have hnd : ¬ p ∣ r.val := by
    intro hd
    have hz : (r.val : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p r.val).mpr hd
    exact hr (hc.symm.trans hz)
  have hpos : 0 < r.val := by
    by_contra h
    have hz : r.val = 0 := by omega
    exact hnd (hz ▸ dvd_zero p)
  exact ⟨e,r.val,he,hpos,ZMod.val_lt r,ZMod.natCast_zmod_val r,
    hp.coprime_pow_of_not_dvd hnd⟩


#print axioms exists_coordinate
#print axioms exists_coprime_cardinality
end ControllerCastBaseline
