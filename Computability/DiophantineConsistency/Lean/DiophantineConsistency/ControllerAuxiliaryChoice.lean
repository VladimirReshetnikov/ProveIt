import DiophantineConsistency.ControllerOrbitTransport
import Mathlib.Data.Nat.Prime.Basic

/-!
# Choosing the auxiliary Boolean bit and a coprime subset cardinality

The projection to a prime modulus is actual modular arithmetic. The bit
and least positive cardinality are constructed, not supplied. Actual
power-orbit coordinates and safe dummy positions remain separate.
-/

namespace DiophantineConsistency.ControllerAuxiliaryChoice

set_option Elab.async false
set_option maxRecDepth 10000

/-- Two translates by a nonzero element cannot both vanish. -/
theorem exists_boolean_sub_ne_zero {A : Type*} [AddGroup A]
    (t b : A) (hb : b ≠ 0) : ∃ e : ℕ, e ≤ 1 ∧ t-e • b ≠ 0 := by
  by_cases ht : t = 0
  · refine ⟨1,by omega,?_⟩
    simpa only [one_nsmul,ht,zero_sub,neg_ne_zero] using hb
  · exact ⟨0,by omega,by simpa only [zero_nsmul,sub_zero] using ht⟩

/-- The actual residue after the Boolean choice has a least representative
strictly between0 andC0, coprime to every power of the auxiliary prime. -/
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

end DiophantineConsistency.ControllerAuxiliaryChoice
