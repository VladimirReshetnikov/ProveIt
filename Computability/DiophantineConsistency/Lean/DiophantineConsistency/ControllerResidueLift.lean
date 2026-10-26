import DiophantineConsistency.ControllerAuxiliaryChoice

/-!
# Constructing every affine subset residue with one optional Boolean term

The explicit coordinate injection and affine weight formula are structural
inputs. The Boolean term, cardinality, coordinate target and finite subset
are constructed here. The actual power-orbit interface is still separate.
-/

namespace DiophantineConsistency.ControllerResidueLift

open ControllerAuxiliaryChoice ControllerOrbitTransport
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000

/-- Lift a known small residue to its actual quotient coordinate. -/
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

/-- All target residues are realized by an actual subset and one Boolean
multiple of b, once the affine coordinate injection is supplied. -/
theorem exists_subset_boolean_sum {C0 T p : ℕ} [NeZero C0] [NeZero T]
    {α : Type*} [DecidableEq α]
    (hp : Nat.Prime p) (hdiv : p ∣ C0) (n : ℕ) (hT : T = p^n) (hCT : C0 < T)
    (index : ZMod T → α) (hinj : Function.Injective index)
    (weight : α → ZMod (C0*T))
    (hw : ∀ z, weight (index z) = 1+(C0 : ZMod (C0*T))*(z.val : ZMod (C0*T)))
    (t b : ZMod (C0*T))
    (hb : ZMod.castHom hdiv (ZMod p)
      (ZMod.castHom (dvd_mul_right C0 T) (ZMod C0) b) ≠ 0) :
    ∃ e a : ℕ, ∃ s : Finset α,
      e ≤ 1 ∧ 0 < a ∧ a < C0 ∧ s.card = a ∧
      (∑ x ∈ s, weight x)+(e : ZMod (C0*T))*b = t := by
  let phi : ZMod (C0*T) →+* ZMod C0 := ZMod.castHom (dvd_mul_right C0 T) (ZMod C0)
  obtain ⟨e,a,he,hapos,ha,hres,hcop⟩ :=
    exists_coprime_cardinality hp hdiv (phi t) (phi b) hb n
  let r := t-(e : ZMod (C0*T))*b
  have hr : phi r = (a : ZMod C0) := by
    simpa only [r,map_sub,map_mul,map_natCast] using hres.symm
  obtain ⟨u,hu⟩ := exists_coordinate r a ha hr
  have hcopT : Nat.Coprime a T := by rw [hT]; exact hcop
  have haT : a ≤ T := by omega
  refine ⟨e,a,targetSubset index a hcopT u,he,hapos,ha,
    targetSubset_card index hinj a hcopT haT u,?_⟩
  rw [targetSubset_modular_sum C0 index hinj weight hw a hcopT haT u,← hu]
  exact sub_add_cancel t ((e : ZMod (C0*T))*b)

end DiophantineConsistency.ControllerResidueLift
