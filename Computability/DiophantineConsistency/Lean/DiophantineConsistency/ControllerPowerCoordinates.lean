import DiophantineConsistency.ControllerResidueLift
import Mathlib.GroupTheory.OrderOfElement

/-! A full affine coordinate parametrization is constructed from the actual
order and projection of a modular generator. No orbit-coordinate map is
supplied as a premise. -/
namespace DiophantineConsistency.ControllerPowerCoordinates

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem exists_power_coordinates {C0 T : ℕ} [NeZero T] (hC0 : 1 < C0)
    (g : ZMod (C0*T))
    (hproject : ZMod.castHom (dvd_mul_right C0 T) (ZMod C0) g = 1)
    (horder : orderOf g = T) :
    ∃ e : ZMod T ≃ ZMod T, ∀ z : ZMod T,
      g^(e z).val = 1+(C0 : ZMod (C0*T))*(z.val : ZMod (C0*T)) := by
  classical
  letI : NeZero C0 := ⟨by omega⟩
  have hex (j : ZMod T) : ∃ u : ZMod T,
      g^j.val = 1+(C0 : ZMod (C0*T))*(u.val : ZMod (C0*T)) := by
    have hp : ZMod.castHom (dvd_mul_right C0 T) (ZMod C0) (g^j.val) = (1 : ℕ) := by
      rw [map_pow, hproject, one_pow, Nat.cast_one]
    simpa only [Nat.cast_one] using
      ControllerResidueLift.exists_coordinate (g^j.val) 1 hC0 hp
  choose u hu using hex
  have hinj : Function.Injective u := by
    intro i j hij
    have hp : g^i.val = g^j.val := by rw [hu i, hu j, hij]
    have hi : i.val < orderOf g := by rw [horder]; exact ZMod.val_lt i
    have hj : j.val < orderOf g := by rw [horder]; exact ZMod.val_lt j
    apply ZMod.val_injective
    exact pow_injOn_Iio_orderOf hi hj hp
  let f : ZMod T ≃ ZMod T :=
    Equiv.ofBijective u ⟨hinj, Finite.surjective_of_injective hinj⟩
  refine ⟨f.symm,?_⟩
  intro z
  have hz : u (f.symm z) = z := f.apply_symm_apply z
  rw [hu, hz]

end DiophantineConsistency.ControllerPowerCoordinates
