import Trace74OffsetNatural

/-! Carrier divisibility is invariant under the strong-seed coordinate update. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74CarrierUpdate
open Trace74ChartAssembly Trace74DynamicRegisters
variable {R : Type*} [CommRing R]

/-- The changed chart term is a multiple of the unchanged modulus; the
signed offset and modulus themselves ignore coordinate 3. -/
theorem update_three (p : Fin 4 → R) (v : Fin 10 → R) (i : R)
    (hdiv : (chart p v).M ∣ (chart p v).Z) :
    (chart p (Function.update v 3 i)).M ∣ (chart p (Function.update v 3 i)).Z := by
  let w := Function.update v 3 i
  have hm : (chart p w).M=(chart p v).M := by rfl
  have ho : (components p w).offset=(components p v).offset := by rfl
  have hoff : (chart p v).M ∣ (components p v).offset := by
    have h := dvd_sub hdiv (dvd_mul_right (chart p v).M
      (v 7-(chart p v).V*(chart p v).V*(components p v).B))
    rw [Z_formula] at h
    simpa using h
  rw [Z_formula,hm,ho]
  exact dvd_add (dvd_mul_right _ _) hoff

#print axioms Trace74CarrierUpdate.update_three
end Trace74CarrierUpdate
