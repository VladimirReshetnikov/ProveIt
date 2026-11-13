import Trace74OffsetQuotient

/-! Bind the carrier modulus to a model element on a positive base chart. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74OffsetNatural
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75Factors Trace74ChartAssembly Trace74DynamicRegisters
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The actual chart modulus is the cast of the natural truncated-subtraction
formula when the two base factors are positive. -/
theorem modulus_eval (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hX : 0<X p v) (hY : 0<Y p v) :
    (chart (ports p) (fun j => ι (v j))).M=ι (M p v) := by
  have hA : 0<A p v := add_pos (mul_pos hX hY) hY
  have hA1 : 1≤A p v := pos_iff_one_le.mp hA
  have h4A : 1<4*A p v := lt_of_lt_of_le (by simp : (1:V)<4)
    (by simpa using mul_le_mul_of_nonneg_left hA1 (by simp : (0:V)≤4))
  have hsub : 4*A p v-1+1=4*A p v := tsub_add_cancel_of_le (le_of_lt h4A)
  have hcast : ι (4*A p v-1) = 4*ι (A p v)-1 := by
    apply eq_sub_iff_add_eq.mpr
    rw [← map_one (ι : V →+* DiffRing V), ← map_add, hsub,map_mul,map_ofNat]
  simp only [M,map_mul]
  rw [hcast]
  simp only [A,Y,X,q,Trace75Factors.b,ports,chart,map_mul,map_add,map_one,map_natCast]

/-- Actual carrier divisibility on such a tuple gives all signed offset data
needed for the base-witness construction. -/
theorem signed_offset (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hX : 0<X p v) (hY : 0<Y p v)
    (hdiv : (chart (ports p) (fun j => ι (v j))).M ∣
      (chart (ports p) (fun j => ι (v j))).Z) :
    ∃ C G P S : V,
      (components (ports p) (fun j => ι (v j))).offset = ι C-ι G ∧
      ι C-ι G=ι (M p v)*(ι P-ι S) :=
  Trace74OffsetQuotient.signed_offset (ports p) v (M p v) (modulus_eval p v hX hY) hdiv

#print axioms Trace74OffsetNatural.modulus_eval
#print axioms Trace74OffsetNatural.signed_offset
end Trace74OffsetNatural
