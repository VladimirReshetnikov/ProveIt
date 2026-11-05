import Trace74StrongCarrierChart

/-! Extract the signed offset quotient needed by the zero-witness assembly. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74OffsetQuotient
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing
open Trace74ChartAssembly Trace74DynamicRegisters
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Divisibility of the actual chart's Z register gives the signed natural
offset and quotient required by `exists_positive_zero_from_base`. -/
theorem signed_offset (p : Fin 4 → DiffRing V) (v : Fin 10 → V) (M : V)
    (hM : (chart p (fun j => ι (v j))).M = ι M)
    (hdiv : (chart p (fun j => ι (v j))).M ∣
      (chart p (fun j => ι (v j))).Z) :
    ∃ C G P S : V,
      (components p (fun j => ι (v j))).offset = ι C-ι G ∧
      ι C-ι G=ι M*(ι P-ι S) := by
  let w := fun j => ι (v j)
  have ho : (chart p w).M ∣ (components p w).offset := by
    have h := dvd_sub hdiv (dvd_mul_right (chart p w).M
      (w 7-(chart p w).V*(chart p w).V*(components p w).B))
    rw [Z_formula] at h
    dsimp only [w] at h ⊢
    simpa using h
  obtain ⟨K,hK⟩ := ho
  obtain ⟨C,G,hcg⟩ := exists_mk ((components p w).offset)
  obtain ⟨P,S,hps⟩ := exists_mk K
  rw [mk_eq_sub] at hcg hps
  refine ⟨C,G,P,S,hcg,?_⟩
  rw [←hcg,hK,hM,hps]

#print axioms Trace74OffsetQuotient.signed_offset
end Trace74OffsetQuotient
