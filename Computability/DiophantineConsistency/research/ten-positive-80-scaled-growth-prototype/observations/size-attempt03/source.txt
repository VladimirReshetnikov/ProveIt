import Direct80Factors

/-! The X-size assumption follows from a small beta lower bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80Size
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency TenPositive80Factors
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem x_lower (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : (15:V)≤(p 0:V)) (hv : ∀j,0<v j) : 16≤X p v := by
  have hj : 1≤v 0 := pos_iff_one_le.mp (hv 0)
  have hw : 1≤v 5 := pos_iff_one_le.mp (hv 5)
  have hq : 16≤q p v := by
    unfold q b
    calc
      (16:V)=15*1+1 := by ring
      _≤(p 0:V)*v 0+1 := by
        simpa only [add_comm] using add_le_add_right (mul_le_mul hb hj (by simp) (by simp)) 1
  calc
    (16:V)≤q p v := hq
    _≤v 5*q p v := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (show (0:V)≤q p v by simp)
    _=X p v := by rfl

#print axioms Direct80Size.x_lower
end Direct80Size
