import Trace74OddOrdinateKBound
import Trace74FirstPellGap

/-! UNCHECKED DRAFT. First-index geometry from actual positive trace74 graph zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74FirstIndexGeometry
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75Factors Trace74Pell Trace74OddOrdinateKBound Trace74FirstPellGap
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem small_k_implies_X_lt_two_Y (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0)
    (hsmall : k v=8*firstParam p v+4) : X p v<2*Y p v := by
  let X0 : V := X p v
  let Y0 : V := Y p v
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y0 := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hK : 4*(Y0*(X0+1)+1)^2≤(8*X0*(Y0*Y0)+4)*(Y0+1) := by
    have h := graph_k_lower p v hb hv hz
    rw [hsmall] at h
    calc
      4*(Y0*(X0+1)+1)^2≤(8*firstParam p v+4)*(Y0+1) := h
      _=(8*X0*(Y0*Y0)+4)*(Y0+1) := by dsimp [firstParam,X0,Y0]; ring
  by_contra hn
  have hXY : 2*Y0≤X0 := le_of_not_gt hn
  have hprod : 2*X0*Y0≤X0^2 := calc
    2*X0*Y0=(2*Y0)*X0 := by ring
    _≤X0*X0 := mul_le_mul_of_nonneg_right hXY (by simp)
    _=X0^2 := by ring
  have hbase : 2*X0*Y0^3≤X0^2*Y0^2 := calc
    2*X0*Y0^3=(2*X0*Y0)*Y0^2 := by ring
    _≤X0^2*Y0^2 := mul_le_mul_of_nonneg_right hprod (by simp)
  have hpos : 0<Y0^2+2*X0*Y0+Y0 := by
    exact add_pos_of_nonneg_of_pos (by simp) hY
  have hrest : 2*X0*Y0^2+Y0+1 <
      (2*X0*Y0^2+Y0+1)+(Y0^2+2*X0*Y0+Y0) := lt_add_of_pos_right _ hpos
  have hcombined := add_lt_add_of_le_of_lt hbase hrest
  have hscaled := mul_lt_mul_of_pos_left hcombined (by norm_num : (0:V)<4)
  have hcontr : (8*X0*(Y0*Y0)+4)*(Y0+1) < 4*(Y0*(X0+1)+1)^2 := by
    calc
      (8*X0*(Y0*Y0)+4)*(Y0+1)=4*(2*X0*Y0^3+(2*X0*Y0^2+Y0+1)) := by ring
      _<4*(X0^2*Y0^2+((2*X0*Y0^2+Y0+1)+(Y0^2+2*X0*Y0+Y0))) := hscaled
      _=4*(Y0*(X0+1)+1)^2 := by ring
  exact (not_lt_of_ge hK) hcontr

theorem graph_geometry_or_large_k (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0) :
    X p v<2*Y p v ∨ 32*(firstParam p v)^2+32*firstParam p v+6≤k v := by
  rcases graph_first_pell_gap p v hb hv hz with hsmall | hlarge
  · exact Or.inl (small_k_implies_X_lt_two_Y p v hb hv hz hsmall)
  · exact Or.inr hlarge

#print axioms Trace74FirstIndexGeometry.small_k_implies_X_lt_two_Y
#print axioms Trace74FirstIndexGeometry.graph_geometry_or_large_k
end Trace74FirstIndexGeometry
