import Trace75Size
import Trace75Residue

/-! Trace75 graph's K register is positive at every positive zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace75Kpos
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open Trace75Factors Trace75Pell Trace75Size Trace75Residue
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_c_above_x (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : value75 (ports p) (fun j => ι (v j)) = 0) : X p v<c p v := by
  have hklower := (graph_rank_size p v hb hv hz).1
  let P : V := firstParam p v
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hy : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hY1 : 1≤Y p v := pos_iff_one_le.mp hy
  have hXP : X p v≤P := by
    change X p v≤X p v*(Y p v*Y p v)
    exact le_mul_of_one_le_right (by simp) (one_le_mul hY1 hY1)
  have hPk : P<k v := calc
    P≤8*P := by simpa only [one_mul] using mul_le_mul_of_nonneg_right (show (1:V)≤8 by norm_num) (show (0:V)≤P by simp)
    _<8*P+4 := lt_add_of_pos_right _ (by norm_num)
    _≤k v := hklower
  have hkc : k v≤c p v := by
    change k v≤k v*Y p v+v 8
    exact le_trans (le_mul_of_one_le_right (by simp) hY1) (by simp)
  exact lt_of_lt_of_le (lt_of_le_of_lt hXP hPk) hkc

theorem graph_K_positive (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    0<(regs (ports p) (fun j => ι (v j))).K := by
  have hc := graph_c_above_x p v hb hv hz
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hx : 0<X p v := mul_pos (hv 5) hq
  have hxr : (0:DiffRing V)<ι (X p v) := by
    simpa only [map_zero] using (ι_lt_ι.mpr hx)
  have hcr : (ι (X p v):DiffRing V)<ι (c p v) := ι_lt_ι.mpr hc
  have hgap : (0:DiffRing V)<3*ι (c p v)-2*ι (X p v) := by linarith
  have hxeval : (regs (ports p) (fun j => ι (v j))).X=ι (X p v) := by
    simp only [X_def,q_def,h_def,ports,X,q,b,map_mul,map_add,map_one,map_natCast]
  rw [K_def,hxeval,c_eval]
  have hprod := mul_pos hxr hgap
  linarith

#print axioms Trace75Kpos.graph_K_positive
end Trace75Kpos
