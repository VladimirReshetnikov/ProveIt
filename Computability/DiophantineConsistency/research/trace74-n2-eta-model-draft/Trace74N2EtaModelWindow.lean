import Trace74N2EtaIdentity
import Trace74N2EtaWindow

/-! UNCHECKED DRAFT. Bind generic eta-window to the same 74 graph witness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74N2EtaModelWindow
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75Factors Trace74Pell Trace74N2EtaIdentity Trace74N2EtaWindow
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_small_k_right_window (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0)
    (hq4 : 4≤q p v) (hsmall : k v=8*firstParam p v+4) :
    2*Y p v<X p v+3 := by
  have hw : 1≤v 5 := pos_iff_one_le.mp (hv 5)
  have hs : 1≤v 6 := pos_iff_one_le.mp (hv 6)
  have hqX : q p v≤X p v := by
    change q p v≤v 5*q p v
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (show (0:V)≤q p v by simp)
  have hq3Y : q p v*q p v*q p v≤Y p v := by
    change q p v*q p v*q p v≤(q p v*q p v*q p v)*v 6
    exact le_mul_of_one_le_right (by simp) hs
  have h16 : 16≤q p v*q p v := calc
    16=(4:V)*4 := by ring
    _≤q p v*q p v := mul_le_mul hq4 hq4 (by simp) (by simp)
  have h64 : 64≤Y p v := calc
    64=(16:V)*4 := by ring
    _≤(q p v*q p v)*q p v := mul_le_mul h16 hq4 (by simp) (by simp)
    _≤Y p v := hq3Y
  have hx4 : 4≤X p v := le_trans hq4 hqX
  have hxR : (4:DiffRing V)≤ι (X p v) := by
    rw [←map_ofNat (ι : V →+* DiffRing V) 4,ι_le_ι]
    exact hx4
  have hyR : (64:DiffRing V)≤ι (Y p v) := by
    rw [←map_ofNat (ι : V →+* DiffRing V) 64,ι_le_ι]
    exact h64
  have heR : (0:DiffRing V)<ι (v 8) := by
    rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]
    exact hv 8
  have h := eta_window (ι (X p v)) (ι (Y p v)) (ι (v 8)) hxR hyR heR
    (graph_eta_identity p v hb hv hz hsmall)
  apply ι_lt_ι.mp
  simpa only [map_add,map_mul,map_ofNat] using h

#print axioms Trace74N2EtaModelWindow.graph_small_k_right_window
end Trace74N2EtaModelWindow
