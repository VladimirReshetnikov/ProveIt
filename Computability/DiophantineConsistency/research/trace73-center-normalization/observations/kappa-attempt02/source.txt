import Trace75Kappa

/-! Bound a trace75 transport quotient below every positive strong root. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75KappaRoot
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75Factors Trace75Kpos Trace75Kappa Trace75Residue
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem quotient_below_root (p : Fin 4 → ℕ) (v : Fin 10 → V) (kappa f : V)
    (hb : 0 < (p 0 : V)) (hv : ∀ j, 0 < v j)
    (hK : (regs (ports p) (fun j => ι (v j))).K =
      (regs (ports p) (fun j => ι (v j))).H * ι kappa)
    (hf : 1 + delta p v * U p v * U p v * E p v = f*f) : kappa < f := by
  let X0 := X p v
  let Y0 := Y p v
  let C := c p v
  let rr := regs (ports p) (fun j => ι (v j))
  have hb0 : 0 < b p v := mul_pos hb (hv 0)
  have hq : 0 < q p v := add_pos hb0 (by simp)
  have hx : 0 < X0 := mul_pos (hv 5) hq
  have hy : 0 < Y0 := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hk : 0 < k v := add_pos (hv 8) (hv 9)
  have hc : 0 < C := add_pos (mul_pos hk hy) (hv 8)
  have hx1 : 1 ≤ X0 := pos_iff_one_le.mp hx
  have hy1 : 1 ≤ Y0 := pos_iff_one_le.mp hy
  have hc1 : 1 ≤ C := pos_iff_one_le.mp hc
  have hxR : (1:DiffRing V) ≤ ι X0 := by simpa only [map_one] using ι_le_ι.mpr hx1
  have hyR : (1:DiffRing V) ≤ ι Y0 := by simpa only [map_one] using ι_le_ι.mpr hy1
  have hcR : (1:DiffRing V) ≤ ι C := by simpa only [map_one] using ι_le_ι.mpr hc1
  have hYprod : 0 ≤ (ι Y0-1)*(ι X0+1) := mul_nonneg (sub_nonneg.mpr hyR) (by linarith)
  have hXC : 0 ≤ (ι X0 : DiffRing V)*ι C := mul_nonneg (by linarith) (by linarith)
  have hH : rr.H = 4*ι Y0*(ι X0+1)-1 := by
    dsimp [rr, X0, Y0]
    simp only [H_def,Am1_def,X_def,Y_def,q_def,h_def,ports,X,Y,q,b,map_mul,map_add,map_one,map_natCast]
    ring
  have hKshape : rr.K = ι X0*(3*ι C-2*ι X0)+2 := by
    dsimp [rr, X0, C]
    rw [K_def]
    simp only [X_def,q_def,h_def,ports,X,q,b,map_mul,map_add,map_one,map_natCast]
    rw [c_eval]
  have hHbound : 4*ι X0+3 ≤ rr.H := by rw [hH]; nlinarith [hYprod]
  have hHpos : 0 < rr.H := by linarith
  have hHc := mul_le_mul_of_nonneg_right hHbound (show (0:DiffRing V) ≤ ι C by linarith)
  have hsmall : rr.K < rr.H * ι C := by rw [hKshape]; nlinarith [hHc,hXC,hxR,hcR]
  have hkltR : (ι kappa : DiffRing V) < ι C := by
    by_contra hn
    have hle : (ι C : DiffRing V) ≤ ι kappa := le_of_not_gt hn
    have h := mul_le_mul_of_nonneg_left hle (le_of_lt hHpos)
    rw [←hK] at h
    exact (not_le_of_gt hsmall) h
  have hklt : kappa < C := ι_lt_ι.mp hkltR
  obtain ⟨hd,hu,he,_⟩ := factors_positive p v hb hv
  have hd1 : 1 ≤ delta p v := pos_iff_one_le.mp hd
  have he1 : 1 ≤ E p v := pos_iff_one_le.mp he
  have hi1 : 1 ≤ v 3 := pos_iff_one_le.mp (hv 3)
  have hcu : C ≤ U p v := calc
    C ≤ C*C := le_mul_of_one_le_right (by simp) hc1
    _ ≤ v 3*(C*C) := le_mul_of_one_le_left (by simp) hi1
  have hsq : C*C ≤ U p v*U p v := mul_self_le_mul_self (by simp) hcu
  have hD : U p v*U p v ≤ delta p v*(U p v*U p v) :=
    le_mul_of_one_le_left (by simp) hd1
  have hE : delta p v*(U p v*U p v) ≤ delta p v*(U p v*U p v)*E p v :=
    le_mul_of_one_le_right (by simp) he1
  have hlt : C*C < f*f := by
    calc
      C*C ≤ U p v*U p v := hsq
      _ ≤ delta p v*(U p v*U p v) := hD
      _ ≤ delta p v*(U p v*U p v)*E p v := hE
      _ < 1 + delta p v*U p v*U p v*E p v := by
        have h := lt_add_of_pos_left (delta p v*(U p v*U p v)*E p v) (by simp : (0:V)<1)
        simpa only [mul_assoc] using h
      _ = f*f := hf
  have hcf : C < f := by
    by_contra hnot
    have hfC : f ≤ C := le_of_not_gt hnot
    have := mul_self_le_mul_self (by simp : (0:V)≤f) hfC
    exact (not_le_of_gt hlt) this
  exact lt_trans hklt hcf

#print axioms Trace75KappaRoot.quotient_below_root
end Trace75KappaRoot
