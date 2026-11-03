import Trace75GraphUnweighted
import Trace75Kpos

/-! A positive natural quotient of the actual trace75 projection. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75Kappa
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75Factors Trace75Kpos
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_positive_kappa (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V))
    (hh : (p 3:V)<2*(p 0:V)) (hv : ∀j,0<v j)
    (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    ∃ kappa : V, 0<kappa ∧
      (regs (ports p) (fun j => ι (v j))).K=
        (regs (ports p) (fun j => ι (v j))).H*ι kappa := by
  let rr := regs (ports p) (fun j => ι (v j))
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hy : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hx : 0<X p v := mul_pos (hv 5) hq
  have hA : 0<A p v := add_pos (mul_pos hx hy) hy
  have hAeval : rr.Am1=ι (A p v) := by
    dsimp [rr,A,X,Y,q,b,ports]
    simp only [Am1_def,X_def,Y_def,q_def,h_def,ports,map_mul,map_add,map_one,map_natCast]
  have hA1 : (1:DiffRing V)≤ι (A p v) := by
    rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]
    exact pos_iff_one_le.mp hA
  have hH : 0<rr.H := by
    rw [show rr.H=4*rr.Am1-1 by dsimp [rr]; rw [H_def],hAeval]
    linarith
  have hK : 0<rr.K := graph_K_positive p v hb hv hz
  obtain ⟨z,hz'⟩ := Trace75GraphUnweighted.graph_unweighted p v hb31 hl hh hv hz
  change rr.K=rr.H*z at hz'
  have hzpos : 0<z := by
    by_contra hn
    have hzle : z≤0 := le_of_not_gt hn
    have hbad := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hH) hzle
    rw [←hz'] at hbad
    exact (not_le_of_gt hK) hbad
  rcases nonneg_or_nonpos z with ⟨kappa,hkap⟩|⟨kappa,hkap⟩
  · refine ⟨kappa,?_,?_⟩
    · apply ι_lt_ι.mp
      simpa only [map_zero,hkap] using hzpos
    · simpa only [hkap] using hz'
  · have hneg : z≤0 := by rw [hkap]; exact neg_nonpos.mpr (ι_nonneg kappa)
    exact False.elim ((not_le_of_gt hzpos) hneg)

#print axioms Trace75Kappa.graph_positive_kappa
end Trace75Kappa
