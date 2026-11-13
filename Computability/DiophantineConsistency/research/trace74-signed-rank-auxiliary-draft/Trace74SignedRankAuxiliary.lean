import Trace74JoinedSquare
import Trace75SignedRank

/-! UNCHECKED DRAFT. Guard-free signed-rank auxiliary congruence. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74SignedRankAuxiliary
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence ArithmeticPellHalfIndex
open Trace75Factors Trace74Representatives Trace74JoinedSquare Trace75SignedRank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_signed_rank_auxiliary (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0) :
    let D := delta p v
    let U0 := U p v
    let E0 := E p v
    let A0 := A p v
    let F := 1+2*(D*U0*U0*E0)
    ∃ rp rn I j h : V, 0<I ∧ 0<j ∧ c p v*c p v∣I ∧
      (regs (ports p) (masked p v)).rank=ι rp-ι rn ∧
      xcoord j (A0-1)=F ∧ ycoord j (A0-1)=I ∧
      SignMod F (c p v) (ycoord (2*h+1) (A0-1)) ∧
      SignMod (c p v) (absdiff rp rn) (2*h+1) := by
  let D : V := delta p v
  let U0 : V := U p v
  let E0 : V := E p v
  let a : V := D*U0*U0*E0
  let F : V := 1+2*a
  let C : V := c p v
  let rr := regs (ports p) (masked p v)
  let x : DiffRing V := rr.V
  obtain ⟨tau,f,V0,y,I,j,h,htau,hf,hV,hy,hI,hj,ht,hf2,hIeq,hdiv,hjx,hjy,hauxx,hauxy,hVsq,hgc,htransfer⟩ :=
    strong_and_auxiliary_indices_with_graph_residue p v hb hv hz
  obtain ⟨rp,rn,hr⟩ := exists_mk rr.rank
  have hrank : rr.rank=ι rp-ι rn := by rw [hr,mk_eq_sub]
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hk : 0<k v := add_pos (hv 8) (hv 9)
  have hcpos : 0<C := add_pos (mul_pos hk hY) (hv 8)
  have hFpos : 0<F := by dsimp [F]; simp
  have hcdiv : C∣2*a := ⟨2*D*(v 3)*(v 3)*C*C*C*E0,by dsimp [a,U0,U,C]; ring⟩
  have hfmod : F%C=(1:V)%C := by
    dsimp [F]
    exact mod_add_remove_right_of_dvd hcdiv hcpos
  have hx : x=ι F*(ι (v 4*C)+ι rn-ι rp)-ι C := by
    dsimp [x,rr]
    rw [V_def,b_def,f_eq,a_eq,Trace74Representatives.delta_eval,Trace74Representatives.U_eval,
      Trace74Representatives.E_eval,Trace74Representatives.c_eval,hrank]
    dsimp [F,a,D,U0,E0,C,masked,Trace74Mask.oldVal]
    simp only [pow_two,map_mul,map_add,map_one,map_ofNat]
    ring
  have hRank : SignMod C V0 (absdiff rp rn) :=
    rank_residue_of_square C F (v 4) rp rn V0 x hcpos hfmod hx hVsq
  have hcI : C∣I := dvd_trans (dvd_mul_right C C) hdiv
  have hD : 0<D := (factors_positive p v hb hv).1
  have hU : 0<U0 := (factors_positive p v hb hv).2.1
  have hI2 : 2≤I := by
    have hpos : 1≤U0*tau*f := pos_iff_one_le.mp (mul_pos (mul_pos hU htau) hf)
    rw [hIeq]
    simpa only [mul_assoc,mul_one] using mul_le_mul_of_nonneg_left hpos (by simp : (0:V)≤2)
  have hJ2 : 2≤D*I := le_trans hI2 (le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp hD))
  have hJpos : 0<D*I := lt_of_lt_of_le (by simp : (0:V)<2) hJ2
  have hsub : D*I-2+2=D*I := tsub_add_cancel_of_le hJ2
  have hu : V0=oddQuotient h (D*I-2) := by
    apply mul_left_cancel₀ (ne_of_gt hJpos)
    calc
      (D*I)*V0=xcoord (2*h+1) (D*I-2) := hauxx.symm
      _=(D*I)*oddQuotient h (D*I-2) := by rw [odd_exact,hsub]
  have hdJ : C∣D*I := dvd_mul_of_dvd_right hcI D
  have hindex : SignMod C V0 (2*h+1) := by
    rw [hu]
    exact quotient_mod_divisor (D*I) C h hJ2 hcpos hdJ
  have htarget : SignMod F C (ycoord (2*h+1) (A p v-1)) :=
    sign_trans hFpos (sign_symm hgc) htransfer
  exact ⟨rp,rn,I,j,h,hI,hj,hdiv,hrank,hjx,hjy,htarget,sign_trans hcpos (sign_symm hRank) hindex⟩

#print axioms Trace74SignedRankAuxiliary.graph_signed_rank_auxiliary
end Trace74SignedRankAuxiliary
