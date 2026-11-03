import ScaledFromUnscaled

/-! Positive scaled interval witnesses from an unscaled source. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace TenPositiveScaledWitnessFromUnscaled
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing
open ArithmeticPellRecurrence TenPositiveScaledFromUnscaled
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem scaled_witnesses (X Y S r eta zeta : V)
    (hX : 1≤X) (hY : 1≤Y) (hSY : Y≤S) (hr : 0<r)
    (hXeq : X=Exp.exp (2*r+1)) (h72 : 72*r<X+1)
    (heta : 0<eta) (hzeta : 0<zeta)
    (hck : ycoord (2*r+1) (Y*(X+1))=
      2*ycoord (r+1) (2*(X*Y*Y-1)+1)*Y+eta)
    (hk : 2*ycoord (r+1) (2*(X*Y*Y-1)+1)=eta+zeta) :
    let P:=X*S*S
    let B:=2*(P-1)+1
    let a:=S*(X+1)-1
    let K:=2*ycoord (r+1) B
    let C:=ycoord (2*r+1) a
    ∃ eta' zeta' : V, 0<eta' ∧ 0<zeta' ∧ C=K*Y+eta' ∧ K=eta'+zeta' := by
  let P:=X*S*S
  let B:=2*(P-1)+1
  let a:=S*(X+1)-1
  let K:=2*ycoord (r+1) B
  let C:=ycoord (2*r+1) a
  obtain ⟨hl,hu⟩ := scaled_interval X Y S r eta zeta hX hY hSY hr hXeq h72 heta hzeta hck hk
  let eta':=C-K*Y
  have hetapos : 0<eta' := tsub_pos_iff_lt.mpr hl
  have hsum : K*Y+eta'=C := by
    dsimp [eta']
    rw [add_comm,tsub_add_cancel_of_le (le_of_lt hl)]
  have hleft : (ι C:DiffRing V)=ι (K*Y)+ι eta' := by rw [←map_add,hsum]
  have huR : (ι C:DiffRing V)<ι (K*(Y+1)) := ι_lt_ι.mpr hu
  have heR : (ι eta':DiffRing V)<ι K := by
    simp only [map_mul,map_add,map_one] at huR hleft
    nlinarith
  have he : eta'<K := ι_lt_ι.mp heR
  let zeta':=K-eta'
  have hzpos : 0<zeta' := tsub_pos_iff_lt.mpr he
  have hK : K=eta'+zeta' := by
    dsimp [zeta']
    rw [add_comm,tsub_add_cancel_of_le (le_of_lt he)]
  exact ⟨eta',zeta',hetapos,hzpos,hsum.symm,hK⟩

#print axioms TenPositiveScaledWitnessFromUnscaled.scaled_witnesses
end TenPositiveScaledWitnessFromUnscaled
