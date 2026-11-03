import Direct80FreshInterval
import DiophantineConsistency.ModelArithmetic

/-! Positive source interval witnesses for the fresh unscaled Pell pair. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace TenPositive80FreshFirstMain
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open ArithmeticPellRecurrence
open CompactFixedBeta CompactSymbolicPorts
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank TenPositive80FreshInterval
attribute [local irreducible] CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_fresh_first_main (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v) :
    ∃ r eta zeta : V, 0 < r ∧ 0 < eta ∧ 0 < zeta ∧ rankNat p v=2*r+1 ∧
      let X0:=X p v
      let Y0:=Y p v
      let K:=2*ycoord (r+1) (2*(X0*Y0*Y0-1)+1)
      let C:=ycoord (2*r+1) (Y0*(X0+1))
      C=K*Y0+eta ∧ K=eta+zeta := by
  obtain ⟨r,hr,hR,hl,hu⟩ := graph_fresh_interval p v hp0 hp2 hp3 hv hz
  let X0:=X p v
  let Y0:=Y p v
  let K:=2*ycoord (r+1) (2*(X0*Y0*Y0-1)+1)
  let C:=ycoord (2*r+1) (Y0*(X0+1))
  let eta:=C-K*Y0
  have heta : 0<eta := tsub_pos_iff_lt.mpr hl
  have hsum : K*Y0+eta=C := by
    dsimp [eta]
    rw [add_comm,tsub_add_cancel_of_le (le_of_lt hl)]
  have hleft : (ι C:DiffRing V)=ι (K*Y0)+ι eta := by rw [←map_add,hsum]
  have huR : (ι C:DiffRing V)<ι (K*(Y0+1)) := ι_lt_ι.mpr hu
  have heR : (ι eta:DiffRing V)<ι K := by
    simp only [map_mul,map_add,map_one] at huR hleft
    nlinarith
  have he : eta<K := ι_lt_ι.mp heR
  let zeta:=K-eta
  have hzeta : 0<zeta := tsub_pos_iff_lt.mpr he
  have hk : K=eta+zeta := by
    dsimp [zeta]
    rw [add_comm,tsub_add_cancel_of_le (le_of_lt he)]
  exact ⟨r,eta,zeta,hr,heta,hzeta,hR,hsum.symm,hk⟩

#print axioms TenPositive80FreshFirstMain.graph_fresh_first_main
end TenPositive80FreshFirstMain
