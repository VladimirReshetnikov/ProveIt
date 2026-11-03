import Direct80FreshFirstMain
import Direct80GraphPower
import DiophantineConsistency.ArithmeticPellPowerRecovery

/-! Positive projection quotient for the fresh unscaled main root. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace TenPositive80FreshProjection
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open ArithmeticPellRecurrence ArithmeticPellPowerRecovery
open CompactFixedBeta CompactSymbolicPorts
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank
open TenPositive80FreshFirstMain TenPositive80SymbolicPortBounds
attribute [local irreducible] CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_fresh_projection (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v) :
    ∃ r eta zeta gamma : V, 0 < r ∧ 0 < eta ∧ 0 < zeta ∧ 0 < gamma ∧
      rankNat p v=2*r+1 ∧
      let X0:=X p v
      let Y0:=Y p v
      let a:=Y0*(X0+1)
      let K:=2*ycoord (r+1) (2*(X0*Y0*Y0-1)+1)
      let C:=ycoord (2*r+1) a
      C=K*Y0+eta ∧ K=eta+zeta ∧
      xcoord (2*r+1) a=X0+a*C+(4*a+3)*gamma := by
  obtain ⟨r,eta,zeta,hr,heta,hzeta,hR,hC,hK⟩ :=
    graph_fresh_first_main p v hp0 hp2 hp3 hv hz
  obtain ⟨h31,hl,hh,hodd⟩ := fixed_bounds (V:=V) p hp0 hp2 hp3
  have hX : X p v=Exp.exp (2*r+1) := by
    have h := Direct80GraphPower.graph_power p v h31 hl hh hv hz hodd
    rwa [hR] at h
  let a:=Y p v*(X p v+1)
  obtain ⟨z,hzq⟩ := projection_quotient a (2*r)
  let gamma:=ycoord (2*r) a+2*z
  have h2r : 0<2*r := mul_pos (by simp) hr
  have hy : 0<ycoord (2*r) a := lt_of_lt_of_le h2r (time_le_y (2*r) a)
  have hg : 0<gamma := lt_of_lt_of_le hy (le_add_of_nonneg_right (by simp))
  refine ⟨r,eta,zeta,gamma,hr,heta,hzeta,hg,hR,hC,hK,?_⟩
  change xcoord (2*r+1) a=X p v+a*ycoord (2*r+1) a+(4*a+3)*gamma
  rw [hX,x_succ,y_succ,exp_succ,hzq]
  dsimp [gamma,ArithmeticPellRecurrence.delta]
  ring

#print axioms TenPositive80FreshProjection.graph_fresh_projection
end TenPositive80FreshProjection
