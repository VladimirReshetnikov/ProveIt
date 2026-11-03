import Direct80FreshProjection
import DiophantineConsistency.ArithmeticPellCongruences

/-! Exact unscaled source main offset from a graph zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace TenPositive80FreshMainOffset
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open ArithmeticPellRecurrence ArithmeticPellCongruences
open CompactFixedBeta CompactSymbolicPorts
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank
open TenPositive80FreshProjection TenPositive80SymbolicPortBounds
attribute [local irreducible] CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_fresh_main_offset (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v) :
    ∃ r eta zeta gamma h : V, 0 < r ∧ 0 < eta ∧ 0 < zeta ∧ 0 < gamma ∧
      rankNat p v=2*r+1 ∧
      let X0:=X p v
      let Y0:=Y p v
      let a:=Y0*(X0+1)
      let K:=2*ycoord (r+1) (2*(X0*Y0*Y0-1)+1)
      let C:=ycoord (2*r+1) a
      C=K*Y0+eta ∧ K=eta+zeta ∧
      xcoord (2*r+1) a=X0+a*C+(4*a+3)*gamma ∧
      K=rankNat p v+1+(Y0*(q p v*q p v))*h := by
  obtain ⟨r,eta,zeta,gamma,hr,heta,hzeta,hgamma,hR,hC,hK,hproj⟩ :=
    graph_fresh_projection p v hp0 hp2 hp3 hv hz
  obtain ⟨h31,_hl,_hh,_hodd⟩ := fixed_bounds (V:=V) p hp0 hp2 hp3
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num) h31
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hX : 0<X p v := mul_pos (hv 5) hq
  let P:=X p v*Y p v*Y p v
  let B:=2*(P-1)+1
  have hP : 0<P := mul_pos (mul_pos hX hY) hY
  have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
  have hdiv : (2*P)∣B+1 := by
    refine ⟨1,?_⟩
    calc
      B+1=2*(P-1+1) := by dsimp [B]; ring
      _=2*P := by rw [hP1]
      _=(2*P)*1 := by ring
  obtain ⟨_z,s,_hx,hys⟩ := residue_quotients (r+1) B (2*P) hdiv
  have hsplit : 2*ycoord (r+1) B=rankNat p v+1+4*P*s := by
    rw [hys,hR]
    ring
  have h4P : 4*P=(Y p v*(q p v*q p v))*(4*(q p v*q p v)*(v 5)*(v 6)) := by
    dsimp [P,X,Y]
    ring
  refine ⟨r,eta,zeta,gamma,4*(q p v*q p v)*(v 5)*(v 6)*s,
    hr,heta,hzeta,hgamma,hR,hC,hK,hproj,?_⟩
  change 2*ycoord (r+1) B=rankNat p v+1+
    (Y p v*(q p v*q p v))*(4*(q p v*q p v)*(v 5)*(v 6)*s)
  rw [hsplit,h4P]
  ring

#print axioms TenPositive80FreshMainOffset.graph_fresh_main_offset
end TenPositive80FreshMainOffset
