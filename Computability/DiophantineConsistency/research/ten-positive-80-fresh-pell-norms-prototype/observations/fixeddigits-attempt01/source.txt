import Direct80FreshFirstMain

/-! Explicit fresh first/main Pell norms from an actual 80-graph zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace TenPositive80FreshPellNorms
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open ArithmeticPellRecurrence
open CompactFixedBeta CompactSymbolicPorts
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank
open TenPositive80FreshFirstMain TenPositive80SymbolicPortBounds
attribute [local irreducible] CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_fresh_pell_norms (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v) :
    ∃ r eta zeta tau d : V, 0 < r ∧ 0 < eta ∧ 0 < zeta ∧ 0 < tau ∧ 0 < d ∧
      rankNat p v=2*r+1 ∧
      let X0:=X p v
      let Y0:=Y p v
      let P:=X0*Y0*Y0
      let K:=2*ycoord (r+1) (2*(P-1)+1)
      let C:=ycoord (2*r+1) (Y0*(X0+1))
      C=K*Y0+eta ∧ K=eta+zeta ∧
      tau*tau=1+P*(P+1)*K*K ∧
      d*d=1+ArithmeticPellRecurrence.delta (Y0*(X0+1))*C*C := by
  obtain ⟨r,eta,zeta,hr,heta,hzeta,hR,hC,hK⟩ :=
    graph_fresh_first_main p v hp0 hp2 hp3 hv hz
  let X0:=X p v
  let Y0:=Y p v
  let P:=X0*Y0*Y0
  let B:=2*(P-1)+1
  let a:=Y0*(X0+1)
  let K:=2*ycoord (r+1) B
  let C:=ycoord (2*r+1) a
  let tau:=xcoord (r+1) B
  let d:=xcoord (2*r+1) a
  have h31 := (fixed_bounds (V:=V) p hp0 hp2 hp3).1
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num) h31
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y0 := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hX : 0<X0 := mul_pos (hv 5) hq
  have hP : 0<P := mul_pos (mul_pos hX hY) hY
  have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
  have hdelta : ArithmeticPellRecurrence.delta B=4*P*(P+1) := by
    dsimp [B,ArithmeticPellRecurrence.delta]
    calc
      (2*(P-1)+1+1)*(2*(P-1)+1+3) = 4*(P-1+1)*(P-1+1+1) := by ring
      _=4*P*(P+1) := by rw [hP1]
  have hfirst : tau*tau=1+P*(P+1)*K*K := by
    have h := norm (r+1) B
    rw [hdelta] at h
    dsimp [tau,K]
    calc
      xcoord (r+1) B*xcoord (r+1) B =
          1+4*P*(P+1)*ycoord (r+1) B*ycoord (r+1) B := h
      _=1+P*(P+1)*(2*ycoord (r+1) B)*(2*ycoord (r+1) B) := by ring
  have hmain : d*d=1+ArithmeticPellRecurrence.delta a*C*C := norm (2*r+1) a
  have ht : 0<tau := lt_of_lt_of_le (by simp : (0:V)<1) (one_le_x (r+1) B)
  have hd : 0<d := lt_of_lt_of_le (by simp : (0:V)<1) (one_le_x (2*r+1) a)
  exact ⟨r,eta,zeta,tau,d,hr,heta,hzeta,ht,hd,hR,hC,hK,hfirst,hmain⟩

#print axioms TenPositive80FreshPellNorms.graph_fresh_pell_norms
end TenPositive80FreshPellNorms
