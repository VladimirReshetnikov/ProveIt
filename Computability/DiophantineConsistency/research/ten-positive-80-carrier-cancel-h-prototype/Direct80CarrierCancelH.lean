import Direct80CarrierDivisibility

/-! Cancel the graph H factor by its explicit unit certificate modulo μ². -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace TenPositive80CarrierCancelH
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open TenPositive80Graph TenPositive80Factors TenPositive80CarrierIdentity TenPositive80CarrierDivisibility
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem cancel_one_minus_multiple {R : Type*} [CommRing R] (m t x : R)
    (h : m*m∣(m*t-1)*x) : m*m∣x := by
  obtain ⟨s,hs⟩ := h
  refine ⟨s*(-(m*t+1))+t*t*x,?_⟩
  calc
    x=((m*t-1)*x)*(-(m*t+1))+(m*m)*(t*t*x) := by ring
    _=(m*m)*s*(-(m*t+1))+(m*m)*(t*t*x) := by rw [hs]
    _=(m*m)*(s*(-(m*t+1))+t*t*x) := by ring

theorem graph_cancel_H (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    let w : Fin 10 → DiffRing V := fun j => ι (v j)
    let h := (hExpr (integerPorts p)).evalRing w
    let m := (muExpr (integerPorts p)).evalRing w
    let e := (eExpr (integerPorts p)).evalRing w
    m*m∣h*e := by
  let w : Fin 10 → DiffRing V := fun j => ι (v j)
  let h := (hExpr (integerPorts p)).evalRing w
  let m := (muExpr (integerPorts p)).evalRing w
  let H := (HExpr (integerPorts p)).evalRing w
  let e := (eExpr (integerPorts p)).evalRing w
  let t : DiffRing V := 4*ι (Y p v)*(ι (X p v)+1)
  have hH : H=m*t-1 := by
    dsimp [H,HExpr,m,muExpr,qExpr,hExpr,w,t,Y,X,q,b,integerPorts]
    simp only [Expr.evalRing_ofNat,Int.cast_natCast,Nat.cast_one,Nat.cast_ofNat,
      map_mul,map_add,map_one,map_natCast]
    ring
  have hd := graph_carrier_divisibility p v hb hv hz
  change m*m∣h*H*e at hd
  have hd' : m*m∣(m*t-1)*(h*e) := by
    rw [←hH]
    simpa only [mul_comm,mul_left_comm,mul_assoc] using hd
  exact cancel_one_minus_multiple m t (h*e) hd'

#print axioms TenPositive80CarrierCancelH.graph_cancel_H
end TenPositive80CarrierCancelH
