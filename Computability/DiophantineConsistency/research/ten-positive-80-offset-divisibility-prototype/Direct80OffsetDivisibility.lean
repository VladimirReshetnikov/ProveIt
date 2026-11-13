import SignedBezout
import Direct80GraphParity

/-! Even-radix unit cancels the remaining h from the signed carrier offset. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositive80OffsetDivisibility
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open TenPositive80Graph TenPositive80Factors TenPositive80CarrierIdentity TenPositive80CarrierCancelH TenPositiveSignedBezout
open Direct80GraphParity
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_offset_divisible (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v)
    (hbeta : ∃u : V, (p 0:V)=2*u+1) :
    let w : Fin 10 → DiffRing V := fun j => ι (v j)
    let m := (muExpr (integerPorts p)).evalRing w
    m*m∣(eExpr (integerPorts p)).evalRing w := by
  let w : Fin 10 → DiffRing V := fun j => ι (v j)
  let m := (muExpr (integerPorts p)).evalRing w
  let h := (hExpr (integerPorts p)).evalRing w
  let e := (eExpr (integerPorts p)).evalRing w
  have hm : m=ι (mu p v) := by
    simp only [m,muExpr,qExpr,hExpr,w,mu,q,b,integerPorts,Expr.evalRing_mul,Expr.evalRing_add,
      Expr.evalRing_constant,Expr.evalRing_var,Expr.evalRing_ofNat,Int.cast_natCast,
      Nat.cast_one,map_mul,map_add,map_one,map_natCast]
  have he : h=ι (b p v) := by
    simp only [h,hExpr,w,b,integerPorts,Expr.evalRing_mul,Expr.evalRing_constant,
      Expr.evalRing_var,Int.cast_natCast,map_mul,map_natCast]
  have hd := graph_cancel_H p v hb hv hz
  change m*m∣h*e at hd
  rw [hm,he,←map_mul] at hd
  have hbez := (graph_even_and_unit p v hb hl hh hv hz hbeta).2
  have hfinal := cancel_signed_factor (b p v) (mu p v*mu p v) e hbez hd
  change m*m∣e
  rw [hm,←map_mul]
  exact hfinal

#print axioms TenPositive80OffsetDivisibility.graph_offset_divisible
end TenPositive80OffsetDivisibility
