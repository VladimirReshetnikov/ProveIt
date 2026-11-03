import Direct80CarrierIdentity

/-! Nonnegative actual transport implies the positive graph mask gap. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositive80TransportMask
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open TenPositive80Graph TenPositive80Factors TenPositive80CarrierIdentity
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_mask_of_nonnegative_transport (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hvF : 0<v 1) (hvw : 0<v 5)
    (hB : 0≤(BExpr (integerPorts p)).evalRing (fun j => ι (v j))) :
    v 1+v 2<q p v := by
  let w : Fin 10 → DiffRing V := fun j => ι (v j)
  let coefficient : DiffRing V := ι (p 1:V)+ι (v 5)
  let gap : DiffRing V := ι (q p v)-ι (v 1)-ι (v 2)
  have hqeval : (qExpr (integerPorts p)).evalRing w=ι (q p v) := by
    simp only [qExpr,hExpr,w,q,b,integerPorts,Expr.evalRing_mul,Expr.evalRing_add,
      Expr.evalRing_constant,Expr.evalRing_var,Expr.evalRing_ofNat,Int.cast_natCast,
      Nat.cast_one,map_mul,map_add,map_one,map_natCast]
  have hBeval : (BExpr (integerPorts p)).evalRing w=coefficient*gap-ι (v 1) := by
    simp only [BExpr,Expr.evalRing_mul,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_var,
      Expr.evalRing_constant,hqeval]
    dsimp [coefficient,gap,w,integerPorts]
    simp only [Int.cast_natCast,map_natCast]
  have hw : (0:DiffRing V)<ι (v 5) := by
    rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hvw
  have hf : (0:DiffRing V)<ι (v 1) := by
    rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hvF
  have hcoef : 0<coefficient := add_pos_of_nonneg_of_pos (ι_nonneg _) hw
  have hprod : 0<coefficient*gap := by rw [hBeval] at hB; linarith
  have hgap : 0<gap := pos_of_mul_pos_right hprod (le_of_lt hcoef)
  have hlt : (ι (v 1+v 2):DiffRing V)<ι (q p v) := by
    rw [map_add]
    dsimp [gap] at hgap
    linarith
  exact ι_lt_ι.mp hlt

#print axioms TenPositive80TransportMask.positive_mask_of_nonnegative_transport
end TenPositive80TransportMask
