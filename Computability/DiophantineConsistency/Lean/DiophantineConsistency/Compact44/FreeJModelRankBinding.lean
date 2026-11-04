import DiophantineConsistency.Compact44.FreeJAdaptiveLift
import DiophantineConsistency.Compact44.CompactConstructedRank

/-! Bind the exact free-J rank expression to the compact represented rank. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FreeJModelRankBinding
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticPacking ArithmeticRepunit
open CompactConstructedRank FreeJAdaptiveLift
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem cast_sub_of_le (x y : V) (h : y≤x) :
    ι (x-y) = ι x-ι y := by
  have h' := congrArg (fun z : V => ι z) (tsub_add_cancel_of_le h)
  simp only [map_add] at h'
  calc ι (x-y) = (ι (x-y)+ι y)-ι y := by ring
    _ = ι x-ι y := by rw [h']

/-- Coordinate and symbolic port bindings for one valuation suffice; no
    graph zero or equation-specific port identification is assumed. -/
theorem graph_rank_of_packing (p : Fin 4 → ℤ) (v : Fin 12 → V)
    {K N s : V} {X : V → V} [𝚺₁-Function₁ X]
    (hpack : PackingInput 590069 K low high N s X)
    (hJ : v 0=rep 590069 N)
    (hF : v 1=Fw 590069 K N s X)
    (hA : v 2=alpha 590069 K N s X)
    (hbeta : ι (v 0)*((p 0 : ℤ) : DiffRing V)=ι (Exp.exp (590069*N)-1))
    (hMC : ((p 2 : ℤ) : DiffRing V)=ι (low:V))
    (hMF : ((p 3 : ℤ) : DiffRing V)=ι (high+(Exp.exp (590069:V)-1))) :
    (rankExpr p).evalRing (fun j => ι (v j))=ι (rank K N s X) := by
  let q : V := Exp.exp (590069*N)
  let F : V := Fw 590069 K N s X
  let A : V := alpha 590069 K N s X
  let J : V := rep 590069 N
  have hq : 1≤q := one_le_exp _
  have hFq : F≤q := le_of_lt (lt_of_lt_of_le (F_lt_M hpack) tsub_le_self)
  have hq1 : ι (q-1)=ι q-1 := by simpa only [map_one] using cast_sub_of_le q 1 hq
  have hqF : ι (q-F)=ι q-ι F := cast_sub_of_le q F hFq
  have hq2 : ι (q^2-1)=ι q^2-1 := by
    simpa only [map_one,map_pow] using cast_sub_of_le (q^2) 1 (one_le_pow₀ hq)
  have hgraph : (rankExpr p).evalRing (fun j => ι (v j)) =
      (ι A+(ι q-ι F)*ι (q-1))*(ι q*ι q-1)+
        ι J*(ι (low:V)+ι (high+(Exp.exp (590069:V)-1))*ι q) := by
    simp only [rankExpr,Expr.evalRing_mul,Expr.evalRing_add,Expr.evalRing_sub,
      Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]
    rw [hbeta,hJ,hF,hA,hMC,hMF,hq1]
    ring
  rw [hgraph]
  change _ = ι (((q-1)*(q-F)+A)*(q^2-1)+
    ((low:V)+q*(high+(Exp.exp (590069:V)-1)))*J)
  simp only [map_add,map_mul,hqF,hq2,hq1]
  ring

#print axioms FreeJModelRankBinding.graph_rank_of_packing
end FreeJModelRankBinding
