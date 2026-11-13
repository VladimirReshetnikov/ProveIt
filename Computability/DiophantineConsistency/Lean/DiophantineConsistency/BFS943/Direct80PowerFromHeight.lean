import DiophantineConsistency.BFS943.Direct80ProductHeight

/-! Conditional graph power equality from the full-product height bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80PowerFromHeight
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank TenPositive80NaturalProjection
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_power_of_height (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v)
    (hheight : b p v*(X p v+Exp.exp (rankNat p v))*
      (Exp.exp (rankNat p v)*X p v+1)<Hnat p v) : X p v=Exp.exp (rankNat p v) :=
  Direct80ProductHeight.equality_of_height (b p v) (X p v) (Exp.exp (rankNat p v)) (Hnat p v)
    (mul_pos hb (hv 0)) hheight (Direct80GraphProduct.graph_entire_product p v hb hl hh hv hz)

#print axioms Direct80PowerFromHeight.graph_power_of_height
end Direct80PowerFromHeight
