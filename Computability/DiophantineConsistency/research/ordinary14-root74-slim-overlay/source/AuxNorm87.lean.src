import FourFields87
import NaturalRank87
import StrongNorm87
import DiophantineConsistency.Compact44.P72Aux

/-! Source-only auxiliary norm from the 87 own-zero. Imports are unelaborated
drafts; no P72 exact-index or endpoint conclusion is asserted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.AuxNorm87Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs ArithmeticPellHalfIndex
open NaturalRank84Draft StrongNorm87Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def coeff (beta : V) (v : Fin 14 → V) : DiffRing V :=
  ι (Delta v)*(ι (v 3)*ι (v 3)-1)
def zvalue (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V) : DiffRing V :=
  (ι (v 3)*ι (v 3))*(ι (v 5)*ι (c v)-AuxGraphNormClientDraft.rank p beta v)-ι (c v)

/-- Evaluate the shared 86 auxiliary field as its signed quadratic identity. -/
theorem aux_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hport : (p 0 : DiffRing V)=ι beta) :
    let z := zvalue p beta v
    let Q := coeff beta v
    FirstFields86Draft.eval (P86ResidueGraph.graph p).aux v =
      (z+ι (v 11))*(z+ι (v 11))-Q*((z+ι (v 11))*(z+ι (v 11))-z*z) := by
  simp [FirstFields86Draft.eval,P86ResidueGraph.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    zvalue,coeff,AuxGraphNormClientDraft.rank,
    a,c,FirstFields86Draft.k,Delta,hport,map_add,map_mul,map_one] <;> ring

/-- Extract the natural absolute-difference auxiliary norm from the same 87
own-zero, with all four natural port representations and positive valuation. -/
theorem aux_norm (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hport : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)
    (hMC : (p 2 : DiffRing V)=ι MC) (hMF : (p 3 : DiffRing V)=ι MF)
    (hv : ∀ j, 0<v j) (hz : InternalZero (P87ShiftedGuard.graph p).output v) :
    let R := naturalRank beta MC MF v
    let c := StrongNorm87Draft.c v
    let Delta := StrongNorm87Draft.Delta v
    let Vp := v 3*v 3*(v 5*c)
    let Vn := v 3*v 3*R+c
    let Qa := Delta*(v 3*v 3-1)
    Qa*(absdiff Vp Vn*absdiff Vp Vn)+absdiff (Vp+v 11) Vn*absdiff (Vp+v 11) Vn =
      1+Qa*(absdiff (Vp+v 11) Vn*absdiff (Vp+v 11) Vn) := by
  let R := naturalRank beta MC MF v
  let c := StrongNorm87Draft.c v
  let Delta := StrongNorm87Draft.Delta v
  let Vp := v 3*v 3*(v 5*c)
  let Vn := v 3*v 3*R+c
  let Qa := Delta*(v 3*v 3-1)
  have hR : AuxGraphNormClientDraft.rank p beta v=ι R :=
    NaturalRank87Draft.rank_of_87_zero p beta K MC MF v hport hK hMC hMF (hv 1) (hv 6) hz
  have hf1 : 1≤v 3 := pos_iff_one_le.mp (hv 3)
  have hf2 : 1≤v 3*v 3 := one_le_mul_of_one_le_of_one_le hf1 hf1
  have hQa : ι Qa=coeff beta v := by
    simp only [Qa,coeff,map_mul,P72Root.ι_tsub hf2,map_one]
  have hzvalue : zvalue p beta v=ι Vp-ι Vn := by
    simp [zvalue,hR,Vp,Vn,map_add,map_mul]
    <;> ring
  have haux := (FourFields87Draft.fields_of_zero p v hz).2.2.1
  rw [aux_eval p beta v hport] at haux
  have hcore : (ι (Vp+v 11)-ι Vn)*(ι (Vp+v 11)-ι Vn)-ι Qa*
      ((ι (Vp+v 11)-ι Vn)*(ι (Vp+v 11)-ι Vn)-(ι Vp-ι Vn)*(ι Vp-ι Vn))=1 := by
    rw [←hQa,hzvalue] at haux
    simp only [map_add] at haux ⊢
    linear_combination haux
  apply ι_injective
  simp only [map_add,map_mul,map_one,P72Aux.ι_absdiff_sq]
  linear_combination hcore

end DiophantineConsistency.AuxNorm87Draft

#print axioms DiophantineConsistency.AuxNorm87Draft.aux_norm
