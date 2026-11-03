import Trace74BoundaryGraphWitness

/-! UNCHECKED DRAFT: small-port specialization, retaining explicit finite Pell
    input hypotheses. It is not a numerical certificate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74BoundarySeedConditional
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing ArithmeticPellRecurrence
open Trace75Factors Trace75Rank Trace74BoundaryGraphWitness Trace74Mask
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def ports31 : Fin 4 → ℕ := ![1,1,28,0]
def source31 (s : V) : Fin 10 → V := ![1,1,0,1,1,1073741824,s,1,1,1]

/-- The remaining hypotheses are exactly the exponential and the two Pell
    source equations; their R=31 numerical instance is not proved here. -/
theorem positive_boundary_of_source (s eta zeta : V)
    (hs : 0<s) (heta : 0<eta) (hzeta : 0<zeta)
    (hXeq : X ports31 (source31 s)=Exp.exp (2*(15:V)+1))
    (hck : ycoord (2*(15:V)+1) (Y ports31 (source31 s)*(X ports31 (source31 s)+1))=
      2*ycoord ((15:V)+1) (2*(X ports31 (source31 s)*Y ports31 (source31 s)*Y ports31 (source31 s)-1)+1)*Y ports31 (source31 s)+eta)
    (hk : 2*ycoord ((15:V)+1) (2*(X ports31 (source31 s)*Y ports31 (source31 s)*Y ports31 (source31 s)-1)+1)=eta+zeta) :
    ∃ w : Fin 10 → V, (∀ j,0<w j) ∧ w 0=1 ∧ w 1=1 ∧ w 2=1 ∧
      value74 (ports ports31) (fun j => ι (w j))=0 := by
  have hb : (0:V)<(ports31 0:V) := by norm_num [ports31]
  have hv : ∀ j,j ≠ 2 → 0<source31 s j := by
    intro j hj
    fin_cases j <;> simp_all [source31]
  have hmaskpos : 0<q ports31 (source31 s)-source31 s 1-source31 s 2 := by
    norm_num [q,b,ports31,source31]
  have hmask : source31 s 1+source31 s 2<q ports31 (source31 s) := by
    norm_num [q,b,ports31,source31]
  have htransport : ((ports31 1:V)+source31 s 5)*
      (q ports31 (source31 s)-source31 s 1-source31 s 2)=
      source31 s 1+b ports31 (source31 s)*(1073741824:V) := by
    norm_num [q,b,ports31,source31]
  have hR : rankNat ports31 (source31 s)=2*(15:V)+1 := by
    norm_num [rankNat,q,b,ports31,source31]
  have hphase : (2*(15:V)+1)%4=3 := by norm_num
  have h72 : 72*(15:V)<X ports31 (source31 s)+1 := by
    norm_num [X,q,b,ports31,source31]
  obtain ⟨w,hw,hw0,hw1,hw2,hzero⟩ :=
    graph_74_zero_of_source ports31 (source31 s) 15 eta zeta 1073741824
      hb hv (by norm_num) hmaskpos hmask htransport hR hphase hXeq h72 heta hzeta hck hk
  refine ⟨w,hw,?_,?_,?_,hzero⟩
  · simpa [source31] using hw0
  · simpa [source31] using hw1
  · simpa [q,b,ports31,source31] using hw2

#print axioms Trace74BoundarySeedConditional.positive_boundary_of_source
end Trace74BoundarySeedConditional
