import Trace74BoundaryGraphWitness

/-! UNCHECKED DRAFT: avoid expanding a large model numeral by making the radix
    multiplier a parameter. Finite exponential, phase, growth and Pell inputs
    remain explicit hypotheses. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74BoundarySeedParametric
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing ArithmeticPellRecurrence
open Trace75Factors Trace75Rank Trace74BoundaryGraphWitness Trace74Mask
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def ports31 : Fin 4 → ℕ := ![1,1,28,0]
def source31 (W s : V) : Fin 10 → V := ![1,1,0,1,1,W,s,1,1,1]

/-- This conditional draft does not certify the audited finite R=31 seed. -/
theorem positive_boundary_of_source (W s eta zeta : V)
    (hW : 0<W) (hs : 0<s) (heta : 0<eta) (hzeta : 0<zeta)
    (hphase : (2*(15:V)+1)%4=3)
    (hXeq : X ports31 (source31 W s)=Exp.exp (2*(15:V)+1))
    (h72 : 72*(15:V)<X ports31 (source31 W s)+1)
    (hck : ycoord (2*(15:V)+1) (Y ports31 (source31 W s)*(X ports31 (source31 W s)+1))=
      2*ycoord ((15:V)+1) (2*(X ports31 (source31 W s)*Y ports31 (source31 W s)*Y ports31 (source31 W s)-1)+1)*Y ports31 (source31 W s)+eta)
    (hk : 2*ycoord ((15:V)+1) (2*(X ports31 (source31 W s)*Y ports31 (source31 W s)*Y ports31 (source31 W s)-1)+1)=eta+zeta) :
    ∃ w : Fin 10 → V, (∀ j,0<w j) ∧ w 0=1 ∧ w 1=1 ∧ w 2=1 ∧
      value74 (ports ports31) (fun j => ι (w j))=0 := by
  have h21 : (2:V)-1=1 := by
    apply add_right_cancel (b:=1)
    rw [tsub_add_cancel_of_le (show (1:V)≤2 by norm_num)]
    norm_num
  have h41 : (4:V)-1=3 := by
    apply add_right_cancel (b:=1)
    rw [tsub_add_cancel_of_le (show (1:V)≤4 by norm_num)]
    norm_num
  have hb : (0:V)<(ports31 0:V) := by norm_num [ports31]
  have hv : ∀ j,j ≠ 2 → 0<source31 W s j := by
    intro j hj
    fin_cases j <;> simp_all [source31]
  have hmaskpos : 0<q ports31 (source31 W s)-source31 W s 1-source31 W s 2 := by
    norm_num [q,b,ports31,source31,h21]
  have hmask : source31 W s 1+source31 W s 2<q ports31 (source31 W s) := by
    norm_num [q,b,ports31,source31]
  have htransport : ((ports31 1:V)+source31 W s 5)*
      (q ports31 (source31 W s)-source31 W s 1-source31 W s 2)=
      source31 W s 1+b ports31 (source31 W s)*W := by
    simp [q,b,ports31,source31,h21,add_comm]
  have hR : rankNat ports31 (source31 W s)=2*(15:V)+1 := by
    norm_num [rankNat,q,b,ports31,source31,h21,h41]
  obtain ⟨w,hw,hw0,hw1,hw2,hzero⟩ :=
    graph_74_zero_of_source ports31 (source31 W s) 15 eta zeta W
      hb hv (by norm_num) hmaskpos hmask htransport hR hphase hXeq h72 heta hzeta hck hk
  refine ⟨w,hw,?_,?_,?_,hzero⟩
  · simpa [source31] using hw0
  · simpa [source31] using hw1
  · simpa [q,b,ports31,source31,h21] using hw2

#print axioms Trace74BoundarySeedParametric.positive_boundary_of_source
end Trace74BoundarySeedParametric
