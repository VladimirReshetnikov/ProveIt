import CompactRankResidueJoin
import DiophantineConsistency.ArithmeticOuterSeed
import DiophantineConsistency.ArithmeticPellAuxiliarySeed

/-! Outer and auxiliary Pell seeds for any compact physical packing. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactOuterPellSeed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPow ArithmeticBinaryPopulation ArithmeticPacking ArithmeticPellRecurrence
open ArithmeticOuterSeed ArithmeticPellAuxiliarySeed ArithmeticPellHalfIndex
open CompactConstructedRank CompactRankResidueJoin
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The rank forced by a compact packing supplies both complete seed families. -/
theorem seeds {K N s : V} {X : V → V} [𝚺₁-Function₁ X]
    (h : PackingInput 590069 K low high N s X) :
    let u := (590069:V)*N
    let R := rank K N s X
    ∃ sY n eta zeta gamma : V,
      0<sY ∧ 0<n ∧ 0<eta ∧ 0<zeta ∧ 0<gamma ∧
      SeedRelations u R sY n eta zeta gamma ∧
      sY*Exp.exp u^3 ≤ power (Exp.exp R+1) R ∧
      (let Y := sY*Exp.exp u^3
      let a := Exp.exp R*Y+Y
      let c := ycoord R a
      ∃ f i T w y : V, 0 < f ∧ 0 < i ∧ 0 < T ∧ 0 < w ∧ 0 < y ∧
        f=xcoord (R*c) a ∧ ycoord (R*c) a=i*c*c ∧
        f*f=1+delta a*(i*c*c)*(i*c*c) ∧
        let I := delta a*i*c*c
        y=ycoord R (I-2) ∧ xcoord R (I-2)=I*w ∧
        w=oddQuotient ((R-1)/2) (I-2) ∧
        (w+c)%(f*f)=0 ∧ (w+R)%c=0 ∧
        f*f*c*T=w+c+f*f*R ∧ w=absdiff (f*f*c*T) (f*f*R+c) ∧
        I*I*w*w+y*y=1+I*I*y*y) := by
  obtain ⟨hpop,hphase,_⟩ := properties h
  have hu : (0:V)<590069*N := mul_pos (by norm_num) (N_pos h)
  have hodd : ∃ r, rank K N s X=2*r+1 :=
    ⟨(rank K N s X-1)/2, (phase_indices (rank K N s X) hphase).2.1⟩
  obtain ⟨sY,n,eta,zeta,gamma,hsY,hn,he,hz,hg,hseed,hsize⟩ :=
    outer_seed_with_size (590069*N) (rank K N s X) hu hodd hpop
  refine ⟨sY,n,eta,zeta,gamma,hsY,hn,he,hz,hg,hseed,hsize,?_⟩
  exact auxiliary_seed
    (Exp.exp (rank K N s X)*(sY*Exp.exp (590069*N)^3)+sY*Exp.exp (590069*N)^3)
    (rank K N s X) hphase

#print axioms CompactOuterPellSeed.seeds
end CompactOuterPellSeed
