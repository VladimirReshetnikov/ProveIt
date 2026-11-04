import DiophantineConsistency.ArithmeticMaskPopulation

/-! Source draft: factor radix and repeated-mask population over abstract model
    values, retaining all bounds, residues, and the repunit witness explicitly. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74GenericRepunitPopulation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticBinaryPopulation ArithmeticRepunit
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem radix_and_mask_population (d N J beta MC HP : V)
    (hd : 3≤d) (hN : 0<N) (hJ : J=rep d N) (hbeta : beta+1=Exp.exp d)
    (hMC : MC<Exp.exp d) (hHP : HP<Exp.exp d)
    (hMC2 : MC%2=0) (hHP8 : HP%8=4)
    (hsum : population MC+population HP=d) :
    beta*J+1=Exp.exp (d*N) ∧
      population (MC*J+1)+population (HP*J-1)=d*N+2 := by
  have hb : beta=Exp.exp d-1 := by rw [←hbeta,add_tsub_cancel_right]
  have hradix : beta*J+1=Exp.exp (d*N) := by
    rw [hJ,hb]
    exact repunit_identity d N
  have hpop := ArithmeticMaskPopulation.repeated_mask_population d N MC HP
    hd hN hMC hHP hMC2 hHP8 hsum
  refine ⟨hradix,?_⟩
  rw [hJ]
  exact hpop

#print axioms Trace74GenericRepunitPopulation.radix_and_mask_population
end Trace74GenericRepunitPopulation
