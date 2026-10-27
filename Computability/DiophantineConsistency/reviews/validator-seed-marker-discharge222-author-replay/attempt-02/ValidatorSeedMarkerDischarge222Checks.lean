import ZFCinPA.ValidatorSeedMarkerDischarge222

set_option autoImplicit false
set_option Elab.async false
namespace LeanProofs.ZFCinPA.ValidatorSeedMarkerDischarge222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open scoped LO.FirstOrder.Arithmetic
open ValidatorFullSeedTheory222 ValidatorSeedMarkerDischarge222
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example : 𝚺₁-Function₁[V] domainCode via domainGraph := domain_defined
example : 𝚺₁-Function₁[V] emptyCode via emptyGraph := empty_defined
example (j : V) : shift ℒₛₑₜ (domainCode j)=domainCode (j+1) := shift_domain j
example (j : V) : shift ℒₛₑₜ (emptyCode j)=emptyCode (j+1) := shift_empty j
example (j : V) (h : Derivable seedTheory (residual (j+1))) :
    Derivable seedTheory (residual j) := discharge_succ j h
example (N : V) (h : Derivable seedTheory (residual N)) :
    Provable seedTheory (^⊥ : V) := provable_falsum_of_residual N h
example (h : Derivable seedTheory (residual (0:V))) :
    Provable seedTheory (^⊥ : V) := discharge_zero h
#print axioms domain_defined
#print axioms empty_defined
#print axioms domain_binding
#print axioms empty_binding
#print axioms shift_domain_instance
#print axioms free_negative_domain
#print axioms sideSet_succ
#print axioms residual_succ
#print axioms tag_nonempty_provable
#print axioms discharge_succ
#print axioms discharge_all
#print axioms empty_object_provable
#print axioms discharge_zero
#print axioms provable_falsum_of_residual
end LeanProofs.ZFCinPA.ValidatorSeedMarkerDischarge222Checks
