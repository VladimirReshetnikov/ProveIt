import PA194PAeqTargetInventory
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeq
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (U : Theory language) [U.Δ₁]

theorem target_axiom_witness (σ : Sentence language) (hσ : σ ∈ U) :
    Proof U (Bootstrapping.axm {⌜σ⌝} ⌜σ⌝ : V) (⌜σ⌝ : V) := by
  refine ⟨by simp, Derivation.axm ?_ (by simp) ?_⟩
  · simp
  · simpa using hσ

theorem target_axiom_provable (σ : Sentence language) (hσ : σ ∈ U) :
    Provable U (⌜σ⌝ : V) := ⟨_,target_axiom_witness U σ hσ⟩

def targetFixedSentences : List (Sentence language) :=
  fixedAxioms.map (fun p => p.univCl)
def targetFixedTheory : Theory language := fun σ => σ ∈ targetFixedSentences
noncomputable instance targetFixedTheory_delta1 : targetFixedTheory.Δ₁ :=
  Theory.Δ₁.ofList targetFixedSentences

theorem zeroNotSucc_mem : zeroNotSucc.univCl ∈ targetFixedTheory := by
  change zeroNotSucc.univCl ∈ targetFixedSentences
  apply List.mem_map.mpr
  exact ⟨zeroNotSucc, by simp [fixedAxioms], rfl⟩

theorem targetFixed_subset_ordinary : targetFixedTheory ⊆ ordinaryPAeq := by
  intro σ hσ
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hσ
  exact ⟨p, PAeqAxiom.fixed p hp, rfl⟩

theorem zeroNotSucc_mem_ordinary : zeroNotSucc.univCl ∈ ordinaryPAeq :=
  targetFixed_subset_ordinary zeroNotSucc_mem

theorem zeroNotSucc_witness :
    Proof targetFixedTheory
      (Bootstrapping.axm {⌜zeroNotSucc.univCl⌝} ⌜zeroNotSucc.univCl⌝ : V)
      (⌜zeroNotSucc.univCl⌝ : V) :=
  target_axiom_witness targetFixedTheory _ zeroNotSucc_mem

#print axioms target_axiom_witness
#print axioms target_axiom_provable
#print axioms zeroNotSucc_mem
#print axioms targetFixed_subset_ordinary
#print axioms zeroNotSucc_mem_ordinary
#print axioms zeroNotSucc_witness
end PA194PAeq
