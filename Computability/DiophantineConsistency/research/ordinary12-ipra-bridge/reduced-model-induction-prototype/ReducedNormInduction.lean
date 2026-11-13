import DiophantineConsistency.ReducedNormState
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ReducedNormInduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticGcdNormalization
open ReducedNormState
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_impossible {r a b : V} (hb : 0<b)
    (hn : (r+1)*((0:V)*b)*((0:V)*b)=r*(a*a)+b*b) : False := by
  have hb2 : 0<b*b := mul_pos hb hb
  have hp : 0<r*(a*a)+b*b := add_pos_of_nonneg_of_pos (by simp) hb2
  have he : (0:V)=r*(a*a)+b*b := by simpa using hn
  rw [←he] at hp
  exact (Arithmetic.lt_irrefl (0:V)) hp

theorem unit_index_denominator {r a b : V} (hr : 0<r) (hu : Bez a b 1)
    (hn : (r+1)*((1:V)*b)*((1:V)*b)=r*(a*a)+b*b) : b=1 := by
  have he : r*(b*b)+b*b=r*(a*a)+b*b := by calc
    r*(b*b)+b*b=(r+1)*((1:V)*b)*((1:V)*b) := by ring
    _=r*(a*a)+b*b := hn
  have hs : b*b=a*a := mul_left_cancel₀ (ne_of_gt hr) (add_right_cancel he)
  have hba : b=a := by
    apply le_antisymm
    · by_contra hnle
      have hlt : a<b := lt_of_not_ge hnle
      have hsq : a*a<b*b := mul_self_lt_mul_self (Arithmetic.zero_le a) hlt
      rw [hs] at hsq
      exact (Arithmetic.lt_irrefl _) hsq
    · by_contra hnle
      have hlt : b<a := lt_of_not_ge hnle
      have hsq : b*b<a*a := mul_self_lt_mul_self (Arithmetic.zero_le b) hlt
      rw [hs] at hsq
      exact (Arithmetic.lt_irrefl _) hsq
  have hdiv : b∣(1:V) := bez_divisor hu (by rw [hba]) (dvd_refl b)
  exact Arithmetic.dvd_antisymm hdiv (one_dvd b)

theorem reduced_denominator_one {r v a b : V} (hr : 0<r) (hb : 0<b)
    (hu : Bez a b 1) (hn : (r+1)*(v*b)*(v*b)=r*(a*a)+b*b) : b=1 := by
  by_contra hbne
  let P : V → Prop := fun k => ∃ x : V, Bez x b 1 ∧
    (r+1)*(k*b)*(k*b)=r*(x*x)+b*b
  have hP : 𝚺₁-Predicate P := by dsimp [P,Bez]; definability
  have hex : P v := ⟨a,hu,hn⟩
  obtain ⟨k,hk,hmin⟩ := InductionOnHierarchy.least_number 𝚺 1 hP hex
  obtain ⟨x,hbez,hnorm⟩ := hk
  have hkpos : 0<k := by
    by_contra hnpos
    have hk0 : k=0 := le_antisymm (le_of_not_gt hnpos) (Arithmetic.zero_le k)
    subst k
    exact zero_impossible hb hnorm
  have hkne : k≠1 := by
    intro hk1
    subst k
    exact hbne (unit_index_denominator hr hbez hnorm)
  have hkgt : 1<k := lt_of_le_of_ne (pos_iff_one_le.mp hkpos) (Ne.symm hkne)
  obtain ⟨s,j,t,hs,hjpos,hjlt,htbez,htnorm,_,_⟩ := smaller_reduced_state hr hkgt hb hbez hnorm
  exact hmin j hjlt ⟨t,htbez,htnorm⟩
end ReducedNormInduction
#print axioms ReducedNormInduction.zero_impossible
#print axioms ReducedNormInduction.unit_index_denominator
#print axioms ReducedNormInduction.reduced_denominator_one
