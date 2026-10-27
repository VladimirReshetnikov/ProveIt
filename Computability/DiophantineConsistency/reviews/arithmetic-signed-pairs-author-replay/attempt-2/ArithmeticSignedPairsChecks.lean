import DiophantineConsistency.ArithmeticSignedPairs

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticSignedPairsChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticSignedPairs
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (p q : Pair V) : magnitude (multiply p q)=magnitude p*magnitude q := magnitude_multiply p q
example (u z : V) : magnitude (u+z,z)=u := magnitude_of_add (by ring)
example (u z : V) : magnitude (z,u+z)=u := by
  change magnitude (swap (u+z,z))=u
  rw [magnitude_swap]
  exact magnitude_of_add (by ring)
example (z : V) : magnitude (z,z)=0 := by simp [magnitude]
example : magnitude (natural (0:V))=0 := by simp [magnitude,natural]
example : magnitude (swap (natural (1:V)))=1 := by simp [magnitude,natural,swap]
example (p q r s t : Pair V)
    (h : Equivalent (product5 p q r s t) (natural (1:V)))
    (hp : p.1+1≠p.2) (hq : q.1+1≠q.2) (hr : r.1+1≠r.2) (ht : t.1+1≠t.2) :
    s.1=s.2+1 := (product5_positive h hp hq hr ht).2.2.2.1
example (a : V) (ha : 0<a) (p q r s t : Pair V)
    (h : Equivalent (scale a (product5 p q r s t)) (natural a))
    (hp : p.1+1≠p.2) (hq : q.1+1≠q.2) (hr : r.1+1≠r.2) (ht : t.1+1≠t.2) :
    p.1=p.2+1 ∧ q.1=q.2+1 ∧ r.1=r.2+1 ∧ s.1=s.2+1 ∧ t.1=t.2+1 :=
  scaled_product5_positive a ha h hp hq hr ht

#print axioms equivalent_trans
#print axioms equivalent_multiply
#print axioms magnitude_multiply
#print axioms product5_magnitudes
#print axioms positive_of_magnitude_one
#print axioms product5_positive
#print axioms scaled_product5_positive
end DiophantineConsistency.ArithmeticSignedPairsChecks
