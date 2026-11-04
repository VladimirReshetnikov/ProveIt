import DiophantineConsistency.Compact44.RotationStraddling
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace RotationCoverage
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem coverage (L e b w : V) (hwindow : b+w ≤ L) :
    (∃ s u, b=e+s ∧ L=e+(s+w+u)) ∨
    (∃ u, e=b+w+u) ∨
    (∃ a t, a<w ∧ e=b+a ∧ L=e+((w-a)+t)) := by
  by_cases heb : e≤b
  · left
    have hs : e+(b-e)=b := add_tsub_cancel_of_le heb
    have hu : b+w+(L-(b+w))=L := add_tsub_cancel_of_le hwindow
    refine ⟨b-e,L-(b+w), hs.symm, ?_⟩
    calc
      L = b+w+(L-(b+w)) := hu.symm
      _ = (e+(b-e))+w+(L-(b+w)) := by rw [hs]
      _ = e+((b-e)+w+(L-(b+w))) := by ring
  · have hbe : b<e := not_le.mp heb
    by_cases hwrap : b+w≤e
    · right; left
      exact ⟨e-(b+w), (add_tsub_cancel_of_le hwrap).symm⟩
    · right; right
      have hew : e<b+w := not_le.mp hwrap
      have hba : b+(e-b)=e := add_tsub_cancel_of_le (le_of_lt hbe)
      have ha : e-b<w := (add_lt_add_iff_left b).mp (by rw [hba]; exact hew)
      have hs : (b+(e-b))+(w-(e-b)) = b+w := by
        calc
          _ = b+((e-b)+(w-(e-b))) := by ring
          _ = b+w := by rw [add_tsub_cancel_of_le (le_of_lt ha)]
      have ht : b+w+(L-(b+w))=L := add_tsub_cancel_of_le hwindow
      refine ⟨e-b,L-(b+w),ha,hba.symm,?_⟩
      calc
        L = b+w+(L-(b+w)) := ht.symm
        _ = (b+(e-b))+((w-(e-b))+(L-(b+w))) := by
          rw [← add_assoc, hs]
        _ = e+((w-(e-b))+(L-(b+w))) := by rw [hba]

theorem digit_index (s : V) : ∃ q r, s=67*q+r ∧ r<67 := by
  refine ⟨s/67,s%67,?_, mod_lt _ (by norm_num)⟩
  exact (div_add_mod s 67).symm
#print axioms RotationCoverage.coverage
#print axioms RotationCoverage.digit_index
end RotationCoverage
