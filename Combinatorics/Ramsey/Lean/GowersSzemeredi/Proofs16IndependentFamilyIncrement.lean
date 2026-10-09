import GowersSzemeredi.Proofs16FrequencyIndependence
import GowersSzemeredi.Proofs16SpanGeneratorInclusion

/-! Adjoin escaping values at selected indices and account exactly for
the increase of the total independent-frequency cardinality. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def extendIndependentFamily {N : Nat} {I : Type*} (D : I → Finset (ZMod N))
    (E : Finset I) (v : I → ZMod N) (i : I) : Finset (ZMod N) :=
  if i ∈ E then insert (v i) (D i) else D i

theorem extendIndependentFamily_properties {N : Nat} [NeZero N] {I : Type*}
    (D K : I → Finset (ZMod N)) (E : Finset I) (v : I → ZMod N) (R : Nat)
    (hD : ∀ i, AddDissociated (D i : Set (ZMod N)))
    (hDK : ∀ i, D i ⊆ boundedFrequencySpan (fun b : K i => (b : ZMod N)) R)
    (hvalue : ∀ i ∈ E, v i ∈ boundedFrequencySpan (fun b : K i => (b : ZMod N)) R ∧
      v i ∉ boundedFrequencySpan (fun b : D i => (b : ZMod N)) 1) :
    ∀ i, AddDissociated (extendIndependentFamily D E v i : Set (ZMod N)) ∧
      extendIndependentFamily D E v i ⊆ boundedFrequencySpan (fun b : K i => (b : ZMod N)) R ∧
      D i ⊆ extendIndependentFamily D E v i := by
  intro i
  by_cases hi : i ∈ E
  · simp only [extendIndependentFamily,if_pos hi]
    exact ⟨addDissociated_insert_of_not_mem_unit_span _ _ (hD i) (hvalue i hi).2,
      Finset.insert_subset_iff.mpr ⟨(hvalue i hi).1,hDK i⟩,Finset.subset_insert _ _⟩
  · simpa only [extendIndependentFamily,if_neg hi] using
      And.intro (hD i) (And.intro (hDK i) (Finset.Subset.refl (D i)))

theorem extendIndependentFamily_card {N : Nat} [NeZero N] {I : Type*}
    (D : I → Finset (ZMod N)) (E : Finset I) (v : I → ZMod N)
    (hescape : ∀ i ∈ E, v i ∉ boundedFrequencySpan (fun b : D i => (b : ZMod N)) 1) (i : I) :
    (extendIndependentFamily D E v i).card = (D i).card + if i ∈ E then 1 else 0 := by
  by_cases hi : i ∈ E
  · have hnot : v i ∉ D i := fun h => hescape i hi
      (addSpan_subset_boundedFrequencySpan_one (D i) (Finset.subset_addSpan h))
    simp only [extendIndependentFamily,if_pos hi,Finset.card_insert_of_notMem hnot]
  · simp only [extendIndependentFamily,if_neg hi,Nat.add_zero]

theorem extendIndependentFamily_total_card {N : Nat} [NeZero N] {I : Type*}
    (D : I → Finset (ZMod N)) (Omega E : Finset I) (v : I → ZMod N) (hE : E ⊆ Omega)
    (hescape : ∀ i ∈ E, v i ∉ boundedFrequencySpan (fun b : D i => (b : ZMod N)) 1) :
    (∑ i ∈ Omega, (extendIndependentFamily D E v i).card) =
      (∑ i ∈ Omega, (D i).card)+E.card := by
  simp_rw [extendIndependentFamily_card D E v hescape]
  rw [Finset.sum_add_distrib]
  congr 1
  have hfilter : Omega.filter (fun i => i ∈ E) = E := Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr hE)
  simp only [← Finset.sum_filter,Finset.sum_const,smul_eq_mul,mul_one,hfilter]

end LeanProofs.GowersSzemeredi
