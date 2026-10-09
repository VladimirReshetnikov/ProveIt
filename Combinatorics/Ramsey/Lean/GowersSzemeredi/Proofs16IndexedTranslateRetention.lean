import GowersSzemeredi.Proofs16BohrRecentering

/-! Translation averaging for indexed configurations retains repeated
values of the index map with their full multiplicity. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem indexed_translate_filter_sum {N : Nat} [NeZero N] {I : Type*}
    (Q : Finset I) (x : I → ZMod N) (P : Finset (ZMod N)) :
    (∑ t : ZMod N, ((Q.filter fun q => x q-t ∈ P).card : Real)) =
      (Q.card : Real)*P.card := by
  have hcard (t : ZMod N) : ((Q.filter fun q => x q-t ∈ P).card : Real) =
      ∑ q ∈ Q, realSetIndicator P (x q-t) := by simp [realSetIndicator]
  simp_rw [hcard]
  rw [Finset.sum_comm]
  have hs (q : I) : (∑ t : ZMod N, realSetIndicator P (x q-t)) = P.card :=
    ((Equiv.subLeft (x q)).sum_comp (realSetIndicator P)).trans (sum_realSetIndicator P)
  simp only [hs,Finset.sum_const,nsmul_eq_mul]

/-- Some translate of a density-eta test set retains eta times the
configuration mass, independently of collisions in the index map. -/
theorem exists_dense_indexed_translate {N : Nat} [NeZero N] {I : Type*}
    (Q : Finset I) (x : I → ZMod N) (P : Finset (ZMod N))
    {eta mass : Real} (hmass : 0 ≤ mass) (hQ : mass ≤ Q.card)
    (hP : eta*N ≤ (P.card : Real)) :
    ∃ t : ZMod N, eta*mass ≤ ((Q.filter fun q => x q-t ∈ P).card : Real) := by
  have hs : (∑ _t : ZMod N, eta*mass) ≤
      ∑ t : ZMod N, ((Q.filter fun q => x q-t ∈ P).card : Real) := by
    rw [indexed_translate_filter_sum]
    simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left hP hmass
    have h2 := mul_le_mul_of_nonneg_right hQ (Nat.cast_nonneg P.card : (0 : Real) ≤ P.card)
    nlinarith only [h1,h2]
  obtain ⟨t,_,ht⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hs
  exact ⟨t,ht⟩

end LeanProofs.GowersSzemeredi
