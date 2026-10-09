import GowersSzemeredi.Proofs16PopularCommonIndexAgreement

/-! Fix the exact bounded index set at each position of a configuration.
The number of patterns is at most (m+1)^(K*ell), including empty sets. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem exists_common_bounded_index_pattern {X : Type*} {m K ell : Nat}
    (Q : Finset X) (I : X → Fin ell → Finset (Fin m)) (hQ : Q.Nonempty)
    (hI : ∀ q ∈ Q, ∀ j, (I q j).card ≤ K) :
    ∃ (J : Fin ell → Finset (Fin m)) (R : Finset X), (∀ j, (J j).card ≤ K) ∧ R ⊆ Q ∧
      Q.card ≤ (m+1)^(K*ell)*R.card ∧ R.Nonempty ∧ ∀ q ∈ R, I q = J := by
  let code := fun q j => boundedIndexCode K (I q j)
  have hsum : (∑ c : Fin ell → Fin K → Option (Fin m), (Q.filter fun q => code q = c).card) = Q.card := by
    simpa only [Finset.mem_univ,Finset.filter_true] using
      Finset.sum_card_fiberwise_eq_card_filter Q Finset.univ code
  have hle : (∑ _c : Fin ell → Fin K → Option (Fin m), Q.card) ≤
      ∑ c : Fin ell → Fin K → Option (Fin m),
        Fintype.card (Fin ell → Fin K → Option (Fin m))*(Q.filter fun q => code q = c).card := by
    rw [← Finset.mul_sum,hsum]
    simp
  obtain ⟨c,_,hc⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hle
  let R := Q.filter fun q => code q = c
  have hcount : Q.card ≤ (m+1)^(K*ell)*R.card := by
    simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_option,R,pow_mul] using hc
  have hR : R.Nonempty := by
    apply Finset.card_pos.mp
    have hq := Finset.card_pos.mpr hQ
    by_contra hn
    have he : R.card = 0 := by omega
    simp only [he,Nat.mul_zero] at hcount
    omega
  obtain ⟨q0,hq0⟩ := hR
  have hq0Q := (Finset.mem_filter.mp hq0).1
  refine ⟨I q0,R,hI q0 hq0Q,Finset.filter_subset _ _,hcount,⟨q0,hq0⟩,?_⟩
  intro q hq
  obtain ⟨hqQ,hcode⟩ := Finset.mem_filter.mp hq
  funext j
  apply boundedIndexCode_injective_on (hI q hqQ j) (hI q0 hq0Q j)
  exact congrFun (hcode.trans (Finset.mem_filter.mp hq0).2.symm) j

end LeanProofs.GowersSzemeredi
