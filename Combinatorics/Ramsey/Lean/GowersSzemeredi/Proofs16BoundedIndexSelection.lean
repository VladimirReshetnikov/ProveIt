import GowersSzemeredi.Proofs16GlobalCoherentAnchors

/-! Bounded index sets have codes of length `K` over `m+1` symbols.
Pigeonholing those codes retains whole configurations with one common
index set, including when `m < K` or the index set is empty. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def boundedIndexCode {m : Nat} (K : Nat) (I : Finset (Fin m)) : Fin K → Option (Fin m) :=
  fun j => (I.sort (· ≤ ·))[j.val]?

theorem boundedIndexCode_injective_on {m K : Nat} {I J : Finset (Fin m)}
    (hI : I.card ≤ K) (hJ : J.card ≤ K) (he : boundedIndexCode K I = boundedIndexCode K J) : I = J := by
  have hl : I.sort (· ≤ ·) = J.sort (· ≤ ·) := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < K
    · exact congrFun he ⟨i,hi⟩
    · have hli : (I.sort (· ≤ ·)).length ≤ i := by rw [Finset.length_sort]; omega
      have hlj : (J.sort (· ≤ ·)).length ≤ i := by rw [Finset.length_sort]; omega
      rw [List.getElem?_eq_none hli,List.getElem?_eq_none hlj]
  have ht := congrArg List.toFinset hl
  simpa only [Finset.sort_toFinset] using ht

theorem exists_common_bounded_index_set {X : Type*} {m K : Nat}
    (Q : Finset X) (I : X → Finset (Fin m)) (hQ : Q.Nonempty)
    (hI : ∀ q ∈ Q, (I q).card ≤ K) :
    ∃ (J : Finset (Fin m)) (R : Finset X), J.card ≤ K ∧ R ⊆ Q ∧
      Q.card ≤ (m+1)^K*R.card ∧ R.Nonempty ∧ ∀ q ∈ R, I q = J := by
  classical
  let code := fun q => boundedIndexCode K (I q)
  have hsum : (∑ c : Fin K → Option (Fin m), (Q.filter fun q => code q = c).card) = Q.card := by
    simpa only [Finset.mem_univ,Finset.filter_true] using
      Finset.sum_card_fiberwise_eq_card_filter Q Finset.univ code
  have hle : (∑ _c : Fin K → Option (Fin m), Q.card) ≤
      ∑ c : Fin K → Option (Fin m), Fintype.card (Fin K → Option (Fin m))*(Q.filter fun q => code q = c).card := by
    rw [← Finset.mul_sum,hsum]
    simp
  obtain ⟨c,_,hc⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hle
  let R := Q.filter fun q => code q = c
  have hcount : Q.card ≤ (m+1)^K*R.card := by
    simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_option,R] using hc
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
  apply boundedIndexCode_injective_on (hI q hqQ) (hI q0 hq0Q)
  exact hcode.trans (Finset.mem_filter.mp hq0).2.symm

end LeanProofs.GowersSzemeredi
