import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem polynomial_support_card_le {σ R : Type*} [Fintype σ] [CommSemiring R]
    (p : MvPolynomial σ R) {s : ℕ} (hp : p.totalDegree ≤ s) :
    p.support.card ≤ (s + 1) * (Fintype.card σ + 1) ^ s := by
  classical
  let code : p.support → (Σ n : Fin (s + 1), Fin n.val → σ) := fun m =>
    ⟨⟨m.val.toMultiset.toList.length, by
      rw [Multiset.length_toList, Finsupp.card_toMultiset]
      exact Nat.lt_succ_of_le ((MvPolynomial.le_totalDegree m.property).trans hp)⟩,
      m.val.toMultiset.toList.get⟩
  have hinj : Function.Injective code := by
    intro m n hmn
    have hl := congrArg (fun z : Σ n : Fin (s + 1), Fin n.val → σ => List.ofFn z.2) hmn
    change List.ofFn m.val.toMultiset.toList.get = List.ofFn n.val.toMultiset.toList.get at hl
    rw [List.ofFn_get, List.ofFn_get] at hl
    have hm := congrArg (fun l : List σ => (l : Multiset σ)) hl
    rw [Multiset.coe_toList, Multiset.coe_toList] at hm
    apply Subtype.ext
    ext x
    have hx := congrArg (fun m : Multiset σ => m.count x) hm
    simpa only [Finsupp.count_toMultiset] using hx
  have hcard := Fintype.card_le_of_injective code hinj
  simp only [Fintype.card_coe, Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin] at hcard
  calc
    p.support.card ≤ ∑ n : Fin (s + 1), Fintype.card σ ^ n.val := hcard
    _ ≤ ∑ _n : Fin (s + 1), (Fintype.card σ + 1) ^ s := by
      apply Finset.sum_le_sum
      intro n _
      exact (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
        (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt_succ n.isLt))
    _ = (s + 1) * (Fintype.card σ + 1) ^ s := by simp

end Erdos3

end

end OAI
