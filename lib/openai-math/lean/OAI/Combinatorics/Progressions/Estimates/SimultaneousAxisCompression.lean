import OAI.Combinatorics.Progressions.Polynomial.PolynomialAxisCompression

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_simultaneous_axis_compression (s : ℕ) (hs : 1 ≤ s)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type*} [Fintype I] {N n : ℕ} [NeZero N] {p L g : ℝ},
      2 ≤ p → 2 ≤ L → (n : ℝ) ≤ p → 1 ≤ g → g ≤ Real.exp p →
      Odd N → Real.exp ((p + L + 2) ^ C) ≤ N →
      ∀ f : I → Fin n → ZMod N → ℝ, (∀ i j x, 0 ≤ f i j x ∧ f i j x ≤ Real.exp p) →
      (∀ i j, CyclicNiltestUpperComparison.{0} s N ((p + L + 2) ^ C)
        (Real.exp (-((p + L + 2) ^ C))) (f i j) (fun _ => g)) →
      ∃ S : Finset (Fin n → ZMod N),
        (S.card : ℝ) ≤ (Fintype.card I : ℝ) * Real.exp (-L) * (N : ℝ) ^ n ∧
        (∀ i t y, 0 ≤ normalizedAxisProduct (f i) t ((1 + epsilon) * g) y ∧
          normalizedAxisProduct (f i) t ((1 + epsilon) * g) y ≤ Real.exp (p ^ 2)) ∧
        ∀ t, t ∉ S → ∀ i, CyclicNiltestUpperComparison.{0} (s - 1) N L (Real.exp (-L))
          (normalizedAxisProduct (f i) t ((1 + epsilon) * g)) (fun _ => 1) := by
  classical
  obtain ⟨C, hC, hcompress⟩ := exists_polynomial_axis_compression s hs hepsilon hepsilon1
  refine ⟨C, hC, ?_⟩
  intro I _ N n _ p L g hp hL hn hg hgb hodd hN f hf hcompare
  have hex (i : I) := hcompress hp hL hn hg hgb hodd hN (f i) (hf i) (hcompare i)
  choose S hS hcap hgood using hex
  let E := Finset.univ.biUnion S
  have hsub (i : I) : S i ⊆ E := by
    intro t ht
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ht⟩
  refine ⟨E, ?_, hcap, ?_⟩
  · calc
      (E.card : ℝ) ≤ ∑ i, ((S i).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le : E.card ≤ ∑ i, (S i).card)
      _ ≤ ∑ _i : I, Real.exp (-L) * (N : ℝ) ^ n := Finset.sum_le_sum (fun i _ => hS i)
      _ = _ := by simp [mul_assoc]
  · intro t ht i
    exact hgood i t (fun hi => ht (hsub i hi))

end Erdos3

end

end OAI
