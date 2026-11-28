import GRHArticle.ProgressionFree.PolynomialLayerCharging

/-!
# Weighted count of polynomial charges

A polynomial in a source layer splits one unit of mass equally among
the primes of its assigned degree. Each missing target absorbs the
nonexceptional mass from all degrees together. Exceptional targets are
counted at most once per prime degree.
-/

namespace GRHArticle.ProgressionFree

open Polynomial Finset
open scoped Classical

variable {F : Type*} [Field F]

/-- Count all sources by missing targets and the exceptional sets for
individual prime degrees. The degree budgets may be any nonnegative
weights of sum at most one. -/
theorem card_polynomialSources_le_targets_add_exceptional
    {E : Set F[X]} {C : Set ℕ} (hC : ThreeAPFree C) (N : ℕ)
    (A G : Finset F[X]) (I : Finset ℕ) (step : F[X] → ℕ) (S X : ℕ → Finset F[X])
    (θ : ℕ → ℝ) (hθ : ∀ d ∈ I, 0 ≤ θ d) (hbudget : ∑ d ∈ I, θ d ≤ 1)
    (hA : ∀ f ∈ A, f ≠ 0 ∧ f.natDegree ≤ N ∧ step f ∈ I ∧
      PolynomialLayerStep C (N-f.natDegree) (step f))
    (hS : ∀ d ∈ I, (S d).Nonempty ∧ ∀ p ∈ S d, p ≠ 0 ∧ p.natDegree = d)
    (hG : ∀ f ∈ A, ∀ p ∈ S (step f), polynomialMissingTarget E f p ∈ G)
    (hX : ∀ d ∈ I, ∀ g ∈ G, g ∉ X d → ((S d).filter (· ∣ g)).card ≤ θ d * (S d).card) :
    (A.card : ℝ) ≤ G.card + ∑ d ∈ I, ((X d).card : ℝ) := by
  let B (d : ℕ) := A.filter (fun f ↦ step f = d)
  let D (d : ℕ) := (B d) ×ˢ (S d)
  let target (x : F[X] × F[X]) := polynomialMissingTarget E x.1 x.2
  let count (d : ℕ) (g : F[X]) := ((D d).filter (fun x ↦ target x = g)).card
  have hmaps (d : ℕ) : ((D d : Finset _) : Set _).MapsTo target G := by
    intro x hx
    obtain ⟨hf, hp⟩ := mem_product.mp hx
    obtain ⟨ha, he⟩ := mem_filter.mp hf
    exact hG _ ha _ (he ▸ hp)
  have htotal (d : ℕ) (hd : d ∈ I) :
      ((B d).card : ℝ) = ∑ g ∈ G, (count d g : ℝ) / (S d).card := by
    have hc : (B d).card * (S d).card = ∑ g ∈ G, count d g := by
      simpa only [D,card_product] using card_eq_sum_card_fiberwise (hmaps d)
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    rw [← div_eq_mul_inv, eq_div_iff (by exact_mod_cast (hS d hd).1.card_pos.ne')]
    exact_mod_cast hc
  have hfiber (d : ℕ) (hd : d ∈ I) (g : F[X]) : count d g ≤ ((S d).filter (· ∣ g)).card := by
    apply card_polynomialMissingTarget_fiber_le hC (N := N) (S d) (D d) (hS d hd).2 _ g
    intro x hx
    obtain ⟨hf,hp⟩ := mem_product.mp hx
    obtain ⟨ha,he⟩ := mem_filter.mp hf
    obtain ⟨hf₀, hn, _, hstep⟩ := hA x.1 ha
    exact ⟨hf₀, hn, hp, he ▸ hstep⟩
  have hweight (d : ℕ) (hd : d ∈ I) (g : F[X]) (hg : g ∈ G) :
      (count d g : ℝ) / (S d).card ≤ θ d + (if g ∈ X d then 1 else 0) := by
    have hpos : (0:ℝ) < (S d).card := by exact_mod_cast (hS d hd).1.card_pos
    have hc : (count d g : ℝ) ≤ ((S d).filter (· ∣ g)).card := by exact_mod_cast hfiber d hd g
    by_cases h : g ∈ X d
    · rw [if_pos h]
      have hOne : (count d g : ℝ) / (S d).card ≤ 1 := (div_le_one hpos).mpr
        (by exact_mod_cast (hfiber d hd g).trans (card_filter_le ..))
      linarith only [hOne,hθ d hd]
    · rw [if_neg h,add_zero]
      exact (div_le_iff₀ hpos).mpr (hc.trans (hX d hd g hg h))
  have hcard : A.card = ∑ d ∈ I, (B d).card :=
    card_eq_sum_card_fiberwise (fun f hf ↦ (hA f hf).2.2.1)
  calc
    (A.card : ℝ) = ∑ d ∈ I, ∑ g ∈ G, (count d g : ℝ) / (S d).card := by
      rw [hcard,Nat.cast_sum]
      exact sum_congr rfl htotal
    _ ≤ ∑ d ∈ I, ∑ g ∈ G, (θ d + (if g ∈ X d then 1 else 0)) :=
      sum_le_sum fun d hd ↦ sum_le_sum fun g hg ↦ hweight d hd g hg
    _ = G.card * (∑ d ∈ I, θ d) + ∑ d ∈ I, (((G ∩ X d).card : ℕ) : ℝ) := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := add_le_add (mul_le_of_le_one_right (by positivity) hbudget) (sum_le_sum fun d _ ↦
      Nat.cast_le.mpr (card_le_card fun g hg ↦ (mem_inter.mp hg).2))

end GRHArticle.ProgressionFree
