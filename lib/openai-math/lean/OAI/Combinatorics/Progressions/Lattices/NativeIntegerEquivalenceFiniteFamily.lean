import OAI.Combinatorics.Progressions.Lattices.NativeIntegerHalving

namespace OAI

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped BigOperators

theorem exists_fin_product_budget (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ I J : Type*} [Fintype I] [Fintype J] {s : ℕ} {p : ℝ}
      (f : Fin n → I → (σ → ℤ) → ℂ) (g : Fin n → J → (σ → ℤ) → ℂ),
      0 ≤ p → (Fintype.card I : ℝ) ≤ Real.exp p → (Fintype.card J : ℝ) ≤ Real.exp p →
      (∀ i, NativeIntegerVectorEquivalence s p (f i) (g i)) →
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun a : Fin n → I => fun x => ∏ i, f i (a i) x)
        (fun b : Fin n → J => fun x => ∏ i, g i (b i) x) := by
  obtain ⟨A, _, hprod⟩ := NativeIntegerExpansion.exists_fin_prod_budget n
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + Polynomial.C n * X)
  refine ⟨C, hC, ?_⟩
  intro σ I J _ _ s p f g hp hI hJ E
  have hsum : (p + A) ^ A + n * p ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hcost : (p + A) ^ A ≤ (p + C) ^ C := by
    have hn : 0 ≤ (n : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp
    linarith
  have hnp : (n : ℝ) * p ≤ (p + C) ^ C := by
    have ha : 0 ≤ (p + A) ^ A := by positivity
    linarith
  have hIn : (Fintype.card (Fin n → I) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp p) ^ n := pow_le_pow_left₀ (Nat.cast_nonneg _) hI n
      _ = Real.exp ((n : ℝ) * p) := (Real.exp_nat_mul p n).symm
      _ ≤ _ := Real.exp_le_exp.mpr hnp
  have hJn : (Fintype.card (Fin n → J) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp p) ^ n := pow_le_pow_left₀ (Nat.cast_nonneg _) hJ n
      _ = Real.exp ((n : ℝ) * p) := (Real.exp_nat_mul p n).symm
      _ ≤ _ := Real.exp_le_exp.mpr hnp
  refine ⟨hIn, hJn, ?_⟩
  intro a b
  obtain ⟨F⟩ := hprod (σ := σ) (w := fun _ : σ => 1) (s := s)
    (fun k x => f k (a k) x * star (g k (b k) x)) hp
    (fun k => (E k).expansion (a k) (b k))
  have heq : (fun x => ∏ k, f k (a k) x * star (g k (b k) x)) =
      (fun x => (∏ k, f k (a k) x) * star (∏ k, g k (b k) x)) := by
    funext x
    simp only [Finset.prod_mul_distrib, star_prod]
  exact ⟨heq ▸ F.mono hcost⟩

end Erdos3.NativeIntegerVectorEquivalence

end

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped BigOperators

theorem conjugationPower {σ I J : Type*} [Fintype I] [Fintype J] {s : ℕ} {p : ℝ}
    {f : I → (σ → ℤ) → ℂ} {g : J → (σ → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s p f g) (n : ℕ) :
    NativeIntegerVectorEquivalence s p
      (fun i x => Erdos3.conjugationPower n (f i x))
      (fun j x => Erdos3.conjugationPower n (g j x)) := by
  induction n with
  | zero => exact E
  | succ n ih => exact ih.conjugate

theorem exists_finite_product_budget (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ I J : Type*} [Fintype I] [Fintype J] {s : ℕ} {p : ℝ}
      (f : ι → I → (σ → ℤ) → ℂ) (g : ι → J → (σ → ℤ) → ℂ),
      0 ≤ p → (Fintype.card I : ℝ) ≤ Real.exp p → (Fintype.card J : ℝ) ≤ Real.exp p →
      (∀ i, NativeIntegerVectorEquivalence s p (f i) (g i)) →
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun a : ι → I => fun x => ∏ i, f i (a i) x)
        (fun b : ι → J => fun x => ∏ i, g i (b i) x) := by
  obtain ⟨C, hC, hprod⟩ := exists_fin_product_budget (Fintype.card ι)
  refine ⟨C, hC, ?_⟩
  intro σ I J _ _ s p f g hp hI hJ E
  classical
  let e := (Fintype.equivFin ι).symm
  have F := hprod (fun j => f (e j)) (fun j => g (e j)) hp hI hJ (fun j => E (e j))
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Fintype.card_fun, Fintype.card_fin] using F.left_dimension
  · simpa only [Fintype.card_fun, Fintype.card_fin] using F.right_dimension
  · intro a b
    have h := F.expansion (fun j => a (e j)) (fun j => b (e j))
    have hf (x : σ → ℤ) : (∏ j, f (e j) (a (e j)) x) = ∏ i, f i (a i) x :=
      e.prod_comp (fun i => f i (a i) x)
    have hg (x : σ → ℤ) : (∏ j, g (e j) (b (e j)) x) = ∏ i, g i (b i) x :=
      e.prod_comp (fun i => g i (b i) x)
    simpa only [hf, hg] using h

end Erdos3.NativeIntegerVectorEquivalence

end

end OAI
