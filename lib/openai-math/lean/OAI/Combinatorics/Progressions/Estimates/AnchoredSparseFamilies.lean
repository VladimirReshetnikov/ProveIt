import OAI.Combinatorics.Progressions.Estimates.RealSubspaceIntersectionCorrections
import OAI.Combinatorics.Progressions.Geometry.SparseCoordinateCorrections

namespace OAI

section

namespace Erdos3

theorem exists_anchored_sparse_corrections
    {ι κ σ : Type*} [Fintype ι] [Fintype κ]
    (J : Submodule ℚ (Fin 4 → ι → ℚ)) (K : Finset (Fin 4))
    (v : κ → Fin 4 → ι → ℚ) (hv : Submodule.span ℚ (Set.range v) = J)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hvH : ∀ a k i, RationalHeightLE (v a k i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card (Σ _ : Fin 4, ι) : ℝ) ≤ p)
    (hK : (Fintype.card (Σ _ : K, ι) : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (p + ((p + 2) ^ 3 + (p + 2) ^ 36)) ∧
      l ∣ m ∧ ∀ (α : σ →₀ ℕ), α ≠ 0 →
      ∀ (u u₀ E E₀ Q Q₀ : (Σ _ : Fin 4, ι) → ℝ),
        u - E - Q ∈ realFourCoordinateSpan J →
        u₀ - E₀ - Q₀ ∈ realFourCoordinateSpan J →
        (∀ j : Σ _ : K, ι, u ⟨j.1, j.2⟩ = u₀ ⟨j.1, j.2⟩) →
        ‖E - E₀‖ ≤ Real.exp p / monomialScale T α →
        Q ∈ realDenominatorGrid l → Q₀ ∈ realDenominatorGrid l →
        ∃ e q : (Σ _ : Fin 4, ι) → ℝ,
          ‖e‖ ≤ (Real.exp p + Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p)) /
            monomialScale T α ∧
          q ∈ realDenominatorGrid m ∧
          (fun i => (u - u₀ - e - q) ⟨0, i⟩) ∈
            realRationalCoordinateSpan (fourSparseFirstProjection J K) := by
  obtain ⟨m, hm, hmp, hsolve⟩ := exists_sparse_coordinate_corrections J K v hv hH hl hvH
    hp hι hK hκ hHp hlp T hT
  refine ⟨l * m, Nat.mul_pos hl hm, ?_, dvd_mul_right l m, ?_⟩
  · rw [Nat.cast_mul]
    exact (mul_le_mul hlp hmp (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
  · intro α hα u u₀ E E₀ Q Q₀ hu hu₀ hanchor hE hQ hQ₀
    let ρ : (Σ _ : K, ι) → (Σ _ : Fin 4, ι) := fun j => ⟨j.1, j.2⟩
    let x := (u - E - Q) - (u₀ - E₀ - Q₀)
    let a := (E₀ - E) ∘ ρ
    let b := (Q₀ - Q) ∘ ρ
    have hx : x ∈ realFourCoordinateSpan J := Submodule.sub_mem _ hu hu₀
    have ha : ‖a‖ ≤ Real.exp p / monomialScale T α := by
      apply (pi_norm_restriction_le (E₀ - E) ρ).trans
      simpa only [norm_sub_rev] using hE
    have hb : b ∈ realDenominatorGrid l :=
      realDenominatorGrid_comp l _ (realDenominatorGrid_sub l Q₀ Q hQ₀ hQ) ρ
    have hselect (j : Σ _ : K, ι) : x ⟨j.1, j.2⟩ = a j + b j := by
      change (u ⟨j.1, j.2⟩ - E ⟨j.1, j.2⟩ - Q ⟨j.1, j.2⟩) -
        (u₀ ⟨j.1, j.2⟩ - E₀ ⟨j.1, j.2⟩ - Q₀ ⟨j.1, j.2⟩) =
        (E₀ ⟨j.1, j.2⟩ - E ⟨j.1, j.2⟩) + (Q₀ ⟨j.1, j.2⟩ - Q ⟨j.1, j.2⟩)
      rw [hanchor j]
      ring
    obtain ⟨e, q, _, _, _, _, he, hq, _, hrem⟩ := hsolve α hα a b x hx ha hb hselect
    refine ⟨E - E₀ + e, Q - Q₀ + q, ?_, ?_, ?_⟩
    · calc
        ‖E - E₀ + e‖ ≤ ‖E - E₀‖ + ‖e‖ := norm_add_le _ _
        _ ≤ Real.exp p / monomialScale T α +
            Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p) / monomialScale T α :=
          add_le_add hE he
        _ = _ := (add_div _ _ _).symm
    · simpa only [sub_neg_eq_add] using realDenominatorGrid_sub_product l m
        (Q - Q₀) (-q) (realDenominatorGrid_sub l Q Q₀ hQ hQ₀) (realDenominatorGrid_neg m hq)
    · have heq : u - u₀ - (E - E₀ + e) - (Q - Q₀ + q) = x - e - q := by
        funext j
        change u j - u₀ j - (E j - E₀ j + e j) - (Q j - Q₀ j + q j) =
          ((u j - E j - Q j) - (u₀ j - E₀ j - Q₀ j)) - e j - q j
        ring
      simpa only [heq] using hrem

end Erdos3

end

section

namespace Erdos3

theorem exists_anchored_sparse_family
    {ι κ σ η : Type*} [Fintype ι] [Fintype κ]
    (J : Submodule ℚ (Fin 4 → ι → ℚ)) (K : Finset (Fin 4))
    (v : κ → Fin 4 → ι → ℚ) (hv : Submodule.span ℚ (Set.range v) = J)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l) (hvH : ∀ a k i, RationalHeightLE (v a k i) H)
    {p : ℝ} (hp : 0 ≤ p) (hfour : (Fintype.card (Σ _ : Fin 4, ι) : ℝ) ≤ p)
    (hK : (Fintype.card (Σ _ : K, ι) : ℝ) ≤ p) (hcols : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (p + ((p + 2) ^ 3 + (p + 2) ^ 36)) ∧
      l ∣ m ∧ ∀ (α : σ →₀ ℕ), α ≠ 0 →
      ∀ (u : η → (Σ _ : Fin 4, ι) → ℝ) (β : η → ι → ℝ) (a₀ : η) (M : ℝ),
        2 * M ≤ Real.exp p →
        (∀ a i, u a ⟨0, i⟩ = β a i) →
        (∀ a (j : Σ _ : K, ι), u a ⟨j.1, j.2⟩ = u a₀ ⟨j.1, j.2⟩) →
        (∀ a, ∃ E Q : (Σ _ : Fin 4, ι) → ℝ,
          ‖E‖ ≤ M / monomialScale T α ∧ Q ∈ realDenominatorGrid l ∧
          u a - E - Q ∈ realFourCoordinateSpan J) →
        ∀ a, ∃ e q : ι → ℝ,
          ‖e‖ ≤ (Real.exp p + Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p)) /
            monomialScale T α ∧ q ∈ realDenominatorGrid m ∧
          β a - β a₀ - e - q ∈ realRationalCoordinateSpan (fourSparseFirstProjection J K) := by
  obtain ⟨m, hm, hmp, hlm, hsolve⟩ := exists_anchored_sparse_corrections J K v hv hH hl hvH
    hp hfour hK hcols hHp hlp T hT
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro α hα u β a₀ M hM hfirst hanchor hcorrect a
  obtain ⟨E₀, Q₀, hE₀, hQ₀, hu₀⟩ := hcorrect a₀
  obtain ⟨E, Q, hE, hQ, hu⟩ := hcorrect a
  have hscale : 0 < monomialScale T α :=
    monomialScale_pos T (fun i => (Real.exp_pos _).trans_le (hT i)) α
  have hdiff : ‖E - E₀‖ ≤ Real.exp p / monomialScale T α := by
    calc
      ‖E - E₀‖ ≤ ‖E‖ + ‖E₀‖ := norm_sub_le _ _
      _ ≤ M / monomialScale T α + M / monomialScale T α := add_le_add hE hE₀
      _ = (2 * M) / monomialScale T α := by ring
      _ ≤ Real.exp p / monomialScale T α := div_le_div_of_nonneg_right hM hscale.le
  obtain ⟨e, q, he, hq, hrem⟩ :=
    hsolve α hα (u a) (u a₀) E E₀ Q Q₀ hu hu₀ (hanchor a) hdiff hQ hQ₀
  refine ⟨(fun i => e ⟨0, i⟩), (fun i => q ⟨0, i⟩),
    (pi_norm_restriction_le e (fun i => ⟨0, i⟩)).trans he,
    realDenominatorGrid_comp m q hq (fun i => ⟨0, i⟩), ?_⟩
  have heq : (fun i => (u a - u a₀ - e - q) ⟨0, i⟩) =
      β a - β a₀ - (fun i => e ⟨0, i⟩) - (fun i => q ⟨0, i⟩) := by
    funext i
    simp only [Pi.sub_apply, hfirst]
  rwa [heq] at hrem

end Erdos3

end

end OAI
