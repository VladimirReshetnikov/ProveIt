import OAI.Combinatorics.Progressions.Geometry.CoordinateTreeCardBudget
import OAI.Combinatorics.Progressions.Lattices.CountedSlicePrimeStability
import OAI.Combinatorics.Progressions.Lattices.ResidueStableBoxCongruence
import OAI.Combinatorics.Progressions.Lattices.StablePrimeUpperComparison

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

universe u v w

theorem exists_baseline_marginal_stability (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {σ : Type u} {L : Type v}
      [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [TopologicalSpace (ℝ ⊗[ℚ] L)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p δ : ℝ),
    2 ≤ p → (Fintype.card σ : ℝ) ≤ p → 0 < δ → δ⁻¹ ≤ Real.exp p →
    ∀ T : D.Niltest (fun _ : σ => 1), T.ComplexityLE p →
    ∀ (prime power : ι → ℕ), (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp p) →
    ∀ (mandatory : Finset ι) (r : ℕ), (mandatory.card : ℝ) ≤ p → (r : ℝ) ≤ p →
    ∀ (H N : σ → ℕ) (lo a : σ → ℤ) (M : ℕ), 0 < M → (∀ j, N j ≤ H j) →
    (∀ z ∈ translatedIntegerBox lo N, (T.eval z).im = 0 ∧ 0 ≤ (T.eval z).re ∧ (T.eval z).re ≤ 1) →
    (∀ j, Real.exp (-p) * (H j : ℝ) ≤
      (residueIndexLength (lo j) (lo j + N j) M (a j) : ℝ)) →
    (∀ j, Real.exp ((p + 2) ^ E) ≤ (H j : ℝ)) →
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (prime i ^ power i)), ∃ depth : ℕ,
      (depth : ℝ) ≤ (p + 2) ^ E ∧
      CoordinateDecisionTree.Valid
        (fun I x => mandatory ⊆ I ∧
          ResiduePrimeCoordinateStable T.eval lo N M a (fun i => prime i ^ power i) r δ I x)
        ∅ (fun _ _ => 0) tree depth := by
  obtain ⟨E, hE, hstability⟩ := exists_counted_slice_prime_stability.{u, v, w} s
  refine ⟨E, hE, ?_⟩
  intro ι σ L _ _ _ _ _ _ _ _ _ _ d D p δ hp hσ hδ hδinv T hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr H N lo a M hM hNH hunit hcount hlarge
  obtain ⟨tree, depth, hdepth, htree⟩ := hstability D p δ hp hσ hδ hδinv T.intervalClip
    T.intervalClip_unitInterval ((T.intervalClip_complexityLE p).mpr hcomplexity)
    prime power hprime hinj hprimeBound mandatory r hmandatory hr H N lo a M hM hNH hcount hlarge
  refine ⟨tree, depth, hdepth, htree.map ?_⟩
  intro I x hx
  exact ⟨hx.1, hx.2.congr_on_box (fun z hz => T.intervalClip_eval z (hunit z hz))⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

universe u v w

theorem exists_baseline_stable_slice_costs (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {σ : Type u} {L : Type v}
      [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [TopologicalSpace (ℝ ⊗[ℚ] L)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p δ : ℝ),
    2 ≤ p → (Fintype.card σ : ℝ) ≤ p → 0 < δ → δ⁻¹ ≤ Real.exp p →
    ∀ T : D.Niltest (fun _ : σ => 1), T.ComplexityLE p →
    ∀ (prime power : ι → ℕ), (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp p) →
    ∀ (mandatory : Finset ι) (r : ℕ), (mandatory.card : ℝ) ≤ p → (r : ℝ) ≤ p →
    ∀ (H N : σ → ℕ) (lo a : σ → ℤ) (M : ℕ), 0 < M → (∀ j, N j ≤ H j) →
    (∀ z ∈ translatedIntegerBox lo N, (T.eval z).im = 0 ∧ 0 ≤ (T.eval z).re ∧ (T.eval z).re ≤ 1) →
    ResidueSliceLogCostLE H lo N M a p →
    (∀ j, Real.exp ((p + 2) ^ E) ≤ (H j : ℝ)) →
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (prime i ^ power i)), ∃ depth : ℕ,
      (depth : ℝ) ≤ (p + 2) ^ E ∧
      CoordinateDecisionTree.Valid
        (fun I x => mandatory ⊆ I ∧
          ResiduePrimeCoordinateStable T.eval lo N M a (fun i => prime i ^ power i) r δ I x ∧
          ∀ J : Finset ι, J.card ≤ r → ∀ u : σ → ℤ,
            ResidueSliceLogCostLE H lo N (M.lcm (∏ i ∈ I ∪ J, prime i ^ power i)) u ((p + 2) ^ E))
        ∅ (fun _ _ => 0) tree depth := by
  obtain ⟨E₀, _, hstability⟩ := exists_baseline_marginal_stability.{u, v, w} s
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + 2 + X * ((X + 2) ^ E₀ + X)) + 2
  let P := (X + 2) ^ E₀ + Q + X + 2
  obtain ⟨E, hE, hpoly⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨E, hE, ?_⟩
  intro ι σ L _ _ _ _ _ _ _ _ _ _ d D p δ hp hσ hδ hδinv T hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr H N lo a M hM hNH hunit hcount hlarge
  let B := (p + 2) ^ E₀
  let C := p + (p + 2 + p * (B + p)) + 2
  have hp0 : 0 ≤ p := by linarith
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have hpower : B + C + p + 2 ≤ (p + 2) ^ E := by
    simpa [X, Q, P, B, C, Polynomial.eval₂_pow] using hpoly p hp0
  have hB : B ≤ (p + 2) ^ E := by linarith
  have hC : C ≤ (p + 2) ^ E := by linarith
  have hsmall : p + 2 ≤ (p + 2) ^ E := by linarith
  obtain ⟨tree, depth, hdepth, htree⟩ := hstability D p δ hp hσ hδ hδinv T hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr H N lo a M hM hNH hunit hcount
    (fun j => (Real.exp_le_exp.mpr hB).trans (hlarge j))
  have hwidth : ∀ j, Real.exp (-p) * (H j : ℝ) ≤ (N j : ℝ) := by
    intro j
    exact (hcount j).trans (by exact_mod_cast residueIndexLength_le_width (lo j) (a j) (N j) M hM)
  have hcardTree := htree.with_card_budget depth (by simp)
  refine ⟨tree, depth, hdepth.trans hB, hcardTree.map ?_⟩
  intro I x hx
  refine ⟨hx.1.1, hx.1.2, ?_⟩
  intro J hJ u j
  have hcard : ((I ∪ J).card : ℝ) ≤ B + p := by
    have hunion : ((I ∪ J).card : ℝ) ≤ (I.card : ℝ) + J.card := by
      exact_mod_cast Finset.card_union_le I J
    have hI : (I.card : ℝ) ≤ depth := by exact_mod_cast hx.2
    have hJR : (J.card : ℝ) ≤ r := by exact_mod_cast hJ
    linarith
  have hinitial := residue_slice_counting_cost (lo j) (a j) (H j) (N j) M p hM (hNH j)
    ((Real.exp_le_exp.mpr hsmall).trans (hlarge j)) (hcount j)
  have hcost := residuePrimeCell_log_cost H N lo u M hM
    (fun i => prime i ^ power i) (fun i => pow_pos (hprime i).pos _) (I ∪ J)
    (p + 2) p p (B + p) hp0 hinitial.1 hprimeBound hcard hwidth
    (fun k => (Real.exp_le_exp.mpr hC).trans (hlarge k))
  exact (hcost.mono hC) j

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

universe u v w

theorem exists_baseline_comparison_tree (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {σ : Type u} {L : Type v}
      [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [TopologicalSpace (ℝ ⊗[ℚ] L)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p δ : ℝ),
    2 ≤ p → (Fintype.card σ : ℝ) ≤ p → 0 < δ → δ⁻¹ ≤ Real.exp p →
    ∀ g : D.Niltest (fun _ : σ => 1), g.ComplexityLE p →
    ∀ (prime power : ι → ℕ), (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp p) →
    ∀ (mandatory : Finset ι) (r : ℕ), (mandatory.card : ℝ) ≤ p → (r : ℝ) ≤ p →
    ∀ (parent : σ → ℤ) (H N : σ → ℕ) (lo a : σ → ℤ) (M : ℕ), 0 < M →
    PhysicalSubbox parent H lo N →
    (∀ z ∈ translatedIntegerBox lo N, (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    ResidueSliceLogCostLE H lo N M a p →
    (∀ j, Real.exp ((p + 2) ^ E) ≤ (H j : ℝ)) →
    ∀ (h : (σ → ℤ) → ℂ) (level ε : ℝ), 0 ≤ level →
    ResidueSliceUpperComparison h g.eval parent H ((p + 2) ^ E) level ε →
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (prime i ^ power i)), ∃ depth : ℕ,
      (depth : ℝ) ≤ (p + 2) ^ E ∧
      CoordinateDecisionTree.Valid
        (fun I x => mandatory ⊆ I ∧
          ResiduePrimeCoordinateStable g.eval lo N M a (fun i => prime i ^ power i) r δ I x ∧
          PrimeRefinementUpperBound h g.eval lo N M a (fun i => prime i ^ power i) r level ε δ I x)
        ∅ (fun _ _ => 0) tree depth := by
  obtain ⟨E, hE, hstability⟩ := exists_baseline_stable_slice_costs.{u, v, w} s
  refine ⟨E, hE, ?_⟩
  intro ι σ L _ _ _ _ _ _ _ _ _ _ d D p δ hp hσ hδ hδinv g hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr parent H N lo a M hM
    hbox hunit hcost hlarge h level ε hlevel hupper
  obtain ⟨tree, depth, hdepth, htree⟩ := hstability D p δ hp hσ hδ hδinv g hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr H N lo a M hM
    hbox.length_le hunit hcost hlarge
  refine ⟨tree, depth, hdepth, ?_⟩
  exact htree.with_slice_upper_comparison hupper hbox hM
    (fun i => pow_pos (hprime i).pos _) (selectedPrimePowers_pairwise_coprime prime power hprime hinj) hlevel

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

universe u v w

theorem exists_baseline_no_increment_tree (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {σ : Type u} {L : Type v}
      [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [TopologicalSpace (ℝ ⊗[ℚ] L)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p δ : ℝ),
    2 ≤ p → (Fintype.card σ : ℝ) ≤ p → 0 < δ → δ⁻¹ ≤ Real.exp p →
    ∀ T : D.Niltest (fun _ : σ => 1), T.ComplexityLE p →
    ∀ (prime power : ι → ℕ), (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp p) →
    ∀ (mandatory : Finset ι) (r : ℕ), (mandatory.card : ℝ) ≤ p → (r : ℝ) ≤ p →
    ∀ (H N : σ → ℕ) (parent lo a : σ → ℤ) (M : ℕ), 0 < M → PhysicalSubbox parent H lo N →
    (∀ z ∈ translatedIntegerBox lo N, (T.eval z).im = 0 ∧ 0 ≤ (T.eval z).re ∧ (T.eval z).re ≤ 1) →
    ResidueSliceLogCostLE H lo N M a p →
    (∀ j, Real.exp ((p + 2) ^ E) ≤ (H j : ℝ)) →
    ∀ (h : (σ → ℤ) → ℂ) (level ε : ℝ), 0 ≤ level →
    ResidueSliceUpperComparison h T.eval parent H ((p + 2) ^ E) level ε →
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (prime i ^ power i)), ∃ depth : ℕ,
      (depth : ℝ) ≤ (p + 2) ^ E ∧
      CoordinateDecisionTree.Valid
        (fun I x => mandatory ⊆ I ∧
          ResiduePrimeCoordinateStable T.eval lo N M a (fun i => prime i ^ power i) r δ I x ∧
          PrimeRefinementUpperBound h T.eval lo N M a (fun i => prime i ^ power i) r level ε δ I x)
        ∅ (fun _ _ => 0) tree depth := by
  obtain ⟨E, hE, hstability⟩ := exists_baseline_stable_slice_costs.{u, v, w} s
  refine ⟨E, hE, ?_⟩
  intro ι σ L _ _ _ _ _ _ _ _ _ _ d D p δ hp hσ hδ hδinv T hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr H N parent lo a M hM hbox hunit hcost hlarge
    h level ε hlevel hupper
  obtain ⟨tree, depth, hdepth, htree⟩ := hstability D p δ hp hσ hδ hδinv T hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr H N lo a M hM hbox.length_le hunit hcost hlarge
  exact ⟨tree, depth, hdepth, htree.with_slice_upper_comparison hupper hbox hM
    (fun i => pow_pos (hprime i).pos _) (selectedPrimePowers_pairwise_coprime prime power hprime hinj) hlevel⟩

end Erdos3

end

end OAI
