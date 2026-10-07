import OAI.Combinatorics.Progressions.Lattices.ResidueSliceUpperFailure

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def PrimeRefinementUpperBound {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (h g : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (r : ℕ) (level ε δ : ℝ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) : Prop :=
  ∀ J : Finset ι, Disjoint I J → J.card ≤ r → ∀ y : ∀ i, σ → ZMod (q i),
    (∀ i ∈ I, y i = x i) → Nonempty (ResiduePrimeCoordinateCell lo N M a q (I ∪ J) y) →
    (residuePrimeCoordinateMean h lo N M a q (I ∪ J) y).re ≤
      level * (residuePrimeCoordinateMean g lo N M a q I x).re + ε + level * δ

theorem CoordinateDecisionTree.Valid.with_slice_upper_comparison {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {parent lo a : σ → ℤ} {H N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
    {r : ℕ} {δ P level ε : ℝ} {mandatory I : Finset ι} {x : ∀ i, σ → ZMod (q i)}
    {tree : CoordinateDecisionTree ι (fun i => σ → ZMod (q i))} {d : ℕ}
    (htree : CoordinateDecisionTree.Valid
      (fun A z => mandatory ⊆ A ∧ ResiduePrimeCoordinateStable g lo N M a q r δ A z ∧
        ∀ J : Finset ι, J.card ≤ r → ∀ u : σ → ℤ,
          ResidueSliceLogCostLE H lo N (M.lcm (∏ i ∈ A ∪ J, q i)) u P) I x tree d)
    (hupper : ResidueSliceUpperComparison h g parent H P level ε)
    (hbox : PhysicalSubbox parent H lo N) (hM : 0 < M) (hqpos : ∀ i, 0 < q i)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j))) (hlevel : 0 ≤ level) :
    CoordinateDecisionTree.Valid
      (fun A z => mandatory ⊆ A ∧ ResiduePrimeCoordinateStable g lo N M a q r δ A z ∧
        PrimeRefinementUpperBound h g lo N M a q r level ε δ A z) I x tree d := by
  apply htree.map
  intro A z hz
  refine ⟨hz.1, hz.2.1, ?_⟩
  intro J hAJ hJ y hzy hne
  apply hz.2.1.refinement_upper_bound hlevel J hAJ hJ y hzy hne
  exact hupper.on_prime_cell hbox M hM q hqpos hcop (A ∪ J) y (hz.2.2 J hJ) hne

end Erdos3

end

end OAI
