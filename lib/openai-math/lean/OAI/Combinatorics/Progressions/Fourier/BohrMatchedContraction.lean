import OAI.Combinatorics.Progressions.Dynamics.MatchedPotentialContraction
import OAI.Combinatorics.Progressions.Fourier.BohrTorusApproximation

namespace OAI

section

namespace Erdos3

open scoped BigOperators Pointwise NNReal

variable {N : ℕ} [NeZero N]

theorem bohr_matched_potential_contraction
    (L : CyclicBohr.Set N) (hL : L.IsRankRegular) (S C : Finset (ZMod N))
    (hS : S.Nonempty) (hC : C.Nonempty) {kappa : ℝ≥0}
    (hSL : S ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f g : ZMod N → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ L.carrier → f x = 0)
    (hgsupport : ∀ x, x ∉ L.carrier → g x = 0)
    {u v M K c : ℝ} (hu : 0 < u) (hv : 0 < v) (hc : 0 < c) (hc1 : c ≤ 1)
    (hmeanf : (𝔼 x ∈ L.carrier, f x) ≤ u) (hmeang : (𝔼 x ∈ L.carrier, g x) ≤ v)
    (hcapg : ∀ x, g x / v ≤ M)
    (hcellf : ∀ x, cellAverage C f x / u ≤ K)
    (hcellg : ∀ x, cellAverage C g x / v ≤ K)
    (herror : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) ≤ c / 2)
    (hsecond : (1 + c ≤ 𝔼 x ∈ L.carrier, cellAverage C (fun y => f y / u) x ^ 2) ∨
      (1 + c ≤ 𝔼 x ∈ L.carrier, cellAverage C (fun y => g y / v) x ^ 2)) :
    let rho := 1 - c / (8 * (1 + Real.sqrt K) ^ 2)
    3 / 4 ≤ rho ∧ rho < 1 ∧
      (𝔼 z ∈ matchedCellSpace L.carrier S,
        (matchedFirstCell C f z * matchedSecondCell C g z) ^ (1 / 4 : ℝ)) ≤
        rho * (u * v) ^ (1 / 4 : ℝ) := by
  intro rho
  let eta : ℝ := 400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)
  have heta : 0 ≤ eta := by dsimp [eta]; positivity
  have hsymm : -L.carrier = L.carrier := by
    ext x
    constructor
    · intro h
      obtain ⟨y, hy, rfl⟩ := Finset.mem_neg.mp h
      exact (L.neg_mem_iff y).2 hy
    · intro h
      exact Finset.mem_neg.mpr ⟨-x, (L.neg_mem_iff x).2 h, neg_neg x⟩
  have hTV : ∀ s ∈ S, ∀ t ∈ S,
      (∑ x, |realUniformMass L.carrier (x - (s + t)) - realUniformMass L.carrier x|) ≤ eta := by
    intro s hs t ht
    exact CyclicBohr.Set.uniformMass_translation_le_of_rankRegular hL hkappa
      (CyclicBohr.Set.add_mem_ndilate (hSL hs) (hSL ht))
  have hsecond' :
      (1 + c / 2 + M ^ 2 * eta ≤ 𝔼 x ∈ L.carrier, cellAverage C (fun y => f y / u) x ^ 2) ∨
      (1 + c / 2 + M ^ 2 * eta ≤ 𝔼 x ∈ L.carrier, cellAverage C (fun y => g y / v) x ^ 2) := by
    change M ^ 2 * eta ≤ c / 2 at herror
    rcases hsecond with hsecond | hsecond
    · left; linarith
    · right; linarith
  have h := matched_potential_contraction L.carrier S C L.carrier_nonempty hsymm hS hC f g hf hg
    hfsupport hgsupport hu hv heta hmeanf hmeang hcapg hcellf hcellg hTV hsecond'
  have heq : c / 2 / (4 * (1 + Real.sqrt K) ^ 2) = c / (8 * (1 + Real.sqrt K) ^ 2) := by
    rw [div_div]
    congr 1
    ring
  rw [heq] at h
  have hbounds := quarter_contraction_factor_bounds (M := K) (c := c / 2)
    (by linarith) (by linarith)
  rw [heq] at hbounds
  exact ⟨hbounds.1, hbounds.2, h⟩

end Erdos3

end

end OAI
