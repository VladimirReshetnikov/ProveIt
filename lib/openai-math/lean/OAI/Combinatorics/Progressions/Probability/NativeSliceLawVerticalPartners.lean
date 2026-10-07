import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairFamily

namespace OAI

section

namespace Erdos3
open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_sliceLaw_localPivot_weighted_native_vertical_partners
    {Ω K X σ τ : Type*} [Fintype Ω] [Fintype K] [Fintype X] [DecidableEq X]
    {L : K → Type*} {Llocal : Ω → K → Type*}
    [∀ k, LieRing (L k)] [∀ k, LieAlgebra ℚ (L k)]
    [∀ a k, LieRing (Llocal a k)] [∀ a k, LieAlgebra ℚ (Llocal a k)]
    {s : ℕ} {d : K → ℕ} {sLocal dLocal : Ω → K → ℕ}
    [∀ k, TopologicalSpace (ℝ ⊗[ℚ] L k)]
    [∀ k, IsTopologicalAddGroup (ℝ ⊗[ℚ] L k)]
    [∀ k, ContinuousSMul ℝ (ℝ ⊗[ℚ] L k)] [∀ k, T2Space (ℝ ⊗[ℚ] L k)]
    [∀ a k, TopologicalSpace (ℝ ⊗[ℚ] Llocal a k)]
    [∀ a k, IsTopologicalAddGroup (ℝ ⊗[ℚ] Llocal a k)]
    [∀ a k, ContinuousSMul ℝ (ℝ ⊗[ℚ] Llocal a k)]
    [∀ a k, T2Space (ℝ ⊗[ℚ] Llocal a k)]
    (D : ∀ k, RationalFilteredNilmanifold (L k) s (d k))
    (Dlocal : ∀ a k, RationalFilteredNilmanifold (Llocal a k) (sLocal a k) (dLocal a k))
    {w : σ → ℕ} {wLocal : τ → ℕ}
    (Q : ∀ k, (D k).Niltest w) (P : ∀ a k, (Dlocal a k).Niltest wLocal)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    {N : X → ℕ} (stride : Ω → K → ℕ)
    (S : ∀ a k, ResidueBoxSlice N (stride a k))
    (hstride : ∀ a ∈ H, ∀ k, 0 < stride a k)
    (hlen : ∀ a k i, 0 < (S a k).length i)
    (pointAmbient : Ω → integerBox N → σ → ℤ) (pointLocal : Ω → K → integerBox N → τ → ℤ)
    (twist : Ω → K → integerBox N → ℂ) {pNative pLocal r q : ℝ}
    (hpLocal : 0 ≤ pLocal) (hr : 0 ≤ r) (hpq : pNative ≤ q)
    (hprecision : pLocal + r + 1 ≤ q)
    (hQ : ∀ k, (Q k).ComplexityLE pNative)
    (hcap : ∀ k, ((Q k).normBound : ℝ) ≤ 1)
    (hP : ∀ a ∈ H, ∀ k, (P a k).ComplexityLE pLocal)
    (htwist : ∀ a ∈ H, ∀ k t, ‖twist a k t‖ ≤ 1)
    (hcorr : ∀ a ∈ H, ∀ k, Real.exp (-r) ≤
      ‖((S a k).fullSliceLaw (hlen a k)).complexMean (fun t =>
        ((P a k).eval (pointLocal a k t) * twist a k t) * (Q k).eval (pointAmbient a t))‖) :
    ∃ (freq : ∀ k, L k →ₗ[ℚ] ℚ) (V : ∀ k, (D k).Niltest w) (retained : Finset Ω),
      retained ⊆ H ∧ 0 < outer.mass retained ∧
      Real.exp (-verticalDecompositionBudget q * Fintype.card K) * outer.mass H ≤
        outer.mass retained ∧
      (∀ k, (V k).ComplexityLE pNative ∧ (V k).orbit = (Q k).orbit ∧
        (V k).normBound = (Q k).normBound ∧ (V k).lipBound = (Q k).lipBound ∧
        ((V k).normBound : ℝ) ≤ 1) ∧
      (∀ k i, rationalLogHeight (freq k ((D k).basis i)) ≤ verticalDecompositionBudget q) ∧
      (∀ k (z : (D k).RealGroup), z ∈ (D k).filtration.realification.subgroup s → ∀ x,
        (V k).observable (z • x) =
          character ((realifyFunctional (freq k) z.coord : ℝ) : CircleFourier.Circle) *
            (V k).observable x) ∧
      (∀ k (z : (D k).RealGroup), z ∈ (D k).filtration.realification.subgroup s →
        z ∈ (D k).realLattice → ∃ n : ℤ, realifyFunctional (freq k) z.coord = n) ∧
      (∀ k (z : (D k).RealGroup) (c : ℂ),
        (∀ x, (Q k).observable (z • x) = c * (Q k).observable x) →
        ∀ x, (V k).observable (z • x) = c * (V k).observable x) ∧
      ∀ a ∈ retained, ∀ k, Real.exp (-r) / (2 * Real.exp (verticalDecompositionBudget q)) ≤
        ‖((S a k).fullSliceLaw (hlen a k)).complexMean (fun t =>
          ((P a k).eval (pointLocal a k t) * twist a k t) * (V k).eval (pointAmbient a t))‖ := by
  classical
  have hfiniteCorr (a : Ω) (ha : a ∈ H) (k : K) :
      Real.exp (-r) ≤ ‖𝔼 t ∈ (S a k).fullSlicePoints,
        ((P a k).eval (pointLocal a k t) * twist a k t) * (Q k).eval (pointAmbient a t)‖ := by
    rw [← (S a k).fullSliceLaw_complexMean_eq_expect_points (hlen a k) (hstride a ha k)]
    exact hcorr a ha k
  obtain ⟨freq, V, retained, hsub, hpos, hmass, hcert, hheight, hvert, hint,
      hpres, hselected⟩ := exists_localPivot_weighted_native_vertical_partners
    D Dlocal Q P outer H hH (fun a k => (S a k).fullSlicePoints)
    pointAmbient pointLocal twist hpLocal hr hpq hprecision hQ hcap hP
    (fun a ha k t _ => htwist a ha k t) hfiniteCorr
  refine ⟨freq, V, retained, hsub, hpos, hmass, hcert, hheight, hvert, hint, hpres, ?_⟩
  intro a ha k
  rw [(S a k).fullSliceLaw_complexMean_eq_expect_points (hlen a k) (hstride a (hsub ha) k)]
  exact hselected a ha k

end Erdos3

end

end OAI
