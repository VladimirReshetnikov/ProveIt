import OAI.Combinatorics.Progressions.Nilpotent.IdealInvariantNiltestBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct NNReal

theorem exists_cellwise_niltest_discretization
    {I J Ξ : Type*} [Fintype I] [Fintype J] [PseudoMetricSpace Ξ]
    (N : ℕ) [NeZero N] {K : ZMod N → Type*}
    [∀ h, LieRing (K h)] [∀ h, LieAlgebra ℚ (K h)] {s : ℕ} {d : ZMod N → ℕ}
    [∀ h, TopologicalSpace (ℝ ⊗[ℚ] K h)] [∀ h, IsTopologicalAddGroup (ℝ ⊗[ℚ] K h)]
    [∀ h, ContinuousSMul ℝ (ℝ ⊗[ℚ] K h)] [∀ h, T2Space (ℝ ⊗[ℚ] K h)]
    (D : ∀ h, RationalFilteredNilmanifold (K h) s (d h))
    (g : ∀ h, (D h).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (F : I → ∀ h, (D h).Space → Ξ → ℝ)
    (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ) (E : ZMod N → Set (ZMod N))
    (xi : ZMod N → ZMod N → Ξ) (T : ZMod N → ZMod N → ℝ)
    {L M : ℝ≥0} {rho delta p : ℝ}
    (hA : ∀ i n, 0 ≤ A i n) (hB : ∀ j n, 0 ≤ B j n)
    (hAsum : ∀ n, ∑ i, A i n = 1) (hBsum : ∀ n, ∑ j, B j n = 1)
    (hF : ∀ i h z a, 0 ≤ F i h z a ∧ F i h z a ≤ 1)
    (hFirstLip : ∀ i h, let := (D h).metricSpace; ∀ a, LipschitzWith M (fun z => F i h z a))
    (hSecondLip : ∀ i h z, LipschitzWith L (F i h z))
    (hGeometry : ∀ h, (D h).GeometryComplexityLE p)
    (hBudget : Real.log (3 + (M : ℝ)) ≤ p)
    (hT : ∀ i h n, n ∉ E h → 0 < A i n →
      |T h n - F i h ((D h).cyclicOrbitPoint (g h) N (fun _ : Unit => n)) (xi h n)| ≤ delta)
    (hdiam : ∀ i j h n n', n ∉ E h → n' ∉ E h →
      0 < A i n * B j (n + h) → 0 < A i n' * B j (n' + h) →
      dist (xi h n) (xi h n') ≤ rho) :
    ∃ U : I → J → (h : ZMod N) → (D h).Niltest (fun _ : Unit => 1),
      (∀ i j h, (U i j h).UnitIntervalValued) ∧
      (∀ i j h, (U i j h).ComplexityLE p) ∧
      (∀ i j h, (¬∃ n, n ∉ E h ∧ 0 < A i n * B j (n + h)) →
        ∀ x, (U i j h).eval x = 0) ∧
      ∀ h n, n ∉ E h →
        |T h n - ∑ i, ∑ j, A i n * B j (n + h) *
          ((U i j h).evalCyclic N (fun _ : Unit => n)).re| ≤ delta + L * rho := by
  let z : (h : ZMod N) → ZMod N → (D h).Space :=
    fun h n => (D h).cyclicOrbitPoint (g h) N (fun _ : Unit => n)
  obtain ⟨a, hempty, herr⟩ := exists_cellwise_positive_shift_discretization A B E z xi F T
    hA hB hAsum hBsum hT hSecondLip hdiam
  let U : I → J → (h : ZMod N) → (D h).Niltest (fun _ : Unit => 1) :=
    fun i j h => (D h).sectionNiltest (g h) (F i h) (hF i h) M (hFirstLip i h) (a i j h)
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · intro i j h
    exact (D h).sectionNiltest_unit_interval (g h) (F i h) (hF i h) M (hFirstLip i h) (a i j h)
  · intro i j h
    exact (D h).sectionNiltest_complexityLE (g h) (F i h) (hF i h) M (hFirstLip i h)
      (a i j h) (hGeometry h) hBudget
  · intro i j h hcell x
    dsimp only [U]
    rw [hempty i j h hcell]
    exact (D h).sectionNiltest_none_eval (g h) (F i h) (hF i h) M (hFirstLip i h) x
  · intro h n hn
    have heval (i : I) (j : J) : ((U i j h).evalCyclic N (fun _ : Unit => n)).re =
        frozenRealSection (F i h) (a i j h) (z h n) := rfl
    simpa only [heval] using herr h n hn

end Erdos3

end

end OAI
