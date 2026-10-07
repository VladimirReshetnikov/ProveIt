import OAI.Combinatorics.Progressions.Sampling.IntegralScoredKernel

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct BigOperators

theorem exists_scored_native_polynomial_patch (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ X L : Type*} [Fintype X]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (T : D.Niltest (fun _ : σ => 1))
      (a : X → ℝ) (u : X → σ → ℤ) {p : ℝ},
      0 ≤ p → T.ComplexityLE p → T.UnitIntervalValued →
      Real.exp (-p) ≤ (𝔼 x, a x * (T.eval (u x)).re) →
      ∃ P : PolynomialPatch σ s (finrank ℚ L),
        (finrank ℚ L : ℝ) + Real.log (2 + (P.kernel.lip : ℝ)) ≤ (p + 2) ^ C ∧
        Real.exp (-((p + 2) ^ C)) ≤
          (𝔼 x, a x * P.value (fun j => (u x j : ℝ))) := by
  obtain ⟨C, hC, hkernel⟩ := exists_integral_scored_kernel s
  refine ⟨C + 1, by omega, ?_⟩
  intro σ X L _ _ _ d _ _ _ _ D T a u p hp hT hpositive hscore
  obtain ⟨E, omega, _, hmono, hcentral, hweights, hlayers, hgrid, _, _, hcoords,
    _, r, z, phi, hr, _, _, _, hphi, hsource, V, _, hV, hscoreV, hinner,
    Phi, hPhiCost, hPhi, _⟩ := hkernel D T a u hp hT hpositive hscore
  let := E.metricSpace
  let P := E.filtration.orderedPolynomialPatch E.basis omega hlayers
    (fun i => (hweights i).1) (fun i => (hweights i).2) hmono (E.grid : ℝ) z⁻¹ V.orbit Phi
  have hsupport : Function.support (fun x => (V.observable x).re) ⊆ phi.target := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := hinner (V.realObservable_tsupport (subset_closure hx))
    exact phi.map_source (closedBox_subset_chart_source phi hr hsource hv)
  have hvalue (v : σ → ℝ) : P.value v = (V.evalReal v).re := by
    let : MetricSpace (E.filtration.realification.Group ⧸
      E.lattice.map NilpotentLieBCHGroup.realificationHom) := E.metricSpace
    exact E.filtration.orderedPolynomialPatch_chart_value E.basis omega hlayers E.lattice
      hcentral (fun i => (hweights i).1) (fun i => (hweights i).2) hmono E.grid
      (by omega) hcoords z V.orbit phi hphi (fun x => (V.observable x).re) hsupport Phi hPhi v
  have heval (v : σ → ℤ) : P.value (fun j => (v j : ℝ)) = (V.eval v).re :=
    (hvalue _).trans (congrArg Complex.re (V.evalReal_integer v))
  have hpow : 0 ≤ (p + 2) ^ C := pow_nonneg (by linarith) C
  have hbudget : 2 * (p + 2) ^ C ≤ (p + 2) ^ (C + 1) := by
    rw [pow_succ]
    nlinarith
  refine ⟨P, ?_, ?_⟩
  · have hdim := hV.1.1
    change (finrank ℚ L : ℝ) ≤ (p + 2) ^ C at hdim
    change (finrank ℚ L : ℝ) + Real.log (2 + (Phi.lip : ℝ)) ≤ _
    linarith
  · have hmonoBudget : (p + 2) ^ C ≤ (p + 2) ^ (C + 1) := by linarith
    apply (Real.exp_le_exp.mpr (neg_le_neg hmonoBudget)).trans
    simpa only [heval] using hscoreV

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

universe u

theorem exists_scored_cyclic_patch (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {X : Type*} [Fintype X]
      (T : ZMod N → ℝ) (a : X → ℝ) (n : X → ZMod N) {p : ℝ},
      0 ≤ p → PositiveCyclicNiltest.{u} s N p T →
      Real.exp (-p) ≤ (𝔼 x, a x * T (n x)) →
      ∃ d : ℕ, ∃ P : PolynomialPatch Unit s d,
        (d : ℝ) + Real.log (2 + (P.kernel.lip : ℝ)) ≤ (p + 2) ^ C ∧
        Real.exp (-((p + 2) ^ C)) ≤ (𝔼 x, a x * P.value (fun _ => ((n x).val : ℝ))) := by
  obtain ⟨A, _, hconvert⟩ := RationalFilteredNilmanifold.exists_scored_native_polynomial_patch s
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    ((Polynomial.X + (Polynomial.X + 2) ^ 2 + 5) ^ A)
  refine ⟨C, hC, ?_⟩
  intro N _ X _ T a n p hp hT hscore
  rcases hT with @⟨L, lie, alg, t, dim, top, add, smul, t2, D, ht, U, hU, hUc, hUeval⟩
  let V := U.raiseStep ht
  let r := raisedNiltestBudget p
  have hpR : p ≤ r := le_raisedNiltestBudget p
  have hr : 0 ≤ r := hp.trans hpR
  have heval (x : X) : (V.eval (fun _ : Unit => ((n x).val : ℤ))).re = T (n x) := by
    dsimp only [V]
    rw [RationalFilteredNilmanifold.Niltest.raiseStep_eval]
    exact (hUeval (n x)).symm
  have hscoreV : Real.exp (-r) ≤ (𝔼 x, a x * (V.eval (fun _ : Unit => ((n x).val : ℤ))).re) := by
    apply (Real.exp_le_exp.mpr (neg_le_neg hpR)).trans
    simpa only [heval] using hscore
  obtain ⟨P, hcost, hscoreP⟩ := hconvert (D.raiseStep ht) V a
    (fun x _ => ((n x).val : ℤ)) hr (U.raiseStep_complexity ht hp hUc)
    (U.raiseStep_unit_interval ht hU) hscoreV
  have hb : (r + 2) ^ A ≤ (p + 2) ^ C := by
    have heq : r + 2 = p + (p + 2) ^ 2 + 5 := by
      dsimp only [r, raisedNiltestBudget]
      ring
    rw [heq]
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨_, P, hcost.trans hb, ?_⟩
  have hs := (Real.exp_le_exp.mpr (neg_le_neg hb)).trans hscoreP
  simpa only [Int.cast_natCast] using hs

end Erdos3

end

end OAI
