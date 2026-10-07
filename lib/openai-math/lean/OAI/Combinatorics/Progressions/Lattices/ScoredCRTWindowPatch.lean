import OAI.Combinatorics.Progressions.Polynomial.CRTPolynomialPatchComposition
import OAI.Combinatorics.Progressions.Polynomial.ScoredCyclicPolynomialPatch

namespace OAI

section

namespace Erdos3

open scoped BigOperators

universe u

theorem exists_scored_windowed_crt_patch (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {J : Type*} [Fintype J] [DecidableEq J]
      (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)]
      (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))
      (T : ZMod (∏ j, N j) → ℝ) (w : RepresentativeWindow)
      (a : ((j : J) → ZMod (N j)) → ℝ) {p : ℝ},
      0 ≤ p → PositiveCyclicNiltest.{u} s (∏ j, N j) p T →
      Real.log (2 + (w.lip : ℝ)) ≤ p →
      Real.exp (-p) ≤ (𝔼 x, (a x * T ((ZMod.prodEquivPi N hN).symm x)) *
        w.value ((((ZMod.prodEquivPi N hN).symm x).val : ℝ) / (∏ j, N j : ℕ))) →
      ∃ d : ℕ, ∃ P : PolynomialPatch J s d,
        (d : ℝ) + Real.log (2 + (P.kernel.lip : ℝ)) ≤ (p + 2) ^ C ∧
        Real.exp (-((p + 2) ^ C)) ≤ (𝔼 x, a x * P.value (fun j => ((x j).val : ℝ))) := by
  obtain ⟨A, _, hconvert⟩ := exists_scored_cyclic_patch.{u} s
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    ((Polynomial.X + 2) ^ A + Polynomial.X + 1)
  refine ⟨C, hC, ?_⟩
  intro J _ _ N _ _ hN T w a p hp hT hw hscore
  let b := fun x : (j : J) → ZMod (N j) =>
    a x * w.value ((((ZMod.prodEquivPi N hN).symm x).val : ℝ) / (∏ j, N j : ℕ))
  have hscore' : Real.exp (-p) ≤ (𝔼 x, b x * T ((ZMod.prodEquivPi N hN).symm x)) := by
    have heq : (𝔼 x, b x * T ((ZMod.prodEquivPi N hN).symm x)) =
        (𝔼 x, (a x * T ((ZMod.prodEquivPi N hN).symm x)) *
          w.value ((((ZMod.prodEquivPi N hN).symm x).val : ℝ) / (∏ j, N j : ℕ))) := by
      apply Finset.expect_congr rfl
      intro x _
      dsimp only [b]
      ring
    rw [heq]
    exact hscore
  obtain ⟨d, Q, hQ, hscoreQ⟩ := hconvert T b (ZMod.prodEquivPi N hN).symm hp hT hscore'
  let P := w.composeCRTPatch N hN s hs Q
  have hcost : ((1 + d : ℕ) : ℝ) + Real.log (2 + (P.kernel.lip : ℝ)) ≤
      (p + 2) ^ A + p + 1 := w.composeCRTPatch_cost N hN s hs Q hQ hw
  have hb : (p + 2) ^ A + p + 1 ≤ (p + 2) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  have hsame : (𝔼 x, a x * P.value (fun j => ((x j).val : ℝ))) =
      (𝔼 x, b x * Q.value (fun _ => (((ZMod.prodEquivPi N hN).symm x).val : ℝ))) := by
    apply Finset.expect_congr rfl
    intro x _
    rw [show P.value (fun j => ((x j).val : ℝ)) = _ from
      w.composeCRTPatch_value_residues N hN s hs Q x]
    dsimp only [b]
    ring
  refine ⟨1 + d, P, hcost.trans hb, ?_⟩
  rw [hsame]
  exact (Real.exp_le_exp.mpr (neg_le_neg (show (p + 2) ^ A ≤ (p + 2) ^ C by linarith))).trans hscoreQ

end Erdos3

end

end OAI
