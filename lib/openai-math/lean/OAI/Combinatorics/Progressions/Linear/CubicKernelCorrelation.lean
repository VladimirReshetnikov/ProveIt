import OAI.Combinatorics.Progressions.Estimates.CubicAnchorExpansion

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_triple_box_anchor_correlation {X : Type*} [Fintype X] [Nonempty X]
    (K : X → X → X → ℂ) :
    ∃ a : Fin 3 → X, (finiteTripleBoxCorrelation K).re ≤
      ‖𝔼 z : Fin 3 → X, K (z 0) (z 1) (z 2) * tripleBoxAnchorFactor K a z‖ := by
  have hmean : (finiteTripleBoxCorrelation K).re =
      𝔼 a : Fin 3 → X, (𝔼 z : Fin 3 → X,
        K (z 0) (z 1) (z 2) * tripleBoxAnchorFactor K a z).re := by
    rw [← tripleBoxKernel_mean, expect_tripleBoxSlice, expect_re]
    simp_rw [tripleBoxKernel_slice]
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean.le
  exact ⟨a, ha.trans (Complex.re_le_norm _)⟩

theorem exists_cubic_kernel_correlation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 0 ≤ p →
      ∀ (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
        {N : ℕ} [NeZero N] (i j : Fin V.outputDim × Fin V.outputDim) (shift : ℤ),
      Real.exp (-p) ≤ (finiteTripleBoxCorrelation (fun k h y : ZMod N =>
        V.cubicAntisymmetricPair i j h.val y.val ((k.val : ℤ) + shift))).re →
      Nonempty (NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 ((p + C) ^ C)
        Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => V.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))) := by
  obtain ⟨A, _, hanchor⟩ := NativeMultidegreeNilcharacter.exists_cubic_anchor_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + (X + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro p hp V N _ i j shift hbias
  let K := fun k h y : ℤ => V.cubicAntisymmetricPair i j h y (k + shift)
  let Kc := fun k h y : ZMod N => K k.val h.val y.val
  obtain ⟨a, ha⟩ := exists_triple_box_anchor_correlation Kc
  obtain ⟨E⟩ := hanchor V i j shift (fun k => ((a k).val : ℤ))
  have hcorr : Real.exp (-p) ≤ ‖𝔼 z : Fin 3 → ZMod N,
      V.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift) *
        star (star (tripleBoxAnchorFactor K (fun k => ((a k).val : ℤ))
          (fun k => ((z k).val : ℤ))))‖ := by
    simpa only [Kc, K, tripleBoxAnchorFactor, star_star] using hbias.trans ha
  obtain ⟨W⟩ := NativeSampleCorrelation.exists_of_expansion E.conjugate hp hcorr
  have hcost : p + (p + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨W.mono hcost⟩

end Erdos3

end

end OAI
