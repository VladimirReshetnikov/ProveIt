import OAI.Combinatorics.Progressions.Estimates.CyclicProductDetection

namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

theorem cyclic_pair_niltest_detection.{u,v}
    {s : ℕ} {F : ℝ → ℝ} (hdet : CyclicProductNiltestDetection.{u,0} s F)
    {ι : Type v} {L : ι → Type u} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
    {d : ι → ℕ} [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)]
    [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    {p : ℝ} (hp : 2 ≤ p) (w : Fin 1 → ℕ) (hw : ∀ j, 0 < w j)
    (T : ∀ i, (D i).Niltest w) (hT : ∀ i, (T i).ComplexityLE p)
    (N : ℕ) [NeZero N] (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (i j : ι) (a : ZMod N)
    (hc : Real.exp (-p) ≤ ‖𝔼 x, f x * (T i).eval (fun _ => (x.val : ℤ)) *
      star ((T j).eval (fun _ => ((x + a).val : ℤ)))‖) :
    Real.exp (-F p) ≤ gowersNorm (s + 1) f := by
  let index : Fin 2 → ι := ![i, j]
  let D' := fun k : Fin 2 => D (index k)
  let U : ∀ k : Fin 2, (D' k).Niltest w := fun k =>
    if k = 0 then (T (index k)).conjugate else T (index k)
  have hU : ∀ k, (U k).ComplexityLE p := by
    intro k
    dsimp only [U]
    split_ifs <;> exact hT (index k)
  let shifts : Fin 2 → ZMod N := ![0, a]
  have heval (x : ZMod N) :
      translatedCyclicProduct shifts (fun k n => (U k).eval (fun _ => n)) x =
        star ((T i).eval (fun _ => (x.val : ℤ))) *
          (T j).eval (fun _ => ((x + a).val : ℤ)) := by
    simp [translatedCyclicProduct, Fin.prod_univ_two, shifts, U, D', index, add_comm]
    rfl
  have hcorr : Real.exp (-p) ≤ ‖finiteCorrelation Finset.univ f
      (translatedCyclicProduct shifts (fun k n => (U k).eval (fun _ => n)))‖ := by
    convert hc using 1
    congr 1
    unfold finiteCorrelation
    apply Finset.expect_congr rfl
    intro x _
    rw [heval]
    simp only [star_mul, star_star]
    ring
  exact hdet D' p (by linarith) (by simpa using hp) w hw U hU N shifts f hf hcorr

end Erdos3

end

end OAI
