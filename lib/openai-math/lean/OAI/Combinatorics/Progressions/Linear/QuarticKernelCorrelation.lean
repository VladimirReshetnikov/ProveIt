import OAI.Combinatorics.Progressions.Estimates.MixedAnchorExpansion

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_quartic_kernel_correlation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 0 ≤ p →
      ∀ (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
        {N : ℕ} [NeZero N] (i j : Fin W.outputDim),
      Real.exp (-p) ≤ (boxPhaseMoment 4 (fun x : Fin 4 → ZMod N =>
        W.quarticAntisymmetric i j (fun k => ((x k).val : ℤ)))).re →
      Nonempty (NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 ((p + C) ^ C)
        Finset.univ (fun x : Fin 4 → ZMod N => fun k => ((x k).val : ℤ))
        (fun x => W.quarticAntisymmetric i j (fun k => ((x k).val : ℤ)))) := by
  obtain ⟨A, _, hanchor⟩ := NativeMultidegreeNilcharacter.exists_quartic_anchor_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + (X + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro p hp W N _ i j hbias
  let K := W.quarticAntisymmetric i j
  let Kc := fun x : Fin 4 → ZMod N => K (fun k => ((x k).val : ℤ))
  obtain ⟨a, ha⟩ := exists_box_corner_anchor_correlation Kc
  obtain ⟨E⟩ := hanchor W i j (fun k => ((a k).val : ℤ))
  have hmap (x : Fin 4 → ZMod N) : boxCornerAnchor Kc a x =
      boxCornerAnchor K (fun k => ((a k).val : ℤ)) (fun k => ((x k).val : ℤ)) :=
    boxCornerAnchor_map (fun z : ZMod N => (z.val : ℤ)) K a x
  have hcorr : Real.exp (-p) ≤ ‖𝔼 x : Fin 4 → ZMod N,
      K (fun k => ((x k).val : ℤ)) *
        star (star (boxCornerAnchor K (fun k => ((a k).val : ℤ))
          (fun k => ((x k).val : ℤ))))‖ := by
    have h := hbias.trans ha
    simp_rw [hmap] at h
    simpa only [Kc, star_star] using h
  obtain ⟨S⟩ := NativeSampleCorrelation.exists_of_expansion E.conjugate hp hcorr
  have hcost : p + (p + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨S.mono hcost⟩

end Erdos3

end

end OAI
