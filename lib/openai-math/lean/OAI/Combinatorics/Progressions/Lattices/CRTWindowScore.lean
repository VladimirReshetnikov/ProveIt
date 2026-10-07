import OAI.Combinatorics.Progressions.Geometry.RepresentativeWindowTransport

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
  [∀ j, NeZero (N j)] [NeZero (∏ j, N j)]
  (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))

theorem crt_representative_patch_score (s : ℕ) (hs : 1 ≤ s)
    (f : ZMod (∏ j, N j) → ℝ) (w : RepresentativeWindow) :
    (𝔼 u : (j : J) → ZMod (N j),
      f ((ZMod.prodEquivPi N hN).symm u) *
        (w.crtPatch N hN s hs).value (fun j => ((u j).val : ℝ))) =
      𝔼 x, f x * w.value ((x.val : ℝ) / (∏ j, N j : ℕ)) := by
  apply Fintype.expect_equiv (ZMod.prodEquivPi N hN).symm.toEquiv
  intro u
  rw [w.crtPatch_value_residues N hN s hs]
  rfl

theorem exists_scored_crt_representative_patch (s : ℕ) (hs : 1 ≤ s)
    (f : ZMod (∏ j, N j) → ℝ) {M sigma : ℝ} (hM : 0 < M) (hsigma : 0 < sigma)
    (hf : ∀ x, |f x| ≤ M) (hscore : sigma ≤ 𝔼 x, f x)
    (hsize : 1 / ((∏ j, N j : ℕ) : ℝ) ≤ sigma / (100 * M)) :
    ∃ w : RepresentativeWindow,
      (w.lip : ℝ) = 100 * M / sigma + representativeWindowPartitionLip ∧
      3 * sigma / (4 * representativeWindowCount) ≤
        𝔼 u : (j : J) → ZMod (N j),
          f ((ZMod.prodEquivPi N hN).symm u) *
            (w.crtPatch N hN s hs).value (fun j => ((u j).val : ℝ)) := by
  let eta : ℝ≥0 := ⟨sigma / (100 * M), by positivity⟩
  have heta : 0 < eta := by change 0 < sigma / (100 * M); positivity
  obtain ⟨i, hi⟩ := exists_localizedRepresentativeWindow_score f hM hsigma hf hscore
    eta heta le_rfl hsize
  let w := localizedRepresentativeWindow eta heta i
  refine ⟨w, ?_, ?_⟩
  · change (sigma / (100 * M))⁻¹ + (representativeWindowPartitionLip : ℝ) = _
    rw [inv_div]
  · rw [crt_representative_patch_score N hN s hs]
    exact hi

end Erdos3

end

end OAI
