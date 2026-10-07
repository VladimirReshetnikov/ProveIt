import OAI.Combinatorics.Progressions.Estimates.UniformPhysicalVisitBounds

namespace OAI

section

namespace Erdos3
open scoped BigOperators

variable {X : Type*} [Fintype X] [decX : DecidableEq X]

theorem physicalResidue_reparamPatch_score {s d : ℕ}
    (N H : X → ℕ) (lo a : X → ℤ) (M : ℕ) (hM : 0 < M)
    (hbox : PhysicalSubbox (fun _ => 0) N lo H)
    (hlen : ∀ i, 0 < residueIndexLength (lo i) (lo i + H i) M (a i))
    (f : (X → ℤ) → ℝ) (target : ℝ) (A : PolynomialPatch X s d) :
    let S := ResidueBoxSlice.ofPhysicalResidue N H lo a M hM hbox hlen
    relativePatchSliceScore S f target (S.reparamPatch A) =
      (physicalResidueMean (fun x =>
        (((f x - target) * A.value (fun i => (x i : ℝ)) : ℝ) : ℂ)) lo H M a).re := by
  classical
  have hdec : decX = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  subst decX
  intro S
  let e := ResidueBoxSlice.ofPhysicalResidueEquiv N H lo a M hM hbox hlen
  have he (t : ∀ i, Fin (S.length i)) (i : X) :
      (e t i).val = ((S.point t i).val : ℤ) :=
    ResidueBoxSlice.ofPhysicalResidueEquiv_val N H lo a M hM hbox hlen t i
  calc
    _ = 𝔼 t : ∀ i, Fin (S.length i),
        (f (fun i => ((S.point t i).val : ℤ)) - target) *
          A.value (fun i => ((S.point t i).val : ℝ)) := by
      unfold relativePatchSliceScore
      apply Finset.expect_congr rfl
      intro t _
      rw [ResidueBoxSlice.reparamPatch_value]
    _ = 𝔼 x : IntegerResidueBox lo (fun i => lo i + H i) (fun _ => (M : ℤ)) a,
        (f (fun i => (x i).val) - target) *
          A.value (fun i => ((x i).val : ℝ)) := by
      apply Fintype.expect_equiv e
      intro t
      simp only [he, Int.cast_natCast]
    _ = _ := by
      simp only [physicalResidueMean, Finset.expect_eq_sum_div_card,
        ← Complex.ofReal_sum, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
        Complex.ofReal_re]

theorem relativePatchSliceConclusion_of_physicalResidueMean {s d : ℕ}
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (A : PolynomialPatch X s d)
    (lo : X → ℤ) (H : X → ℕ) (M : ℕ) (a : X → ℤ) (target cost : ℝ)
    (hM : 0 < M) (hbox : PhysicalSubbox (fun _ => 0) N lo H)
    (hlen : ∀ i, 0 < residueIndexLength (lo i) (lo i + H i) M (a i))
    (hcost : ResidueSliceLogCostLE N lo H M a cost)
    (hcomplexity : relativePatchComplexity A ≤ cost)
    (hscore : Real.exp (-cost) ≤ (physicalResidueMean (fun x =>
      (((f x - target) * A.value (fun i => (x i : ℝ)) : ℝ) : ℂ)) lo H M a).re) :
    RelativePatchSliceConclusion s N f target d cost := by
  let S := ResidueBoxSlice.ofPhysicalResidue N H lo a M hM hbox hlen
  refine ⟨M, hM, S, d, S.reparamPatch A, hcost, le_rfl, hcomplexity, ?_⟩
  rw [physicalResidue_reparamPatch_score N H lo a M hM hbox hlen f target A]
  exact hscore

theorem relativePatchSliceConclusion_of_nonempty_physicalResidueMean {s d : ℕ}
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (A : PolynomialPatch X s d)
    (lo : X → ℤ) (H : X → ℕ) (M : ℕ) (a : X → ℤ) (target cost : ℝ)
    (hM : 0 < M) (hbox : PhysicalSubbox (fun _ => 0) N lo H)
    (hne : Nonempty (IntegerResidueBox lo (fun i => lo i + H i) (fun _ => (M : ℤ)) a))
    (hcost : ResidueSliceLogCostLE N lo H M a cost)
    (hcomplexity : relativePatchComplexity A ≤ cost)
    (hscore : Real.exp (-cost) ≤ (physicalResidueMean (fun x =>
      (((f x - target) * A.value (fun i => (x i : ℝ)) : ℝ) : ℂ)) lo H M a).re) :
    RelativePatchSliceConclusion s N f target d cost := by
  obtain ⟨x⟩ := hne
  have hlen i : 0 < residueIndexLength (lo i) (lo i + H i) M (a i) := by
    rw [residueIndexLength_eq_card _ _ _ _ (Nat.cast_pos.mpr hM)]
    exact Finset.card_pos.mpr ⟨(x i).val, (x i).property⟩
  exact relativePatchSliceConclusion_of_physicalResidueMean N f A lo H M a target cost
    hM hbox hlen hcost hcomplexity hscore

end Erdos3

end

end OAI
