import OAI.Combinatorics.Progressions.Probability.CommonSectionAmbientDensityMultiple

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

variable {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]

noncomputable def lowJetAmbientSites
    (z : JetAmbientIndex (fun j : Fin m => BoundedBooleanJet α (j.val + 1)) J → UnitAddCircle) :
    JetAmbientIndex (fun _ : Fin m => Finset α) J → UnitAddCircle :=
  fun t => ∑ r, boundedBooleanReconstructionMatrix α (t.1.val + 1) t.2.1 r • z ⟨t.1, r, t.2.2⟩

theorem lowJetAmbientSites_lipschitz :
    LipschitzWith (∑ j : Fin m, (Fintype.card (BoundedBooleanJet α (j.val + 1)) : ℝ≥0))
      (lowJetAmbientSites (α := α) (J := J)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (by positivity)).mpr
  rintro ⟨j, s, i⟩
  have hterm (r : BoundedBooleanJet α (j.val + 1)) :
      dist (boundedBooleanReconstructionMatrix α (j.val + 1) s r • z ⟨j,r,i⟩)
        (boundedBooleanReconstructionMatrix α (j.val + 1) s r • w ⟨j,r,i⟩) ≤ dist z w := by
    simp only [boundedBooleanReconstructionMatrix]
    split_ifs
    · simpa only [one_zsmul] using dist_le_pi_dist z w ⟨j,r,i⟩
    · simpa only [zero_zsmul, dist_self] using (dist_nonneg : 0 ≤ dist z w)
  have hc : (Fintype.card (BoundedBooleanJet α (j.val + 1)) : ℝ≥0) ≤
      ∑ j : Fin m, (Fintype.card (BoundedBooleanJet α (j.val + 1)) : ℝ≥0) :=
    Finset.single_le_sum
      (f := fun j : Fin m => (Fintype.card (BoundedBooleanJet α (j.val + 1)) : ℝ≥0))
      (fun _ _ => zero_le) (Finset.mem_univ j)
  calc
    _ ≤ ∑ _r : BoundedBooleanJet α (j.val + 1), dist z w :=
      (dist_sum_sum_le _ _ _).trans (Finset.sum_le_sum (fun r _ => hterm r))
    _ = (Fintype.card (BoundedBooleanJet α (j.val + 1)) : ℝ) * dist z w := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) dist_nonneg

theorem lowJetAmbientSites_coefficient {K : Type*} [Fintype K]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (D : Matrix α K ℤ)
    (x : CoefficientTorus (K := K) U) :
    lowJetAmbientSites (coveredJetAmbientTorus U 1
      (euclideanCoefficientJetMap U root D (fun j =>
        (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α)) x)) =
      coefficientAmbientSiteEvaluation (integerAffineCube root D) (coefficientAmbientTorus U x) := by
  funext t
  rcases t with ⟨j, s, i⟩
  simp only [lowJetAmbientSites, coveredJetAmbientTorus_coefficient, Nat.cast_one, one_mul,
    coefficientAmbientSiteEvaluation, Finset.smul_sum, ← mul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.sum_smul]
  congr 1
  have h := boundedBooleanReconstruction_siteMatrix root D (j.val + 1)
  rw [Matrix.mul_assoc, booleanJetExtractionMatrix_mul_boundedSite] at h
  exact congrFun (congrFun h s) e

end Erdos3.VectorPolynomial

end

end OAI
