import GowersSzemeredi.Proofs16UniformFaceParameter
import GowersSzemeredi.Proofs15ZeroDensityRestriction

/-! Assemble the inductive extraction of Lemma 16.4 in every dimension.
Thresholds are uniform over the relation and its graph selections. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem relationProjection_graph_selection {N d : Nat}
    (Gamma : Finset (Point N d × ZMod N)) :
    ∃ phi : Point N d → ZMod N, GraphContained (relationProjection Gamma) phi Gamma := by
  classical
  let phi := fun x => if hx : ∃ y, (x, y) ∈ Gamma then Classical.choose hx else 0
  refine ⟨phi, ?_⟩
  intro x hx
  have hex : ∃ y, (x, y) ∈ Gamma := by
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hx
    exact ⟨z.2, by simpa [← hzx] using hz⟩
  exact (show (x, phi x) ∈ Gamma by
    dsimp [phi]
    rw [dif_pos hex]
    exact Classical.choose_spec hex)

theorem relationProjection_supported {N d : Nat}
    (Gamma : Finset (Point N d × ZMod N)) :
    RelationSupportedOn Gamma (relationProjection Gamma) := by
  intro z hz
  exact Finset.mem_image.mpr ⟨z, hz, rfl⟩

theorem lemma_16_4_extraction (k : Nat) (theta gamma : Real)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hth : ∀ l : Nat, 1 ≤ l → l ≤ k → Theorem162At l) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N → Odd N →
      ∀ Gamma : Finset (Point N (k + 1) × ZMod N),
        RelationProductProperty gamma Gamma →
        (∃ H : Finset (Point N (k + 1)), (H.card : Real) < theta * (N : Real) ^ (k + 1) ∧
          RelationSupportedOn Gamma H) ∨
        ∃ (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N),
          GraphContained B phi Gamma ∧ Section16StructuredPair theta gamma B phi := by
  obtain ⟨Np, hNp⟩ := restrict_proper_faces_common_parameter k hth gamma theta hg hg1 ht ht1
  have ht2 : 0 < theta / 2 := by positivity
  have ht21 : theta / 2 ≤ 1 := by linarith
  obtain ⟨Na, hNa⟩ := lemma_15_6_of_density_lower_all k (theta / 2) gamma ht2 ht21 hg hg1
  refine ⟨max Np Na, ?_⟩
  intro N _ _ hN ho Gamma hrelation
  by_cases hsmall : ((relationProjection Gamma).card : Real) < theta * (N : Real) ^ (k + 1)
  · exact Or.inl ⟨relationProjection Gamma, hsmall, relationProjection_supported Gamma⟩
  · obtain ⟨phi, hgraph⟩ := relationProjection_graph_selection Gamma
    have hprod := hrelation (relationProjection Gamma) phi hgraph
    obtain ⟨C, hCB, hCcard, hCfaces⟩ := hNp N ((le_max_left _ _).trans hN)
      (relationProjection Gamma) phi (le_of_not_gt hsmall) hprod
    obtain ⟨B, hBC, hcount, hrespect⟩ := hNa N ((le_max_right _ _).trans hN)
      (Fact.out : N.Prime) ho C phi hCcard (hprod.mono hCB)
    refine Or.inr ⟨B, phi, ?_, hCfaces.mono hBC, ?_, ?_⟩
    · intro x hx
      exact hgraph x (hCB (hBC hx))
    · have heq : theta / 2 * gamma / 2 = theta * gamma / 4 := by ring
      simpa only [section16ThetaOne, heq] using hcount
    · simpa only [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2), Real.rpow_ofNat,
        inv_pow] using hrespect

/-- The exact catalogue form of Lemma 16.4, including induction dimension zero. -/
theorem lemma_16_4_holds : lemma_16_4 := by
  intro k theta gamma ht ht1 hg hg1 hth
  obtain ⟨N0, hN0⟩ := lemma_16_4_extraction k theta gamma ht ht1 hg hg1 hth
  exact ⟨N0, fun N _ _ hN ho Gamma _hcard hprod => hN0 N hN ho Gamma hprod⟩

end LeanProofs.GowersSzemeredi
