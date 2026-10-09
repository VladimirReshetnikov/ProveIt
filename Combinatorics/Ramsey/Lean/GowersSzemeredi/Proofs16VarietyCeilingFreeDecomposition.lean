import GowersSzemeredi.Proofs16VarietyLossPower
import GowersSzemeredi.Proofs16PolynomialVarietyRelationDecomposition

/-! The actual dimension-three relation decomposition with no inner-loss
ceilings or rounded thresholds in its controls. Deep variety structure
and all unquantified structure constants remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section16VarietyThreeCeilingFreeGraphBound (D : Nat) (theta gamma : Real) : Real → Real :=
  section16VarietyCeilingFreeGraphBound (section16VarietyExtractionCount D gamma (theta / 4)) theta gamma

def section16VarietyThreeCeilingFreeExponent (C p Cv pv Cs ps D : Nat)
    (theta gamma : Real) : Real → Real :=
  section16VarietyCeilingFreeExponent C p Cv pv D
    (section16VarietyExtractionCount D gamma (theta / 4))
    (9 * section16VarietySpectrumCount D (theta / 2) gamma)
    (section16VarietyExtractionDensity gamma (theta / 4)) theta gamma
    (section16PolynomialJointVarietyExponent Cs ps
      (section16VarietySpectrumCount D (theta / 2) gamma) D
      (section16VarietySpectrumDensity (theta / 2) gamma))

theorem MultiplyLinearWith.variety_three_ceiling_free {N C p Cv pv Cs ps D : Nat}
    [NeZero N] {theta gamma : Real} {Gamma : Finset (Point N 3 × ZMod N)}
    (h : MultiplyLinearWith (section16VarietyThreeGraphBound D theta gamma)
      (section16VarietyThreePieceExponent C p Cv pv Cs ps D theta gamma) Gamma)
    (hC : 2 ≤ C) (hp : 0 < p) (hCv : 2 ≤ Cv) (hpv : 0 < pv) (hCs : 2 ≤ Cs) (hps : 0 < ps)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    MultiplyLinearWith (section16VarietyThreeCeilingFreeGraphBound D theta gamma)
      (section16VarietyThreeCeilingFreeExponent C p Cv pv Cs ps D theta gamma) Gamma := by
  obtain ⟨hc, hc1⟩ := section16VarietyExtractionDensity_pos_le_one gamma
    (by positivity : 0 < theta / 4) (by linarith : theta / 4 ≤ 1)
  obtain ⟨hcs, hcs1⟩ := section16VarietySpectrumDensity_pos_le_one
    (by positivity : 0 < theta / 2) (by linarith : theta / 2 ≤ 1) hg hg1
  have hE := section16PolynomialJointVarietyExponent_pos Cs
    (section16VarietySpectrumCount D (theta / 2) gamma) D hps hcs hcs1
  have hE1 := section16PolynomialJointVarietyExponent_le_one hCs hps
    (section16VarietySpectrumCount D (theta / 2) gamma) D hcs hcs1
  apply MultiplyLinearWith.variety_ceiling_free_controls
    (q := 9 * section16VarietySpectrumCount D (theta / 2) gamma)
    (C := C) (p := p) (Cv := Cv) (pv := pv) (D := D)
    _ hC hCv hp hpv hc hc1 ht ht1 hg hg1 hE hE1
  apply h.congr_controls
  · intro rho _ _
    rfl
  · intro rho _ _
    dsimp only [section16VarietyThreePieceExponent, section16PolynomialVarietyThreeExponent]
    simp only [Nat.cast_mul, Nat.cast_ofNat]

/-- The statement of `exists_ceiling_free_variety_relation_decomposition` at fixed constants. -/
def CeilingFreeVarietyRelationDecompositionAt (C p Cv pv Cs ps : Nat) : Prop :=
  ∀ D : Nat, MilicevicDeepVarietyStructure D →
  ∀ (theta gamma : Real), 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N 3 × ZMod N),
        (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real)^3 →
        RelationProductProperty gamma Gamma →
        ∃ q : Nat, ∃ G : Fin q → Finset (Point N 3 × ZMod N), ∃ J : Finset (Point N 3),
          (∀ i, G i ⊆ Gamma ∧ MultiplyLinearWith
            (section16VarietyThreeCeilingFreeGraphBound D theta gamma)
            (section16VarietyThreeCeilingFreeExponent C p Cv pv Cs ps D theta gamma)
            (G i)) ∧
          (q : Real) ≤ gamma ^ (-(2 : Int)) / section16VarietyPieceMass theta gamma ∧
          (1 - theta) * (N : Real)^3 ≤ J.card ∧
          restrictRelation Gamma J ⊆ section16FinsetUnion G

/-- `exists_ceiling_free_variety_relation_decomposition` at the constants of its input. -/
theorem ceilingFreeVarietyRelationDecompositionAt_of {C p Cv pv Cs ps : Nat} (hC : 2 ≤ C) (hp : 0 < p) (hCv : 2 ≤ Cv) (hpv : 0 < pv) (hCs : 2 ≤ Cs) (hps : 0 < ps)
    (hcover : PolynomialVarietyRelationDecompositionAt C p Cv pv Cs ps) : CeilingFreeVarietyRelationDecompositionAt C p Cv pv Cs ps := by
  unfold CeilingFreeVarietyRelationDecompositionAt
  intro D hD theta gamma ht ht1 hg hg1
  obtain ⟨N0, hN0⟩ := hcover D hD theta gamma ht ht1 hg hg1
  refine ⟨N0, ?_⟩
  intro N _ _ hN Gamma hcard hprod
  obtain ⟨q, G, J, hG, hq, hJ, hcov⟩ := hN0 N hN Gamma hcard hprod
  exact ⟨q, G, J, fun i => ⟨(hG i).1,
    (hG i).2.variety_three_ceiling_free hC hp hCv hpv hCs hps ht ht1 hg hg1⟩, hq, hJ, hcov⟩

/-- Actual relation covers inherit the explicit inner-loss powers, without
any additional geometric assumptions beyond deep variety structure. -/
theorem exists_ceiling_free_variety_relation_decomposition :
  ∃ C p Cv pv Cs ps : Nat, 2 ≤ C ∧ 0 < p ∧ 2 ≤ Cv ∧ 0 < pv ∧ 2 ≤ Cs ∧ 0 < ps ∧
  ∀ D : Nat, MilicevicDeepVarietyStructure D →
  ∀ (theta gamma : Real), 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N 3 × ZMod N),
        (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real)^3 →
        RelationProductProperty gamma Gamma →
        ∃ q : Nat, ∃ G : Fin q → Finset (Point N 3 × ZMod N), ∃ J : Finset (Point N 3),
          (∀ i, G i ⊆ Gamma ∧ MultiplyLinearWith
            (section16VarietyThreeCeilingFreeGraphBound D theta gamma)
            (section16VarietyThreeCeilingFreeExponent C p Cv pv Cs ps D theta gamma)
            (G i)) ∧
          (q : Real) ≤ gamma ^ (-(2 : Int)) / section16VarietyPieceMass theta gamma ∧
          (1 - theta) * (N : Real)^3 ≤ J.card ∧
          restrictRelation Gamma J ⊆ section16FinsetUnion G := by
  obtain ⟨C, p, Cv, pv, Cs, ps, hC, hp, hCv, hpv, hCs, hps, hcover⟩ := exists_polynomial_variety_relation_decomposition
  exact ⟨C, p, Cv, pv, Cs, ps, hC, hp, hCv, hpv, hCs, hps, ceilingFreeVarietyRelationDecompositionAt_of hC hp hCv hpv hCs hps hcover⟩

end LeanProofs.GowersSzemeredi
