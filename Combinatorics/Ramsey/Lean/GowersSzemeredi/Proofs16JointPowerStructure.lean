import GowersSzemeredi.Proofs16JointPowerProfile
import GowersSzemeredi.Proofs16PowerDecomposition

/-! The contextual lift and finite extraction give a genuine structural
cover with their actual quantitative controls. This large-box assertion
keeps its threshold and does not assert the unresolved source controls. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A product relation, restricted to a set of almost full projected mass,
has a joint proper multilinear cover with uniform explicit power controls.
Only the preceding exact structural dimensions are assumed. -/
theorem section16_joint_power_structure_of_dimension_induction {k : Nat} (hk : 1 ≤ k)
    (hth : ∀ l : Nat, 1 ≤ l → l ≤ k → Theorem162At l)
    (theta gamma : Real) (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N (k + 1) × ZMod N),
        (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ (k + 1) →
        RelationProductProperty gamma Gamma →
        ∃ J : Finset (Point N (k + 1)),
          (1 - theta) * (N : Real) ^ (k + 1) ≤ J.card ∧
          Section16JointPowerCoverProfile theta gamma k (restrictRelation Gamma J) := by
  obtain ⟨N0, hN0⟩ := section16_power_decomposition_of_dimension_induction hk hth
    theta gamma ht ht1 hg hg1
  refine ⟨N0, fun N _ _ hN Gamma hcard hprod => ?_⟩
  obtain ⟨q, G, J, hG, hq, hJ, hc⟩ := hN0 N hN Gamma hcard hprod
  have h := section16_joint_power_profile_of_pieces hk ht ht1 hg hg1 G (fun i => (hG i).2) hq
  exact ⟨J, hJ, fun rho hr hr1 => (h rho hr hr1).mono hc⟩

/-- The two-dimensional instance has no remaining structural or lifting
hypothesis. Its positive exponent and finite starting width are the actual
ones proved by the contextual construction and finite refinement. -/
theorem section16_bilinear_joint_power_structure
    (theta gamma : Real) (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N 2 × ZMod N),
        (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ 2 →
        RelationProductProperty gamma Gamma →
        ∃ J : Finset (Point N 2), (1 - theta) * (N : Real) ^ 2 ≤ J.card ∧
          Section16JointPowerCoverProfile theta gamma 1 (restrictRelation Gamma J) := by
  apply section16_joint_power_structure_of_dimension_induction (k := 1) le_rfl _ theta gamma ht ht1 hg hg1
  intro l hl hl1
  have heq : l = 1 := by omega
  subst l
  exact lemma_16_3_holds

end LeanProofs.GowersSzemeredi
