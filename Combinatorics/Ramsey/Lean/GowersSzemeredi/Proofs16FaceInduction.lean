import GowersSzemeredi.Proofs16CoordinateFaces
import GowersSzemeredi.Proofs16Basic

/-! Applying the lower-dimensional induction hypothesis to a partial
function and to any one of its coordinate faces, with exact deletion loss. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem partialGraph_card {N l : Nat} (B : Finset (Point N l))
    (phi : Point N l → ZMod N) : (partialGraph B phi).card = B.card := by
  classical
  exact Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)

theorem restrictRelation_partialGraph {N l : Nat} (B J : Finset (Point N l))
    (phi : Point N l → ZMod N) :
    restrictRelation (partialGraph B phi) J = partialGraph (B ∩ J) phi := by
  classical
  ext ⟨x, y⟩
  simp [restrictRelation, partialGraph, and_assoc, and_comm]

theorem MultiplyLinearFunction.mono {N l : Nat} [NeZero N]
    {B C : Finset (Point N l)} {phi : Point N l → ZMod N} {gamma r : Real}
    (h : MultiplyLinearFunction gamma r B phi) (hCB : C ⊆ B) :
    MultiplyLinearFunction gamma r C phi := by
  exact multiplyLinear_downward_closed_holds N l gamma r _ _
    (Finset.image_subset_image hCB) h

theorem ProperCrossSectionsMultiplyLinear.mono {N d : Nat} [NeZero N]
    {B C : Finset (Point N d)} {phi : Point N d → ZMod N} {gamma r : Real}
    (h : ProperCrossSectionsMultiplyLinear gamma r B phi) (hCB : C ⊆ B) :
    ProperCrossSectionsMultiplyLinear gamma r C phi := by
  intro l hl F
  exact (h l hl F).mono (F.domain_mono hCB)

/-- The relation formulation of the induction hypothesis gives a subset of
a partial-function domain, losing at most theta*N^l points. -/
theorem Theorem162At.restrict_function {l : Nat} (hth : Theorem162At l)
    (gamma theta : Real) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ (B : Finset (Point N l)) (phi : Point N l → ZMod N),
        HasProductProperty B phi gamma →
        ∃ B' : Finset (Point N l), B' ⊆ B ∧
          (B.card : Real) - theta * (N : Real) ^ l ≤ B'.card ∧
          MultiplyLinearFunction gamma (gamma ^ (-(2 : Int)) * multipleS theta gamma l) B' phi := by
  obtain ⟨N0, hN0⟩ := hth gamma theta hg hg1 ht ht1
  refine ⟨N0, ?_⟩
  intro N _ _ hN B phi hprod
  have hginv : 1 ≤ gamma ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)
  have hB : (B.card : Real) ≤ (N : Real) ^ l := by
    exact_mod_cast (show B.card ≤ N ^ l by simpa [Point, ZMod.card] using Finset.card_le_univ B)
  have hgraph : ((partialGraph B phi).card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ l := by
    rw [partialGraph_card]
    exact hB.trans (le_mul_of_one_le_left (by positivity) hginv)
  obtain ⟨J, hJ, hcover⟩ := hN0 N hN (partialGraph B phi) hgraph (partialGraph_relationProductProperty hprod)
  refine ⟨B ∩ J, Finset.inter_subset_left, ?_, ?_⟩
  · have hsum : ((B ∪ J).card : Real) + (B ∩ J).card = B.card + J.card := by
      exact_mod_cast Finset.card_union_add_card_inter B J
    have hunion : ((B ∪ J).card : Real) ≤ (N : Real) ^ l := by
      exact_mod_cast (show (B ∪ J).card ≤ N ^ l by
        simpa [Point, ZMod.card] using Finset.card_le_univ (B ∪ J))
    linarith
  · rw [restrictRelation_partialGraph] at hcover
    exact hcover

/-- The threshold for this face restriction is independent of the ambient
dimension, the chosen face, and the partial-function domain. -/
theorem Theorem162At.restrict_coordinate_face {l : Nat} (hth : Theorem162At l)
    (gamma theta : Real) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∃ N0 : Nat, ∀ (N d : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ (B : Finset (Point N d)) (phi : Point N d → ZMod N),
        HasProductProperty B phi gamma → ∀ F : CoordinateFace N d l,
          ∃ B' : Finset (Point N l), B' ⊆ F.domain B ∧
            ((F.domain B).card : Real) - theta * (N : Real) ^ l ≤ B'.card ∧
            MultiplyLinearFunction gamma (gamma ^ (-(2 : Int)) * multipleS theta gamma l)
              B' (F.pullback phi) := by
  obtain ⟨N0, hN0⟩ := hth.restrict_function gamma theta hg hg1 ht ht1
  exact ⟨N0, fun N d _ _ hN B phi hprod F =>
    hN0 N hN (F.domain B) (F.pullback phi) (hprod.coordinateFace F)⟩

end LeanProofs.GowersSzemeredi
