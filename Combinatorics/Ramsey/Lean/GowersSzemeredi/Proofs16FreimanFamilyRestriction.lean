import GowersSzemeredi.Proofs16BaseCaseCubicExtraction
import GowersSzemeredi.Proofs16FaceInduction
import GowersSzemeredi.Proofs13RowCoefficients

/-! Retain fixed Freiman-family witnesses under restrictions and translations.
The one-dimensional product-property extraction loses only the requested
ambient mass, with no dependence on later box-cover losses.

`Section16FreimanFamilyCover.translate` is in
`Proofs16FreimanFamilyRestrictionSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-- A partial function is contained in a fixed family of order-eight Freiman graphs. -/
def Section16FreimanFamilyCover {N : Nat} [NeZero N] (q : Nat)
    (B : Finset (Point N 1)) (phi : Point N 1 → ZMod N) : Prop :=
  ∃ (D : Fin q → Finset (Point N 1)) (f : Fin q → Point N 1 → ZMod N),
    (∀ i, FreimanHom 8 (pointOneDomain (D i)) (pointOneMap (f i))) ∧
    partialGraph B phi ⊆ section16FinsetUnion (fun i => partialGraph (D i) (f i))

theorem Section16FreimanFamilyCover.mono {N q : Nat} [NeZero N]
    {B C : Finset (Point N 1)} {phi : Point N 1 → ZMod N}
    (h : Section16FreimanFamilyCover q B phi) (hCB : C ⊆ B) :
    Section16FreimanFamilyCover q C phi := by
  obtain ⟨D, f, hf, hc⟩ := h
  exact ⟨D, f, hf, (Finset.image_subset_image hCB).trans hc⟩

/-- Extract a large subset of a partial-function domain with a fixed family
bound. No modulus threshold or inner box-cover loss is used. -/
theorem section16_restrict_function_freiman_family {N : Nat} [Fact N.Prime]
    {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1)
    (B : Finset (Point N 1)) (phi : Point N 1 → ZMod N)
    (hprod : HasProductProperty B phi gamma) :
    ∃ C : Finset (Point N 1), C ⊆ B ∧
      (B.card : Real) - theta * N ≤ C.card ∧
      Section16FreimanFamilyCover (section16BaseFamilyBound gamma theta) C phi := by
  have hginv : 1 ≤ gamma ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)
  have hsize : ((partialGraph B phi).card : Real) ≤ gamma ^ (-(2 : Int)) * N := by
    rw [partialGraph_card]
    have hB : (B.card : Real) ≤ N := by
      exact_mod_cast (show B.card ≤ N by simpa [Point, ZMod.card] using Finset.card_le_univ B)
    exact hB.trans (le_mul_of_one_le_left (by positivity) hginv)
  obtain ⟨J, D, f, hJ, hf, hc⟩ := section16_extract_uniform_base_family hg hg1 ht ht1
    (partialGraph B phi) hsize (partialGraph_relationProductProperty hprod)
  refine ⟨B ∩ J, Finset.inter_subset_left, ?_, D, f, hf, ?_⟩
  · have hu : ((B ∪ J).card : Real) ≤ N := by
      exact_mod_cast (show (B ∪ J).card ≤ N by
        simpa [Point, ZMod.card] using Finset.card_le_univ (B ∪ J))
    have hs : ((B ∪ J).card : Real) + (B ∩ J).card = B.card + J.card := by
      exact_mod_cast Finset.card_union_add_card_inter B J
    nlinarith only [hu, hs, hJ]
  · rwa [restrictRelation_partialGraph] at hc

end LeanProofs.GowersSzemeredi
