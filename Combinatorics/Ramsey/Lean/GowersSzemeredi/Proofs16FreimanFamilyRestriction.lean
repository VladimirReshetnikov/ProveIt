import GowersSzemeredi.Proofs16BaseCaseCubicExtraction
import GowersSzemeredi.Proofs16FaceInduction
import GowersSzemeredi.Proofs13RowCoefficients

/-! Retain fixed Freiman-family witnesses under restrictions and translations.
The one-dimensional product-property extraction loses only the requested
ambient mass, with no dependence on later box-cover losses. -/
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

/-- Translate the graph domains and precompose the functions by the inverse
translation. Equal-length additive relations are preserved. -/
theorem Section16FreimanFamilyCover.translate {N q : Nat} [NeZero N]
    {B : Finset (Point N 1)} {phi : Point N 1 → ZMod N}
    (h : Section16FreimanFamilyCover q B phi) (t : Point N 1) :
    Section16FreimanFamilyCover q (B.image (fun x => x + t)) (fun x => phi (x - t)) := by
  classical
  obtain ⟨D, f, hf, hc⟩ := h
  let D' := fun i => (D i).image (fun x => x + t)
  let f' := fun i x => f i (x - t)
  refine ⟨D', f', ?_, ?_⟩
  · intro i
    have hh := (hf i).translate_input (-(t 0)) (J := pointOneDomain (D' i)) (by
      intro z hz
      rw [mem_pointOneDomain] at hz ⊢
      obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hz
      have heval := congrFun heq 0
      have hpoint : (pointOneEquiv N).symm (-t 0 + z) = x := by
        funext j
        fin_cases j
        change -t 0 + z = x 0
        change x 0 + t 0 = z at heval
        rw [← heval]
        abel
      rwa [hpoint])
    convert hh using 1
    funext z
    change f i ((pointOneEquiv N).symm z - t) = f i ((pointOneEquiv N).symm (-t 0 + z))
    congr 1
    funext j
    fin_cases j
    change z - t 0 = -t 0 + z
    abel
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have horig := hc (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp horig
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hi
    have hwx : w = x := congrArg Prod.fst heq
    subst w
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨x + t, ?_, ?_⟩⟩
    · exact Finset.mem_image.mpr ⟨x, hw, rfl⟩
    · simpa [f', add_sub_cancel_right] using heq

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
  classical
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
