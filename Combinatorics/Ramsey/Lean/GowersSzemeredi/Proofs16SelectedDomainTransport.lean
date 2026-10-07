import GowersSzemeredi.Proofs16GoodGraphGeometry
import GowersSzemeredi.Proofs16CommonBaseAssembly
import GowersSzemeredi.Proofs16LargePieceMass

/-! A selected subdomain is sufficient for the exact large-piece argument.
It need not retain every point selected by the common-base construction. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The precise mass and unit-cover obligation after choosing a common base.
This proposition allows further selection inside its good domain. -/
def Section16SelectedUnitDomain {N k : Nat} [NeZero N] {theta gamma : Real}
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (D : Section16CommonBaseData theta gamma B phi) : Prop :=
  ∃ C : Finset (Point N (k + 1)), C ⊆ section16GoodDomain B (D.H ∩ D.J) D.Y D.x0 ∧
    (N : Real) ^ (k + 1) / multipleS theta gamma (k + 1) ≤ C.card ∧
    MultiplyLinearFunction gamma 1 C (section16PhiOne phi D.x0)

/-- Translation preserves the exact mass and cover of any selected part of
the good domain, without changing any common-base data field. -/
theorem section16_selected_domain_subrelation {N k : Nat} [NeZero N] [Fact N.Prime]
    (Gamma : Finset (Point N (k + 1) × ZMod N))
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (H : Finset (Point N k)) (Y : (h : Point N k) → Finset (Section16CubeElement B h))
    (x0 : Point N k) (C : Finset (Point N (k + 1))) {gamma r : Real}
    (hgraph : GraphContained B phi Gamma) (hC : C ⊆ section16GoodDomain B H Y x0)
    (hML : MultiplyLinearFunction gamma r C (section16PhiOne phi x0)) :
    ∃ E ⊆ Gamma, E.card = C.card ∧ MultiplyLinear gamma r E := by
  classical
  let t := appendCoordinate x0 (0 : ZMod N)
  let E := (partialGraph C (section16PhiOne phi x0)).image (fun z => (z.1 + t, z.2))
  have hinj : Function.Injective (fun z : Point N (k + 1) × ZMod N => (z.1 + t, z.2)) := by
    intro a b hab
    exact Prod.ext (add_right_cancel (Prod.mk.inj hab).1) (Prod.mk.inj hab).2
  refine ⟨E, ?_, ?_, MultiplyLinear.translate hML t⟩
  · exact (Finset.image_subset_image (Finset.image_subset_image hC)).trans
      (section16TranslatedGoodGraph_subset Gamma B phi H Y x0 hgraph)
  · rw [Finset.card_image_of_injective _ hinj, partialGraph_card]

/-- Covering the whole good domain implies the weaker selection obligation,
but the latter does not require that universal-witness assertion. -/
theorem Section16CommonBaseData.selected_unit_domain_of_full_cover
    {N k : Nat} [NeZero N] {theta gamma : Real}
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (D : Section16CommonBaseData theta gamma B phi)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hML : MultiplyLinearFunction gamma 1 (section16GoodDomain B (D.H ∩ D.J) D.Y D.x0)
      (section16PhiOne phi D.x0)) : Section16SelectedUnitDomain D := by
  refine ⟨_, Finset.Subset.rfl, ?_, hML⟩
  rw [section16GoodDomain_card]
  exact (section16_common_base_mass_budget ht ht1 hg hg1).trans D.good_mass

/-- A successful selection gives exactly the source large-piece mass. -/
theorem Section16SelectedUnitDomain.large_piece {N k : Nat} [NeZero N] [Fact N.Prime]
    {theta gamma : Real} {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    {D : Section16CommonBaseData theta gamma B phi} (h : Section16SelectedUnitDomain D)
    (Gamma : Finset (Point N (k + 1) × ZMod N)) (hgraph : GraphContained B phi Gamma) :
    ∃ E ⊆ Gamma, (N : Real) ^ (k + 1) / multipleS theta gamma (k + 1) ≤ E.card ∧
      MultiplyLinear gamma 1 E := by
  obtain ⟨C, hC, hm, hML⟩ := h
  obtain ⟨E, hE, heq, hcover⟩ := section16_selected_domain_subrelation Gamma B phi
    (D.H ∩ D.J) D.Y D.x0 C hgraph hC hML
  exact ⟨E, hE, by simpa only [heq] using hm, hcover⟩

end LeanProofs.GowersSzemeredi
