import GowersSzemeredi.Proofs16RemainderCover
import GowersSzemeredi.Proofs16CommonBaseAssembly
import GowersSzemeredi.Proofs16FinalSections
import GowersSzemeredi.Proofs16Lemma9

/-! The actual common-base data and structured pair now construct the
line-cover and section-cover inputs to the final Section 16 lifting step. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Lemma 16.9 applies to the constructed common-base data: its remainder
premise follows from the proper-face covers rather than an extra assumption. -/
theorem Section16CommonBaseData.all_box_line_covers
    {N k : Nat} [NeZero N] [Fact N.Prime] {theta gamma : Real}
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (D : Section16CommonBaseData theta gamma B phi)
    (h : Section16StructuredPair theta gamma B phi) (hk : 1 ≤ k)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    Section16AllBoxLineCovers theta gamma (section16GoodDomain B (D.H ∩ D.J) D.Y D.x0)
      (section16PhiOne phi D.x0) := by
  exact section16_all_box_line_covers N k hk theta gamma ht ht1 hg hg1
    B phi D.H D.J (D.H ∩ D.J) D.Y D.phiPrime D.x0 rfl
    D.spectrum D.selection D.identity
    (h.good_domain_remainder_cover hk ht ht1 hg hg1 (D.H ∩ D.J) D.Y D.x0)

/-- Both geometric cover inputs to the final lift hold for the genuine
common-base construction. The stronger unit-parameter conclusion is still
an independent obligation; the unrestricted packaged lemma is not used. -/
theorem Section16CommonBaseData.lifting_cover_inputs
    {N k : Nat} [NeZero N] [Fact N.Prime] {theta gamma : Real}
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (D : Section16CommonBaseData theta gamma B phi)
    (h : Section16StructuredPair theta gamma B phi) (hk : 1 ≤ k)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    FinalCoordinateSectionsMultiplyLinear gamma
      (gamma ^ (-(2 : Int)) * multipleS ((2 : Real) ^ (-(k + 2 : Real)) * theta) gamma k)
      (section16GoodDomain B (D.H ∩ D.J) D.Y D.x0) (section16PhiOne phi D.x0) ∧
    Section16AllBoxLineCovers theta gamma (section16GoodDomain B (D.H ∩ D.J) D.Y D.x0)
      (section16PhiOne phi D.x0) :=
  ⟨h.good_domain_final_sections (D.H ∩ D.J) D.Y D.x0,
    D.all_box_line_covers h hk ht ht1 hg hg1⟩

end LeanProofs.GowersSzemeredi
