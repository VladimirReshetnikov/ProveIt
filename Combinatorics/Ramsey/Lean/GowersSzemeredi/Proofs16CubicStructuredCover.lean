import GowersSzemeredi.Proofs16CubicCommonBase
import GowersSzemeredi.Proofs16CubicAllScaleCover
import GowersSzemeredi.Proofs16CubicStructuredExtraction
import GowersSzemeredi.Proofs16GoodGraphGeometry

/-! A genuine dimension-two graph piece with explicit all-box controls.
Both the spectrum and slice inputs are constructed from the preceding
extractions. The result retains a positive density and lies in the original
graph. Comparison with the manuscript's prescribed controls remains separate. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem MultiplyLinearWith.translate {N k : Nat} [NeZero N] [Fact N.Prime]
    {Qb Eb : Real → Real} {Gamma : Finset (Point N k × ZMod N)}
    (h : MultiplyLinearWith Qb Eb Gamma) (t : Point N k) :
    MultiplyLinearWith Qb Eb (Gamma.image (fun z => (z.1 + t, z.2))) := by
  classical
  intro theta ht ht1 P hP
  obtain ⟨M, q, H, Q, mu, hH, hHcard, hpart, hproper, hq, hw, hmu, hcover⟩ :=
    h theta ht ht1 (P.translate (-t)) (hP.translate (-t))
  refine ⟨M, q, H.image (fun x => x + t), fun j => (Q j).translate t,
    fun j i x => mu j i (x + -t), ?_, ?_, ?_, fun j => (hproper j).translate t,
    hq, ?_, fun j i => (hmu j i).translate (-t), ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hh := (Box.translate_mem_carrier (P.translate (-t)) t y).mpr (hH hy)
    simpa using hh
  · rw [Finset.card_image_of_injective _ (add_left_injective t)]
    simpa using hHcard
  · simpa using hpart.translate t
  · intro j
    simpa using hw j
  · intro j x hx hh y hxy
    obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp hxy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    have haQ := (Box.translate_mem_carrier (Q j) t a).mp hx
    have haH := (add_left_injective t).mem_finset_image.mp hh
    obtain ⟨i, hi⟩ := hcover j a haQ haH b hab
    exact ⟨i, by simpa using hi⟩

def section16CubicTwoGraphBound (q : Nat) (theta gamma rho : Real) : Real :=
  max (section16CubicLiftGraphBound q 1 (rho / 4) theta gamma) 9

def section16CubicTwoExponent (q : Nat) (theta gamma rho : Real) : Real :=
  let Qd := fun _ : Real => ((3 * section16CubicSpectrumCount theta gamma : Nat) : Real)
  let Ed := cubicBaseExponent (section16CubicSpectrumCount theta gamma)
  section16CappedWidthExponent
    (section16CubicLiftExponent q 1 (rho / 4) theta gamma Qd Ed)
    (section16CubicLiftThreshold q 1 (rho / 4) theta gamma Qd Ed)

theorem section16CubicTwoExponent_pos {q : Nat} {theta gamma rho : Real}
    (hq : 0 < q) (ht : 0 < theta) (hg : 0 < gamma) (hr : 0 < rho) :
    0 < section16CubicTwoExponent q theta gamma rho := by
  apply section16CappedWidthExponent_pos
  exact section16CubicLiftExponent_pos hq (by decide) (by positivity) ht hg
    (cubicBaseExponent_pos (section16CubicSpectrumCount_pos theta gamma) (by positivity))

/-- Construct both inputs to the affine lift and translate its output back
inside the original graph without losing any of its selected mass. -/
theorem section16_cubic_structured_piece {N q : Nat} [Fact N.Prime]
    {theta gamma : Real} {B : Finset (Point N 2)} {phi : Point N 2 → ZMod N}
    (hq : 0 < q) (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (h : Section16StructuredPair theta gamma B phi)
    (hf : Section16FinalFreimanFamilies q B phi) :
    ∃ Gamma : Finset (Point N 2 × ZMod N), Gamma ⊆ partialGraph B phi ∧
      section16ThetaTwo (section16ThetaOne theta gamma 1) * (N : Real)^2 ≤ Gamma.card ∧
      MultiplyLinearWith (section16CubicTwoGraphBound q theta gamma)
        (section16CubicTwoExponent q theta gamma) Gamma := by
  obtain ⟨D, hline⟩ := section16_cubic_common_base_line_covers ht ht1 hg hg1 h
  have hslice := (hf.good_domain (D.H ∩ D.J) D.Y D.x0).cubic_slice_provider hq
  have hML := hline.cubic_multiplyLinearWith hq hslice (by decide) ht ht1 hg hg1
    (fun s hs _ => cubicBaseExponent_pos (section16CubicSpectrumCount_pos theta gamma) hs)
  refine ⟨section16TranslatedGoodGraph B phi (D.H ∩ D.J) D.Y D.x0, ?_, ?_, ?_⟩
  · apply section16TranslatedGoodGraph_subset
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · rw [section16TranslatedGoodGraph_card]
    exact D.good_mass
  · convert hML.translate (appendCoordinate D.x0 0) using 1 <;>
      norm_num [section16CubicTwoGraphBound, section16CubicTwoExponent, section16TranslatedGoodGraph]
    all_goals
      funext rho
      simp [section16CubicTwoGraphBound, section16CubicTwoExponent]


/-- Unconditional extraction from a dense two-dimensional product-property
graph, with explicit controls uniform in the ambient prime and in the graph. -/
theorem section16_cubic_product_graph_piece {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N → Odd N →
      ∀ (B : Finset (Point N 2)) (phi : Point N 2 → ZMod N),
        theta * (N : Real)^2 ≤ B.card → HasProductProperty B phi gamma →
        ∃ Gamma : Finset (Point N 2 × ZMod N), Gamma ⊆ partialGraph B phi ∧
          section16ThetaTwo (section16ThetaOne (theta / 2) gamma 1) * (N : Real)^2 ≤ Gamma.card ∧
          MultiplyLinearWith
            (section16CubicTwoGraphBound (section16BaseFamilyBound gamma (theta / 4)) (theta / 2) gamma)
            (section16CubicTwoExponent (section16BaseFamilyBound gamma (theta / 4)) (theta / 2) gamma)
            Gamma := by
  obtain ⟨N0, hN0⟩ := section16_cubic_structured_extraction ht ht1 hg hg1
  refine ⟨N0, ?_⟩
  intro N _ _ hN ho B phi hB hprod
  obtain ⟨C, hCB, hC, hf⟩ := hN0 N hN ho B phi hB hprod
  obtain ⟨Gamma, hG, hmass, hML⟩ := section16_cubic_structured_piece
    (section16BaseFamilyBound_pos gamma (theta / 4)) (by positivity) (by linarith) hg hg1 hC hf
  exact ⟨Gamma, hG.trans (Finset.image_subset_image hCB), hmass, hML⟩

end LeanProofs.GowersSzemeredi
