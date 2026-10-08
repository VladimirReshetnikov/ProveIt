import GowersSzemeredi.Proofs16PolynomialCommonBaseCover
import GowersSzemeredi.Proofs16CubicStructuredCover

/-! Dense graph pieces with polynomial spectrum-count recurrence controls.

In dimension two the spectrum cover and cubic slice provider are constructed
from the existing base case. Thus these pieces do not assume a new structure
theorem or an external slice provider. The constants C and p come from the
proved simultaneous recurrence and are existential.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section16PolynomialCubicTwoExponent (C p q : Nat) (theta gamma rho : Real) : Real :=
  let Qb := fun _ : Real => ((3 * section16CubicSpectrumCount theta gamma : Nat) : Real)
  let Eb := cubicBaseExponent (section16CubicSpectrumCount theta gamma)
  section16CappedWidthExponent
    (section16PolynomialCubicExponent 1 p q theta gamma Qb Eb rho)
    (section16PolynomialCubicThreshold 1 C p q theta gamma Qb Eb rho)

/-- Construct the slice and spectrum inputs for a structured two-dimensional
pair, retaining the selected mass and translating the cover into its graph. -/
theorem exists_polynomial_cubic_structured_piece :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ (N q : Nat) [NeZero N] [Fact N.Prime], 0 < q →
    ∀ (theta gamma : Real), 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    ∀ (B : Finset (Point N 2)) (phi : Point N 2 → ZMod N),
      Section16StructuredPair theta gamma B phi → Section16FinalFreimanFamilies q B phi →
      ∃ Gamma : Finset (Point N 2 × ZMod N), Gamma ⊆ partialGraph B phi ∧
        section16ThetaTwo (section16ThetaOne theta gamma 1) * (N : Real)^2 ≤ Gamma.card ∧
        MultiplyLinearWith (section16CubicTwoGraphBound q theta gamma)
          (section16PolynomialCubicTwoExponent C p q theta gamma) Gamma := by
  obtain ⟨C, p, hC, hp, hcover⟩ := exists_polynomial_common_base_cover 1
  refine ⟨C, p, hC, hp, ?_⟩
  intro N q _ _ hq theta gamma ht ht1 hg hg1 B phi h hf
  obtain ⟨D, _⟩ := section16_cubic_common_base_line_covers ht ht1 hg hg1 h
  have hslice := (hf.good_domain (D.H ∩ D.J) D.Y D.x0).cubic_slice_provider hq
  have hML := hcover N (by decide) theta gamma ht ht1 hg hg1 _ _
    (fun s hs hs1 => ⟨by positivity,
      cubicBaseExponent_pos (section16CubicSpectrumCount_pos theta gamma) hs,
      cubicBaseExponent_le_one (section16CubicSpectrumCount_pos theta gamma) hs hs1⟩)
    B phi D h q hq hslice
  refine ⟨section16TranslatedGoodGraph B phi (D.H ∩ D.J) D.Y D.x0, ?_, ?_, ?_⟩
  · apply section16TranslatedGoodGraph_subset
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · rw [section16TranslatedGoodGraph_card]
    exact D.good_mass
  · convert hML.translate (appendCoordinate D.x0 0) using 1 <;>
      norm_num [section16CubicTwoGraphBound, section16PolynomialCubicTwoExponent,
        section16TranslatedGoodGraph]
    all_goals
      funext rho
      simp [section16CubicTwoGraphBound, section16PolynomialCubicTwoExponent]

/-- An unconditional dense product-property graph piece with the new
polynomial recurrence controls, uniform in the graph and ambient prime. -/
theorem exists_polynomial_cubic_product_graph_piece :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ (theta gamma : Real), 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N → Odd N →
      ∀ (B : Finset (Point N 2)) (phi : Point N 2 → ZMod N),
        theta * (N : Real)^2 ≤ B.card → HasProductProperty B phi gamma →
        ∃ Gamma : Finset (Point N 2 × ZMod N), Gamma ⊆ partialGraph B phi ∧
          section16ThetaTwo (section16ThetaOne (theta / 2) gamma 1) * (N : Real)^2 ≤ Gamma.card ∧
          MultiplyLinearWith
            (section16CubicTwoGraphBound (section16BaseFamilyBound gamma (theta / 4)) (theta / 2) gamma)
            (section16PolynomialCubicTwoExponent C p
              (section16BaseFamilyBound gamma (theta / 4)) (theta / 2) gamma) Gamma := by
  obtain ⟨C, p, hC, hp, hpiece⟩ := exists_polynomial_cubic_structured_piece
  refine ⟨C, p, hC, hp, ?_⟩
  intro theta gamma ht ht1 hg hg1
  obtain ⟨N0, hN0⟩ := section16_cubic_structured_extraction ht ht1 hg hg1
  refine ⟨N0, ?_⟩
  intro N _ _ hN ho B phi hB hprod
  obtain ⟨D, hDB, hD, hf⟩ := hN0 N hN ho B phi hB hprod
  obtain ⟨Gamma, hG, hmass, hML⟩ := hpiece N (section16BaseFamilyBound gamma (theta / 4))
    (section16BaseFamilyBound_pos gamma (theta / 4)) (theta / 2) gamma
    (by positivity) (by linarith) hg hg1 D phi hD hf
  exact ⟨Gamma, hG.trans (Finset.image_subset_image hDB), hmass, hML⟩

end LeanProofs.GowersSzemeredi
