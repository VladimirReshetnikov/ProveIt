import OAI.Combinatorics.Progressions.Lattices.AnchoredCoefficientResidueAmbient

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem exists_anchored_affine_coefficient_congruence_removal (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    (origin : Option K → I → ℝ)
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (_hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (origin + fun k j => (z (k, j) : ℝ))‖ ≤ ε := by
  obtain ⟨A, hA, hremove⟩ := exists_anchored_affine_coefficient_ambient_residue_removal m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ origin J _ P hP hn hd U C hC hCP frequency hbound hbad p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR G hG V hV hwidth
  have hh (r : G) := hremove origin hP hn hd U hC hCP frequency hbound hbad p hp hm stride hs hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR (columnResidueRepresentative stride r.val) V hV hwidth
  choose hZ hrem using hh
  exact selectedResidueSmoothPMF_bound_of_cells stride hs G hG V hV hZ _ hrem

end Erdos3.VectorPolynomial

end

end OAI
