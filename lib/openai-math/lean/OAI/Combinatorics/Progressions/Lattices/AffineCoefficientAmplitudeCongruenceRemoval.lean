import OAI.Combinatorics.Progressions.Lattices.RetainedAffineCommonCover

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

theorem exists_affine_coefficient_amplitude_residue_uniform_removal (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
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
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (F : (Option K × I → ℝ) → ℂ) (_hF : ∀ x, ‖F x‖ ≤ 1)
    {Lip : ℝ≥0} (_hLip : LipschitzWith Lip F) (_hLipP : (Lip : ℝ) ≤ Real.exp P),
    ∃ hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
        (residueProfileWidth stride V),
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride _hs V hV hZ z).toReal : ℂ) *
      (F (fun t => (residueLatticeArray residue stride z t : ℝ) / V t) *
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ)))‖ ≤ ε := by
  obtain ⟨A₀, _, hbudget⟩ := exists_mode_residue_threshold_exp_budget m
  obtain ⟨A, hA, habsorb⟩ := exists_natPolynomial_eval_budget
    ((2 * Polynomial.X + 2 + Polynomial.C A₀) ^ A₀)
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U C hC hCP frequency hbound hbad p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR residue V hV hwidth F hF Lip hLip hLipP
  let P' := 2 * P + 2
  have hPP : P ≤ P' := by dsimp [P']; linarith
  have hP' : 0 ≤ P' := hP.trans hPP
  have hExp := Real.exp_le_exp.mpr hPP
  have hacc := modeAmplitudeAccuracy_pos Lip.coe_nonneg hε
  have haccexp : 1 / modeAmplitudeAccuracy Lip ε ≤ Real.exp P' :=
    modeAmplitudeAccuracy_inv_le_exp hP Lip.coe_nonneg hLipP hε hεP
  have hcut : (P' + A₀) ^ A₀ ≤ (P + A) ^ A := by
    simpa [P', Polynomial.eval₂_pow] using habsorb P hP
  obtain ⟨hside, hrankBudget⟩ := hbudget (Fintype.card I) (Fintype.card (Option K × I))
    P' C 1 S ρ (modeAmplitudeAccuracy Lip ε) hP' (hn.trans hPP) (hd.trans hPP)
    hC (hCP.trans hExp) zero_le_one (Real.one_le_exp hP') hS (hSP.trans hExp)
    hρ (hρP.trans hExp) hacc haccexp
  exact affine_coefficient_amplitude_residue_removal_at_error U hC frequency hbound hbad
    p hp hm stride hs hS hρ hε hstride F hF hLip H
    (fun k => hside.trans ((Real.exp_le_exp.mpr hcut).trans (hsize k))) hrank
    (hrankBudget.trans ((Real.exp_le_exp.mpr hcut).trans hR)) residue V hV hwidth

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

theorem exists_affine_coefficient_amplitude_ambient_residue_removal (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
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
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (F : (Option K × I → ℝ) → ℂ) (_hF : ∀ x, ‖F x‖ ≤ 1)
    {Lip : ℝ≥0} (_hLip : LipschitzWith Lip F) (_hLipP : (Lip : ℝ) ≤ Real.exp P),
    ∃ hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
        (residueProfileWidth stride V),
    ‖∑' z : Option K × I → ℤ, ((residueSmoothPMF residue stride _hs V hV hZ z).toReal : ℂ) *
      (F (fun t => (z t : ℝ) / V t) *
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (z (k, j) : ℝ)))‖ ≤ ε := by
  obtain ⟨A, hA, hremove⟩ := exists_affine_coefficient_amplitude_residue_uniform_removal m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U C hC hCP frequency hbound hbad p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR residue V hV hwidth F hF Lip hLip hLipP
  obtain ⟨hZ, hrem⟩ := hremove hP hn hd U hC hCP frequency hbound hbad p hp hm stride hs hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR residue V hV hwidth F hF hLip hLipP
  refine ⟨hZ, ?_⟩
  rw [residueSmoothPMF_expectation]
  exact hrem

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

theorem exists_affine_coefficient_amplitude_congruence_removal (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
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
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (F : (Option K × I → ℝ) → ℂ) (_hF : ∀ x, ‖F x‖ ≤ 1)
    {Lip : ℝ≥0} (_hLip : LipschitzWith Lip F) (_hLipP : (Lip : ℝ) ≤ Real.exp P),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
      (F (fun t => (z t : ℝ) / V t) *
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (z (k, j) : ℝ)))‖ ≤ ε := by
  obtain ⟨A, hA, hremove⟩ := exists_affine_coefficient_amplitude_ambient_residue_removal m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U C hC hCP frequency hbound hbad p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR G hG V hV hwidth F hF Lip hLip hLipP
  have hh (r : G) := hremove hP hn hd U hC hCP frequency hbound hbad p hp hm stride hs hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR (columnResidueRepresentative stride r.val) V hV hwidth F hF hLip hLipP
  choose hZ hrem using hh
  exact selectedResidueSmoothPMF_bound_of_cells stride hs G hG V hV hZ _ hrem

end Erdos3.VectorPolynomial

end

end OAI
