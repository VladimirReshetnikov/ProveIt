import OAI.Combinatorics.Progressions.Fourier.CoefficientResidualCharacter

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

theorem coefficientResidualFunctional_eq_zero_iff_oneSite {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (t : K → ℤ) (difference : Fin 0 → K → ℤ)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
    coefficientResidualFunctional U t frequency = 0 ↔
      affineCubeModeFactors U t difference frequency := by
  change (coefficientArrayFunctional U frequency).comp (coefficientResidualArray U t) = 0 ↔ _
  rw [coefficientResidualArray_factor_iff]
  have hsite : (fun s : Finset (Fin 0) => affineSite (fun k => (t k : ℝ))
      (fun i k => (difference i k : ℝ)) s) =
      (fun (_s : Finset (Fin 0)) (k : Option K) => k.elim (1 : ℝ) (fun k => (t k : ℝ))) := by
    funext s k
    have hs : s = ∅ := Subsingleton.elim _ _
    subst s
    cases k <;> simp [affineSite]
  constructor
  · rintro ⟨M, hM⟩ j
    obtain ⟨Mj, hMj⟩ := coefficientArray_factor_to_bounded_site U t (∅ : Finset (Fin 0)) frequency M hM j
    refine ⟨Mj, ?_⟩
    let L := (coefficientFunctional (fun d a => (frequency j d a : ℝ))).comp (map (U j).subtype)
    have hb : ∀ p : VectorPolynomial K ℝ (U j), DegreeLE (1 : K → ℕ) (j.val + 1) p →
        L p = Mj (VectorPolynomial.siteEvaluation (fun _ : Finset (Fin 0) => fun k => (t k : ℝ)) p) := hMj
    have hh := (homogeneous_site_factorization_iff (j.val + 1)
      (fun _ : Finset (Fin 0) => fun k => (t k : ℝ)) L Mj).mpr hb
    change ∀ p, Homogeneous (j.val + 1) p → affineModeLift L p = _ at hh
    simpa only [L, affineModeLift_comp_map, LinearMap.comp_apply, hsite] using hh
  · intro hf
    apply coefficientArray_factor_of_bounded_site (S := Finset (Fin 0)) U t frequency
    intro j
    obtain ⟨Mj, hMj⟩ := affineCubeModeFactors_bounded U t difference frequency hf j
    refine ⟨Mj, ?_⟩
    have he : (fun (s : Finset (Fin 0)) k => ((affineSite t difference s (some k) : ℤ) : ℝ)) =
        (fun (_s : Finset (Fin 0)) k => (t k : ℝ)) := by
      funext s k
      have hs : s = ∅ := Subsingleton.elim _ _
      subst s
      simp [affineSite]
    simpa only [he] using hMj

end Erdos3.BooleanCubeKernel

end

end OAI
