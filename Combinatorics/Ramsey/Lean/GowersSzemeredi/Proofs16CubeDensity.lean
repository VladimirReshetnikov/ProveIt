import GowersSzemeredi.Proofs16InducedCounting

/-! # Identifying cube-counting functions with domain fibre cardinalities -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- A fixed-side, fixed-cross-section cube is determined by its base point. -/
theorem section16_cube_fibre_card {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (h : Point N k) (s : ZMod N) :
    ((section16CubeMultifunctionDomain B h).fibre s).card =
      countWhere (fun x : Point N k => ∀ e, appendCoordinate (AxisCube.vertex (x, h) e) s ∈ B) := by
  classical
  apply Finset.card_bij (fun C _ => C.val.1.base)
  · intro C hC
    have hside : C.val.1.side = h := by
      have hc := C.property
      simp only [section16CubeDomain, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      exact hc.1
    have hs : C.val.2 = s := by
      simpa only [MultifunctionDomain.fibre, section16CubeMultifunctionDomain,
        Finset.mem_filter, Finset.mem_univ, true_and] using hC
    have hvertex : ∀ e, appendCoordinate (C.val.1.vertex e) C.val.2 ∈ B := by
      have hc := C.property
      simp only [section16CubeDomain, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      exact hc.2
    have hcube : (C.val.1.base, h) = C.val.1 := Prod.ext rfl hside.symm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcube, ← hs]
    exact hvertex
  · intro C hC D hD heq
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext heq
      have hc := C.property
      have hd := D.property
      simp only [section16CubeDomain, Finset.mem_filter, Finset.mem_univ, true_and] at hc hd
      exact hc.1.trans hd.1.symm
    · have hc : C.val.2 = s := by
        simpa only [MultifunctionDomain.fibre, section16CubeMultifunctionDomain,
          Finset.mem_filter, Finset.mem_univ, true_and] using hC
      have hd : D.val.2 = s := by
        simpa only [MultifunctionDomain.fibre, section16CubeMultifunctionDomain,
          Finset.mem_filter, Finset.mem_univ, true_and] using hD
      exact hc.trans hd.symm
  · intro x hx
    have hmem : ((x, h), s) ∈ section16CubeDomain B h := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simpa only [section16CubeDomain, Finset.mem_filter, Finset.mem_univ, true_and,
        AxisCube.side, and_true, true_and] using hx
    refine ⟨⟨((x, h), s), hmem⟩, ?_, rfl⟩
    simp [MultifunctionDomain.fibre, section16CubeMultifunctionDomain]

/-- On an indicator function the higher cube correlation counts the cubes
in each cross-section, with the same unnormalized Fourier convention. -/
theorem section16_cube_correlation_eq_fibreCount {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (h : Point N k) :
    higherCubeCorrelation (section16PointIndicator B) h =
      domainFibreCountFunction (section16CubeMultifunctionDomain B h) := by
  classical
  funext s
  rw [domainFibreCountFunction, section16_cube_fibre_card]
  have hproduct (x : Point N k) :
      (∏ e : Fin k → Bool,
        let z := section16PointIndicator B (appendCoordinate (AxisCube.vertex (x, h) e) s)
        if Even (boolWeight e + k) then z else star z) =
      (if ∀ e, appendCoordinate (AxisCube.vertex (x, h) e) s ∈ B then (1 : Complex) else 0) := by
    simp only [section16PointIndicator]
    by_cases hall : ∀ e, appendCoordinate (AxisCube.vertex (x, h) e) s ∈ B
    · simp [hall]
    · rw [if_neg hall]
      obtain ⟨e, he⟩ := not_forall.mp hall
      apply Finset.prod_eq_zero (Finset.mem_univ e)
      simp [he]
  change (∑ x : Point N k, ∏ e : Fin k → Bool,
      let z := section16PointIndicator B (appendCoordinate (AxisCube.vertex (x, h) e) s)
      if Even (boolWeight e + k) then z else star z) = _
  simp_rw [hproduct]
  simp [countWhere]
  congr 1
  ext x
  simp

/-- The spectra in Sections 10 and 16 use exactly the same Fourier function. -/
theorem section16_spectrum_eq_domain {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (h : Point N k) (delta : Real) :
    section16LargeSpectrum B h delta =
      domainLargeSpectrum (section16CubeMultifunctionDomain B h)
        (delta * (N : Real) ^ (k + 1)) := by
  unfold section16LargeSpectrum domainLargeSpectrum
  rw [section16_cube_correlation_eq_fibreCount]

/-- There are at most N^(k+1) fixed-side cubes, one per base and cross-section. -/
theorem section16_cube_card_le {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (h : Point N k) :
    (section16CubeDomain B h).card ≤ N ^ (k + 1) := by
  classical
  let D := section16CubeMultifunctionDomain B h
  have hsum : (∑ s : ZMod N, (D.fibre s).card) =
      Fintype.card (Section16CubeElement B h) := by
    rw [Fintype.card]
    exact (Finset.card_eq_sum_card_fiberwise (s := Finset.univ)
      (t := Finset.univ) (f := D.index) (by simp)).symm
  rw [section16CubeElement_card] at hsum
  rw [← hsum]
  calc
    (∑ s : ZMod N, (D.fibre s).card) ≤ ∑ _s : ZMod N, N ^ k :=
      Finset.sum_le_sum fun s _ => section16CubeMultifunctionDomain_fibre_card_le B h s
    _ = N ^ (k + 1) := by simp [pow_succ, mul_comm]

end LeanProofs.GowersSzemeredi
