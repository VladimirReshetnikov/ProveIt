import OAI.Combinatorics.Progressions.Geometry.DerivativeVerticalCoordinates

namespace OAI

section

namespace Erdos3

theorem realDenominatorGrid_div_nat {ι : Type*} (l I : ℕ) (hI : 0 < I)
    (x : ι → ℝ) (hx : x ∈ realDenominatorGrid l) :
    ((I : ℝ)⁻¹ • x) ∈ realDenominatorGrid (l * I) := by
  have hIr : (I : ℝ) ≠ 0 := by exact_mod_cast hI.ne'
  obtain ⟨z, hz⟩ := hx
  refine ⟨z, ?_⟩
  funext i
  have hi := congrFun hz i
  change (z i : ℝ) = (l : ℝ) * x i at hi
  change (z i : ℝ) = ((l * I : ℕ) : ℝ) * ((I : ℝ)⁻¹ * x i)
  rw [hi, Nat.cast_mul]
  field_simp

theorem divided_derivative_lattice_coordinates
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq κ]
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hs : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (I : ℕ) (hI : 0 < I) (y : σ → ℝ)
    (v : EuclideanSpace ℝ (σ ⊕ κ))
    (hv : v ∈ euclideanDerivativeLattice T hT scale hs Y A l hl)
    (hshift : euclideanDerivativeShiftMap T hT v = (I : ℝ) • y) :
    ∃ r : κ → ℝ, r ∈ realDenominatorGrid (l * I) ∧
      ∀ j, ((I : ℝ)⁻¹ • v) (Sum.inr j) = scale j * (Y y j - A r j) := by
  have hIr : (I : ℝ) ≠ 0 := by exact_mod_cast hI.ne'
  have hv' := (euclideanDerivativeLattice_mem_iff T hT scale hs Y A l hl v).mp hv
  rw [← SetLike.mem_coe, derivativeLattice_carrier] at hv'
  obtain ⟨h, r, hr, he⟩ := hv'
  have hleft (i) : v (Sum.inl i) = (h i : ℝ) / T i :=
    congrArg (fun x : (σ → ℝ) × (κ → ℝ) => x.1 i) he
  have hright (j) : v (Sum.inr j) =
      scale j * (Y (fun i => (h i : ℝ)) j - A r j) := by
    have hc := congrArg (fun x : (σ → ℝ) × (κ → ℝ) => x.2 j) he
    change (productEuclideanEquiv.symm v).2 j = _
    simpa only [derivativeGridPoint, LinearMap.toMatrix'_mulVec,
      LinearEquiv.coe_coe, Pi.sub_apply] using hc
  have hh : (fun i => (h i : ℝ)) = (I : ℝ) • y := by
    funext i
    have hi := congrFun hshift i
    change T i * v (Sum.inl i) = (I : ℝ) * y i at hi
    rw [hleft, mul_div_cancel₀ _ (hT i)] at hi
    exact hi
  refine ⟨(I : ℝ)⁻¹ • r, realDenominatorGrid_div_nat l I hI r hr, ?_⟩
  intro j
  change (I : ℝ)⁻¹ * v (Sum.inr j) = _
  rw [hright, hh, map_smul, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

theorem divided_derivative_horizontal_coordinates
    {σ κ : Type*} [Fintype σ] [Fintype κ]
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (I : ℕ) (hI : 0 < I)
    (y : σ → ℝ) (v : EuclideanSpace ℝ (σ ⊕ κ))
    (hshift : euclideanDerivativeShiftMap T hT v = (I : ℝ) • y) :
    ∀ i, ((I : ℝ)⁻¹ • v) (Sum.inl i) = y i / T i := by
  have hIr : (I : ℝ) ≠ 0 := by exact_mod_cast hI.ne'
  intro i
  have hi := congrFun hshift i
  change T i * v (Sum.inl i) = (I : ℝ) * y i at hi
  have hv : v (Sum.inl i) = ((I : ℝ) * y i) / T i :=
    (eq_div_iff (hT i)).mpr (by simpa only [mul_comm] using hi)
  change (I : ℝ)⁻¹ * v (Sum.inl i) = _
  rw [hv]
  field_simp

end Erdos3

end

end OAI
