import OAI.Combinatorics.Progressions.Linear.SpanKernelGenerators

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem exists_bounded_rational_image_basis {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) {H : ℕ} (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ b : Module.Basis (Fin (Module.finrank ℚ (LinearMap.range A.mulVecLin)))
      ℚ (LinearMap.range A.mulVecLin),
      ∀ i j, RationalHeightLE ((b i : ι → ℚ) j) H := by
  have hspan : Submodule.span ℚ (Set.range A.col) = LinearMap.range A.mulVecLin :=
    A.range_mulVecLin.symm
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range A.col)
  rw [hspan] at hex
  obtain ⟨v, hv, hvspan, hli⟩ := hex
  refine ⟨(Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hvspan), ?_⟩
  intro i j
  simp only [Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.coe_span_apply]
  obtain ⟨k, hk⟩ := hv i
  rw [← hk]
  exact hA j k

section Intersection

variable {η κ : Type*} [Fintype η] [Fintype κ] [DecidableEq κ]
variable {ρ : η → Type*} [∀ i, Fintype (ρ i)]

def jointMatrix (A : ∀ i, Matrix (ρ i) κ ℚ) : Matrix (Σ i, ρ i) κ ℚ :=
  fun ij k => A ij.1 ij.2 k

omit [Fintype η] [∀ i, Fintype (ρ i)] [DecidableEq κ] in
theorem jointMatrix_ker (A : ∀ i, Matrix (ρ i) κ ℚ) :
    LinearMap.ker (jointMatrix A).mulVecLin = ⨅ i, LinearMap.ker (A i).mulVecLin := by
  ext x
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, Matrix.mulVecLin_apply,
    funext_iff, Pi.zero_apply]
  exact ⟨fun h i j => h ⟨i, j⟩, fun h ij => h ij.1 ij.2⟩

theorem exists_bounded_rational_intersection_basis (A : ∀ i, Matrix (ρ i) κ ℚ)
    {H : ℕ} (hH : 1 ≤ H) (hA : ∀ i j k, RationalHeightLE (A i j k) H) :
    ∃ r : ℕ, r ≤ ∑ i, Fintype.card (ρ i) ∧
      ∃ b : Module.Basis (Fin (Module.finrank ℚ
        (⨅ i, LinearMap.ker (A i).mulVecLin : Submodule ℚ (κ → ℚ))))
        ℚ (⨅ i, LinearMap.ker (A i).mulVecLin : Submodule ℚ (κ → ℚ)),
        ∀ i j, RationalHeightLE ((b i : κ → ℚ) j) (rationalKernelHeight r H) := by
  have h := exists_bounded_rational_kernel_basis (jointMatrix A) hH
    (fun ij k => hA ij.1 ij.2 k)
  rw [← jointMatrix_ker A]
  simpa only [Fintype.card_sigma] using h

end Intersection

end Erdos3

end

end OAI
