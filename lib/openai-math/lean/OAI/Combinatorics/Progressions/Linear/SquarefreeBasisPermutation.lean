import Mathlib.LinearAlgebra.StdBasis
import OAI.Combinatorics.Progressions.Estimates.SquarefreePermutationFiltration
import OAI.Combinatorics.Progressions.Linear.BasisGradedCoordinateBasis

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)
  {κ : SquarefreeIndex ι → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.squarefreeCoefficientLayer π a))

noncomputable def squarefreeBasis : Basis (Σ a, κ a) ℚ (F.SquarefreeAlgebra π) :=
  (Pi.basis b).map (F.squarefreeAlgebraEquiv π).symm

theorem squarefreeBasis_repr (x : F.SquarefreeAlgebra π) (j : Σ a, κ a) :
    (F.squarefreeBasis π b).repr x j = (b j.1).repr (F.squarefreeAlgebraEquiv π x j.1) j.2 := by
  rfl

theorem squarefreeBasis_coefficient_self (a : SquarefreeIndex ι) (j : κ a) :
    squarefreePolynomialEquiv (F.squarefreeBasis π b ⟨a, j⟩).val a = (b a j).val := by
  classical
  change (F.squarefreeAlgebraEquiv π (F.squarefreeBasis π b ⟨a, j⟩) a).val = _
  simp only [squarefreeBasis, Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basis_apply,
    Pi.single_eq_same]

theorem squarefreeBasis_coefficient_ne (a c : SquarefreeIndex ι) (h : a ≠ c) (j : κ a) :
    squarefreePolynomialEquiv (F.squarefreeBasis π b ⟨a, j⟩).val c = 0 := by
  classical
  change (F.squarefreeAlgebraEquiv π (F.squarefreeBasis π b ⟨a, j⟩) c).val = _
  simp only [squarefreeBasis, Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basis_apply,
    Pi.single_eq_of_ne (Ne.symm h), ZeroMemClass.coe_zero]

theorem squarefreeBasis_monomial (j : Σ a, κ a) :
    (F.squarefreeBasis π b j).val = squarefreeMonomial j.1 (b j.1 j.2).val := by
  apply squarefreePolynomialEquiv.injective
  ext a
  by_cases h : j.1 = a
  · subst a
    rw [F.squarefreeBasis_coefficient_self, squarefreePolynomialEquiv_monomial_self]
  · rw [F.squarefreeBasis_coefficient_ne π b _ _ h,
      squarefreePolynomialEquiv_monomial_ne _ _ h]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)
  {κ : SquarefreeIndex ι → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.squarefreeCoefficientLayer π a))

theorem squarefreeSupport_eq_span (P : SquarefreeIndex ι → Prop) :
    (squarefreeSupportModule P).comap (F.squarefreeAdaptedSubalgebra π).incl.toLinearMap =
      Submodule.span ℚ (F.squarefreeBasis π b '' {j | P j.1}) := by
  ext x
  rw [basis_mem_span_image_iff]
  constructor
  · intro hx j hj
    have hz : F.squarefreeAlgebraEquiv π x j.1 = 0 := Subtype.ext (hx j.1 hj)
    rw [F.squarefreeBasis_repr, hz, map_zero, Finsupp.zero_apply]
  · intro hx a ha
    have hz : F.squarefreeAlgebraEquiv π x a = 0 := by
      apply (b a).repr.injective
      ext j
      simpa only [F.squarefreeBasis_repr, map_zero, Finsupp.zero_apply] using hx ⟨a, j⟩ ha
    exact congrArg Subtype.val hz

noncomputable def squarefreeSupportedBasis (P : SquarefreeIndex ι → Prop) :
    Basis {j : Σ a, κ a // P j.1} ℚ
      ((squarefreeSupportModule P).comap (F.squarefreeAdaptedSubalgebra π).incl.toLinearMap) :=
  supportedSubmoduleBasis (F.squarefreeBasis π b) _ _ (F.squarefreeSupport_eq_span π b P)

theorem squarefreeSupportedBasis_coe (P : SquarefreeIndex ι → Prop)
    (j : {j : Σ a, κ a // P j.1}) :
    (F.squarefreeSupportedBasis π b P j).val = F.squarefreeBasis π b j.val :=
  supportedSubmoduleBasis_coe _ _ _ _ j

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem squarefreeCoefficientLayer_permute (e : ι ≃ ι) (he : ∀ i, π (e i) = π i)
    (a : SquarefreeIndex ι) :
    F.squarefreeCoefficientLayer π (SquarefreeIndex.permute e a) = F.squarefreeCoefficientLayer π a := by
  classical
  simp only [squarefreeCoefficientLayer, SquarefreeIndex.permute_zero_iff,
    SquarefreeIndex.permute_blockDegree π e he a]

theorem squarefreeBasis_permute
    (b : ∀ U : Submodule ℚ L, Basis (Fin (finrank ℚ U)) ℚ U)
    (e : ι ≃ ι) (he : ∀ i, π (e i) = π i)
    (j : Σ a : SquarefreeIndex ι, Fin (finrank ℚ (F.squarefreeCoefficientLayer π a))) :
    ∃ k, F.squarefreeBlockPermute π e he (F.squarefreeBasis π (fun a => b (F.squarefreeCoefficientLayer π a)) j) =
      F.squarefreeBasis π (fun a => b (F.squarefreeCoefficientLayer π a)) k := by
  have hex : ∃ k,
      (b (F.squarefreeCoefficientLayer π (SquarefreeIndex.permute e j.1)) k).val =
        (b (F.squarefreeCoefficientLayer π j.1) j.2).val := by
    rw [F.squarefreeCoefficientLayer_permute π e he]
    exact ⟨j.2, rfl⟩
  obtain ⟨k, hk⟩ := hex
  refine ⟨⟨SquarefreeIndex.permute e j.1, k⟩, ?_⟩
  apply Subtype.ext
  rw [F.squarefreeBlockPermute_apply, F.squarefreeBasis_monomial, squarefreePermute_monomial,
    F.squarefreeBasis_monomial]
  exact congrArg (squarefreeMonomial (SquarefreeIndex.permute e j.1)) hk.symm

end Erdos3.MultidegreeLieFiltration

end

end OAI
