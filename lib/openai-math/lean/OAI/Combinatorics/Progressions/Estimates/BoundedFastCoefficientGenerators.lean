import OAI.Combinatorics.Progressions.Linear.FastCoefficientSpanning

namespace OAI

section

namespace Erdos3

def fastKernelGeneratorHeight (n m r H : ℕ) : ℕ :=
  (m + 1) * (rationalKernelHeight r ((n + 1) * H ^ n) * H) ^ m

def fastCoefficientGeneratorHeight (n m r H : ℕ) : ℕ :=
  (n + 1) * fastKernelGeneratorHeight n m r H ^ n

namespace NilpotentLieFiltration

open Module

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
  [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]

theorem exists_bounded_reduced_fast_kernel_generators
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H) :
    ∃ r : ℕ, r ≤ Fintype.card (QuotientTopSymbolIndex s w ω) ∧
      ∃ z : κ → F.squareFiltration.quotientTop.PolynomialSymbol w,
        Submodule.span ℚ (Set.range z) = U ⊓ (F.reducedSquareSndSymbolMap w).ker.toSubmodule ∧
        ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (z i) j)
          (fastKernelGeneratorHeight (Fintype.card (ReducedSquareSymbolIndex s w ω))
            (Fintype.card κ) r H) := by
  have hPv (i : κ) (j : QuotientTopSymbolIndex s w ω) :
      RationalHeightLE ((F.quotientTopSymbolBasis e ω hF w).repr (F.reducedSquareSndSymbolMap w (v i)) j)
        ((Fintype.card (ReducedSquareSymbolIndex s w ω) + 1) *
          H ^ Fintype.card (ReducedSquareSymbolIndex s w ω)) := by
    simpa only [mul_one, LieHom.coe_toLinearMap] using linearMap_coordinate_height
      (F.reducedSquareSymbolBasis e ω hF w) (F.quotientTopSymbolBasis e ω hF w)
      (F.reducedSquareSndSymbolMap w).toLinearMap
      (F.reducedSquareSndSymbolMap_basis_height e ω hF w) (v i) (hv i) j
  have hB : 1 ≤ (Fintype.card (ReducedSquareSymbolIndex s w ω) + 1) *
      H ^ Fintype.card (ReducedSquareSymbolIndex s w ω) := by
    have hp : 0 < H := lt_of_lt_of_le Nat.zero_lt_one hH
    exact Nat.succ_le_of_lt (by positivity)
  have he := exists_bounded_span_kernel_generators
    (F.reducedSquareSymbolBasis e ω hF w) (F.quotientTopSymbolBasis e ω hF w)
    (F.reducedSquareSndSymbolMap w).toLinearMap v hB hv hPv
  simpa only [hspan, fastKernelGeneratorHeight, LieHom.ker_toSubmodule] using he

theorem exists_bounded_fast_coefficient_generators (hw : ∀ i, 0 < w i)
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H) :
    ∃ r : ℕ, r ≤ Fintype.card (QuotientTopSymbolIndex s w ω) ∧
      ∃ z : κ → F.FirstCoefficientModule w,
        Submodule.span ℚ (Set.range z) = F.firstCoefficientFastSubmodule w hw U ∧
        ∀ i j, RationalHeightLE ((F.firstCoefficientBasis e ω hF w).repr (z i) j)
          (fastCoefficientGeneratorHeight (Fintype.card (ReducedSquareSymbolIndex s w ω))
            (Fintype.card κ) r H) := by
  have he := F.exists_bounded_reduced_fast_kernel_generators e ω hF w U v hspan hH hv
  obtain ⟨r, hr, z, hz, hzh⟩ := he
  exact ⟨r, hr, F.firstCoefficientFastSubmodule_spanning_height e ω hF w hw U z hz hzh⟩

end NilpotentLieFiltration
end Erdos3

end

end OAI
