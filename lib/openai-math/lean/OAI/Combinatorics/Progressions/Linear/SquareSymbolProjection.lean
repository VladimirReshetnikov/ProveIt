import Mathlib.LinearAlgebra.Isomorphisms
import OAI.Combinatorics.Progressions.Polynomial.RelativeSquarePolynomial

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def filteredFirstJetConstant : F.FilteredFirstJet w →ₗ[ℚ] L ⧸ F.layer 2 :=
  (F.shiftedPolynomialIdeal w 2).toSubmodule.liftQ
    ((F.layer 2).mkQ.comp (F.adaptedCoefficientMap w 0)) (by
      intro p hp
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      change coefficients p.val 0 ∈ F.layer 2
      have hc : coefficients p.val 0 ∈ F.layer (Finsupp.weight w 0 + 2) := hp 0
      simpa only [map_zero, Nat.zero_add] using hc)

@[simp] theorem filteredFirstJetConstant_map (p : F.adaptedLieSubalgebra w) :
    F.filteredFirstJetConstant w (F.filteredFirstJetMap w p) =
      (F.layer 2).mkQ (coefficients p.val 0) := rfl

noncomputable def normalizedFirstJetKernel : Submodule ℚ (F.FilteredFirstJet w) :=
  LinearMap.ker (F.filteredFirstJetSymbol w).toLinearMap ⊓ LinearMap.ker (F.filteredFirstJetConstant w)

theorem normalizedRelativeFirstJet_range :
    LinearMap.range (F.normalizedRelativeFirstJet w) = F.normalizedFirstJetKernel w := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    constructor
    · change F.polynomialSymbolMap w p.val = 0
      exact (F.polynomialSymbolMap_eq_zero_iff w p.val).mpr p.property.1
    · change (F.layer 2).mkQ (coefficients p.val.val 0) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr p.property.2
  · intro hx
    obtain ⟨p, rfl⟩ := F.filteredFirstJetMap_surjective w x
    have hp : p ∈ F.shiftedAdaptedIdeal w :=
      (F.polynomialSymbolMap_eq_zero_iff w p).mp hx.1
    have hzero : coefficients p.val 0 ∈ F.layer 2 :=
      (Submodule.Quotient.mk_eq_zero _).mp hx.2
    exact ⟨⟨p, hp, hzero⟩, rfl⟩

variable (hw : ∀ i, 0 < w i)

theorem relativeSquareSymbolMap_ker :
    LinearMap.ker (F.normalizedRelativeFirstJet w) = LinearMap.ker (F.relativeSquareSymbolMap w hw) := by
  ext p
  change F.normalizedRelativeFirstJet w p = 0 ↔ F.relativeSquareSymbolMap w hw p = 0
  simpa only [map_zero] using (F.relativeSquareSymbolMap_eq_iff w hw p 0).symm

noncomputable def relativeFirstJetRangeEquiv :
    LinearMap.range (F.normalizedRelativeFirstJet w) ≃ₗ[ℚ]
      LinearMap.range (F.relativeSquareSymbolMap w hw) :=
  (F.normalizedRelativeFirstJet w).quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ (F.relativeSquareSymbolMap_ker w hw)).trans
      (F.relativeSquareSymbolMap w hw).quotKerEquivRange)

theorem relativeFirstJetRangeEquiv_apply (p : F.normalizedRelativeSubmodule w) :
    (F.relativeFirstJetRangeEquiv w hw ⟨F.normalizedRelativeFirstJet w p, ⟨p, rfl⟩⟩ :
      F.squareFiltration.PolynomialSymbol w) = F.relativeSquareSymbolMap w hw p := by
  dsimp only [relativeFirstJetRangeEquiv, LinearEquiv.trans_apply]
  rw [(F.normalizedRelativeFirstJet w).quotKerEquivRange_symm_apply_image p ⟨p, rfl⟩]
  rfl

noncomputable def normalizedRelativeKernelEquiv :
    F.normalizedFirstJetKernel w ≃ₗ[ℚ] LinearMap.range (F.relativeSquareSymbolMap w hw) :=
  (LinearEquiv.ofEq _ _ (F.normalizedRelativeFirstJet_range w).symm).trans
    (F.relativeFirstJetRangeEquiv w hw)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def squareSndSymbolMap : F.squareFiltration.PolynomialSymbol w →ₗ⁅ℚ⁆ F.PolynomialSymbol w :=
  F.squareFiltration.filteredPolynomialSymbolMap F F.squareSnd (fun _ _ hx => hx.2.1) w

theorem squareSndSymbolMap_map_eq_zero_iff (r : F.squareFiltration.adaptedLieSubalgebra w) :
    F.squareSndSymbolMap w (F.squareFiltration.polynomialSymbolMap w r) = 0 ↔
      ∀ α, (coefficients r.val α).val.2 ∈ F.layer (Finsupp.weight w α + 1) := by
  change F.polynomialSymbolMap w
    (F.squareFiltration.filteredPolynomialMap F F.squareSnd (fun _ _ hx => hx.2.1) w r) = 0 ↔ _
  rw [F.polynomialSymbolMap_eq_zero_iff]
  change (∀ α, coefficients (VectorPolynomial.map F.squareSnd.toLinearMap r.val) α ∈
    F.layer (Finsupp.weight w α + 1)) ↔ _
  simp only [coefficients_map]
  rfl

variable (hw : ∀ i, 0 < w i)

theorem squareSndSymbolMap_relative (p : F.normalizedRelativeSubmodule w) :
    F.squareSndSymbolMap w (F.relativeSquareSymbolMap w hw p) = 0 := by
  apply (F.squareSndSymbolMap_map_eq_zero_iff w (F.relativeSquareLift w hw p)).mpr
  intro α
  change (coefficients (F.relativeSquarePolynomial w hw p) α).val.2 ∈ _
  rw [F.relativeSquarePolynomial_coefficient]
  exact (F.layer _).zero_mem

theorem relativeSquareSymbolMap_range :
    LinearMap.range (F.relativeSquareSymbolMap w hw) = (F.squareSndSymbolMap w).ker.toSubmodule := by
  apply le_antisymm
  · rintro x ⟨p, rfl⟩
    exact F.squareSndSymbolMap_relative w hw p
  · intro x hx
    obtain ⟨r, rfl⟩ := F.squareFiltration.polynomialSymbolMap_surjective w x
    have hs : ∀ α, (coefficients r.val α).val.2 ∈ F.layer (Finsupp.weight w α + 1) :=
      (F.squareSndSymbolMap_map_eq_zero_iff w r).mp hx
    let p : VectorPolynomial σ ℚ L :=
      VectorPolynomial.map F.squareFst.toLinearMap r.val - VectorPolynomial.map F.squareSnd.toLinearMap r.val
    have hc (α : σ →₀ ℕ) : coefficients p α =
        (coefficients r.val α).val.1 - (coefficients r.val α).val.2 := by
      simp only [p, map_sub, Finsupp.sub_apply, coefficients_map]
      rfl
    have hp : ∀ α, coefficients p α ∈ F.layer (Finsupp.weight w α + 1) := by
      intro α
      rw [hc]
      exact (r.property α).2.2
    have hpa : p ∈ F.adaptedLieSubalgebra w :=
      fun α => F.antitone (Nat.le_succ _) (hp α)
    have hp0 : coefficients p 0 ∈ F.layer 2 := by
      rw [hc]
      exact (F.mem_squareLieSubalgebra _).mp (coefficients r.val 0).property
    let q : F.normalizedRelativeSubmodule w := ⟨⟨p, hpa⟩, hp, hp0⟩
    refine ⟨q, ?_⟩
    apply (F.squareFiltration.polynomialSymbolMap_eq_iff w (F.relativeSquareLift w hw q) r).mpr
    intro α
    rw [map_sub, Finsupp.sub_apply]
    change (coefficients (F.relativeSquarePolynomial w hw q) α).val - (coefficients r.val α).val ∈
      F.squareLayer (Finsupp.weight w α + 1)
    rw [F.relativeSquarePolynomial_coefficient]
    change (coefficients p α, (0 : L)) - (coefficients r.val α).val ∈ _
    rw [hc]
    have he : ((coefficients r.val α).val.1 - (coefficients r.val α).val.2, (0 : L)) -
        (coefficients r.val α).val = (-(coefficients r.val α).val.2, -(coefficients r.val α).val.2) := by
      apply Prod.ext <;> dsimp <;> abel
    rw [he]
    exact ⟨(F.layer _).neg_mem (hs α), (F.layer _).neg_mem (hs α), by simp⟩

noncomputable def normalizedRelativeSquareKernelEquiv :
    F.normalizedFirstJetKernel w ≃ₗ[ℚ] (F.squareSndSymbolMap w).ker :=
  (F.normalizedRelativeKernelEquiv w hw).trans
    (LinearEquiv.ofEq _ _ (F.relativeSquareSymbolMap_range w hw))

end Erdos3.NilpotentLieFiltration

end

end OAI
