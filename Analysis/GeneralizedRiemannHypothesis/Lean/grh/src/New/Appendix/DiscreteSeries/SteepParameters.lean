import Lib.General.LinearAlgebra.MatricesNearIdentity

/-!
# Steep parameters and the setting of Laplace's method

This file begins the localization near the compact subgroups. It concerns a group `S` that maps to
`U(ε) × U(η)`, for two vectors of signs `ε` and `η`, together with the parameters of two discrete
series. Let `μ` and `μ'` be the diagonal matrices of the weights of their lowest `K`-types. Among
other properties, the function `φ s = tr (μ (g - 1)) - tr (μ' (g' - 1))` of the image `(g, g')` of
`s`, the difference of the two phases, is additive and purely imaginary.
The file defines the phase difference `New.HCParam.phase`, steep parameters, the properties
`New.DiscreteSeries.IsLaplaceDatum` and the integrand `New.HCParam.laplaceIntegrand`. It also
proves the polar decomposition of an invertible matrix.

## Main definitions and results

* `New.DiscreteSeries.IsLaplaceDatum`: the properties of `j : S →* U(ε) × U(η)` and `φ` that
  Laplace's method uses; `New.HCParam.laplaceIntegrand` is the function that is integrated.
* `New.DiscreteSeries.IsSteep`: the parameter `l` for the signs `ε` is steep with respect to `B`
  and the splitting `e : X ⊕ Fin M ≃ n` of the coordinates.

Notions from other files:
* `New.USign ε`: the unitary group `U(ε)` of the diagonal matrix `signMatrix ε` of the signs `ε`.
* `New.HCParam.lowestKType l`: the highest weight of the lowest `K`-type of the parameter `l`.
* `New.HCParam.dsCoeff l`: the matrix coefficient of that `K`-type, as a function of a matrix.

## Relation to the literature

See `New.Appendix.DiscreteSeries.Localization` for related work.
-/

noncomputable section

section Localization

open Finset Matrix Complex ComplexConjugate Set ComplexOrder Int New.HCParam

namespace New.DiscreteSeries

open MatrixOrder in
/-- Polar decomposition: an invertible matrix is a unitary matrix times a positive semidefinite
matrix. -/
lemma exists_unitary_mul_posSemidef {X : Type} [Fintype X] [DecidableEq X] {a : Matrix X X ℂ}
    (ha : IsUnit a) :
    ∃ k ∈ unitaryGroup X ℂ, ∃ z : Matrix X X ℂ, z.PosSemidef ∧ a = k * z := by
  let z : Matrix X X ℂ := CFC.abs a
  have hz : z.PosSemidef := (CFC.abs_nonneg a).posSemidef
  have hz_sq : z * z = aᴴ * a := CFC.abs_mul_abs a
  have hz_det : IsUnit z.det := (isUnit_iff_isUnit_det z).1
    (isUnit_of_mul_isUnit_left (y := z) (by simpa [hz_sq] using ha.star.mul ha))
  refine ⟨a * z⁻¹, mem_unitaryGroup_iff'.2 ?_, z, hz,
    (nonsing_inv_mul_cancel_right _ _ hz_det).symm⟩
  calc star (a * z⁻¹) * (a * z⁻¹) = z⁻¹ * (z * z) * z⁻¹ := by
        simp [hz_sq, star_eq_conjTranspose, hz.isHermitian.inv.eq, mul_assoc]
    _ = 1 := by rw [nonsing_inv_mul_cancel_left _ _ hz_det, mul_nonsing_inv _ hz_det]

open Norms.Frobenius

variable {n m X S : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype X]
  [DecidableEq X] [Group S] {ε : n → ℤˣ} (l : HCParam ε) {η : m → ℤˣ} (k : HCParam η)
  (j : S →* USign ε × USign η) (τ : X → m) (B : ℝ) {M : ℕ} (e : X ⊕ Fin M ≃ n) (φ : S → ℂ)

/-! ### The setting of Laplace's method -/

/-- The difference `tr (μ Y) - tr (μ' Y')` of the two phases at `x = (Y, Y')`, where `μ` and `μ'`
are the weights of the lowest `K`-types of `l` and `k`, as diagonal matrices. -/
def _root_.New.HCParam.phase (x : Matrix n n ℂ × Matrix m m ℂ) : ℂ :=
  (intDiagonal l.lowestKType * x.1).trace - (intDiagonal k.lowestKType * x.2).trace

/-- The parameter `l` for the signs `ε` is steep with respect to `B` and the splitting
`e : X ⊕ Fin M ≃ n` of the coordinates: on `X` the sign is `+1` and the weight of the lowest
`K`-type is `0`; on the other `M` coordinates the signs are `+, -, +, …` and the weight decreases
strictly in `[-3 B, -B]`. -/
structure IsSteep : Prop where
  /-- The sign `ε` is `+1` on `X`. -/
  sign_inl (x : X) : ε (e (Sum.inl x)) = 1
  /-- On the other `M` indices the signs alternate, starting with `+1`. -/
  sign_inr (i : Fin M) : ε (e (Sum.inr i)) = (-1) ^ (i : ℕ)
  /-- The weight `l.lowestKType` of the lowest `K`-type is `0` on `X`. -/
  weight_eq_zero (x : X) : l.lowestKType (e (Sum.inl x)) = 0
  /-- On the other `M` indices the weight is strictly decreasing. -/
  weight_strictAnti : StrictAnti fun i : Fin M ↦ l.lowestKType (e (Sum.inr i))
  /-- On the other `M` indices the weight lies between `-3 B` and `-B`. -/
  weight_mem (i : Fin M) : (l.lowestKType (e (Sum.inr i)) : ℝ) ∈ Set.Icc (-3 * B) (-B)

/-- The pair `(g - 1, g' - 1)` for the two components `g`, `g'` of `j s`. -/
abbrev subOnePair (s : S) : Matrix n n ℂ × Matrix m m ℂ :=
  ((((j s).1 : GL n ℂ) : Matrix n n ℂ) - 1, (((j s).2 : GL m ℂ) : Matrix m m ℂ) - 1)

/-- The function to which Laplace's method applies: the coefficient of `l` at the first
component of `j s`, times the conjugate of the coefficient of `k` at the second, times
`exp (-φ s)`, for a function `φ` on `S` (under `IsLaplaceDatum`, the difference of the two phases).
-/
def _root_.New.HCParam.laplaceIntegrand (s : S) : ℂ :=
  l.dsCoeff (j s).1 * conj (k.dsCoeff (j s).2) * cexp (-φ s)

/-- The properties of `j : S →* U(ε) × U(η)` and `φ` that Laplace's method uses: `l` is steep, the
difference of the two phases is an additive and imaginary function `φ`, the two traces agree, the
weights of `k` are nonnegative, at most `3 B` if `η` takes both signs, and zero on the image of
`τ`, where the signs are `+1`, and the image of `j` contains a diagonal copy of `U(X)`. -/
structure IsLaplaceDatum : Prop extends IsSteep l B e where
  /-- `φ s` is the difference of the two phases at `j s - 1`. -/
  phase_eq (s : S) : l.phase k (subOnePair j s) = φ s
  /-- The two components of `j s`, minus `1`, have the same trace. -/
  trace_eq (s : S) : (subOnePair j s).1.trace = (subOnePair j s).2.trace
  /-- The function `φ` is additive. -/
  phase_mul (s t : S) : φ (s * t) = φ s + φ t
  /-- The function `φ` is purely imaginary. -/
  re_phase_eq_zero (s : S) : (φ s).re = 0
  /-- In the second factor the sign is `+1` and the weight `k.lowestKType` is `0` on the image
  of `τ`. -/
  sign_weight_right (x : X) : η (τ x) = 1 ∧ k.lowestKType (τ x) = 0
  /-- The weight `k.lowestKType` is nonnegative, and at most `3 B` at each index whose sign
  differs from that of some other index; if `η` takes both signs, this is every index. -/
  weight_nonneg_and_le (i i' : m) : 0 ≤ k.lowestKType i ∧ (η i ≠ η i' → k.lowestKType i ≤ 3 * B)
  /-- The image of `j` contains a diagonal copy of `U(X)`, placed by `e` in the first factor and by
  `τ` in the second: `inclMatrix ℂ σ` is the matrix of the map `σ` of indices, whose column `x`
  is the standard basis vector at `σ x`. -/
  exists_diagonal : ∀ u ∈ unitaryGroup X ℂ, ∃ s : S,
    subOnePair j s =
      (inclMatrix ℂ (e ∘ Sum.inl) * (u - 1) * (inclMatrix ℂ (e ∘ Sum.inl))ᴴ,
        inclMatrix ℂ τ * (u - 1) * (inclMatrix ℂ τ)ᴴ)

end New.DiscreteSeries

end Localization

end
