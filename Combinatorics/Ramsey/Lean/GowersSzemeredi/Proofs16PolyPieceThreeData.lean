import GowersSzemeredi.Proofs16BaseCaseCubicExtraction
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Degree.Monomial
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Data.Finset.DenselyOrdered
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Factorial.NatCast
import Mathlib.GroupTheory.CosetCover
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic

/-! **One three-dimensional piece with its data** (Notes L.5, D3).

`section16_poly_piece_three_data`: let `(B, φ)` be a three-dimensional
partial function inside a relation `Γ`. Assume it meets Lemma 16.4's
arrangement conditions at `k = 2` and has the product property. Then there is
a `PolyPieceThreeData` of `Γ` of mass `3θ′`, where `θ′ = θ₂/8`
(`threeBudget`). This is the dimension-two construction
(`section16_poly_piece_two_data`) one level up:
* Lemmas 16.5 and 16.7 give the dense selection, the base point `x₀` and
  the identity `φ₁ = φ′ + φ″` on the good domain `B₁` (`|B₁| ≥ 8θ′N³`).
* The spectrum relation, translated by `x₀`, is a two-dimensional product
  relation (`RelationProductProperty.translate`). It decomposes into pieces
  of the uniform class at `(θ′, δ)` off a good set `J_T`.
* The remainder is `g₁(dropMid w) + g₂(dropFirst w) − g₃(lastPt3 w)` with
  the face functions of `midFace3`, `firstFace3`, `lastFace3`. The first two
  face graphs decompose into pieces at `(θ′, γ)` off `J₁`, `J₂`. The third
  has Freiman families off `J₃`.
* The slices decompose into pieces at `(θ′, γ)` off `C t`
  (`section16_slice_decomposition_three`).
* Five deletions of at most `θ′N³` points each leave `3θ′N³`.

All the data is then rebuilt in the original frame `w = origPt x₀ z`.

`origPt_eq_add`, `origPt_injective`, `phiOne_eq_origPt`,
`section16_poly_piece_three_data`, `threeBudget`, `threeDelta`, `threeFaceCount`
and `threeThreshold` are in `Proofs16PolyPieceThreeDataSide`, outside the final
route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

theorem card_point_le_pow {N : Nat} [NeZero N] (k : Nat) (S : Finset (Point N k)) :
    (S.card : Real) ≤ (N : Real) ^ k := by
  have h := Finset.card_le_univ S
  have hc : Fintype.card (Point N k) = N ^ k := by
    simp [Point, ZMod.card]
  rw [hc] at h
  exact_mod_cast h

theorem one_le_gamma_inv_sq {gamma : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    (1 : Real) ≤ gamma ^ (-(2 : Int)) := by
  rw [zpow_neg, zpow_ofNat]
  exact (one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)

end LeanProofs.GowersSzemeredi
