import Mathlib.Data.ZMod.Basic
import OAI.Combinatorics.Progressions.Estimates.FiniteMarkedFreezingCellBound
import OAI.Combinatorics.Progressions.Sampling.NativeMarkedFreezingSliceScore

namespace OAI

section

namespace Erdos3.ResidueBoxSlice

variable {ι : Type*} {N : ι → ℕ} {q : ℕ}

def affineIntegerPoint (A : ResidueBoxSlice N q) (origin : ι → ℤ) (step : ℕ)
    (j : ∀ i, Fin (A.length i)) : ι → ℤ :=
  fun i => origin i + step * (A.point j i).val

theorem affineIntegerPoint_residue (A : ResidueBoxSlice N q)
    (origin : ι → ℤ) (step : ℕ) (j : ∀ i, Fin (A.length i)) :
    (fun i => (A.affineIntegerPoint origin step j i : ZMod q)) =
      fun i => ((origin i + (step : ℤ) * A.start i : ℤ) : ZMod q) := by
  funext i
  simp only [affineIntegerPoint, point, Nat.cast_add, Nat.cast_mul, Int.cast_add, Int.cast_mul,
    Int.cast_natCast]
  simp

theorem exists_constant_freezing_pair {I J : Type*}
    (A : ResidueBoxSlice N q) (hlen : ∀ i, 0 < A.length i)
    (origin : ι → ℤ) (step : ℕ) (T : ι → ℝ) (hT : ∀ i, 0 < T i)
    {Q : ℕ} (hQ : 0 < Q)
    (hparent : ∀ i n, n < N i → |(origin i : ℝ) + step * n| ≤ T i)
    (hwidth : ∀ i, (step : ℝ) * q * A.length i ≤ 2 * T i / Q)
    (leftLabel : (ι → Fin (Q + 1)) → I) (rightLabel : (ι → ZMod q) → J)
    (f : (ι → ℤ) → ℂ) (frozen : I → J → (ι → ℤ) → ℂ) {ε : ℝ}
    (hfreeze : ∀ a (x : ι → ℤ), (∀ i, |(x i : ℝ)| ≤ T i) →
      (∀ i, |(x i : ℝ) - normalizedRealBoxGrid T Q a i| ≤ T i * (2 / Q)) →
      ‖f x - frozen (leftLabel a) (rightLabel (fun i => (x i : ZMod q))) x‖ ≤ ε) :
    ∃ a : ι → Fin (Q + 1),
      ∀ j : ∀ i, Fin (A.length i),
        ‖f (A.affineIntegerPoint origin step j) -
          frozen (leftLabel a)
            (rightLabel (fun i => ((origin i + (step : ℤ) * A.start i : ℤ) : ZMod q)))
            (A.affineIntegerPoint origin step j)‖ ≤ ε := by
  obtain ⟨a, ha⟩ := A.exists_affine_normalized_cell hlen (fun i => (origin i : ℝ))
    (step : ℝ) (Nat.cast_nonneg _) T hT hQ hparent hwidth
  refine ⟨a, fun j => ?_⟩
  have hbound (i) : |(A.affineIntegerPoint origin step j i : ℝ)| ≤ T i := by
    simpa only [affineIntegerPoint, Int.cast_add, Int.cast_mul, Int.cast_natCast] using
      hparent i (A.point j i).val (A.point j i).isLt
  have hcell (i) : |(A.affineIntegerPoint origin step j i : ℝ) -
      normalizedRealBoxGrid T Q a i| ≤ T i * (2 / Q) := by
    simpa only [affineIntegerPoint, Int.cast_add, Int.cast_mul, Int.cast_natCast] using ha j i
  simpa only [A.affineIntegerPoint_residue origin step j] using
    hfreeze a (A.affineIntegerPoint origin step j) hbound hcell

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3
open scoped BigOperators

def affineParentIntegerPoint {ι : Type*} (N : ι → ℕ)
    (origin : ι → ℤ) (step : ℕ) (x : ∀ i, Fin (N i)) : ι → ℤ :=
  fun i => origin i + step * (x i).val

theorem exists_long_affine_residue_cell_frozen_score
    {ι I J : Type*} [Fintype ι] [DecidableEq ι] (N : ι → ℕ)
    (hN : ∀ i, 0 < N i) (q Q : ℕ) (hq : 0 < q) (hQ : 0 < Q)
    (origin : ι → ℤ) (step : ℕ) (T : ι → ℝ) (hT : ∀ i, 0 < T i)
    (hparent : ∀ i n, n < N i → |(origin i : ℝ) + step * n| ≤ T i)
    (hparentwidth : ∀ i, (step : ℝ) * N i ≤ 2 * T i)
    (hlarge : ∀ i, 2 * (q : ℝ) ≤ (1 / (Q : ℝ)) * N i)
    (score : (ι → ℤ) → ℝ) (f : (ι → ℤ) → ℂ)
    (frozen : I → J → (ι → ℤ) → ℂ)
    (leftLabel : (ι → Fin (Q + 1)) → I) (rightLabel : (ι → ZMod q) → J)
    {B τ ε θ S : ℝ} (hB : 0 ≤ B) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) (hθ : 0 < θ)
    (hscoreBound : ∀ x : ι → ℤ, (∀ i, |(x i : ℝ)| ≤ T i) → |score x| ≤ 1)
    (hcap : ∀ x : ι → ℤ, (∀ i, |(x i : ℝ)| ≤ T i) → score x * (f x).re ≤ B)
    (hfreeze : ∀ a (x : ι → ℤ), (∀ i, |(x i : ℝ)| ≤ T i) →
      (∀ i, |(x i : ℝ) - normalizedRealBoxGrid T Q a i| ≤ T i * (2 / Q)) →
      ‖f x - frozen (leftLabel a) (rightLabel (fun i => (x i : ZMod q))) x‖ ≤ ε)
    (hscore : S ≤ 𝔼 x : (∀ i, Fin (N i)),
      score (affineParentIntegerPoint N origin step x) *
        (f (affineParentIntegerPoint N origin step x)).re)
    (hbudget : τ + ε + B * θ < S) :
    ∃ A : ResidueBoxSlice N q, (∀ i, 0 < A.length i) ∧
      (∀ i, θ * N i / (4 * q * Q * (Fintype.card ι + 1 : ℝ)) ≤ A.length i) ∧
      ∃ z : ι → Fin (Q + 1),
        (∀ j : ∀ i, Fin (A.length i),
          ‖f (A.affineIntegerPoint origin step j) -
            frozen (leftLabel z)
              (rightLabel (fun i => ((origin i + (step : ℤ) * A.start i : ℤ) : ZMod q)))
              (A.affineIntegerPoint origin step j)‖ ≤ ε) ∧
        τ < 𝔼 j : (∀ i, Fin (A.length i)),
          score (A.affineIntegerPoint origin step j) *
            (frozen (leftLabel z)
              (rightLabel (fun i => ((origin i + (step : ℤ) * A.start i : ℤ) : ZMod q)))
              (A.affineIntegerPoint origin step j)).re := by
  classical
  let point := affineParentIntegerPoint N origin step
  let residue := fun r : ι → ZMod q => fun i => (origin i : ZMod q) + (step : ZMod q) * r i
  let V := fun r z x => (frozen (leftLabel z) (rightLabel (residue r)) (point x)).re
  have hbound (x : ∀ i, Fin (N i)) (i) : |(point x i : ℝ)| ≤ T i := by
    simpa only [point, affineParentIntegerPoint, Int.cast_add, Int.cast_mul,
      Int.cast_natCast] using hparent i (x i).val (x i).isLt
  have hclose (r : ι → ZMod q) (z : ι → Fin (Q + 1)) (x : ∀ i, Fin (N i))
      (hr : ∀ i, ((x i).val : ZMod q) = r i)
      (hz : ∀ i, |(origin i : ℝ) + (step : ℝ) * (x i).val -
        normalizedRealBoxGrid T Q z i| ≤ T i * (2 / Q)) :
      dist (f (point x)).re (V r z x) ≤ ε := by
    have hres : (fun i => (point x i : ZMod q)) = residue r := by
      funext i
      simp only [point, affineParentIntegerPoint, Int.cast_add, Int.cast_mul,
        Int.cast_natCast, hr, residue]
    have hcell (i) : |(point x i : ℝ) - normalizedRealBoxGrid T Q z i| ≤ T i * (2 / Q) := by
      simpa only [point, affineParentIntegerPoint, Int.cast_add, Int.cast_mul,
        Int.cast_natCast] using hz i
    have hn := hfreeze z (point x) (hbound x) hcell
    rw [hres] at hn
    exact (show dist (f (point x)).re (V r z x) ≤
        ‖f (point x) - frozen (leftLabel z) (rightLabel (residue r)) (point x)‖ by
      simpa only [Real.dist_eq, V, Complex.sub_re] using
        Complex.abs_re_le_norm (f (point x) -
          frozen (leftLabel z) (rightLabel (residue r)) (point x))).trans hn
  obtain ⟨A, hlen, hlong, r, z, hr, hz, hs⟩ := exists_long_residue_cell_frozen_score
    N hN q Q hq hQ (fun i => (origin i : ℝ)) (step : ℝ) (Nat.cast_nonneg _)
    T hT hparent hparentwidth hlarge (fun x => score (point x)) (fun x => (f (point x)).re)
    V hB hτ hε hθ (fun x => hscoreBound (point x) (hbound x))
    (fun x => hcap (point x) (hbound x)) hclose hscore hbudget
  let jzero : ∀ i, Fin (A.length i) := fun i => ⟨0, hlen i⟩
  have hrstart : ∀ i, (A.start i : ZMod q) = r i := by
    intro i
    simpa only [ResidueBoxSlice.point, jzero, Nat.mul_zero, Nat.add_zero] using hr jzero i
  have hresidue : residue r =
      fun i => ((origin i + (step : ℤ) * A.start i : ℤ) : ZMod q) := by
    funext i
    simp only [residue, Int.cast_add, Int.cast_mul, Int.cast_natCast, hrstart]
  refine ⟨A, hlen, hlong, z, ?_, ?_⟩
  · intro j
    have hcell (i) : |(A.affineIntegerPoint origin step j i : ℝ) -
        normalizedRealBoxGrid T Q z i| ≤ T i * (2 / Q) := by
      simpa only [ResidueBoxSlice.affineIntegerPoint, Int.cast_add, Int.cast_mul,
        Int.cast_natCast] using hz j i
    have hn := hfreeze z (A.affineIntegerPoint origin step j) (hbound (A.point j)) hcell
    simpa only [A.affineIntegerPoint_residue origin step j] using hn
  · dsimp only [V] at hs
    rw [hresidue] at hs
    exact hs

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators

theorem exists_long_affine_residue_cell_frozen_score_with_cell
    {ι I J : Type*} [Fintype ι] [DecidableEq ι] (N : ι → ℕ)
    (hN : ∀ i, 0 < N i) (q Q : ℕ) (hq : 0 < q) (hQ : 0 < Q)
    (origin : ι → ℤ) (step : ℕ) (T : ι → ℝ) (hT : ∀ i, 0 < T i)
    (hparent : ∀ i n, n < N i → |(origin i : ℝ) + step * n| ≤ T i)
    (hparentwidth : ∀ i, (step : ℝ) * N i ≤ 2 * T i)
    (hlarge : ∀ i, 2 * (q : ℝ) ≤ (1 / (Q : ℝ)) * N i)
    (score : (ι → ℤ) → ℝ) (f : (ι → ℤ) → ℂ)
    (frozen : I → J → (ι → ℤ) → ℂ)
    (leftLabel : (ι → Fin (Q + 1)) → I) (rightLabel : (ι → ZMod q) → J)
    {B τ ε θ S : ℝ} (hB : 0 ≤ B) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) (hθ : 0 < θ)
    (hscoreBound : ∀ x : ι → ℤ, (∀ i, |(x i : ℝ)| ≤ T i) → |score x| ≤ 1)
    (hcap : ∀ x : ι → ℤ, (∀ i, |(x i : ℝ)| ≤ T i) → score x * (f x).re ≤ B)
    (hfreeze : ∀ a (x : ι → ℤ), (∀ i, |(x i : ℝ)| ≤ T i) →
      (∀ i, |(x i : ℝ) - normalizedRealBoxGrid T Q a i| ≤ T i * (2 / Q)) →
      ‖f x - frozen (leftLabel a) (rightLabel (fun i => (x i : ZMod q))) x‖ ≤ ε)
    (hscore : S ≤ 𝔼 x : (∀ i, Fin (N i)),
      score (affineParentIntegerPoint N origin step x) *
        (f (affineParentIntegerPoint N origin step x)).re)
    (hbudget : τ + ε + B * θ < S) :
    ∃ A : ResidueBoxSlice N q, (∀ i, 0 < A.length i) ∧
      (∀ i, θ * N i / (4 * q * Q * (Fintype.card ι + 1 : ℝ)) ≤ A.length i) ∧
      ∃ z : ι → Fin (Q + 1),
        (∀ (j : ∀ i, Fin (A.length i)) i,
          |(A.affineIntegerPoint origin step j i : ℝ) -
            normalizedRealBoxGrid T Q z i| ≤ T i * (2 / Q)) ∧
        (∀ j : ∀ i, Fin (A.length i),
          ‖f (A.affineIntegerPoint origin step j) -
            frozen (leftLabel z)
              (rightLabel (fun i => ((origin i + (step : ℤ) * A.start i : ℤ) : ZMod q)))
              (A.affineIntegerPoint origin step j)‖ ≤ ε) ∧
        τ < 𝔼 j : (∀ i, Fin (A.length i)),
          score (A.affineIntegerPoint origin step j) *
            (frozen (leftLabel z)
              (rightLabel (fun i => ((origin i + (step : ℤ) * A.start i : ℤ) : ZMod q)))
              (A.affineIntegerPoint origin step j)).re := by
  classical
  let point := affineParentIntegerPoint N origin step
  let residue := fun r : ι → ZMod q => fun i => (origin i : ZMod q) + (step : ZMod q) * r i
  let V := fun r z x => (frozen (leftLabel z) (rightLabel (residue r)) (point x)).re
  have hbound (x : ∀ i, Fin (N i)) (i) : |(point x i : ℝ)| ≤ T i := by
    simpa only [point, affineParentIntegerPoint, Int.cast_add, Int.cast_mul,
      Int.cast_natCast] using hparent i (x i).val (x i).isLt
  have hclose (r : ι → ZMod q) (z : ι → Fin (Q + 1)) (x : ∀ i, Fin (N i))
      (hr : ∀ i, ((x i).val : ZMod q) = r i)
      (hz : ∀ i, |(origin i : ℝ) + (step : ℝ) * (x i).val -
        normalizedRealBoxGrid T Q z i| ≤ T i * (2 / Q)) :
      dist (f (point x)).re (V r z x) ≤ ε := by
    have hres : (fun i => (point x i : ZMod q)) = residue r := by
      funext i
      simp only [point, affineParentIntegerPoint, Int.cast_add, Int.cast_mul,
        Int.cast_natCast, hr, residue]
    have hcell (i) : |(point x i : ℝ) - normalizedRealBoxGrid T Q z i| ≤ T i * (2 / Q) := by
      simpa only [point, affineParentIntegerPoint, Int.cast_add, Int.cast_mul,
        Int.cast_natCast] using hz i
    have hn := hfreeze z (point x) (hbound x) hcell
    rw [hres] at hn
    exact (show dist (f (point x)).re (V r z x) ≤
        ‖f (point x) - frozen (leftLabel z) (rightLabel (residue r)) (point x)‖ by
      simpa only [Real.dist_eq, V, Complex.sub_re] using
        Complex.abs_re_le_norm (f (point x) -
          frozen (leftLabel z) (rightLabel (residue r)) (point x))).trans hn
  obtain ⟨A, hlen, hlong, r, z, hr, hz, hs⟩ := exists_long_residue_cell_frozen_score
    N hN q Q hq hQ (fun i => (origin i : ℝ)) (step : ℝ) (Nat.cast_nonneg _)
    T hT hparent hparentwidth hlarge (fun x => score (point x)) (fun x => (f (point x)).re)
    V hB hτ hε hθ (fun x => hscoreBound (point x) (hbound x))
    (fun x => hcap (point x) (hbound x)) hclose hscore hbudget
  let jzero : ∀ i, Fin (A.length i) := fun i => ⟨0, hlen i⟩
  have hrstart : ∀ i, (A.start i : ZMod q) = r i := by
    intro i
    simpa only [ResidueBoxSlice.point, jzero, Nat.mul_zero, Nat.add_zero] using hr jzero i
  have hresidue : residue r =
      fun i => ((origin i + (step : ℤ) * A.start i : ℤ) : ZMod q) := by
    funext i
    simp only [residue, Int.cast_add, Int.cast_mul, Int.cast_natCast, hrstart]
  have hcell (j : ∀ i, Fin (A.length i)) (i) :
      |(A.affineIntegerPoint origin step j i : ℝ) -
        normalizedRealBoxGrid T Q z i| ≤ T i * (2 / Q) := by
    simpa only [ResidueBoxSlice.affineIntegerPoint, Int.cast_add, Int.cast_mul,
      Int.cast_natCast] using hz j i
  refine ⟨A, hlen, hlong, z, hcell, ?_, ?_⟩
  · intro j
    have hn := hfreeze z (A.affineIntegerPoint origin step j) (hbound (A.point j)) (hcell j)
    simpa only [A.affineIntegerPoint_residue origin step j] using hn
  · dsimp only [V] at hs
    rw [hresidue] at hs
    exact hs

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {I : Type*} {N : I → ℕ} {q r : ℕ}

theorem composeSlice_integerPoint (S : ResidueBoxSlice N q)
    (T : ResidueBoxSlice S.length r) (j : ∀ i, Fin (T.length i)) :
    (S.composeSlice T).integerPoint j = S.integerPoint (T.point j) := by
  unfold integerPoint
  rw [S.composeSlice_point T]

theorem composeSlice_integerPoint_affine (S : ResidueBoxSlice N q)
    (T : ResidueBoxSlice S.length r) (j : ∀ i, Fin (T.length i)) :
    (S.composeSlice T).integerPoint j =
      T.affineIntegerPoint (fun i => (S.start i : ℤ)) q j := by
  rw [S.composeSlice_integerPoint T]
  funext i
  simp only [integerPoint, point, affineIntegerPoint, Nat.cast_add, Nat.cast_mul]

variable [Fintype I] [DecidableEq I]

theorem composeSlice_integerPoints_eq_affine_image (S : ResidueBoxSlice N q)
    (T : ResidueBoxSlice S.length r) :
    (S.composeSlice T).integerPoints =
      Finset.univ.image (T.affineIntegerPoint (fun i => (S.start i : ℤ)) q) := by
  unfold integerPoints
  apply Finset.image_congr
  intro j _
  exact S.composeSlice_integerPoint_affine T j

theorem composeSlice_integerPoints_eq_image (S : ResidueBoxSlice N q)
    (T : ResidueBoxSlice S.length r) :
    (S.composeSlice T).integerPoints =
      T.integerPoints.image (commonStridePoint (fun i => (S.start i : ℤ)) q) := by
  rw [composeSlice_integerPoints_eq_affine_image, integerPoints, Finset.image_image]
  apply Finset.image_congr
  intro j _
  rfl

theorem composeSlice_integerPoints_subset (S : ResidueBoxSlice N q)
    (T : ResidueBoxSlice S.length r) :
    (S.composeSlice T).integerPoints ⊆ S.integerPoints := by
  intro x hx
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr
    ⟨T.point j, Finset.mem_univ _, (S.composeSlice_integerPoint T j).symm⟩

theorem expect_composeSlice_integerPoints (S : ResidueBoxSlice N q)
    (T : ResidueBoxSlice S.length r) (hq : 0 < q) (hr : 0 < r)
    {V : Type*} [AddCommMonoid V] [Module ℚ≥0 V] (f : (I → ℤ) → V) :
    (𝔼 x ∈ (S.composeSlice T).integerPoints, f x) =
      𝔼 j : (∀ i, Fin (T.length i)),
        f (T.affineIntegerPoint (fun i => (S.start i : ℤ)) q j) := by
  rw [(S.composeSlice T).expect_integerPoints (Nat.mul_pos hq hr) f]
  apply Finset.expect_congr rfl
  intro j _
  exact congrArg f (S.composeSlice_integerPoint_affine T j)

theorem composeSlice_isDenseCommonStrideBox (S : ResidueBoxSlice N q)
    (T : ResidueBoxSlice S.length r) (hq : 0 < q) (hr : 0 < r)
    {cost loss : ℝ} (hS : IsDenseCommonStrideBox N cost S.integerPoints)
    (hT : ∀ i, (S.length i : ℝ) * Real.exp (-loss) ≤ (T.length i : ℝ)) :
    IsDenseCommonStrideBox N (cost + loss) (S.composeSlice T).integerPoints := by
  refine ⟨fun i => ((S.composeSlice T).start i : ℤ), q * r,
    (S.composeSlice T).length, Nat.mul_pos hq hr, ?_,
    (S.composeSlice T).progression_inside, ?_,
    (S.composeSlice T).integerPoints_eq_commonStrideBox⟩
  · intro i
    have hpos : (0 : ℝ) < T.length i :=
      (mul_pos (Nat.cast_pos.mpr (S.length_pos_of_dense hS i))
        (Real.exp_pos _)).trans_le (hT i)
    exact_mod_cast hpos
  · exact S.composeSlice_length_lower T (S.length_lower_of_dense hq hS) hT

theorem composeSlice_isDenseCommonStrideBox_of_fraction (S : ResidueBoxSlice N q)
    (T : ResidueBoxSlice S.length r) (hq : 0 < q) (hr : 0 < r)
    {cost θ denominator : ℝ} (hS : IsDenseCommonStrideBox N cost S.integerPoints)
    (hθ : 0 < θ) (hdenominator : 0 < denominator)
    (hT : ∀ i, θ * S.length i / denominator ≤ (T.length i : ℝ)) :
    IsDenseCommonStrideBox N (cost + Real.log (denominator / θ))
      (S.composeSlice T).integerPoints := by
  apply S.composeSlice_isDenseCommonStrideBox T hq hr hS
  intro i
  simpa only [Real.exp_neg, Real.exp_log (div_pos hdenominator hθ), inv_div,
    ← mul_div_assoc, mul_comm (S.length i : ℝ) θ] using hT i

theorem refined_stride_le_twice_exp_cost (S : ResidueBoxSlice N q) (hq : 0 < q)
    {cost loss : ℝ} (hS : IsDenseCommonStrideBox N cost S.integerPoints)
    (i : I) (hlen : 2 ≤ S.length i) (hr : (r : ℝ) ≤ Real.exp loss) :
    ((q * r : ℕ) : ℝ) ≤ 2 * Real.exp (cost + loss) := by
  have hqbound := S.stride_le_twice_exp_cost i hlen (S.length_lower_of_dense hq hS i)
  calc
    _ = (q : ℝ) * r := Nat.cast_mul _ _
    _ ≤ (2 * Real.exp cost) * Real.exp loss :=
      mul_le_mul hqbound hr (Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

theorem refined_stride_le_exp_cost (S : ResidueBoxSlice N q) (hq : 0 < q)
    {cost loss : ℝ} (hS : IsDenseCommonStrideBox N cost S.integerPoints)
    (i : I) (hlen : 2 ≤ S.length i) (hr : (r : ℝ) ≤ Real.exp loss) :
    ((q * r : ℕ) : ℝ) ≤ Real.exp (cost + loss + 1) := by
  apply (S.refined_stride_le_twice_exp_cost hq hS i hlen hr).trans
  rw [Real.exp_add (cost + loss) 1]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  calc
    _ = Real.exp (cost + loss) * 2 := mul_comm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg _)

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal BigOperators

noncomputable def Niltest.markedFrozenValue
    {σ L T : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d} {v : σ → ℕ}
    (test : D.Niltest v) (F : NilpotentLieFiltration T t) (w : σ → ℕ)
    (S : T →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (EF RF : (F.realification.adaptedPolynomialFiltration w).Group)
    (P : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (kE kR : D.RealGroup) (x : σ → ℤ) : ℂ :=
  test.observable (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
    (fun i => (x i : ℝ)) (D.filtration.frozenMarkedLeft F w S hS EF kE * P *
      D.filtration.frozenMarkedRight F w S hS RF kR)))

def MarkedAffineSliceFreezing
    {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (S : T →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (l : ℕ) (Tbox : σ → ℝ) (A ε B : ℝ) : Prop :=
  ∃ N Q M m n : ℕ, 0 < N ∧ 0 < Q ∧ (Q : ℝ) ≤ max 1 B ∧ 0 < M ∧ 0 < m ∧ 0 < n ∧
    (Fintype.card (Fin d → Fin (N + 1)) : ℝ) ≤ B ∧
    (Fintype.card (σ → Fin (Q + 1)) : ℝ) ≤ B ∧
    (M : ℝ) ≤ B ∧ (m : ℝ) ≤ B ∧ (n : ℝ) ≤ B ∧
    (Fintype.card ((Fin d → Fin (N + 1)) × Fin n) : ℝ) ≤ B ^ 2 ∧
    ∃ (left : (Fin d → Fin (N + 1)) → D.RealGroup) (right : Fin n → D.RealGroup),
      (∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := F.lowerCentralSeries_eq_bot) φ (left j) = 1 ∧
        ∀ i, |(D.basis.baseChange ℝ).repr (left j).coord i| ≤ B) ∧
      (∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := F.lowerCentralSeries_eq_bot) φ (right j) = 1 ∧
        (∀ i, |(D.basis.baseChange ℝ).repr (right j).coord i| ≤ B) ∧
        (D.basis.baseChange ℝ).equivFun (right j).coord ∈ realDenominatorGrid m) ∧
      ∀ (E : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (EF : (F.realification.adaptedPolynomialFiltration w).Group)
        (R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (RF : (F.realification.adaptedPolynomialFiltration w).Group),
        D.filtration.PolynomialSlowBound D.basis w Tbox A E →
        F.PolynomialSlowBound c w Tbox A EF →
        D.filtration.PolynomialRationalGrid D.basis w l R →
        F.PolynomialRationalGrid c w l RF →
        D.filtration.realPolynomialGroupMap F φ hφ w E = EF →
        D.filtration.realPolynomialGroupMap F φ hφ w R = RF →
        (∀ i j,
          D.filtration.realPolynomialGroupMap F φ hφ w
            (D.filtration.frozenMarkedLeft F w S hS EF (left i)) = EF ∧
          D.filtration.realPolynomialGroupMap F φ hφ w
            (D.filtration.frozenMarkedRight F w S hS RF (right j)) = RF) ∧
        ∀ (test : D.Niltest w)
          (g P : (D.filtration.realification.adaptedPolynomialFiltration w).Group),
          E * P * R = g →
          ∀ Nparent : σ → ℕ, (∀ i, 0 < Nparent i) →
          ∀ (origin : σ → ℤ) (step : ℕ),
          (∀ i v, v < Nparent i → |(origin i : ℝ) + step * v| ≤ Tbox i) →
          (∀ i, (step : ℝ) * Nparent i ≤ 2 * Tbox i) →
          (∀ i, 2 * (M : ℝ) ≤ (1 / (Q : ℝ)) * Nparent i) →
          ∀ (score : (σ → ℤ) → ℝ) (Bscore τ θ Sscore : ℝ),
          (test.normBound : ℝ) ≤ Bscore → 0 ≤ τ → 0 < θ →
          (∀ x : σ → ℤ, (∀ i, |(x i : ℝ)| ≤ Tbox i) → |score x| ≤ 1) →
          (Sscore ≤ 𝔼 x : (∀ i, Fin (Nparent i)),
            score (affineParentIntegerPoint Nparent origin step x) *
              (test.observable (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
                (fun i => (affineParentIntegerPoint Nparent origin step x i : ℝ)) g))).re) →
          τ + (test.lipBound : ℝ) * ε + Bscore * θ < Sscore →
          ∃ A : ResidueBoxSlice Nparent M, (∀ i, 0 < A.length i) ∧
            (∀ i, θ * Nparent i / (4 * M * Q * (Fintype.card σ + 1 : ℝ)) ≤ A.length i) ∧
            ∃ i j,
              (∀ x : ∀ i, Fin (A.length i),
                ‖test.observable (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
                    (fun i => (A.affineIntegerPoint origin step x i : ℝ)) g)) -
                  test.markedFrozenValue F w S hS EF RF P (left i) (right j)
                    (A.affineIntegerPoint origin step x)‖ ≤ (test.lipBound : ℝ) * ε) ∧
              τ < 𝔼 x : (∀ i, Fin (A.length i)),
                score (A.affineIntegerPoint origin step x) *
                  (test.markedFrozenValue F w S hS EF RF P (left i) (right j)
                    (A.affineIntegerPoint origin step x)).re

theorem BoundedCellMarkedPolynomialFreezing.affine_slice
    {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {F : NilpotentLieFiltration T t} {c : Basis κ ℚ T} {φ : L →ₗ⁅ℚ⁆ T}
    {hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j}
    {w : σ → ℕ} {S : T →ₗ[ℚ] L}
    {hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j}
    {l : ℕ} {Tbox : σ → ℝ} {A ε B : ℝ}
    (hfreeze : D.BoundedCellMarkedPolynomialFreezing F c φ hφ w S hS l Tbox A ε B)
    (hT : ∀ i, 0 < Tbox i) (hε : 0 ≤ ε) :
    D.MarkedAffineSliceFreezing F c φ hφ w S hS l Tbox A ε B := by
  obtain ⟨N, Q, M, m, n, hN, hQ, hQb, hM, hm, hn, hNc, hQc, hMb, hmb, hnb,
    hpair, left, right, hl, hr, hfreeze⟩ := hfreeze
  refine ⟨N, Q, M, m, n, hN, hQ, hQb, hM, hm, hn, hNc, hQc, hMb, hmb, hnb,
    hpair, left, right, hl, hr, ?_⟩
  intro E EF R RF hE hEF hR hRF hEproj hRproj
  obtain ⟨leftLabel, rightLabel, hmarks, herror⟩ := hfreeze E EF R RF hE hEF hR hRF hEproj hRproj
  refine ⟨hmarks, ?_⟩
  intro test g P hfac Nparent hNp origin step hparent hwidth hlarge score Bscore τ θ Sscore
    hnorm hτ hθ hscoreBound hscore hbudget
  let f : (σ → ℤ) → ℂ := fun x => test.observable (QuotientGroup.mk
    (D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) g))
  let frozen := fun i j => test.markedFrozenValue F w S hS EF RF P (left i) (right j)
  have hcap (x : σ → ℤ) (hx : ∀ i, |(x i : ℝ)| ≤ Tbox i) : score x * (f x).re ≤ Bscore := by
    have hf : |(f x).re| ≤ test.normBound :=
      (Complex.abs_re_le_norm _).trans (test.norm_le _)
    calc
      _ ≤ |score x * (f x).re| := le_abs_self _
      _ = |score x| * |(f x).re| := abs_mul _ _
      _ ≤ 1 * (test.normBound : ℝ) :=
        mul_le_mul (hscoreBound x hx) hf (abs_nonneg _) (by norm_num)
      _ ≤ Bscore := by simpa only [one_mul] using hnorm
  have hclose (a) (x : σ → ℤ) (hx : ∀ i, |(x i : ℝ)| ≤ Tbox i)
      (ha : ∀ i, |(x i : ℝ) - normalizedRealBoxGrid Tbox Q a i| ≤ Tbox i * (2 / Q)) :
      ‖f x - frozen (leftLabel a) (rightLabel (fun i => (x i : ZMod M))) x‖ ≤
        (test.lipBound : ℝ) * ε := herror test g P hfac a x hx ha
  obtain ⟨A, hlen, hlong, z, herr, hretained⟩ := exists_long_affine_residue_cell_frozen_score
    Nparent hNp M Q hM hQ origin step Tbox hT hparent hwidth hlarge score f frozen
    leftLabel rightLabel ((NNReal.coe_nonneg _).trans hnorm) hτ
    (mul_nonneg (NNReal.coe_nonneg _) hε) hθ hscoreBound hcap hclose hscore hbudget
  exact ⟨A, hlen, hlong, leftLabel z,
    rightLabel (fun i => ((origin i + (step : ℤ) * A.start i : ℤ) : ZMod M)),
    herr, hretained⟩

theorem exists_uniform_marked_affine_slice_freezing (s a u : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d t : ℕ} (D : RationalFilteredNilmanifold L s d)
      (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T)
      (ω : Fin d → ℕ)
      (_hDlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (τ : κ → ℕ) (_hFlayers : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
      (φ : L →ₗ⁅ℚ⁆ T) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j),
      (∀ j, ∀ y ∈ F.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
      ∀ w : σ → ℕ, (∀ i, 0 < w i) → ∀ p : ℝ,
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∃ (S : T →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j),
        Function.RightInverse S φ ∧
        (∀ i j, RationalHeightLE (D.basis.repr (S (c j)) i)
          (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊)) ∧
        ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
          ∀ Tbox : σ → ℝ, (∀ i, 0 < Tbox i) →
            D.MarkedAffineSliceFreezing F c φ hφ w S hS l Tbox
              (Real.exp ((p + 2) ^ a)) (Real.exp (-((p + 2) ^ u)))
              (Real.exp ((p + C) ^ C)) := by
  obtain ⟨C, hC, hbase⟩ := exists_uniform_bounded_cell_marked_polynomial_freezing s a u
  refine ⟨C, hC, ?_⟩
  intro σ κ L T _ _ _ _ _ _ _ _ _ _ _ d t D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  obtain ⟨S, hS, hright, hSb, hfreeze⟩ := hbase D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  exact ⟨S, hS, hright, hSb, fun l hl hlp Tbox hT =>
    (hfreeze l hl hlp Tbox hT).affine_slice hT (Real.exp_nonneg _)⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal BigOperators

def ExternalMarkedAffineSliceFreezing
    {X σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (S : T →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (l : ℕ) (Tbox : σ → ℝ) (A ε B : ℝ) : Prop :=
  ∃ N Q M m n : ℕ, 0 < N ∧ 0 < Q ∧ (Q : ℝ) ≤ max 1 B ∧ 0 < M ∧ 0 < m ∧ 0 < n ∧
    (Fintype.card (Fin d → Fin (N + 1)) : ℝ) ≤ B ∧
    (Fintype.card (σ → Fin (Q + 1)) : ℝ) ≤ B ∧
    (M : ℝ) ≤ B ∧ (m : ℝ) ≤ B ∧ (n : ℝ) ≤ B ∧
    (Fintype.card ((Fin d → Fin (N + 1)) × Fin n) : ℝ) ≤ B ^ 2 ∧
    ∃ (left : (Fin d → Fin (N + 1)) → D.RealGroup) (right : Fin n → D.RealGroup),
      (∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := F.lowerCentralSeries_eq_bot) φ (left j) = 1 ∧
        ∀ i, |(D.basis.baseChange ℝ).repr (left j).coord i| ≤ B) ∧
      (∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := F.lowerCentralSeries_eq_bot) φ (right j) = 1 ∧
        (∀ i, |(D.basis.baseChange ℝ).repr (right j).coord i| ≤ B) ∧
        (D.basis.baseChange ℝ).equivFun (right j).coord ∈ realDenominatorGrid m) ∧
      ∀ (E : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (EF : (F.realification.adaptedPolynomialFiltration w).Group)
        (R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (RF : (F.realification.adaptedPolynomialFiltration w).Group),
        D.filtration.PolynomialSlowBound D.basis w Tbox A E →
        F.PolynomialSlowBound c w Tbox A EF →
        D.filtration.PolynomialRationalGrid D.basis w l R →
        F.PolynomialRationalGrid c w l RF →
        D.filtration.realPolynomialGroupMap F φ hφ w E = EF →
        D.filtration.realPolynomialGroupMap F φ hφ w R = RF →
        (∀ i j,
          D.filtration.realPolynomialGroupMap F φ hφ w
            (D.filtration.frozenMarkedLeft F w S hS EF (left i)) = EF ∧
          D.filtration.realPolynomialGroupMap F φ hφ w
            (D.filtration.frozenMarkedRight F w S hS RF (right j)) = RF) ∧
        ∀ (tests : X → D.Niltest w) (physical : (σ → ℤ) → X)
          (weight : (σ → ℤ) → ℂ) (Bweight Bobs Lip : ℝ),
          0 ≤ Bweight → 0 ≤ Bobs → 0 ≤ Lip →
          (∀ x : σ → ℤ, (∀ i, |(x i : ℝ)| ≤ Tbox i) → ‖weight x‖ ≤ Bweight) →
          (∀ z, ((tests z).normBound : ℝ) ≤ Bobs) →
          (∀ z, ((tests z).lipBound : ℝ) ≤ Lip) →
          ∀ (g P : (D.filtration.realification.adaptedPolynomialFiltration w).Group),
          E * P * R = g →
          ∀ Nparent : σ → ℕ, (∀ i, 0 < Nparent i) →
          ∀ (origin : σ → ℤ) (step : ℕ),
          (∀ i v, v < Nparent i → |(origin i : ℝ) + step * v| ≤ Tbox i) →
          (∀ i, (step : ℝ) * Nparent i ≤ 2 * Tbox i) →
          (∀ i, 2 * (M : ℝ) ≤ (1 / (Q : ℝ)) * Nparent i) →
          ∀ τ θ Sscore : ℝ, 0 ≤ τ → 0 < θ →
          (Sscore ≤ 𝔼 x : (∀ i, Fin (Nparent i)),
            (weight (affineParentIntegerPoint Nparent origin step x) *
              (tests (physical (affineParentIntegerPoint Nparent origin step x))).observable
                (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
                  (fun i => (affineParentIntegerPoint Nparent origin step x i : ℝ)) g))).re) →
          τ + Bweight * (Lip * ε) + (Bweight * Bobs) * θ < Sscore →
          ∃ A : ResidueBoxSlice Nparent M, (∀ i, 0 < A.length i) ∧
            (∀ i, θ * Nparent i / (4 * M * Q * (Fintype.card σ + 1 : ℝ)) ≤ A.length i) ∧
            ∃ i j,
              (∀ x : ∀ i, Fin (A.length i),
                ‖(tests (physical (A.affineIntegerPoint origin step x))).observable
                    (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
                      (fun i => (A.affineIntegerPoint origin step x i : ℝ)) g)) -
                  (tests (physical (A.affineIntegerPoint origin step x))).markedFrozenValue
                    F w S hS EF RF P (left i) (right j)
                    (A.affineIntegerPoint origin step x)‖ ≤ Lip * ε) ∧
              (∀ x : ∀ i, Fin (A.length i),
                ‖weight (A.affineIntegerPoint origin step x) *
                    (tests (physical (A.affineIntegerPoint origin step x))).observable
                      (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
                        (fun i => (A.affineIntegerPoint origin step x i : ℝ)) g)) -
                  weight (A.affineIntegerPoint origin step x) *
                    (tests (physical (A.affineIntegerPoint origin step x))).markedFrozenValue
                      F w S hS EF RF P (left i) (right j)
                      (A.affineIntegerPoint origin step x)‖ ≤ Bweight * (Lip * ε)) ∧
              τ < 𝔼 x : (∀ i, Fin (A.length i)),
                (weight (A.affineIntegerPoint origin step x) *
                  (tests (physical (A.affineIntegerPoint origin step x))).markedFrozenValue
                    F w S hS EF RF P (left i) (right j)
                    (A.affineIntegerPoint origin step x)).re

theorem BoundedCellMarkedPolynomialFreezing.external_affine_slice
    {X σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {F : NilpotentLieFiltration T t} {c : Basis κ ℚ T} {φ : L →ₗ⁅ℚ⁆ T}
    {hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j}
    {w : σ → ℕ} {S : T →ₗ[ℚ] L}
    {hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j}
    {l : ℕ} {Tbox : σ → ℝ} {A ε B : ℝ}
    (hfreeze : D.BoundedCellMarkedPolynomialFreezing F c φ hφ w S hS l Tbox A ε B)
    (hT : ∀ i, 0 < Tbox i) (hε : 0 ≤ ε) :
    D.ExternalMarkedAffineSliceFreezing (X := X) F c φ hφ w S hS l Tbox A ε B := by
  obtain ⟨N, Q, M, m, n, hN, hQ, hQb, hM, hm, hn, hNc, hQc, hMb, hmb, hnb,
    hpair, left, right, hl, hr, hfreeze⟩ := hfreeze
  refine ⟨N, Q, M, m, n, hN, hQ, hQb, hM, hm, hn, hNc, hQc, hMb, hmb, hnb,
    hpair, left, right, hl, hr, ?_⟩
  intro E EF R RF hE hEF hR hRF hEproj hRproj
  obtain ⟨leftLabel, rightLabel, hmarks, herror⟩ := hfreeze E EF R RF hE hEF hR hRF hEproj hRproj
  refine ⟨hmarks, ?_⟩
  intro tests physical weight Bweight Bobs Lip hBw hBo hLip hweight hnorm hlip
    g P hfac Nparent hNp origin step hparent hwidth hlarge τ θ Sscore hτ hθ hscore hbudget
  let observed : (σ → ℤ) → ℂ := fun x => (tests (physical x)).observable
    (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) g))
  let frozen := fun i j x => (tests (physical x)).markedFrozenValue
    F w S hS EF RF P (left i) (right j) x
  let weighted := fun x => weight x * observed x
  let weightedFrozen := fun i j x => weight x * frozen i j x
  have hcap (x : σ → ℤ) (hx : ∀ i, |(x i : ℝ)| ≤ Tbox i) :
      (1 : ℝ) * (weighted x).re ≤ Bweight * Bobs := by
    have ho : ‖observed x‖ ≤ Bobs := ((tests (physical x)).norm_le _).trans (hnorm _)
    calc
      _ = (weighted x).re := one_mul _
      _ ≤ ‖weighted x‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
      _ = ‖weight x‖ * ‖observed x‖ := norm_mul _ _
      _ ≤ Bweight * Bobs := mul_le_mul (hweight x hx) ho (norm_nonneg _) hBw
  have hpoint (a) (x : σ → ℤ) (hx : ∀ i, |(x i : ℝ)| ≤ Tbox i)
      (ha : ∀ i, |(x i : ℝ) - normalizedRealBoxGrid Tbox Q a i| ≤ Tbox i * (2 / Q)) :
      ‖observed x - frozen (leftLabel a) (rightLabel (fun i => (x i : ZMod M))) x‖ ≤
        Lip * ε :=
    (herror (tests (physical x)) g P hfac a x hx ha).trans
      (mul_le_mul_of_nonneg_right (hlip _) hε)
  have hclose (a) (x : σ → ℤ) (hx : ∀ i, |(x i : ℝ)| ≤ Tbox i)
      (ha : ∀ i, |(x i : ℝ) - normalizedRealBoxGrid Tbox Q a i| ≤ Tbox i * (2 / Q)) :
      ‖weighted x - weightedFrozen (leftLabel a)
        (rightLabel (fun i => (x i : ZMod M))) x‖ ≤ Bweight * (Lip * ε) := by
    change ‖weight x * observed x - weight x * frozen _ _ x‖ ≤ _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (hweight x hx) (hpoint a x hx ha) (norm_nonneg _) hBw
  obtain ⟨A, hlen, hlong, z, hcell, herr, hretained⟩ :=
    exists_long_affine_residue_cell_frozen_score_with_cell
      Nparent hNp M Q hM hQ origin step Tbox hT hparent hwidth hlarge
      (fun _ => (1 : ℝ)) weighted weightedFrozen leftLabel rightLabel
      (mul_nonneg hBw hBo) hτ (mul_nonneg hBw (mul_nonneg hLip hε)) hθ
      (fun _ _ => by norm_num) hcap hclose
      (by simpa only [one_mul] using hscore) hbudget
  refine ⟨A, hlen, hlong, leftLabel z,
    rightLabel (fun i => ((origin i + (step : ℤ) * A.start i : ℤ) : ZMod M)), ?_, herr, ?_⟩
  · intro x
    have hx (i) : |(A.affineIntegerPoint origin step x i : ℝ)| ≤ Tbox i := by
      simpa only [ResidueBoxSlice.affineIntegerPoint, Int.cast_add, Int.cast_mul,
        Int.cast_natCast] using hparent i (A.point x i).val (A.point x i).isLt
    have hp := hpoint z (A.affineIntegerPoint origin step x) hx (hcell x)
    simpa only [A.affineIntegerPoint_residue origin step x] using hp
  · simpa only [one_mul] using hretained

theorem exists_uniform_external_marked_affine_slice_freezing (s a u : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d t : ℕ} (D : RationalFilteredNilmanifold L s d)
      (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T)
      (ω : Fin d → ℕ)
      (_hDlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (τ : κ → ℕ) (_hFlayers : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
      (φ : L →ₗ⁅ℚ⁆ T) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j),
      (∀ j, ∀ y ∈ F.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
      ∀ w : σ → ℕ, (∀ i, 0 < w i) → ∀ p : ℝ,
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∃ (S : T →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j),
        Function.RightInverse S φ ∧
        (∀ i j, RationalHeightLE (D.basis.repr (S (c j)) i)
          (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊)) ∧
        ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
          ∀ Tbox : σ → ℝ, (∀ i, 0 < Tbox i) →
            D.ExternalMarkedAffineSliceFreezing (X := X) F c φ hφ w S hS l Tbox
              (Real.exp ((p + 2) ^ a)) (Real.exp (-((p + 2) ^ u)))
              (Real.exp ((p + C) ^ C)) := by
  obtain ⟨C, hC, hbase⟩ := exists_uniform_bounded_cell_marked_polynomial_freezing s a u
  refine ⟨C, hC, ?_⟩
  intro X σ κ L T _ _ _ _ _ _ _ _ _ _ _ d t D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  obtain ⟨S, hS, hright, hSb, hfreeze⟩ := hbase D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  exact ⟨S, hS, hright, hSb, fun l hl hlp Tbox hT =>
    (hfreeze l hl hlp Tbox hT).external_affine_slice hT (Real.exp_nonneg _)⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal BigOperators

namespace ExternalMarkedAffineSliceFreezing

structure Dictionary
    {X σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (S : T →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (l : ℕ) (Tbox : σ → ℝ) (A ε B : ℝ) where
  grid : ℕ
  Q : ℕ
  modulus : ℕ
  denominator : ℕ
  rightCount : ℕ
  grid_pos : 0 < grid
  Q_pos : 0 < Q
  modulus_pos : 0 < modulus
  denominator_pos : 0 < denominator
  rightCount_pos : 0 < rightCount
  Q_bound : (Q : ℝ) ≤ max 1 B
  gridCard_bound : (Fintype.card (Fin d → Fin (grid + 1)) : ℝ) ≤ B
  cellCard_bound : (Fintype.card (σ → Fin (Q + 1)) : ℝ) ≤ B
  modulus_bound : (modulus : ℝ) ≤ B
  denominator_bound : (denominator : ℝ) ≤ B
  rightCount_bound : (rightCount : ℝ) ≤ B
  pairCard_bound : (Fintype.card ((Fin d → Fin (grid + 1)) × Fin rightCount) : ℝ) ≤ B ^ 2
  left : (Fin d → Fin (grid + 1)) → D.RealGroup
  right : Fin rightCount → D.RealGroup
  left_bounds : ∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := F.lowerCentralSeries_eq_bot) φ (left j) = 1 ∧
    ∀ i, |(D.basis.baseChange ℝ).repr (left j).coord i| ≤ B
  right_bounds : ∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := F.lowerCentralSeries_eq_bot) φ (right j) = 1 ∧
    (∀ i, |(D.basis.baseChange ℝ).repr (right j).coord i| ≤ B) ∧
    (D.basis.baseChange ℝ).equivFun (right j).coord ∈ realDenominatorGrid denominator
  select : ∀ (E : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (EF : (F.realification.adaptedPolynomialFiltration w).Group)
    (R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (RF : (F.realification.adaptedPolynomialFiltration w).Group),
    D.filtration.PolynomialSlowBound D.basis w Tbox A E →
    F.PolynomialSlowBound c w Tbox A EF →
    D.filtration.PolynomialRationalGrid D.basis w l R →
    F.PolynomialRationalGrid c w l RF →
    D.filtration.realPolynomialGroupMap F φ hφ w E = EF →
    D.filtration.realPolynomialGroupMap F φ hφ w R = RF →
    (∀ i j,
      D.filtration.realPolynomialGroupMap F φ hφ w
        (D.filtration.frozenMarkedLeft F w S hS EF (left i)) = EF ∧
      D.filtration.realPolynomialGroupMap F φ hφ w
        (D.filtration.frozenMarkedRight F w S hS RF (right j)) = RF) ∧
    ∀ (tests : X → D.Niltest w) (physical : (σ → ℤ) → X)
      (weight : (σ → ℤ) → ℂ) (Bweight Bobs Lip : ℝ),
      0 ≤ Bweight → 0 ≤ Bobs → 0 ≤ Lip →
      (∀ x : σ → ℤ, (∀ i, |(x i : ℝ)| ≤ Tbox i) → ‖weight x‖ ≤ Bweight) →
      (∀ z, ((tests z).normBound : ℝ) ≤ Bobs) →
      (∀ z, ((tests z).lipBound : ℝ) ≤ Lip) →
      ∀ (g P : (D.filtration.realification.adaptedPolynomialFiltration w).Group),
      E * P * R = g →
      ∀ Nparent : σ → ℕ, (∀ i, 0 < Nparent i) →
      ∀ (origin : σ → ℤ) (step : ℕ),
      (∀ i v, v < Nparent i → |(origin i : ℝ) + step * v| ≤ Tbox i) →
      (∀ i, (step : ℝ) * Nparent i ≤ 2 * Tbox i) →
      (∀ i, 2 * (modulus : ℝ) ≤ (1 / (Q : ℝ)) * Nparent i) →
      ∀ τ θ Sscore : ℝ, 0 ≤ τ → 0 < θ →
      (Sscore ≤ 𝔼 x : (∀ i, Fin (Nparent i)),
        (weight (affineParentIntegerPoint Nparent origin step x) *
          (tests (physical (affineParentIntegerPoint Nparent origin step x))).observable
            (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
              (fun i => (affineParentIntegerPoint Nparent origin step x i : ℝ)) g))).re) →
      τ + Bweight * (Lip * ε) + (Bweight * Bobs) * θ < Sscore →
      ∃ A : ResidueBoxSlice Nparent modulus, (∀ i, 0 < A.length i) ∧
        (∀ i, θ * Nparent i / (4 * modulus * Q * (Fintype.card σ + 1 : ℝ)) ≤ A.length i) ∧
        ∃ i j,
          (∀ x : ∀ i, Fin (A.length i),
            ‖(tests (physical (A.affineIntegerPoint origin step x))).observable
                (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
                  (fun i => (A.affineIntegerPoint origin step x i : ℝ)) g)) -
              (tests (physical (A.affineIntegerPoint origin step x))).markedFrozenValue
                F w S hS EF RF P (left i) (right j)
                (A.affineIntegerPoint origin step x)‖ ≤ Lip * ε) ∧
          (∀ x : ∀ i, Fin (A.length i),
            ‖weight (A.affineIntegerPoint origin step x) *
                (tests (physical (A.affineIntegerPoint origin step x))).observable
                  (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
                    (fun i => (A.affineIntegerPoint origin step x i : ℝ)) g)) -
              weight (A.affineIntegerPoint origin step x) *
                (tests (physical (A.affineIntegerPoint origin step x))).markedFrozenValue
                  F w S hS EF RF P (left i) (right j)
                  (A.affineIntegerPoint origin step x)‖ ≤ Bweight * (Lip * ε)) ∧
          τ < 𝔼 x : (∀ i, Fin (A.length i)),
            (weight (A.affineIntegerPoint origin step x) *
              (tests (physical (A.affineIntegerPoint origin step x))).markedFrozenValue
                F w S hS EF RF P (left i) (right j)
                (A.affineIntegerPoint origin step x)).re

theorem exists_dictionary
    {X σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {F : NilpotentLieFiltration T t} {c : Basis κ ℚ T} {φ : L →ₗ⁅ℚ⁆ T}
    {hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j}
    {w : σ → ℕ} {S : T →ₗ[ℚ] L}
    {hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j}
    {l : ℕ} {Tbox : σ → ℝ} {A ε B : ℝ}
    (hfreeze : D.ExternalMarkedAffineSliceFreezing (X := X) F c φ hφ w S hS l Tbox A ε B) :
    Nonempty (Dictionary (X := X) D F c φ hφ w S hS l Tbox A ε B) := by
  obtain ⟨grid, Q, modulus, denominator, rightCount, hgrid, hQ, hQbound,
    hmodulus, hdenominator, hrightCount, hgridCard, hcellCard, hmodulusBound,
    hdenominatorBound, hrightCountBound, hpairCard, left, right, hleft, hright,
    hselect⟩ := hfreeze
  exact ⟨⟨grid, Q, modulus, denominator, rightCount, hgrid, hQ, hmodulus,
    hdenominator, hrightCount, hQbound, hgridCard, hcellCard, hmodulusBound,
    hdenominatorBound, hrightCountBound, hpairCard, left, right, hleft, hright,
    hselect⟩⟩

end ExternalMarkedAffineSliceFreezing

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary

open Module
open scoped TensorProduct

variable {X σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {F : NilpotentLieFiltration T t} {c : Basis κ ℚ T} {φ : L →ₗ⁅ℚ⁆ T}
    {hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j}
    {w : σ → ℕ} {S : T →ₗ[ℚ] L}
    {hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j}
    {l : ℕ} {Tbox : σ → ℝ} {A A' ε B : ℝ}
    (dictionary : Dictionary (X := X) D F c φ hφ w S hS l Tbox A ε B)

def mono_slow (hT : ∀ i, 0 < Tbox i) (hslow : A' ≤ A) :
    Dictionary (X := X) D F c φ hφ w S hS l Tbox A' ε B where
  grid := dictionary.grid
  Q := dictionary.Q
  modulus := dictionary.modulus
  denominator := dictionary.denominator
  rightCount := dictionary.rightCount
  grid_pos := dictionary.grid_pos
  Q_pos := dictionary.Q_pos
  modulus_pos := dictionary.modulus_pos
  denominator_pos := dictionary.denominator_pos
  rightCount_pos := dictionary.rightCount_pos
  Q_bound := dictionary.Q_bound
  gridCard_bound := dictionary.gridCard_bound
  cellCard_bound := dictionary.cellCard_bound
  modulus_bound := dictionary.modulus_bound
  denominator_bound := dictionary.denominator_bound
  rightCount_bound := dictionary.rightCount_bound
  pairCard_bound := dictionary.pairCard_bound
  left := dictionary.left
  right := dictionary.right
  left_bounds := dictionary.left_bounds
  right_bounds := dictionary.right_bounds
  select := by
    intro E EF R RF hE hEF
    exact dictionary.select E EF R RF
      (D.filtration.polynomialSlowBound_mono D.basis w Tbox hT hslow E hE)
      (F.polynomialSlowBound_mono c w Tbox hT hslow EF hEF)

variable (hT : ∀ i, 0 < Tbox i) (hslow : A' ≤ A)

@[simp] theorem mono_slow_grid :
    (dictionary.mono_slow hT hslow).grid = dictionary.grid := rfl

@[simp] theorem mono_slow_Q :
    (dictionary.mono_slow hT hslow).Q = dictionary.Q := rfl

@[simp] theorem mono_slow_modulus :
    (dictionary.mono_slow hT hslow).modulus = dictionary.modulus := rfl

@[simp] theorem mono_slow_denominator :
    (dictionary.mono_slow hT hslow).denominator = dictionary.denominator := rfl

@[simp] theorem mono_slow_rightCount :
    (dictionary.mono_slow hT hslow).rightCount = dictionary.rightCount := rfl

@[simp] theorem mono_slow_left :
    (dictionary.mono_slow hT hslow).left = dictionary.left := rfl

@[simp] theorem mono_slow_right :
    (dictionary.mono_slow hT hslow).right = dictionary.right := rfl

end Erdos3.RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_external_marked_affine_slice_freezing_dictionary (s a u : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d t : ℕ} (D : RationalFilteredNilmanifold L s d)
      (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T)
      (ω : Fin d → ℕ)
      (_hDlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (τ : κ → ℕ) (_hFlayers : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
      (φ : L →ₗ⁅ℚ⁆ T) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j),
      (∀ j, ∀ y ∈ F.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
      ∀ w : σ → ℕ, (∀ i, 0 < w i) → ∀ p : ℝ,
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∃ (S : T →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j),
        Function.RightInverse S φ ∧
        (∀ i j, RationalHeightLE (D.basis.repr (S (c j)) i)
          (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊)) ∧
        ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
          ∀ Tbox : σ → ℝ, (∀ i, 0 < Tbox i) →
            ∀ slow : ℝ, slow ≤ Real.exp ((p + 2) ^ a) →
              Nonempty (ExternalMarkedAffineSliceFreezing.Dictionary (X := X)
                D F c φ hφ w S hS l Tbox slow (Real.exp (-((p + 2) ^ u)))
                (Real.exp ((p + C) ^ C))) := by
  obtain ⟨C, hC, hbase⟩ := exists_uniform_external_marked_affine_slice_freezing s a u
  refine ⟨C, hC, ?_⟩
  intro X σ κ L T _ _ _ _ _ _ _ _ _ _ _ d t D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  obtain ⟨S, hS, hright, hSb, hfreeze⟩ := hbase D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  refine ⟨S, hS, hright, hSb, ?_⟩
  intro l hl hlp Tbox hT slow hslow
  obtain ⟨dictionary⟩ := (hfreeze l hl hlp Tbox hT).exists_dictionary
  exact ⟨dictionary.mono_slow hT hslow⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
