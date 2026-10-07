/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Lattices.IntegerFrozenChart
import OAI.Combinatorics.Progressions.Lattices.ResidueBoxSliceSubtypeSites

namespace OAI

section

namespace Erdos3
open scoped TensorProduct BigOperators
variable {I L : Type*} [Fintype I] [DecidableEq I]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

structure LocalMajorSliceTest (D : RationalFilteredNilmanifold L s d)
    (N : I → ℕ) (cost budget : ℝ) where
  stride : ℕ
  stride_pos : 0 < stride
  slice : ResidueBoxSlice N stride
  dense : IsDenseCommonStrideBox N cost slice.integerPoints
  test : D.Niltest (fun _ : I => 1)
  norm : (test.normBound : ℝ) ≤ 1
  complexity : test.ComplexityLE budget

namespace LocalMajorSliceTest
variable {D : RationalFilteredNilmanifold L s d} {N : I → ℕ} {cost budget : ℝ}
noncomputable def weight (A : LocalMajorSliceTest D N cost budget) (x : I → ℤ) : ℂ :=
  star (A.test.eval (commonStrideIndex (fun i => (A.slice.start i : ℤ)) A.stride x))
theorem weight_norm (A : LocalMajorSliceTest D N cost budget) (x : I → ℤ) :
    ‖A.weight x‖ ≤ 1 := by
  simpa only [weight, norm_star] using
    (A.test.norm_eval_le (commonStrideIndex (fun i => (A.slice.start i : ℤ))
      A.stride x)).trans A.norm

noncomputable def full (N : I → ℕ) (hN : ∀ i, 0 < N i)
    (cost budget : ℝ) (hcost : 0 ≤ cost)
    (T : D.Niltest (fun _ : I => 1)) (hT : (T.normBound : ℝ) ≤ 1)
    (hcomplexity : T.ComplexityLE budget) : LocalMajorSliceTest D N cost budget := by
  let A : ResidueBoxSlice N 1 :=
    { start := fun _ => 0
      length := N
      inside := fun i j hj => by simpa using hj }
  refine ⟨1, Nat.zero_lt_one, A, ?_, T, hT, hcomplexity⟩
  have hA := A.isDenseCommonStrideBox Nat.zero_lt_one (ρ := 4) (by norm_num)
    hN (fun i => by dsimp [A]; norm_num)
  have hzero : IsDenseCommonStrideBox N 0 A.integerPoints := by simpa using hA
  exact hzero.mono hcost
end LocalMajorSliceTest

theorem exists_productive_localMajorSlice_coordinate_family
    {Ω X η : Type*} [Fintype Ω]
    (D : RationalFilteredNilmanifold L s d)
    (law : FiniteProbabilityWeights Ω) (good : η → Finset Ω)
    (N : I → ℕ) (hN : ∀ i, 0 < N i) (cost budget δ : ℝ)
    (fallback : LocalMajorSliceTest D N cost budget)
    (physical : Ω → (I → ℤ) → X) (signal : η → X → ℂ)
    (hlocal : ∀ j z, z ∈ good j → ∃ A : LocalMajorSliceTest D N cost budget,
      δ ≤ ‖𝔼 x ∈ A.slice.integerPoints, signal j (physical z x) * A.weight x‖) :
    ∃ chosen : Ω → Option η → LocalMajorSliceTest D N cost budget,
      (∀ j z, z ∈ good j → δ ≤ ‖𝔼 x ∈ (chosen z (some j)).slice.integerPoints,
        signal j (physical z x) * (chosen z (some j)).weight x‖) ∧
      ∀ j, δ * law.mass (good j) ≤ sampledSliceSeminorm law
        (fun z (x : integerBox N) => physical z x.val)
        (fun z a => (chosen z a).slice.subtypeSites)
        (fun z a (x : integerBox N) => (chosen z a).weight x.val) (signal j) := by
  classical
  let chosen (z : Ω) : Option η → LocalMajorSliceTest D N cost budget
    | none => fallback
    | some j => if hz : z ∈ good j then Classical.choose (hlocal j z hz) else fallback
  have hchosen (j : η) (z : Ω) (hz : z ∈ good j) :
      δ ≤ ‖𝔼 x ∈ (chosen z (some j)).slice.integerPoints,
        signal j (physical z x) * (chosen z (some j)).weight x‖ := by
    have he : chosen z (some j) = Classical.choose (hlocal j z hz) := by
      simp only [chosen, dite_eq_left hz]
    rw [he]
    exact Classical.choose_spec (hlocal j z hz)
  refine ⟨chosen, hchosen, ?_⟩
  intro j
  let : Nonempty (integerBox N) := ⟨⟨fun _ => 0,
    (mem_integerBox _ _).mpr (fun i => ⟨le_rfl, by exact_mod_cast hN i⟩)⟩⟩
  apply productive_mass_mul_le_sampledSliceSeminorm law (good j)
    (fun z (x : integerBox N) => physical z x.val)
    (fun z a => (chosen z a).slice.subtypeSites)
    (fun z a (x : integerBox N) => (chosen z a).weight x.val)
    (fun z a => (chosen z a).slice.subtypeSites_nonempty_of_integerPoints
      (chosen z a).dense.nonempty)
    (fun z a x => (chosen z a).weight_norm x.val) (signal j) δ
  intro z hz
  refine ⟨some j, ?_⟩
  rw [(chosen z (some j)).slice.expect_subtypeSites
    (fun x => signal j (physical z x) * (chosen z (some j)).weight x)]
  exact hchosen j z hz
namespace OrdinaryPolynomialPhase

variable {n : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra weight n)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra weight n)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra weight n)]
  [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra weight n)]

noncomputable def zeroLocalMajorSlice (N : I → ℕ) (hN : ∀ i, 0 < N i)
    (cost : ℝ) (hcost : 0 ≤ cost) :
    LocalMajorSliceTest (nilmanifold n) N cost (budget n) := by
  let T := RationalFilteredNilmanifold.Niltest.const (nilmanifold n)
    (fun _ : I => 1) (0 : ℂ)
  apply LocalMajorSliceTest.full N hN cost (budget n) hcost T
  · change ‖(0 : ℂ)‖ ≤ 1
    simp
  · refine ⟨nilmanifold_geometry n, ?_⟩
    change Real.log (2 + ‖(0 : ℂ)‖ + 0) ≤ budget n
    simp only [norm_zero, add_zero]
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith [two_le_budget n]

end OrdinaryPolynomialPhase

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

variable {V : Type*} (Long : V → Prop) [DecidablePred Long]

def frozenLongExtension (fixed : V → ℕ) (x : {i // Long i} → ℤ) : V → ℤ :=
  fun i => if hi : Long i then x ⟨i, hi⟩ else (fixed i : ℤ)

@[simp] theorem frozenLongExtension_long (fixed : V → ℕ)
    (x : {i // Long i} → ℤ) (i : {i // Long i}) :
    frozenLongExtension Long fixed x i.val = x i := by
  simp [frozenLongExtension, i.property]

theorem frozenLongExtension_injective (fixed : V → ℕ) :
    Function.Injective (frozenLongExtension Long fixed) := by
  intro x y h
  funext i
  simpa only [frozenLongExtension_long] using congrFun h i.val

namespace ResidueBoxSlice

variable {N : V → ℕ} {q : ℕ}

def freezeShort (A : ResidueBoxSlice (fun i : {i // Long i} => N i.val) q)
    (fixed : V → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i) :
    ResidueBoxSlice N q where
  start i := if hi : Long i then A.start ⟨i, hi⟩ else fixed i
  length i := if hi : Long i then A.length ⟨i, hi⟩ else 1
  inside i j hj := by
    by_cases hi : Long i
    · simpa only [dite_eq_left hi] using
        A.inside ⟨i, hi⟩ j (by simpa only [dite_eq_left hi] using hj)
    · have hj0 : j = 0 := by simpa only [dite_eq_right hi, Nat.lt_one_iff] using hj
      simpa only [dite_eq_right hi, hj0, mul_zero, add_zero] using hfixed i hi

variable [Fintype V] [DecidableEq V]

theorem freezeShort_integerPoints
    (A : ResidueBoxSlice (fun i : {i // Long i} => N i.val) q)
    (fixed : V → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i) :
    (A.freezeShort Long fixed hfixed).integerPoints =
      A.integerPoints.image (frozenLongExtension Long fixed) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    let t : ∀ i : {i // Long i}, Fin (A.length i) := fun i =>
      ⟨(j i.val).val, by simpa [freezeShort, i.property] using (j i.val).isLt⟩
    refine Finset.mem_image.mpr ⟨A.integerPoint t,
      Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩, ?_⟩
    funext i
    by_cases hi : Long i
    · simp [frozenLongExtension, integerPoint, point, freezeShort, hi, t]
    · have hj0 : (j i).val = 0 := by
        have := (j i).isLt
        simpa only [freezeShort, dite_eq_right hi, Nat.lt_one_iff] using this
      simp [frozenLongExtension, integerPoint, point, freezeShort, hi, hj0]
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hy
    let j : ∀ i, Fin ((A.freezeShort Long fixed hfixed).length i) := fun i =>
      if hi : Long i then
        ⟨(t ⟨i, hi⟩).val, by simp only [freezeShort, dite_eq_left hi]; exact (t ⟨i, hi⟩).isLt⟩
      else ⟨0, by simp [freezeShort, hi]⟩
    refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
    funext i
    by_cases hi : Long i <;>
      simp [frozenLongExtension, integerPoint, point, freezeShort, hi, j]

theorem expect_freezeShort
    (A : ResidueBoxSlice (fun i : {i // Long i} => N i.val) q)
    (fixed : V → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i)
    {W : Type*} [AddCommMonoid W] [Module ℚ≥0 W] (f : (V → ℤ) → W) :
    (𝔼 x ∈ (A.freezeShort Long fixed hfixed).integerPoints, f x) =
      (𝔼 x ∈ A.integerPoints, f (frozenLongExtension Long fixed x)) := by
  rw [freezeShort_integerPoints]
  exact Finset.expect_image (frozenLongExtension_injective Long fixed).injOn

omit [Fintype V] [DecidableEq V] in
theorem freezeShort_commonStrideIndex
    (A : ResidueBoxSlice (fun i : {i // Long i} => N i.val) q)
    (fixed : V → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i) (x : V → ℤ) :
    (fun i : {i // Long i} =>
      commonStrideIndex (fun j => ((A.freezeShort Long fixed hfixed).start j : ℤ)) q x i.val) =
    commonStrideIndex (fun i => (A.start i : ℤ)) q (fun i => x i.val) := by
  funext i
  simp [commonStrideIndex, freezeShort, i.property]

theorem freezeShort_dense
    (A : ResidueBoxSlice (fun i : {i // Long i} => N i.val) q)
    (fixed : V → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i)
    (hq : 0 < q) {cost B : ℝ}
    (hA : IsDenseCommonStrideBox (fun i : {i // Long i} => N i.val) cost A.integerPoints)
    (hB : 1 ≤ B) (hshort : ∀ i, ¬Long i → (N i : ℝ) ≤ B) :
    IsDenseCommonStrideBox N (max cost (Real.log B))
      (A.freezeShort Long fixed hfixed).integerPoints := by
  let A' := A.freezeShort Long fixed hfixed
  refine ⟨fun i => (A'.start i : ℤ), q, A'.length, hq, ?_,
    A'.progression_inside, ?_, A'.integerPoints_eq_commonStrideBox⟩
  · intro i
    by_cases hi : Long i
    · simpa only [A', freezeShort, dite_eq_left hi] using A.length_pos_of_dense hA ⟨i, hi⟩
    · simp [A', freezeShort, hi]
  · intro i
    by_cases hi : Long i
    · calc
        _ ≤ Real.exp (-cost) * (N i : ℝ) :=
          mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.mpr (neg_le_neg (le_max_left _ _))) (Nat.cast_nonneg _)
        _ ≤ A'.length i := by
          simpa only [A', freezeShort, dite_eq_left hi] using
            A.length_lower_of_dense hq hA ⟨i, hi⟩
    · have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
      have hexp : Real.exp (-max cost (Real.log B)) ≤ B⁻¹ := by
        calc
          _ ≤ Real.exp (-Real.log B) :=
            Real.exp_le_exp.mpr (neg_le_neg (le_max_right _ _))
          _ = B⁻¹ := by rw [Real.exp_neg, Real.exp_log hBpos]
      simp only [A', freezeShort, dite_eq_right hi, Nat.cast_one]
      calc
        _ ≤ B⁻¹ * (N i : ℝ) := mul_le_mul_of_nonneg_right hexp (Nat.cast_nonneg _)
        _ ≤ B⁻¹ * B := mul_le_mul_of_nonneg_left (hshort i hi) (inv_nonneg.mpr hBpos.le)
        _ = 1 := inv_mul_cancel₀ hBpos.ne'

end ResidueBoxSlice

def longCoordinateProjection (i : {i // Long i}) : (V → ℤ) →+ ℤ where
  toFun x := x i.val
  map_zero' := rfl
  map_add' _ _ := rfl

namespace RationalFilteredNilmanifold.Niltest

variable [Fintype V] {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d}

noncomputable def liftLong (T : D.Niltest (fun _ : {i // Long i} => 1)) :
    D.Niltest (fun _ : V => 1) :=
  T.linearPullbackHom (longCoordinateProjection Long)

omit [DecidablePred Long] in
@[simp] theorem liftLong_normBound (T : D.Niltest (fun _ : {i // Long i} => 1)) :
    (T.liftLong Long).normBound = T.normBound := rfl

omit [DecidablePred Long] in
@[simp] theorem liftLong_complexityLE (T : D.Niltest (fun _ : {i // Long i} => 1))
    (p : ℝ) : (T.liftLong Long).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

omit [DecidablePred Long] in
theorem eval_liftLong (T : D.Niltest (fun _ : {i // Long i} => 1)) (x : V → ℤ) :
    (T.liftLong Long).eval x = T.eval (fun i => x i.val) :=
  T.eval_linearPullbackHom (longCoordinateProjection Long) x

end RationalFilteredNilmanifold.Niltest

namespace LocalMajorSliceTest

variable [Fintype V] [DecidableEq V] {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {N : V → ℕ} {cost budget B : ℝ}

noncomputable def freezeShort
    (A : LocalMajorSliceTest D (fun i : {i // Long i} => N i.val) cost budget)
    (fixed : V → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i)
    (hB : 1 ≤ B) (hshort : ∀ i, ¬Long i → (N i : ℝ) ≤ B) :
    LocalMajorSliceTest D N (max cost (Real.log B)) budget where
  stride := A.stride
  stride_pos := A.stride_pos
  slice := A.slice.freezeShort Long fixed hfixed
  dense := A.slice.freezeShort_dense Long fixed hfixed A.stride_pos A.dense hB hshort
  test := A.test.liftLong Long
  norm := A.norm
  complexity := A.complexity

theorem freezeShort_weight
    (A : LocalMajorSliceTest D (fun i : {i // Long i} => N i.val) cost budget)
    (fixed : V → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i)
    (hB : 1 ≤ B) (hshort : ∀ i, ¬Long i → (N i : ℝ) ≤ B) (x : V → ℤ) :
    (A.freezeShort Long fixed hfixed hB hshort).weight x = A.weight (fun i => x i.val) := by
  change star ((A.test.liftLong Long).eval
    (commonStrideIndex (fun i => ((A.slice.freezeShort Long fixed hfixed).start i : ℤ))
      A.stride x)) = _
  rw [A.test.eval_liftLong, A.slice.freezeShort_commonStrideIndex]
  rfl

theorem expect_freezeShort
    (A : LocalMajorSliceTest D (fun i : {i // Long i} => N i.val) cost budget)
    (fixed : V → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i)
    (hB : 1 ≤ B) (hshort : ∀ i, ¬Long i → (N i : ℝ) ≤ B)
    (signal : (V → ℤ) → ℂ) :
    (𝔼 x ∈ (A.freezeShort Long fixed hfixed hB hshort).slice.integerPoints,
      signal x * (A.freezeShort Long fixed hfixed hB hshort).weight x) =
    (𝔼 x ∈ A.slice.integerPoints, signal (frozenLongExtension Long fixed x) * A.weight x) := by
  change (𝔼 x ∈ (A.slice.freezeShort Long fixed hfixed).integerPoints,
    signal x * (A.freezeShort Long fixed hfixed hB hshort).weight x) = _
  rw [A.slice.expect_freezeShort]
  apply Finset.expect_congr rfl
  intro x hx
  rw [A.freezeShort_weight]
  congr 2
  funext i
  exact frozenLongExtension_long Long fixed x i

end LocalMajorSliceTest

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

variable {I L : Type*} [Fintype I] [DecidableEq I]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

namespace LocalMajorSliceTest

noncomputable def default (D : RationalFilteredNilmanifold L s d)
    (N : I → ℕ) (hN : ∀ i, 0 < N i) (cost budget : ℝ)
    (hcost : 0 ≤ cost) (hbudget : 1 ≤ budget)
    (hgeometry : D.GeometryComplexityLE budget) :
    LocalMajorSliceTest D N cost budget := by
  let T := RationalFilteredNilmanifold.Niltest.const D (fun _ : I => 1) (0 : ℂ)
  apply full N hN cost budget hcost T
  · change ‖(0 : ℂ)‖ ≤ 1
    simp
  · refine ⟨hgeometry, ?_⟩
    change Real.log (2 + ‖(0 : ℂ)‖ + 0) ≤ budget
    simp only [norm_zero, add_zero]
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith

theorem nonempty (D : RationalFilteredNilmanifold L s d)
    (N : I → ℕ) (hN : ∀ i, 0 < N i) (cost budget : ℝ)
    (hcost : 0 ≤ cost) (hbudget : 1 ≤ budget)
    (hgeometry : D.GeometryComplexityLE budget) :
    Nonempty (LocalMajorSliceTest D N cost budget) :=
  ⟨default D N hN cost budget hcost hbudget hgeometry⟩

end LocalMajorSliceTest

end Erdos3

end

section

namespace Erdos3.LocalMajorSliceTest
open scoped TensorProduct

variable {I L : Type*} [Fintype I] [DecidableEq I]
    [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {N : I → ℕ}
    {cost budget cost' budget' : ℝ}

def mono (packet : LocalMajorSliceTest D N cost budget)
    (hcost : cost ≤ cost') (hbudget : budget ≤ budget') :
    LocalMajorSliceTest D N cost' budget' where
  stride := packet.stride
  stride_pos := packet.stride_pos
  slice := packet.slice
  dense := packet.dense.mono hcost
  test := packet.test
  norm := packet.norm
  complexity := packet.complexity.mono hbudget

@[simp] theorem mono_weight (packet : LocalMajorSliceTest D N cost budget)
    (hcost : cost ≤ cost') (hbudget : budget ≤ budget') (x : I → ℤ) :
    (packet.mono hcost hbudget).weight x = packet.weight x := rfl

end Erdos3.LocalMajorSliceTest

end

section

namespace Erdos3
open scoped TensorProduct BigOperators

variable {I : Type} [Fintype I] [DecidableEq I]

structure UniversalLocalMajorSliceTest (N : I → ℕ) (degree : ℕ)
    (cost budget : ℝ) where
  stride : ℕ
  stride_pos : 0 < stride
  slice : ResidueBoxSlice N stride
  dense : IsDenseCommonStrideBox N cost slice.integerPoints
  value : (I → ℤ) → ℂ
  native : Nonempty (NativeSampleModel (fun _ : I => 1) degree budget id value)

namespace UniversalLocalMajorSliceTest

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

variable {N : I → ℕ} {degree : ℕ} {cost budget : ℝ}

noncomputable def nativeModel (packet : UniversalLocalMajorSliceTest N degree cost budget) :
    NativeSampleModel (fun _ : I => 1) degree budget id packet.value :=
  Classical.choice packet.native

theorem value_eq_native_eval (packet : UniversalLocalMajorSliceTest N degree cost budget)
    (x : I → ℤ) : packet.value x = packet.nativeModel.test.eval x :=
  packet.nativeModel.eval x

noncomputable def weight (packet : UniversalLocalMajorSliceTest N degree cost budget)
    (x : I → ℤ) : ℂ :=
  star (packet.value
    (commonStrideIndex (fun i => (packet.slice.start i : ℤ)) packet.stride x))

theorem weight_eq_native_eval (packet : UniversalLocalMajorSliceTest N degree cost budget)
    (x : I → ℤ) :
    packet.weight x = star (packet.nativeModel.test.eval
      (commonStrideIndex (fun i => (packet.slice.start i : ℤ)) packet.stride x)) := by
  rw [weight, packet.value_eq_native_eval]

theorem weight_norm (packet : UniversalLocalMajorSliceTest N degree cost budget)
    (x : I → ℤ) : ‖packet.weight x‖ ≤ 1 := by
  rw [weight, norm_star]
  exact packet.nativeModel.norm_le _

noncomputable def ofLocalMajorSliceTest
    {L : Type} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L degree d}
    (packet : LocalMajorSliceTest D N cost budget) :
    UniversalLocalMajorSliceTest N degree cost budget where
  stride := packet.stride
  stride_pos := packet.stride_pos
  slice := packet.slice
  dense := packet.dense
  value := packet.test.eval
  native := ⟨{
    L := L
    dim := d
    model := D
    test := packet.test
    norm := by exact_mod_cast packet.norm
    complexity := packet.complexity
    eval := fun _ => rfl }⟩

@[simp] theorem ofLocalMajorSliceTest_weight
    {L : Type} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L degree d}
    (packet : LocalMajorSliceTest D N cost budget) (x : I → ℤ) :
    (ofLocalMajorSliceTest packet).weight x = packet.weight x := rfl

@[simp] theorem ofLocalMajorSliceTest_slice
    {L : Type} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L degree d}
    (packet : LocalMajorSliceTest D N cost budget) :
    (ofLocalMajorSliceTest packet).slice = packet.slice := rfl

noncomputable def default (N : I → ℕ) (hN : ∀ i, 0 < N i)
    (degree : ℕ) (cost budget : ℝ) (hcost : 0 ≤ cost) (hbudget : 2 ≤ budget) :
    UniversalLocalMajorSliceTest N degree cost budget := by
  let model : NativeSampleModel (fun _ : I => 1) degree budget id (fun _ => 1) :=
    NativeSampleModel.constOne hbudget
  exact ofLocalMajorSliceTest (LocalMajorSliceTest.full N hN cost budget hcost
    model.test (by exact_mod_cast model.norm) model.complexity)

theorem nonempty (N : I → ℕ) (hN : ∀ i, 0 < N i)
    (degree : ℕ) (cost budget : ℝ) (hcost : 0 ≤ cost) (hbudget : 2 ≤ budget) :
    Nonempty (UniversalLocalMajorSliceTest N degree cost budget) :=
  ⟨default N hN degree cost budget hcost hbudget⟩

end UniversalLocalMajorSliceTest
end Erdos3

end

section

namespace Erdos3.UniversalLocalMajorSliceTest
open scoped TensorProduct BigOperators

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

variable {I : Type} [Fintype I] [DecidableEq I]
    {N : I → ℕ} {degree : ℕ} {cost budget : ℝ}

def ofNative {value : (I → ℤ) → ℂ}
    (q : ℕ) (hq : 0 < q) (slice : ResidueBoxSlice N q)
    (dense : IsDenseCommonStrideBox N cost slice.integerPoints)
    (model : NativeSampleModel (fun _ : I => 1) degree budget id value) :
    UniversalLocalMajorSliceTest N degree cost budget where
  stride := q
  stride_pos := hq
  slice := slice
  dense := dense
  value := value
  native := ⟨model⟩

noncomputable def toLocalMajorSliceTest
    (packet : UniversalLocalMajorSliceTest N degree cost budget) :
    LocalMajorSliceTest packet.nativeModel.model N cost budget where
  stride := packet.stride
  stride_pos := packet.stride_pos
  slice := packet.slice
  dense := packet.dense
  test := packet.nativeModel.test
  norm := by exact_mod_cast packet.nativeModel.norm
  complexity := packet.nativeModel.complexity

@[simp] theorem toLocalMajorSliceTest_slice
    (packet : UniversalLocalMajorSliceTest N degree cost budget) :
    packet.toLocalMajorSliceTest.slice = packet.slice := rfl

@[simp] theorem toLocalMajorSliceTest_weight
    (packet : UniversalLocalMajorSliceTest N degree cost budget) (x : I → ℤ) :
    packet.toLocalMajorSliceTest.weight x = packet.weight x :=
  (packet.weight_eq_native_eval x).symm

variable (Long : I → Prop) [DecidablePred Long] {B : ℝ}

noncomputable def freezeShort
    (packet : UniversalLocalMajorSliceTest (fun i : {i // Long i} => N i.val)
      degree cost budget)
    (fixed : I → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i)
    (hB : 1 ≤ B) (hshort : ∀ i, ¬Long i → (N i : ℝ) ≤ B) :
    UniversalLocalMajorSliceTest N degree (max cost (Real.log B)) budget :=
  ofLocalMajorSliceTest (packet.toLocalMajorSliceTest.freezeShort Long fixed hfixed hB hshort)

@[simp] theorem freezeShort_stride
    (packet : UniversalLocalMajorSliceTest (fun i : {i // Long i} => N i.val)
      degree cost budget)
    (fixed : I → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i)
    (hB : 1 ≤ B) (hshort : ∀ i, ¬Long i → (N i : ℝ) ≤ B) :
    (packet.freezeShort Long fixed hfixed hB hshort).stride = packet.stride := rfl

@[simp] theorem freezeShort_slice
    (packet : UniversalLocalMajorSliceTest (fun i : {i // Long i} => N i.val)
      degree cost budget)
    (fixed : I → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i)
    (hB : 1 ≤ B) (hshort : ∀ i, ¬Long i → (N i : ℝ) ≤ B) :
    (packet.freezeShort Long fixed hfixed hB hshort).slice =
      packet.slice.freezeShort Long fixed hfixed := rfl

theorem freezeShort_weight
    (packet : UniversalLocalMajorSliceTest (fun i : {i // Long i} => N i.val)
      degree cost budget)
    (fixed : I → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i)
    (hB : 1 ≤ B) (hshort : ∀ i, ¬Long i → (N i : ℝ) ≤ B) (x : I → ℤ) :
    (packet.freezeShort Long fixed hfixed hB hshort).weight x =
      packet.weight (fun i => x i.val) := by
  rw [freezeShort, ofLocalMajorSliceTest_weight,
    LocalMajorSliceTest.freezeShort_weight, toLocalMajorSliceTest_weight]

theorem expect_freezeShort
    (packet : UniversalLocalMajorSliceTest (fun i : {i // Long i} => N i.val)
      degree cost budget)
    (fixed : I → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i)
    (hB : 1 ≤ B) (hshort : ∀ i, ¬Long i → (N i : ℝ) ≤ B)
    (signal : (I → ℤ) → ℂ) :
    (𝔼 x ∈ (packet.freezeShort Long fixed hfixed hB hshort).slice.integerPoints,
      signal x * (packet.freezeShort Long fixed hfixed hB hshort).weight x) =
      𝔼 x ∈ packet.slice.integerPoints,
        signal (frozenLongExtension Long fixed x) * packet.weight x := by
  change (𝔼 x ∈ (packet.slice.freezeShort Long fixed hfixed).integerPoints,
    signal x * (packet.freezeShort Long fixed hfixed hB hshort).weight x) = _
  rw [packet.slice.expect_freezeShort Long fixed hfixed
    (fun x => signal x * (packet.freezeShort Long fixed hfixed hB hshort).weight x)]
  apply Finset.expect_congr rfl
  intro x hx
  rw [freezeShort_weight]
  congr 2
  funext i
  exact frozenLongExtension_long Long fixed x i

theorem expect_subtypeSites_freezeShort
    (packet : UniversalLocalMajorSliceTest (fun i : {i // Long i} => N i.val)
      degree cost budget)
    (fixed : I → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i)
    (hB : 1 ≤ B) (hshort : ∀ i, ¬Long i → (N i : ℝ) ≤ B)
    (signal : (I → ℤ) → ℂ) :
    (𝔼 site ∈ (packet.freezeShort Long fixed hfixed hB hshort).slice.subtypeSites,
      signal site.val * (packet.freezeShort Long fixed hfixed hB hshort).weight site.val) =
      𝔼 x ∈ packet.slice.integerPoints,
        signal (frozenLongExtension Long fixed x) * packet.weight x := by
  rw [(packet.freezeShort Long fixed hfixed hB hshort).slice.expect_subtypeSites
    (fun x => signal x * (packet.freezeShort Long fixed hfixed hB hshort).weight x)]
  exact packet.expect_freezeShort Long fixed hfixed hB hshort signal

end Erdos3.UniversalLocalMajorSliceTest

end

section

namespace Erdos3
open scoped BigOperators TensorProduct Classical

variable {I : Type*} (keep : I → Prop)

noncomputable def frozenShortStarts (fixed : {i // ¬keep i} → ℤ) : I → ℕ :=
  fun i => if hi : keep i then 0 else (fixed ⟨i, hi⟩).toNat

theorem frozenShortStarts_inside {N : I → ℕ} (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < N i.val) :
    ∀ i, ¬keep i → frozenShortStarts keep fixed i < N i := by
  intro i hi
  simp only [frozenShortStarts, dite_eq_right hi]
  have h := hfixed ⟨i, hi⟩
  apply Int.ofNat_lt.mp
  simpa only [Int.toNat_of_nonneg h.1] using h.2

theorem frozenLongExtension_shortStarts (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i) (x : {i // keep i} → ℤ) :
    frozenLongExtension keep (frozenShortStarts keep fixed) x =
      finiteSplitPoint keep x fixed := by
  funext i
  by_cases hi : keep i
  · simp only [frozenLongExtension, finiteSplitPoint, dite_eq_left hi]
  · simp only [frozenLongExtension, frozenShortStarts, finiteSplitPoint, dite_eq_right hi]
    exact Int.toNat_of_nonneg (hfixed ⟨i, hi⟩)

variable [Fintype I] [DecidableEq I]

theorem exists_productive_frozen_localMajor_family
    {Ω X η : Type*} [Fintype Ω] {n : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight n)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight n)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight n)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight n)]
    (law : FiniteProbabilityWeights Ω) (good : η → Finset Ω)
    (N : I → ℕ) (hN : ∀ i, 0 < N i) (cost B δ : ℝ) (hcost : 0 ≤ cost)
    (hB : 1 ≤ B) (hshort : ∀ i, ¬keep i → (N i : ℝ) ≤ B)
    (physical : Ω → (I → ℤ) → X) (signal : η → X → ℂ)
    (hlocal : ∀ j z, z ∈ good j →
      ∃ fixed : {i // ¬keep i} → ℤ, (∀ i, 0 ≤ fixed i ∧ fixed i < N i.val) ∧
      ∃ A : LocalMajorSliceTest (OrdinaryPolynomialPhase.nilmanifold n)
        (fun i : {i // keep i} => N i.val) cost (OrdinaryPolynomialPhase.budget n),
        δ ≤ ‖𝔼 x ∈ A.slice.integerPoints,
          signal j (physical z (finiteSplitPoint keep x fixed)) * A.weight x‖) :
    ∃ chosen : Ω → Option η → LocalMajorSliceTest (OrdinaryPolynomialPhase.nilmanifold n)
        N (max cost (Real.log B)) (OrdinaryPolynomialPhase.budget n),
      ∀ j, δ * law.mass (good j) ≤ sampledSliceSeminorm law
        (fun z (x : integerBox N) => physical z x.val)
        (fun z a => (chosen z a).slice.subtypeSites)
        (fun z a (x : integerBox N) => (chosen z a).weight x.val) (signal j) := by
  obtain ⟨chosen, _, hchosen⟩ := exists_productive_localMajorSlice_coordinate_family
    (OrdinaryPolynomialPhase.nilmanifold n) law good N hN (max cost (Real.log B))
    (OrdinaryPolynomialPhase.budget n) δ
    (OrdinaryPolynomialPhase.zeroLocalMajorSlice N hN (max cost (Real.log B))
      (hcost.trans (le_max_left _ _))) physical signal (by
        intro j z hz
        obtain ⟨fixed, hfixed, A, hA⟩ := hlocal j z hz
        let starts := frozenShortStarts keep fixed
        have hstarts := frozenShortStarts_inside keep fixed hfixed
        refine ⟨A.freezeShort keep starts hstarts hB hshort, ?_⟩
        rw [A.expect_freezeShort keep starts hstarts hB hshort (fun x => signal j (physical z x))]
        simpa only [starts, frozenLongExtension_shortStarts keep fixed (fun i => (hfixed i).1)] using hA)
  exact ⟨chosen, hchosen⟩

end Erdos3

end

end OAI
