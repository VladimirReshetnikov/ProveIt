/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
import OAI.Combinatorics.Progressions.Estimates.FiniteFiberPMF
import OAI.Combinatorics.Progressions.Geometry.UniformDependentSubtypeCoordinates
import OAI.Combinatorics.Progressions.Geometry.UniformDependentSumCoordinates
import OAI.Combinatorics.Progressions.Probability.RelativeSliceFiniteLaw
import OAI.Combinatorics.Progressions.Probability.RelativeSliceParameterCellLaw

namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {keep : X → Prop} [DecidablePred keep] {N : X → ℕ} {q : ℕ}

def fiberParameterLength
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q) (i : X) : ℕ :=
  if hi : keep i then S.length ⟨i, hi⟩ else 1

def fiberParameterStart
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (fixed : {x // ¬keep x} → ℤ) (i : X) : ℤ :=
  if hi : keep i then (S.start ⟨i, hi⟩ : ℤ) else fixed ⟨i, hi⟩

def fiberParameterStride (i : X) : ℕ := if keep i then q else 0

omit [Fintype X] [DecidableEq X] in
theorem fiberParameterLength_pos
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (i : X) : 0 < S.fiberParameterLength i := by
  unfold fiberParameterLength
  split
  · exact hlen _
  · exact Nat.zero_lt_one

omit [Fintype X] [DecidableEq X] in
theorem fiberParameterLength_of_keep
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (i : X) (hi : keep i) : S.fiberParameterLength i = S.length ⟨i, hi⟩ := by
  simp only [fiberParameterLength, dite_eq_left hi]

omit [Fintype X] [DecidableEq X] in
theorem fiberParameterLength_of_not_keep
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (i : X) (hi : ¬keep i) : S.fiberParameterLength i = 1 := by
  simp only [fiberParameterLength, dite_eq_right hi]

def fiberFullParameters
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (u : ∀ k, Fin (S.length k)) (i : X) : Fin (S.fiberParameterLength i) :=
  ⟨if hi : keep i then (u ⟨i, hi⟩).val else 0, by
    by_cases hi : keep i
    · simpa only [fiberParameterLength, dite_eq_left hi] using (u ⟨i, hi⟩).isLt
    · simp only [fiberParameterLength, dite_eq_right hi, Nat.zero_lt_one]⟩

def fiberKeptParameters
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (v : ∀ i, Fin (S.fiberParameterLength i)) (k : {x // keep x}) : Fin (S.length k) :=
  ⟨(v k.val).val, by
    simpa only [fiberParameterLength, dite_eq_left k.property] using (v k.val).isLt⟩

def fiberFullParameterEquiv
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q) :
    (∀ k, Fin (S.length k)) ≃ (∀ i, Fin (S.fiberParameterLength i)) where
  toFun := S.fiberFullParameters
  invFun := S.fiberKeptParameters
  left_inv u := by
    funext k
    apply Fin.ext
    simp only [fiberKeptParameters, fiberFullParameters, dite_eq_left k.property]
  right_inv v := by
    funext i
    apply Fin.ext
    by_cases hi : keep i
    · simp only [fiberFullParameters, fiberKeptParameters, dite_eq_left hi]
    · have hv : (v i).val < 1 := by
        simpa only [fiberParameterLength, dite_eq_right hi] using (v i).isLt
      simp only [fiberFullParameters, dite_eq_right hi]
      omega

def fiberAffineIntegerPoint
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (fixed : {x // ¬keep x} → ℤ) (v : ∀ i, Fin (S.fiberParameterLength i)) : X → ℤ :=
  fun i => S.fiberParameterStart fixed i +
    (fiberParameterStride (keep := keep) (q := q) i : ℤ) * (v i).val

omit [Fintype X] [DecidableEq X] in
theorem fiberAffineIntegerPoint_eq
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (fixed : {x // ¬keep x} → ℤ) (v : ∀ i, Fin (S.fiberParameterLength i)) :
    S.fiberAffineIntegerPoint fixed v = S.fiberIntegerPoint fixed (S.fiberKeptParameters v) := by
  funext i
  by_cases hi : keep i
  · simp only [fiberAffineIntegerPoint, fiberParameterStart, fiberParameterStride,
      fiberIntegerPoint, finiteSplitPoint, dite_eq_left hi, ite_eq_left hi,
      point, fiberKeptParameters, Nat.cast_add, Nat.cast_mul]
  · simp only [fiberAffineIntegerPoint, fiberParameterStart, fiberParameterStride,
      fiberIntegerPoint, finiteSplitPoint, dite_eq_right hi, ite_eq_right hi,
      Nat.cast_zero, zero_mul, add_zero]

def fiberAffinePointInBox
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (v : ∀ i, Fin (S.fiberParameterLength i)) : integerBox N :=
  ⟨S.fiberAffineIntegerPoint fixed v, by
    rw [fiberAffineIntegerPoint_eq]
    exact S.fiberIntegerPoint_mem_integerBox fixed hfixed _⟩

theorem fiberSliceLaw_complexMean
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (test : integerBox N → ℂ) :
    (S.fiberSliceLaw hlen fixed hfixed).complexMean test =
      𝔼 u, test (S.fiberPointInBox fixed hfixed u) := by
  let : ∀ k, Nonempty (Fin (S.length k)) := fun k => ⟨⟨0, hlen k⟩⟩
  exact FiniteProbabilityWeights.uniform_finitePushforward_complexMean _ _

theorem fiberSliceLaw_affine_complexMean
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (test : integerBox N → ℂ) :
    (S.fiberSliceLaw hlen fixed hfixed).complexMean test =
      𝔼 v : (∀ i, Fin (S.fiberParameterLength i)), test (S.fiberAffinePointInBox fixed hfixed v) := by
  rw [fiberSliceLaw_complexMean]
  apply Fintype.expect_equiv S.fiberFullParameterEquiv
  intro u
  congr 1
  apply Subtype.ext
  change S.fiberIntegerPoint fixed u =
    S.fiberAffineIntegerPoint fixed (S.fiberFullParameterEquiv u)
  rw [fiberAffineIntegerPoint_eq]
  exact congrArg (S.fiberIntegerPoint fixed) (S.fiberFullParameterEquiv.left_inv u).symm

noncomputable def fiberAffineLaw
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ)) :
    FiniteProbabilityWeights (integerBox N) := by
  letI : ∀ i, Nonempty (Fin (S.fiberParameterLength i)) :=
    fun i => ⟨⟨0, S.fiberParameterLength_pos hlen i⟩⟩
  exact (FiniteProbabilityWeights.uniform (∀ i, Fin (S.fiberParameterLength i))).finitePushforward
    (S.fiberAffinePointInBox fixed hfixed)

theorem fiberAffineLaw_complexMean
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (test : integerBox N → ℂ) :
    (S.fiberAffineLaw hlen fixed hfixed).complexMean test =
      𝔼 v : (∀ i, Fin (S.fiberParameterLength i)), test (S.fiberAffinePointInBox fixed hfixed v) := by
  let : ∀ i, Nonempty (Fin (S.fiberParameterLength i)) :=
    fun i => ⟨⟨0, S.fiberParameterLength_pos hlen i⟩⟩
  exact FiniteProbabilityWeights.uniform_finitePushforward_complexMean _ _

private theorem weights_eq_of_complexMean {Ω : Type*} [Fintype Ω]
    (p r : FiniteProbabilityWeights Ω)
    (hmean : ∀ test, p.complexMean test = r.complexMean test) : p = r := by
  classical
  have hw (x : Ω) : p.weight x = r.weight x := by
    apply Complex.ofReal_injective
    have h := hmean (fun y => if y = x then 1 else 0)
    simpa only [FiniteProbabilityWeights.complexMean, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h
  cases p
  cases r
  congr
  exact funext hw

theorem fiberSliceLaw_eq_affineLaw
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ)) :
    S.fiberSliceLaw hlen fixed hfixed = S.fiberAffineLaw hlen fixed hfixed := by
  apply weights_eq_of_complexMean
  intro test
  rw [fiberSliceLaw_affine_complexMean, fiberAffineLaw_complexMean]

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (start : PrincipalTupleIndex B h → ℤ)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < L j)

def principalAffineIntervalPoint (t : ∀ j, Fin (H j)) : PrincipalIntegerTuples B h Empty L :=
  fun j _ => ⟨start j + (step j : ℤ) * (t j).val, Finset.mem_Ico.mpr
    ⟨(neg_nonpos.mpr (Int.natCast_nonneg _)).trans (hinside j (t j)).1, (hinside j (t j)).2⟩⟩

omit [Fintype D] [DecidableEq D] [∀ index, Fintype (B index)]
  [∀ index, DecidableEq (B index)] in
@[simp] theorem principalAffineIntervalPoint_value (t : ∀ j, Fin (H j))
    (j : PrincipalTupleIndex B h) (a : Option Empty) :
    (principalAffineIntervalPoint B h L H step start hinside t j a : ℤ) =
      start j + (step j : ℤ) * (t j).val := rfl

omit [Fintype D] [DecidableEq D] [∀ index, Fintype (B index)]
  [∀ index, DecidableEq (B index)] in
theorem principalAffineIntervalPoint_cube (t : ∀ j, Fin (H j))
    (j : PrincipalTupleIndex B h) :
    IntegerScalarCube (L j)
      (fun a => (principalAffineIntervalPoint B h L H step start hinside t j a : ℤ)) := by
  intro row
  have he : row = ∅ := Subsingleton.elim _ _
  simpa only [he, integerScalarCubeValue, Finset.sum_empty, add_zero,
    principalAffineIntervalPoint_value] using hinside j (t j)

variable (hH : ∀ j, 0 < H j)

noncomputable def principalAffineIntervalLaw : FiniteProbabilityWeights (PrincipalIntegerTuples B h Empty L) := by
  letI : ∀ j, Nonempty (Fin (H j)) := fun j => ⟨⟨0, hH j⟩⟩
  exact (FiniteProbabilityWeights.uniform (∀ j, Fin (H j))).finitePushforward
    (principalAffineIntervalPoint B h L H step start hinside)

theorem principalAffineIntervalLaw_mean (f : PrincipalIntegerTuples B h Empty L → ℝ) :
    (principalAffineIntervalLaw B h L H step start hinside hH).mean f =
      𝔼 t : (∀ j, Fin (H j)), f (principalAffineIntervalPoint B h L H step start hinside t) := by
  let : ∀ j, Nonempty (Fin (H j)) := fun j => ⟨⟨0, hH j⟩⟩
  exact FiniteProbabilityWeights.uniform_finitePushforward_mean _ _

theorem principalAffineIntervalLaw_complexMean (f : PrincipalIntegerTuples B h Empty L → ℂ) :
    (principalAffineIntervalLaw B h L H step start hinside hH).complexMean f =
      𝔼 t : (∀ j, Fin (H j)), f (principalAffineIntervalPoint B h L H step start hinside t) := by
  let : ∀ j, Nonempty (Fin (H j)) := fun j => ⟨⟨0, hH j⟩⟩
  exact FiniteProbabilityWeights.uniform_finitePushforward_complexMean _ _

theorem principalAffineIntervalLaw_support
    (y : PrincipalIntegerTuples B h Empty L)
    (hy : (principalAffineIntervalLaw B h L H step start hinside hH).weight y ≠ 0) :
    ∃ t : ∀ j, Fin (H j), principalAffineIntervalPoint B h L H step start hinside t = y := by
  let : ∀ j, Nonempty (Fin (H j)) := fun j => ⟨⟨0, hH j⟩⟩
  by_contra hn
  apply hy
  unfold principalAffineIntervalLaw FiniteProbabilityWeights.finitePushforward
  apply Finset.sum_eq_zero
  intro t _
  exact ite_eq_right (fun ht => hn ⟨t, ht⟩)

theorem principalAffineIntervalLaw_cube_support
    (y : PrincipalIntegerTuples B h Empty L)
    (hy : (principalAffineIntervalLaw B h L H step start hinside hH).weight y ≠ 0)
    (j : PrincipalTupleIndex B h) :
    IntegerScalarCube (L j) (fun a => (y j a : ℤ)) := by
  obtain ⟨t, rfl⟩ := principalAffineIntervalLaw_support B h L H step start hinside hH y hy
  exact principalAffineIntervalPoint_cube B h L H step start hinside t j

theorem principalAffineIntervalLaw_coordinate_support
    (y : PrincipalIntegerTuples B h Empty L)
    (hy : (principalAffineIntervalLaw B h L H step start hinside hH).weight y ≠ 0)
    (j : PrincipalTupleIndex B h) (a : Option Empty) :
    (y j a : ℤ) ∈ integerProgressionSupport (start j) (step j : ℤ) (H j) := by
  obtain ⟨t, rfl⟩ := principalAffineIntervalLaw_support B h L H step start hinside hH y hy
  rw [principalAffineIntervalPoint_value, integerProgressionSupport, mem_translateSupport]
  apply Finset.mem_image.mpr
  refine ⟨((t j).val : ℤ), Finset.mem_Ico.mpr ⟨Int.natCast_nonneg _, by exact_mod_cast (t j).isLt⟩, ?_⟩
  change (step j : ℤ) * (t j).val = _
  ring

noncomputable def principalAffineIntervalAxisLaw (P : D → Prop) :
    FiniteProbabilityWeights (PrincipalAxisTuples (α := Empty) P L) :=
  (principalAffineIntervalLaw B h L H step start hinside hH).finitePushforward
    (principalAxisRestrict P)

theorem principalAffineIntervalAxisLaw_complexMean (P : D → Prop)
    (f : PrincipalAxisTuples (α := Empty) P L → ℂ) :
    (principalAffineIntervalAxisLaw B h L H step start hinside hH P).complexMean f =
      𝔼 t : (∀ j, Fin (H j)),
        f (principalAxisRestrict P (principalAffineIntervalPoint B h L H step start hinside t)) := by
  rw [principalAffineIntervalAxisLaw, FiniteProbabilityWeights.complexMean_finitePushforward,
    principalAffineIntervalLaw_complexMean]

theorem principalAffineIntervalAxisLaw_mass_one (P : D → Prop) :
    ∑ u, (principalAffineIntervalAxisLaw B h L H step start hinside hH P).weight u = 1 :=
  (principalAffineIntervalAxisLaw B h L H step start hinside hH P).total

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {keep : X → Prop} [DecidablePred keep] {N : X → ℕ} {q : ℕ}

theorem fiberParameter_inside
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (i : X) (t : Fin (S.fiberParameterLength i)) :
    0 ≤ S.fiberParameterStart fixed i +
      (fiberParameterStride (keep := keep) (q := q) i : ℤ) * t.val ∧
      S.fiberParameterStart fixed i +
        (fiberParameterStride (keep := keep) (q := q) i : ℤ) * t.val < N i := by
  let zero : ∀ j, Fin (S.fiberParameterLength j) :=
    fun j => ⟨0, S.fiberParameterLength_pos hlen j⟩
  let v := Function.update zero i t
  have hv := (mem_integerBox N _).mp (S.fiberAffinePointInBox fixed hfixed v).property i
  simpa only [fiberAffinePointInBox, fiberAffineIntegerPoint, v, Function.update_self] using hv

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {G P : Type*} [Fintype G] [Fintype P] [DecidableEq G] [DecidableEq P]
variable {keep : G ⊕ P → Prop} [DecidablePred keep] {N : G ⊕ P → ℕ} {q : ℕ}

theorem fiberSliceLaw_affine_sum_complexMean
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (test : integerBox N → ℂ) :
    (S.fiberSliceLaw hlen fixed hfixed).complexMean test =
      𝔼 g : (∀ i, Fin (S.fiberParameterLength (Sum.inl i))),
        𝔼 p : (∀ j, Fin (S.fiberParameterLength (Sum.inr j))),
          test (S.fiberAffinePointInBox fixed hfixed (Sum.rec g p)) := by
  rw [fiberSliceLaw_affine_complexMean]
  exact uniformDependentFin_expect S.fiberParameterLength _

theorem fiberSliceLaw_affine_sum_value_complexMean
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (test : (G ⊕ P → ℤ) → ℂ) :
    (S.fiberSliceLaw hlen fixed hfixed).complexMean (fun x => test x.val) =
      𝔼 g : (∀ i, Fin (S.fiberParameterLength (Sum.inl i))),
        𝔼 p : (∀ j, Fin (S.fiberParameterLength (Sum.inr j))),
          test (Sum.elim
            (fun i => S.fiberParameterStart fixed (Sum.inl i) +
              (fiberParameterStride (keep := keep) (q := q) (Sum.inl i) : ℤ) * (g i).val)
            (fun j => S.fiberParameterStart fixed (Sum.inr j) +
              (fiberParameterStride (keep := keep) (q := q) (Sum.inr j) : ℤ) * (p j).val)) := by
  rw [fiberSliceLaw_affine_sum_complexMean]
  apply Finset.expect_congr rfl
  intro g _
  apply Finset.expect_congr rfl
  intro p _
  congr 1
  funext k
  cases k <;> rfl

theorem fiberSliceLaw_kernel_principal_complexMean
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (hkernel : ∀ i, keep (Sum.inl i)) (test : (G ⊕ P → ℤ) → ℂ) :
    (S.fiberSliceLaw hlen fixed hfixed).complexMean (fun x => test x.val) =
      𝔼 g : (∀ i, Fin (S.fiberParameterLength (Sum.inl i))),
        𝔼 p : (∀ j, Fin (S.fiberParameterLength (Sum.inr j))),
          test (Sum.elim
            (fun i => (S.start ⟨Sum.inl i, hkernel i⟩ : ℤ) + (q : ℤ) * (g i).val)
            (fun j => S.fiberParameterStart fixed (Sum.inr j) +
              (fiberParameterStride (keep := keep) (q := q) (Sum.inr j) : ℤ) * (p j).val)) := by
  rw [fiberSliceLaw_affine_sum_value_complexMean]
  apply Finset.expect_congr rfl
  intro g _
  apply Finset.expect_congr rfl
  intro p _
  congr 2
  funext i
  simp only [fiberParameterStart, fiberParameterStride, dite_eq_left (hkernel i),
    ite_eq_left (hkernel i)]

def fiberKernelParameterEquiv
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hkernel : ∀ i, keep (Sum.inl i)) :
    (∀ i, Fin (S.fiberParameterLength (Sum.inl i))) ≃
      (∀ i, Fin (S.length ⟨Sum.inl i, hkernel i⟩)) where
  toFun g i := ⟨(g i).val, by
    simpa only [fiberParameterLength, dite_eq_left (hkernel i)] using (g i).isLt⟩
  invFun g i := ⟨(g i).val, by
    simpa only [fiberParameterLength, dite_eq_left (hkernel i)] using (g i).isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem fiberSliceLaw_kernel_principal_intervals_complexMean
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (hkernel : ∀ i, keep (Sum.inl i)) (test : (G ⊕ P → ℤ) → ℂ) :
    (S.fiberSliceLaw hlen fixed hfixed).complexMean (fun x => test x.val) =
      𝔼 g : (∀ i, Fin (S.length ⟨Sum.inl i, hkernel i⟩)),
        𝔼 p : (∀ j, Fin (S.fiberParameterLength (Sum.inr j))),
          test (Sum.elim
            (fun i => (S.start ⟨Sum.inl i, hkernel i⟩ : ℤ) + (q : ℤ) * (g i).val)
            (fun j => S.fiberParameterStart fixed (Sum.inr j) +
              (fiberParameterStride (keep := keep) (q := q) (Sum.inr j) : ℤ) * (p j).val)) := by
  rw [fiberSliceLaw_kernel_principal_complexMean S hlen fixed hfixed hkernel]
  apply Fintype.expect_equiv (S.fiberKernelParameterEquiv hkernel)
  intro g
  rfl

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ)

def principalZeroTupleFromIntegerBox (z : integerBox L) :
    PrincipalIntegerTuples B h Empty L :=
  fun j _ => ⟨z.val j, Finset.mem_Ico.mpr
    ⟨(neg_nonpos.mpr (Int.natCast_nonneg _)).trans ((mem_integerBox L z.val).mp z.property j).1,
      ((mem_integerBox L z.val).mp z.property j).2⟩⟩

@[simp] theorem principalZeroTupleFromIntegerBox_value (z : integerBox L)
    (j : PrincipalTupleIndex B h) (a : Option Empty) :
    (principalZeroTupleFromIntegerBox B h L z j a : ℤ) = z.val j := rfl

variable {keep : PrincipalTupleIndex B h → Prop} [DecidablePred keep] {q : ℕ}
variable (S : ResidueBoxSlice (fun j : {j // keep j} => L j.val) q)
variable (hlen : ∀ j, 0 < S.length j)
variable (fixed : {j // ¬keep j} → ℤ)
variable (hfixed : ∀ j, 0 ≤ fixed j ∧ fixed j < (L j.val : ℤ))

noncomputable def principalFiberSliceLaw : FiniteProbabilityWeights (PrincipalIntegerTuples B h Empty L) :=
  (S.fiberSliceLaw hlen fixed hfixed).finitePushforward (principalZeroTupleFromIntegerBox B h L)

theorem principalFiberSliceLaw_complexMean (f : PrincipalIntegerTuples B h Empty L → ℂ) :
    (principalFiberSliceLaw B h L S hlen fixed hfixed).complexMean f =
      𝔼 t : (∀ j, Fin (S.fiberParameterLength j)),
        f (principalZeroTupleFromIntegerBox B h L (S.fiberAffinePointInBox fixed hfixed t)) := by
  rw [principalFiberSliceLaw, FiniteProbabilityWeights.complexMean_finitePushforward,
    ResidueBoxSlice.fiberSliceLaw_affine_complexMean]

theorem principalZeroTupleFromIntegerBox_affinePoint
    (hinside : ∀ j (t : Fin (S.fiberParameterLength j)),
      0 ≤ S.fiberParameterStart fixed j +
          (ResidueBoxSlice.fiberParameterStride (keep := keep) (q := q) j : ℤ) * t.val ∧
        S.fiberParameterStart fixed j +
          (ResidueBoxSlice.fiberParameterStride (keep := keep) (q := q) j : ℤ) * t.val < L j)
    (t : ∀ j, Fin (S.fiberParameterLength j)) :
    principalZeroTupleFromIntegerBox B h L (S.fiberAffinePointInBox fixed hfixed t) =
      principalAffineIntervalPoint B h L S.fiberParameterLength
        (ResidueBoxSlice.fiberParameterStride (keep := keep) (q := q))
        (S.fiberParameterStart fixed) hinside t := by
  funext j a
  apply Subtype.ext
  rfl

theorem principalFiberSliceLaw_eq_affine :
    principalFiberSliceLaw B h L S hlen fixed hfixed =
      principalAffineIntervalLaw B h L S.fiberParameterLength
        (ResidueBoxSlice.fiberParameterStride (keep := keep) (q := q))
        (S.fiberParameterStart fixed) (S.fiberParameter_inside hlen fixed hfixed) (S.fiberParameterLength_pos hlen) := by
  have hm (f : PrincipalIntegerTuples B h Empty L → ℂ) :
      (principalFiberSliceLaw B h L S hlen fixed hfixed).complexMean f =
        (principalAffineIntervalLaw B h L S.fiberParameterLength
          (ResidueBoxSlice.fiberParameterStride (keep := keep) (q := q))
          (S.fiberParameterStart fixed) (S.fiberParameter_inside hlen fixed hfixed) (S.fiberParameterLength_pos hlen)).complexMean f := by
    rw [principalFiberSliceLaw_complexMean, principalAffineIntervalLaw_complexMean]
    apply Finset.expect_congr rfl
    intro t _
    rw [principalZeroTupleFromIntegerBox_affinePoint B h L S fixed hfixed (S.fiberParameter_inside hlen fixed hfixed)]
  have hw (z : PrincipalIntegerTuples B h Empty L) :=
    congrArg Complex.re (hm (fun y => if y = z then 1 else 0))
  simp only [FiniteProbabilityWeights.complexMean_re, apply_ite, Complex.one_re,
    Complex.zero_re, FiniteProbabilityWeights.mean, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hw
  cases hp : principalFiberSliceLaw B h L S hlen fixed hfixed
  cases hr : principalAffineIntervalLaw B h L S.fiberParameterLength
    (ResidueBoxSlice.fiberParameterStride (keep := keep) (q := q))
    (S.fiberParameterStart fixed) (S.fiberParameter_inside hlen fixed hfixed)
    (S.fiberParameterLength_pos hlen)
  simp only [hp, hr] at hw
  congr
  exact funext hw

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {G P : Type*} [Fintype G] [Fintype P] [DecidableEq G] [DecidableEq P]
variable {keep : G ⊕ P → Prop} [DecidablePred keep] {N : G ⊕ P → ℕ} {q : ℕ}

def fiberKernelActiveShortPoint
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (fixed : {x // ¬keep x} → ℤ) (hkernel : ∀ i, keep (Sum.inl i))
    (active : P → Prop) [DecidablePred active]
    (g : ∀ i, Fin (S.length ⟨Sum.inl i, hkernel i⟩))
    (a : ∀ j : {p // active p}, Fin (S.fiberParameterLength (Sum.inr j.val)))
    (s : ∀ j : {p // ¬active p}, Fin (S.fiberParameterLength (Sum.inr j.val))) :
    G ⊕ P → ℤ :=
  Sum.elim
    (fun i => (S.start ⟨Sum.inl i, hkernel i⟩ : ℤ) + (q : ℤ) * (g i).val)
    (finiteSplitPoint active
      (fun j => S.fiberParameterStart fixed (Sum.inr j.val) +
        (fiberParameterStride (keep := keep) (q := q) (Sum.inr j.val) : ℤ) * (a j).val)
      (fun j => S.fiberParameterStart fixed (Sum.inr j.val) +
        (fiberParameterStride (keep := keep) (q := q) (Sum.inr j.val) : ℤ) * (s j).val))

theorem fiberSliceLaw_kernel_active_short_complexMean
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (hkernel : ∀ i, keep (Sum.inl i))
    (active : P → Prop) [DecidablePred active] (test : (G ⊕ P → ℤ) → ℂ) :
    (S.fiberSliceLaw hlen fixed hfixed).complexMean (fun x => test x.val) =
      𝔼 g : (∀ i, Fin (S.length ⟨Sum.inl i, hkernel i⟩)),
        𝔼 a : (∀ j : {p // active p}, Fin (S.fiberParameterLength (Sum.inr j.val))),
          𝔼 s : (∀ j : {p // ¬active p}, Fin (S.fiberParameterLength (Sum.inr j.val))),
            test (S.fiberKernelActiveShortPoint fixed hkernel active g a s) := by
  rw [fiberSliceLaw_kernel_principal_intervals_complexMean S hlen fixed hfixed hkernel]
  apply Finset.expect_congr rfl
  intro g _
  rw [uniformDependentFinSubtype_expect active]
  apply Finset.expect_congr rfl
  intro a _
  apply Finset.expect_congr rfl
  intro s _
  congr 1
  funext k
  cases k with
  | inl i => rfl
  | inr j =>
    by_cases hj : active j <;>
      simp only [fiberKernelActiveShortPoint, Sum.elim_inr, finiteSplitPoint,
        Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_symm_mk, hj, dite_true, dite_false]

theorem fiberSliceLaw_short_kernel_active_complexMean
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (hkernel : ∀ i, keep (Sum.inl i))
    (active : P → Prop) [DecidablePred active] (test : (G ⊕ P → ℤ) → ℂ) :
    (S.fiberSliceLaw hlen fixed hfixed).complexMean (fun x => test x.val) =
      𝔼 s : (∀ j : {p // ¬active p}, Fin (S.fiberParameterLength (Sum.inr j.val))),
        𝔼 g : (∀ i, Fin (S.length ⟨Sum.inl i, hkernel i⟩)),
          𝔼 a : (∀ j : {p // active p}, Fin (S.fiberParameterLength (Sum.inr j.val))),
            test (S.fiberKernelActiveShortPoint fixed hkernel active g a s) := by
  rw [fiberSliceLaw_kernel_active_short_complexMean S hlen fixed hfixed hkernel active]
  calc
    _ = 𝔼 g : (∀ i, Fin (S.length ⟨Sum.inl i, hkernel i⟩)),
        𝔼 s : (∀ j : {p // ¬active p}, Fin (S.fiberParameterLength (Sum.inr j.val))),
          𝔼 a : (∀ j : {p // active p}, Fin (S.fiberParameterLength (Sum.inr j.val))),
            test (S.fiberKernelActiveShortPoint fixed hkernel active g a s) := by
      apply Finset.expect_congr rfl
      intro g _
      exact Finset.expect_comm _ _ _
    _ = _ := Finset.expect_comm _ _ _

end Erdos3.ResidueBoxSlice

end

end OAI
