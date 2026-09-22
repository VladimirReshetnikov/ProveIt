import Mathlib.Order.WellQuasiOrder
import Mathlib.Order.Antichain
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Algebra.Order.Pi
import Mathlib.Algebra.Order.Sub.Prod
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.RingTheory.HahnSeries.Lex
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Finite semigroups of Wick diagrams and valuation Cauchy–Schwarz

This file proves `lem:dickson`, `prop:hilbert`, `prop:module` and `lem:valCS` in
`docs/surcomplex/wick-summability-certificates/article.tex`.

Dickson's lemma is Mathlib's well-quasi-order instance on finite products of
`ℕ`: minimal elements of any subset of `ℕ^ι` form a finite antichain, and every
element lies above a minimal one. For the nonnegative integer kernel `S` of any
additive map to an abelian group, which covers the homogeneous count equation
`Am = Dk`, the coordinatewise minimal nonzero elements form a finite Hilbert
basis. They are exactly the indecomposable nonzero elements, and they generate
`S` as an additive monoid. Every inhomogeneous fiber is the union of translates
of `S` by its finitely many minimal elements.

For a symmetric positive-definite matrix over a linearly ordered field, every
diagonal entry is positive and every off-diagonal square is smaller than the
product of the two diagonal entries. Over the lexicographically ordered Hahn
field this gives the valuation inequality `2 v(C_ij) ≥ v(C_ii) + v(C_jj)`, with
no divisibility assumption on the exponent group.
-/

namespace Surreal.Wick

section Dickson

variable {ι : Type*} [Finite ι]

/-- `lem:dickson`: every subset of `ℕ^ι` has finitely many minimal elements. -/
theorem finite_setOf_minimal (T : Set (ι → ℕ)) : {x | Minimal (· ∈ T) x}.Finite :=
  WellQuasiOrderedLE.finite_of_isAntichain (setOf_minimal_antichain _)

/-- `lem:dickson`: every element of a subset of `ℕ^ι` lies above a minimal one. -/
theorem exists_minimal_le {T : Set (ι → ℕ)} {x : ι → ℕ} (hx : x ∈ T) :
    ∃ y ≤ x, Minimal (· ∈ T) y :=
  exists_minimal_le_of_wellFoundedLT _ x hx

end Dickson

section Hilbert

variable {ι G : Type*} [Finite ι] [AddCommGroup G] (f : (ι → ℕ) →+ G)

omit [Finite ι] in
/-- The difference of comparable kernel elements lies in the kernel; this is why
the homogeneous equation `Am = Dk` makes minimality and indecomposability agree. -/
theorem map_tsub_eq_zero {x y : ι → ℕ} (hx : f x = 0) (hy : f y = 0) (hyx : y ≤ x) :
    f (x - y) = 0 := by
  have h := congrArg f (tsub_add_cancel_of_le hyx)
  rwa [map_add, hx, hy, add_zero] at h

/-- The finite Hilbert basis `𝓗`: minimal nonzero elements of the kernel `S`. -/
def hilbertBasis : Set (ι → ℕ) :=
  {x | Minimal (fun y => f y = 0 ∧ y ≠ 0) x}

/-- `prop:hilbert`: the Hilbert basis is finite. -/
theorem finite_hilbertBasis : (hilbertBasis f).Finite :=
  finite_setOf_minimal {y | f y = 0 ∧ y ≠ 0}

omit [Finite ι] in
/-- `prop:hilbert`: the Hilbert basis consists exactly of the nonzero kernel
elements that are not a sum of two nonzero kernel elements. -/
theorem mem_hilbertBasis_iff {h : ι → ℕ} :
    h ∈ hilbertBasis f ↔ f h = 0 ∧ h ≠ 0 ∧
      ∀ a b, f a = 0 → f b = 0 → a ≠ 0 → b ≠ 0 → a + b ≠ h := by
  constructor
  · rintro ⟨⟨hf, h0⟩, hmin⟩
    refine ⟨hf, h0, fun a b ha hb ha0 hb0 hab => hb0 ?_⟩
    have hle : a ≤ h := hab ▸ le_self_add
    have hge : h ≤ a := hmin ⟨ha, ha0⟩ hle
    have : a + b = a + 0 := by rw [add_zero, hab]; exact le_antisymm hge hle
    exact add_left_cancel this
  · rintro ⟨hf, h0, hind⟩
    refine ⟨⟨hf, h0⟩, fun y ⟨hy, hy0⟩ hyh => ?_⟩
    by_contra hne
    have hyh' : y ≠ h := fun e => hne (e ▸ le_rfl)
    have hd0 : h - y ≠ 0 := by
      intro hd
      exact hyh' (le_antisymm hyh (tsub_eq_zero_iff_le.mp hd))
    exact hind y (h - y) hy (map_tsub_eq_zero f hf hy hyh) hy0 hd0 (add_tsub_cancel_of_le hyh)

/-- `prop:hilbert`: every kernel element is a nonnegative integer combination of
Hilbert basis elements. -/
theorem mem_closure_hilbertBasis {x : ι → ℕ} (hx : f x = 0) :
    x ∈ AddSubmonoid.closure (hilbertBasis f) := by
  induction x using WellFoundedLT.induction with
  | _ x ih =>
    by_cases h0 : x = 0
    · rw [h0]
      exact zero_mem _
    obtain ⟨h, hhx, hmin⟩ := exists_minimal_le (T := {y | f y = 0 ∧ y ≠ 0}) ⟨hx, h0⟩
    have hh : h ∈ hilbertBasis f := hmin
    have hsub : f (x - h) = 0 := map_tsub_eq_zero f hx hmin.prop.1 hhx
    have hlt : x - h < x := by
      refine lt_of_le_of_ne tsub_le_self fun e => hmin.prop.2 ?_
      have := tsub_add_cancel_of_le hhx
      rw [e] at this
      simpa using this
    rw [← add_tsub_cancel_of_le hhx]
    exact add_mem (AddSubmonoid.subset_closure hh) (ih _ hlt hsub)

/-- `prop:module`: every fiber of the count map is the union of the translates of
the kernel by the finitely many minimal elements of the fiber. -/
theorem fiber_eq_biUnion (β : G) :
    {x | f x = β} = ⋃ q ∈ {q | Minimal (fun y => f y = β) q}, (q + ·) '' {s | f s = 0} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, exists_prop]
  constructor
  · intro hx
    obtain ⟨q, hqx, hq⟩ := exists_minimal_le (T := {y | f y = β}) hx
    refine ⟨q, hq, x - q, ?_, add_tsub_cancel_of_le hqx⟩
    have h := congrArg f (tsub_add_cancel_of_le hqx)
    rw [map_add, hx] at h
    have hq' : f q = β := hq.prop
    rw [hq'] at h
    simpa using h
  · rintro ⟨q, hq, s, hs, rfl⟩
    rw [map_add, hs, add_zero]
    exact hq.prop

/-- `prop:module`: each fiber has finitely many minimal elements. -/
theorem finite_minimal_fiber (β : G) : {q | Minimal (fun y => f y = β) q}.Finite :=
  finite_setOf_minimal {y | f y = β}

end Hilbert

section Minor

variable {n F : Type*} [Fintype n] [DecidableEq n] [Field F] [LinearOrder F]
  [IsStrictOrderedRing F]

open Matrix

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- The quadratic form of a symmetric matrix on a vector supported on two indices. -/
theorem quadForm_two {C : Matrix n n F} (hC : C.IsSymm) (i j : n) (a b : F) :
    (a • Pi.single i 1 + b • Pi.single j 1) ⬝ᵥ (C *ᵥ (a • Pi.single i 1 + b • Pi.single j 1)) =
      a ^ 2 * C i i + 2 * a * b * C i j + b ^ 2 * C j j := by
  have hji : C j i = C i j := by
    have := congrFun (congrFun hC i) j
    simpa [Matrix.transpose_apply] using this
  simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply,
    smul_eq_mul]
  rw [hji]
  ring

/-- `lem:valCS`, order part: a symmetric positive-definite matrix has positive
diagonal and strictly dominated off-diagonal squares. -/
theorem diag_pos_and_sq_lt {C : Matrix n n F} (hC : C.IsSymm)
    (hpd : ∀ x : n → F, x ≠ 0 → 0 < x ⬝ᵥ (C *ᵥ x)) {i j : n} (hij : i ≠ j) :
    0 < C i i ∧ C i j ^ 2 < C i i * C j j := by
  have hdiag : ∀ k : n, 0 < C k k := by
    intro k
    have h := hpd (Pi.single k 1) (by simp)
    simpa [mulVec_single_one, single_dotProduct, Matrix.transpose_apply] using h
  refine ⟨hdiag i, ?_⟩
  have hx : (C j j • Pi.single i 1 + (-C i j) • Pi.single j 1 : n → F) ≠ 0 := by
    intro h
    have := congrFun h i
    simp [Pi.single_apply, if_neg hij] at this
    exact (hdiag j).ne' this
  have h := hpd _ hx
  rw [quadForm_two hC i j] at h
  have hj := hdiag j
  nlinarith

end Minor

section Valuation

variable {Γ R : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]

open HahnSeries

/-- `lem:valCS`, valuation part: if `0 < a`, `0 < b` and `c² < ab` in the
lexicographic Hahn order, then `v(a) + v(b) ≤ 2 v(c)`. -/
theorem orderTop_add_le_of_sq_lt {a b c : Lex R⟦Γ⟧} (ha : 0 < a) (hb : 0 < b)
    (hc : c ^ 2 < a * b) :
    (ofLex a).orderTop + (ofLex b).orderTop ≤ (ofLex c).orderTop + (ofLex c).orderTop := by
  by_contra h
  push Not at h
  have hlt : (ofLex (c * c)).orderTop < (ofLex (a * b)).orderTop := by
    simpa [ofLex_mul, orderTop_mul] using h
  have habs := abs_lt_abs_of_orderTop_ofLex hlt
  rw [abs_of_pos (mul_pos ha hb), abs_of_nonneg (mul_self_nonneg c)] at habs
  rw [sq] at hc
  exact lt_asymm hc habs

open Matrix in
/-- `lem:valCS`: for a symmetric positive-definite matrix over the real-type Hahn
field `R((t^Γ))`, every diagonal entry is positive and every off-diagonal entry
satisfies `2 v(C_ij) ≥ v(C_ii) + v(C_jj)`. -/
theorem valuation_cauchySchwarz {Γ' : Type*} [AddCommGroup Γ'] [LinearOrder Γ']
    [IsOrderedAddMonoid Γ'] {n : Type*} [Fintype n] [DecidableEq n]
    {C : Matrix n n (Lex R⟦Γ'⟧)} (hC : C.IsSymm)
    (hpd : ∀ x : n → Lex R⟦Γ'⟧, x ≠ 0 → 0 < x ⬝ᵥ (C *ᵥ x)) {i j : n} (hij : i ≠ j) :
    0 < C i i ∧ (ofLex (C i i)).orderTop + (ofLex (C j j)).orderTop ≤
      (ofLex (C i j)).orderTop + (ofLex (C i j)).orderTop := by
  obtain ⟨hi, hsq⟩ := diag_pos_and_sq_lt hC hpd hij
  obtain ⟨hj, -⟩ := diag_pos_and_sq_lt hC hpd (Ne.symm hij)
  exact ⟨hi, orderTop_add_le_of_sq_lt hi hj hsq⟩

end Valuation

end Surreal.Wick
