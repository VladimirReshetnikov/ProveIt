import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Lattice

/-!
# Strict rational alternative over an ordered `ℚ`-vector space

This file proves `wick:thm:alternative` and `wick:eq:alternative` of
`docs/surcomplex/wick-summability-certificates/article.tex`, and `markov:lem:separation` of
`docs/surreal/markov-generators-at-every-scale/article.tex`.

Let `Γ` be a nonzero ordered `ℚ`-vector space, that is, a nonzero divisible ordered abelian group
(the standing hypothesis `Γ ≠ {0}` of Section 2 of the Wick report). Let `M` be a rational matrix
with finite row type `ι` and finite column type `κ`, and let `b ∈ Γ^ι`. The source takes
`ι = Fin N` and `κ = Fin d`. `strict_alternative` states that exactly one of the following holds:

* `Feasible M b`: some `p ∈ Γ^κ` has `(M p + b)_i > 0` for every row `i`;
* `Obstruction M b`: some nonzero `r ∈ ℚ_{≥0}^ι` has `rᵀ M = 0` and `r ⬝ b ≤ 0`.

`feasible_iff_forall_pos` is the reformulation `wick:eq:alternative`. The proof is the source's
Fourier–Motzkin elimination. One step eliminates coordinate `0`. It keeps the rows whose
coefficient there is zero. For every pair of a row with positive and a row with negative
coefficient, it adds a positive combination of the two that cancels coordinate `0`
(`elimCoeff`). The multipliers are carried along, so an obstruction of the eliminated system
lifts to one of the original system (`obstruction_of_elim`). A solution of the eliminated system
extends by choosing the eliminated coordinate between the finitely many lower and upper bounds
(`feasible_of_elim`). This uses a midpoint (divisibility), a one-sided bound moved by a positive
element (nontriviality), or `0`.

The hypothesis `Nontrivial Γ` is explicit here. It cannot be dropped: over `Γ = 0` the one-row
system `p > 0` has neither a solution nor an obstruction
(`not_feasible_not_obstruction_of_subsingleton`).

`exists_rat_functional_pos` is `markov:lem:separation`: in a finite-dimensional `ℚ`-vector space
with an order compatible with addition, finitely many strictly positive elements are sent to
positive rationals by one `ℚ`-linear functional. The order need only be partial, so this is
slightly more general than the source. The proof differs from the source's convex-hull and
nearest-point argument in `ℝ^a`. It applies the alternative with `Γ = ℚ`, `b = 0` and `M` the
coordinate matrix of the `x_i` in a basis. An obstruction would give `∑ r_i x_i = 0` with `r ≥ 0`
nonzero. Clearing denominators turns this into a nonzero natural combination of positive
elements equal to `0`, which is impossible.

All clauses of the three labels are proved; nothing is pending.
-/

namespace Surreal.Alternative

open Finset

universe u

section Scalars

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Module ℚ Γ]

/-- A positive rational multiple of a positive element of an ordered `ℚ`-vector space is
positive. -/
theorem qsmul_pos {q : ℚ} (hq : 0 < q) {x : Γ} (hx : 0 < x) : 0 < q • x := by
  have h : q.den • (q • x) = q.num • x := by
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, Rat.den_mul_eq_num, Int.cast_smul_eq_zsmul]
  have hpos : 0 < q.num • x := zsmul_pos hx (Rat.num_pos.mpr hq)
  rw [← h] at hpos
  exact (nsmul_pos_iff q.den_ne_zero).mp hpos

/-- A nonnegative rational multiple of a positive element is nonnegative. -/
theorem qsmul_nonneg {q : ℚ} (hq : 0 ≤ q) {x : Γ} (hx : 0 < x) : 0 ≤ q • x := by
  rcases hq.eq_or_lt with rfl | hq
  · simp
  · exact (qsmul_pos hq hx).le

/-- Multiplication by a positive rational is strictly monotone. -/
theorem qsmul_lt_qsmul {q : ℚ} (hq : 0 < q) {x y : Γ} (h : x < y) : q • x < q • y := by
  have := qsmul_pos hq (sub_pos.mpr h)
  rwa [smul_sub, sub_pos] at this

/-- Divisibility makes the order dense: the midpoint lies strictly between. -/
theorem exists_between_of_lt {a b : Γ} (h : a < b) : ∃ x, a < x ∧ x < b := by
  have hy : 0 < (1 / 2 : ℚ) • (b - a) := qsmul_pos (by norm_num) (sub_pos.mpr h)
  refine ⟨a + (1 / 2 : ℚ) • (b - a), lt_add_of_pos_right a hy, ?_⟩
  have e : b - (a + (1 / 2 : ℚ) • (b - a)) = (1 / 2 : ℚ) • (b - a) := by
    rw [← sub_sub, show b - a - (1 / 2 : ℚ) • (b - a) = ((1 : ℚ) - 1 / 2) • (b - a) by
      rw [sub_smul, one_smul]]
    norm_num
  exact sub_pos.mp (by rw [e]; exact hy)

/-- Finitely many lower bounds all strictly below finitely many upper bounds can be separated
by a point of a nonzero ordered `ℚ`-vector space. -/
theorem exists_between_finite [Nontrivial Γ] {P N : Type*} [Finite P] [Finite N]
    (L : P → Γ) (U : N → Γ) (h : ∀ i k, L i < U k) :
    ∃ x : Γ, (∀ i, L i < x) ∧ ∀ k, x < U k := by
  rcases isEmpty_or_nonempty P with hP | hP <;> rcases isEmpty_or_nonempty N with hN | hN
  · exact ⟨0, isEmptyElim, isEmptyElim⟩
  · obtain ⟨k0, hk0⟩ := Finite.exists_min U
    obtain ⟨x, hx⟩ := exists_lt (U k0)
    exact ⟨x, isEmptyElim, fun k => hx.trans_le (hk0 k)⟩
  · obtain ⟨i0, hi0⟩ := Finite.exists_max L
    obtain ⟨x, hx⟩ := exists_gt (L i0)
    exact ⟨x, fun i => (hi0 i).trans_lt hx, isEmptyElim⟩
  · obtain ⟨i0, hi0⟩ := Finite.exists_max L
    obtain ⟨k0, hk0⟩ := Finite.exists_min U
    obtain ⟨x, hx1, hx2⟩ := exists_between_of_lt (h i0 k0)
    exact ⟨x, fun i => (hi0 i).trans_lt hx1, fun k => hx2.trans_le (hk0 k)⟩

end Scalars

section Combination

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {ι ι' κ : Type*}

/-- Rows of the rational combination `c M`. -/
def combRow [Fintype ι] (c : ι' → ι → ℚ) (M : ι → κ → ℚ) : ι' → κ → ℚ :=
  fun l j => ∑ i, c l i * M i j

/-- Constant terms of the rational combination `c b`. -/
def combConst [Fintype ι] (c : ι' → ι → ℚ) (b : ι → V) : ι' → V :=
  fun l => ∑ i, c l i • b i

/-- Evaluating a combined row at `p` is the same combination of the evaluated original rows. -/
theorem comb_eval [Fintype ι] [Fintype κ] (c : ι' → ι → ℚ) (M : ι → κ → ℚ) (b : ι → V)
    (p : κ → V) (l : ι') :
    ∑ j, combRow c M l j • p j + combConst c b l = ∑ i, c l i • (∑ j, M i j • p j + b i) := by
  simp only [combRow, combConst, Finset.sum_smul, smul_add, Finset.smul_sum, mul_smul]
  rw [Finset.sum_add_distrib, Finset.sum_comm]

/-- The combination with a standard basis vector picks out one entry. -/
theorem sum_single_smul [Fintype ι] [DecidableEq ι] (z : ι) (u : ι → V) :
    ∑ i, (Pi.single z (1 : ℚ) : ι → ℚ) i • u i = u z := by
  simp [Pi.single_apply]

end Combination

section Alternative

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Module ℚ Γ]
  {ι ι' κ : Type*}

/-- Alternative (i): some `p ∈ Γ^κ` makes every row of `M p + b` strictly positive. -/
def Feasible [Fintype κ] (M : ι → κ → ℚ) (b : ι → Γ) : Prop :=
  ∃ p : κ → Γ, ∀ i, 0 < ∑ j, M i j • p j + b i

/-- Alternative (ii): a nonzero `r ∈ ℚ_{≥0}^ι` with `rᵀ M = 0` and `r ⬝ b ≤ 0`. -/
def Obstruction [Fintype ι] (M : ι → κ → ℚ) (b : ι → Γ) : Prop :=
  ∃ r : ι → ℚ, (∀ i, 0 ≤ r i) ∧ r ≠ 0 ∧ (∀ j, ∑ i, r i * M i j = 0) ∧ ∑ i, r i • b i ≤ 0

/-- The two alternatives exclude each other. -/
theorem not_feasible_and_obstruction [Fintype ι] [Fintype κ] (M : ι → κ → ℚ) (b : ι → Γ) :
    ¬ (Feasible M b ∧ Obstruction M b) := by
  rintro ⟨⟨p, hp⟩, r, hr0, hrne, hrM, hrb⟩
  have key := comb_eval (fun (_ : Unit) => r) M b p ()
  have h1 : ∑ j, combRow (fun (_ : Unit) => r) M () j • p j = 0 := by
    simp [combRow, hrM]
  rw [h1, zero_add] at key
  simp only [combConst] at key
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hrne
  have hpos : 0 < ∑ i, r i • (∑ j, M i j • p j + b i) :=
    Finset.sum_pos' (fun i _ => qsmul_nonneg (hr0 i) (hp i))
      ⟨i0, mem_univ _, qsmul_pos ((hr0 i0).lt_of_ne' hi0) (hp i0)⟩
  rw [← key] at hpos
  exact (hpos.trans_le hrb).false

omit [IsOrderedAddMonoid Γ] in
/-- An obstruction for a nonnegative combination with nonzero rows is an obstruction for the
original system. -/
theorem obstruction_of_comb [Fintype ι] [Fintype ι'] {c : ι' → ι → ℚ}
    (hc : ∀ l i, 0 ≤ c l i) (hc0 : ∀ l, c l ≠ 0) {M : ι → κ → ℚ} {b : ι → Γ}
    (h : Obstruction (combRow c M) (combConst c b)) : Obstruction M b := by
  obtain ⟨r, hr0, hrne, hrM, hrb⟩ := h
  refine ⟨fun i => ∑ l, r l * c l i,
    fun i => Finset.sum_nonneg fun l _ => mul_nonneg (hr0 l) (hc l i), ?_, ?_, ?_⟩
  · obtain ⟨l0, hl0⟩ := Function.ne_iff.mp hrne
    obtain ⟨i0, hi0⟩ := Function.ne_iff.mp (hc0 l0)
    have hpos : 0 < r l0 * c l0 i0 :=
      mul_pos ((hr0 l0).lt_of_ne' hl0) ((hc l0 i0).lt_of_ne' hi0)
    intro h0
    have h1 := congr_fun h0 i0
    simp only [Pi.zero_apply] at h1
    have : r l0 * c l0 i0 ≤ ∑ l, r l * c l i0 :=
      Finset.single_le_sum (f := fun l => r l * c l i0)
        (fun l _ => mul_nonneg (hr0 l) (hc l i0)) (mem_univ l0)
    linarith
  · intro j
    have := hrM j
    simp only [combRow, Finset.mul_sum] at this
    rw [Finset.sum_comm] at this
    simp only [Finset.sum_mul, mul_assoc]
    exact this
  · simp only [combConst, Finset.smul_sum, smul_smul] at hrb
    rw [Finset.sum_comm] at hrb
    simpa only [Finset.sum_smul] using hrb

end Alternative

section Elimination

section Coefficients

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {ι : Type*} {d : ℕ}

/-- Row indices of one Fourier–Motzkin step eliminating coordinate `0`: the rows whose
coefficient there vanishes, and the pairs of a row with positive and a row with negative
coefficient there. -/
abbrev ElimIdx (M : ι → Fin (d + 1) → ℚ) : Type _ :=
  {i // M i 0 = 0} ⊕ ({i // 0 < M i 0} × {i // M i 0 < 0})

/-- The nonnegative multipliers producing the rows of the eliminated system from the rows of
`M`: a retained row is kept, and a pair `(i, k)` is combined as
`(-M k 0) • row i + M i 0 • row k`, which kills coordinate `0`. -/
def elimCoeff [DecidableEq ι] (M : ι → Fin (d + 1) → ℚ) : ElimIdx M → ι → ℚ
  | .inl z => Pi.single z.1 1
  | .inr (i, k) => (-M k.1 0) • Pi.single i.1 1 + M i.1 0 • Pi.single k.1 1

/-- Entries of a standard basis vector are nonnegative. -/
theorem single_one_nonneg [DecidableEq ι] (z i : ι) : 0 ≤ (Pi.single z (1 : ℚ) : ι → ℚ) i := by
  rw [Pi.single_apply]
  split_ifs <;> norm_num

/-- The elimination multipliers are nonnegative. -/
theorem elimCoeff_nonneg [DecidableEq ι] (M : ι → Fin (d + 1) → ℚ) (l : ElimIdx M) (i : ι) :
    0 ≤ elimCoeff M l i := by
  rcases l with z | ⟨i', k⟩
  · exact single_one_nonneg z.1 i
  · simp only [elimCoeff, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg (neg_pos.mpr k.2).le (single_one_nonneg _ _))
      (mul_nonneg i'.2.le (single_one_nonneg _ _))

/-- Every row of elimination multipliers is nonzero. -/
theorem elimCoeff_ne_zero [DecidableEq ι] (M : ι → Fin (d + 1) → ℚ) (l : ElimIdx M) :
    elimCoeff M l ≠ 0 := by
  rcases l with z | ⟨i, k⟩
  · exact Pi.single_ne_zero_iff.mpr one_ne_zero
  · have hik : i.1 ≠ k.1 := by
      intro h
      have := i.2
      rw [h] at this
      exact lt_asymm this k.2
    intro h
    have := congr_fun h i.1
    simp only [elimCoeff, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
      Pi.single_eq_of_ne hik, Pi.zero_apply] at this
    linarith [k.2]

/-- A retained row combines to itself. -/
theorem sum_elimCoeff_inl [Fintype ι] [DecidableEq ι] (M : ι → Fin (d + 1) → ℚ)
    (z : {i // M i 0 = 0}) (u : ι → V) : ∑ i, elimCoeff M (.inl z) i • u i = u z.1 :=
  sum_single_smul z.1 u

/-- A lower/upper pair combines to `(-M k 0) • u i + M i 0 • u k`. -/
theorem sum_elimCoeff_inr [Fintype ι] [DecidableEq ι] (M : ι → Fin (d + 1) → ℚ)
    (i : {i // 0 < M i 0}) (k : {i // M i 0 < 0}) (u : ι → V) :
    ∑ l, elimCoeff M (.inr (i, k)) l • u l = (-M k.1 0) • u i.1 + M i.1 0 • u k.1 := by
  simp only [elimCoeff, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
    Finset.sum_add_distrib, ← Finset.smul_sum, sum_single_smul]

/-- Every combined row has coefficient `0` in the eliminated coordinate. -/
theorem combRow_elimCoeff_zero [Fintype ι] [DecidableEq ι] (M : ι → Fin (d + 1) → ℚ)
    (l : ElimIdx M) : combRow (elimCoeff M) M l 0 = 0 := by
  rcases l with z | ⟨i, k⟩
  · have := sum_elimCoeff_inl M z (fun l => M l 0)
    simp only [smul_eq_mul] at this
    simp only [combRow]
    rw [this]
    exact z.2
  · have := sum_elimCoeff_inr M i k (fun l => M l 0)
    simp only [smul_eq_mul] at this
    simp only [combRow]
    rw [this]
    ring

/-- The rows of the eliminated system, in the coordinates `1, …, d`. -/
def elimRow [Fintype ι] [DecidableEq ι] (M : ι → Fin (d + 1) → ℚ) : ElimIdx M → Fin d → ℚ :=
  combRow (elimCoeff M) (fun i j => M i j.succ)

/-- The constant terms of the eliminated system. -/
def elimConst [Fintype ι] [DecidableEq ι] (M : ι → Fin (d + 1) → ℚ) (b : ι → V) :
    ElimIdx M → V :=
  combConst (elimCoeff M) b

end Coefficients

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Module ℚ Γ]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

omit [IsOrderedAddMonoid Γ] in
/-- An obstruction for the eliminated system lifts to one for the original system. -/
theorem obstruction_of_elim {M : ι → Fin (d + 1) → ℚ} {b : ι → Γ}
    (h : Obstruction (elimRow M) (elimConst M b)) : Obstruction M b := by
  refine obstruction_of_comb (elimCoeff_nonneg M) (elimCoeff_ne_zero M) ?_
  obtain ⟨r, hr0, hrne, hrM, hrb⟩ := h
  refine ⟨r, hr0, hrne, fun j => ?_, hrb⟩
  induction j using Fin.cases with
  | zero => simp [combRow_elimCoeff_zero]
  | succ j => exact hrM j

/-- A solution of the eliminated system extends to one of the original system; the value of
coordinate `0` is chosen between the finitely many lower and upper bounds. -/
theorem feasible_of_elim [Nontrivial Γ] {M : ι → Fin (d + 1) → ℚ} {b : ι → Γ}
    (h : Feasible (elimRow M) (elimConst M b)) : Feasible M b := by
  obtain ⟨p', hp'⟩ := h
  let u : ι → Γ := fun i => ∑ j, M i j.succ • p' j + b i
  have hrow : ∀ l, 0 < ∑ i, elimCoeff M l i • u i := fun l =>
    (hp' l).trans_eq (comb_eval (elimCoeff M) (fun i (j : Fin d) => M i j.succ) b p' l)
  have hz : ∀ i, M i 0 = 0 → 0 < u i := fun i hi => by
    have := hrow (.inl ⟨i, hi⟩)
    rwa [sum_elimCoeff_inl] at this
  have hpair : ∀ i k, (hi : 0 < M i 0) → (hk : M k 0 < 0) →
      0 < (-M k 0) • u i + M i 0 • u k := fun i k hi hk => by
    have := hrow (.inr (⟨i, hi⟩, ⟨k, hk⟩))
    rwa [sum_elimCoeff_inr] at this
  obtain ⟨x, hxL, hxU⟩ := exists_between_finite
    (fun i : {i // 0 < M i 0} => -((M i.1 0)⁻¹ • u i.1))
    (fun k : {k // M k 0 < 0} => (-M k.1 0)⁻¹ • u k.1) (fun i k => by
      have ha : 0 < M i.1 0 := i.2
      have hb : 0 < -M k.1 0 := neg_pos.mpr k.2
      have e1 : (M i.1 0 * -M k.1 0)⁻¹ * -M k.1 0 = (M i.1 0)⁻¹ := by
        rw [mul_inv, mul_assoc, inv_mul_cancel₀ hb.ne', mul_one]
      have e2 : (M i.1 0 * -M k.1 0)⁻¹ * M i.1 0 = (-M k.1 0)⁻¹ := by
        rw [mul_inv, mul_right_comm, inv_mul_cancel₀ ha.ne', one_mul]
      have h1 := qsmul_pos (inv_pos.mpr (mul_pos ha hb)) (hpair i.1 k.1 i.2 k.2)
      rw [smul_add, smul_smul, smul_smul, e1, e2] at h1
      exact neg_lt_iff_pos_add'.mpr h1)
  refine ⟨Fin.cons x p', fun i => ?_⟩
  rw [Fin.sum_univ_succ, add_assoc]
  simp only [Fin.cons_zero, Fin.cons_succ]
  change 0 < M i 0 • x + u i
  rcases lt_trichotomy (M i 0) 0 with hneg | hzero | hpos
  · have hb : 0 < -M i 0 := neg_pos.mpr hneg
    have h1 := qsmul_lt_qsmul hb (hxU ⟨i, hneg⟩)
    rw [smul_smul, mul_inv_cancel₀ hb.ne', one_smul, neg_smul] at h1
    exact neg_lt_iff_pos_add'.mp h1
  · rw [hzero, zero_smul, zero_add]
    exact hz i hzero
  · have h1 := qsmul_lt_qsmul hpos (hxL ⟨i, hpos⟩)
    rw [smul_neg, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul] at h1
    exact neg_lt_iff_pos_add.mp h1

end Elimination

section Main

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Module ℚ Γ]

/-- Fourier–Motzkin elimination: for `d` unknowns, one of the two alternatives holds. -/
theorem feasible_or_obstruction_fin [Nontrivial Γ] (d : ℕ) {ι : Type u} [Fintype ι]
    (M : ι → Fin d → ℚ) (b : ι → Γ) : Feasible M b ∨ Obstruction M b := by
  induction d generalizing ι with
  | zero =>
    classical
    by_cases h : ∀ i, 0 < b i
    · exact Or.inl ⟨Fin.elim0, fun i => by simpa using h i⟩
    · push Not at h
      obtain ⟨i, hi⟩ := h
      refine Or.inr ⟨Pi.single i 1, single_one_nonneg i, Pi.single_ne_zero_iff.mpr one_ne_zero,
        fun j => j.elim0, ?_⟩
      rwa [sum_single_smul]
  | succ d ih =>
    classical
    rcases ih (elimRow M) (elimConst M b) with h | h
    · exact Or.inl (feasible_of_elim h)
    · exact Or.inr (obstruction_of_elim h)

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Over a nonzero ordered `ℚ`-vector space, at least one of the two alternatives holds. -/
theorem feasible_or_obstruction [Nontrivial Γ] (M : ι → κ → ℚ) (b : ι → Γ) :
    Feasible M b ∨ Obstruction M b := by
  let e := Fintype.equivFin κ
  rcases feasible_or_obstruction_fin (Fintype.card κ) (fun i j => M i (e.symm j)) b with
    ⟨p, hp⟩ | ⟨r, hr0, hrne, hrM, hrb⟩
  · refine Or.inl ⟨fun j => p (e j), fun i => ?_⟩
    have := hp i
    rw [← e.sum_comp] at this
    simpa using this
  · refine Or.inr ⟨r, hr0, hrne, fun j => ?_, hrb⟩
    simpa using hrM (e j)

/-- **Strict rational alternative** (`wick:thm:alternative`). Let `Γ` be a nonzero ordered
`ℚ`-vector space (a nonzero divisible ordered abelian group), `M` a rational matrix and `b` a
vector over `Γ`. Exactly one of the following holds: (i) some `p ∈ Γ^κ` has `M p + b > 0` in
every coordinate; (ii) some nonzero `r ∈ ℚ_{≥0}^ι` has `rᵀ M = 0` and `r ⬝ b ≤ 0`. -/
theorem strict_alternative [Nontrivial Γ] (M : ι → κ → ℚ) (b : ι → Γ) :
    Xor (Feasible M b) (Obstruction M b) := by
  rcases feasible_or_obstruction M b with h | h
  · exact Or.inl ⟨h, fun h' => not_feasible_and_obstruction M b ⟨h, h'⟩⟩
  · exact Or.inr ⟨h, fun h' => not_feasible_and_obstruction M b ⟨h', h⟩⟩

/-- `wick:thm:alternative`, as an equivalence: the system is feasible iff there is no
obstruction. -/
theorem feasible_iff_not_obstruction [Nontrivial Γ] (M : ι → κ → ℚ) (b : ι → Γ) :
    Feasible M b ↔ ¬ Obstruction M b :=
  ⟨fun h h' => not_feasible_and_obstruction M b ⟨h, h'⟩,
    fun h => (feasible_or_obstruction M b).resolve_right h⟩

/-- `wick:eq:alternative`: `M p + b > 0` is solvable over `Γ` iff `r ⬝ b > 0` for every nonzero
`r ∈ ℚ_{≥0}^ι` with `rᵀ M = 0`. -/
theorem feasible_iff_forall_pos [Nontrivial Γ] (M : ι → κ → ℚ) (b : ι → Γ) :
    Feasible M b ↔ ∀ r : ι → ℚ, (∀ i, 0 ≤ r i) → r ≠ 0 → (∀ j, ∑ i, r i * M i j = 0) →
      0 < ∑ i, r i • b i := by
  rw [feasible_iff_not_obstruction]
  constructor
  · intro h r hr0 hrne hrM
    by_contra hle
    exact h ⟨r, hr0, hrne, hrM, not_lt.mp hle⟩
  · rintro h ⟨r, hr0, hrne, hrM, hrb⟩
    exact absurd hrb (not_le.mpr (h r hr0 hrne hrM))

omit [IsOrderedAddMonoid Γ] in
/-- The hypothesis `Nontrivial Γ` of `strict_alternative` cannot be dropped: over `Γ = 0`
(for instance `PUnit`, which carries all the instances) the one-row system `p > 0` has neither
a solution nor an obstruction. -/
theorem not_feasible_not_obstruction_of_subsingleton [Subsingleton Γ] :
    ¬ Feasible (fun _ _ : Unit => (1 : ℚ)) (0 : Unit → Γ) ∧
      ¬ Obstruction (fun _ _ : Unit => (1 : ℚ)) (0 : Unit → Γ) := by
  refine ⟨fun ⟨p, hp⟩ => (hp ()).ne' (Subsingleton.elim _ _), fun ⟨r, _, hrne, hrM, _⟩ => ?_⟩
  apply hrne
  funext i
  cases i
  simpa using hrM ()

end Main

/-- Clearing denominators: every rational vector has a positive multiple with integer entries. -/
theorem exists_int_multiple {ι : Type*} [Fintype ι] (r : ι → ℚ) :
    ∃ (D : ℚ) (m : ι → ℤ), 0 < D ∧ ∀ i, (m i : ℚ) = D * r i := by
  classical
  refine ⟨∏ i, ((r i).den : ℚ), fun i => (∏ j ∈ univ.erase i, ((r j).den : ℤ)) * (r i).num,
    Finset.prod_pos fun i _ => Nat.cast_pos.mpr (r i).den_pos, fun i => ?_⟩
  rw [← Finset.mul_prod_erase univ (fun j => ((r j).den : ℚ)) (mem_univ i)]
  push_cast
  rw [← Rat.den_mul_eq_num]
  ring

/-- **Finite rational sign separation** (`markov:lem:separation`). In a finite-dimensional
`ℚ`-vector space with an order compatible with addition (for instance an ordered-abelian-group
order), finitely many strictly positive elements are sent to positive rationals by a single
`ℚ`-linear functional. The empty family is allowed; then any functional works. -/
theorem exists_rat_functional_pos {W : Type*} [AddCommGroup W] [PartialOrder W]
    [IsOrderedAddMonoid W] [Module ℚ W] [FiniteDimensional ℚ W] {ι : Type*} [Fintype ι]
    (x : ι → W) (hx : ∀ i, 0 < x i) : ∃ ℓ : W →ₗ[ℚ] ℚ, ∀ i, 0 < ℓ (x i) := by
  let B := Module.finBasis ℚ W
  rcases feasible_or_obstruction (fun i j => B.repr (x i) j) (0 : ι → ℚ) with
    ⟨p, hp⟩ | ⟨r, hr0, hrne, hrM, -⟩
  · refine ⟨∑ j, p j • B.coord j, fun i => ?_⟩
    have := hp i
    simpa [mul_comm] using this
  · exfalso
    have hsum : ∑ i, r i • x i = 0 := by
      apply B.repr.injective
      ext j
      simpa [map_sum] using hrM j
    obtain ⟨D, m, hD, hm⟩ := exists_int_multiple r
    have hm0 : ∀ i, 0 ≤ m i := fun i => by
      have : (0 : ℚ) ≤ m i := by
        rw [hm i]
        exact mul_nonneg hD.le (hr0 i)
      exact_mod_cast this
    obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hrne
    have hmpos : 0 < m i0 := by
      have : (0 : ℚ) < m i0 := by
        rw [hm i0]
        exact mul_pos hD ((hr0 i0).lt_of_ne' hi0)
      exact_mod_cast this
    have hzero : ∑ i, m i • x i = 0 :=
      calc ∑ i, m i • x i = ∑ i, (m i : ℚ) • x i := by simp only [Int.cast_smul_eq_zsmul]
        _ = D • ∑ i, r i • x i := by simp only [hm, Finset.smul_sum, mul_smul]
        _ = 0 := by rw [hsum, smul_zero]
    have hpos : 0 < ∑ i, m i • x i :=
      Finset.sum_pos' (fun i _ => zsmul_nonneg (hx i).le (hm0 i))
        ⟨i0, mem_univ _, zsmul_pos (hx i0) hmpos⟩
    exact hpos.ne' hzero

end Surreal.Alternative
