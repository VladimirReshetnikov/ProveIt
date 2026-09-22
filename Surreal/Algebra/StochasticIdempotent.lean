import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Fintype.Lattice

/-!
# Canonical splitting of a stochastic idempotent

This file proves `markov:lem:splitting` of
`docs/surreal/markov-generators-at-every-scale/article.tex` over an arbitrary linearly
ordered field `K` (the source works over `ℝ`). Let `P` be a square row-stochastic matrix
with `P² = P`.

* `exists_splitting`: there are entrywise nonnegative row-stochastic matrices
  `U : n × rank P` and `V : rank P × n` with `P = UV` and `VU = I`.
* The canonical choice. `closedClasses P` is the finite set of closed communicating classes
  of the directed graph of positive entries of `P`; `mem_closedClasses_iff` identifies it
  with the literal definition `IsClosedCommClass` (an equivalence class of mutual
  reachability that no positive entry leaves). `splitV P C` is the stationary probability
  vector of the class `C` extended by zero (`vecMul_splitV`, `sum_splitV`, `splitV_pos`,
  `splitV_eq_zero`, and uniqueness in `eq_splitV_of_stationary`), and
  `splitU P i C = ∑_{k ∈ C} P i k` is the mass that row `i` assigns to `C`. Then
  `splitU_mul_splitV` gives `UV = P` and `splitV_mul_splitU` gives `VU = I`.
* The rank count `card_closedClasses`: the number of closed classes is `rank P`.
* `canonical_splitting` bundles the canonical description, the factorization, the
  stochasticity of both factors and the rank count into one statement.
* The structural facts of the source proof: transient columns vanish, so the transient
  block is zero (`apply_eq_zero_of_transient`); each closed block is `𝟙 ν_C` with `ν_C > 0`
  (`apply_eq_splitV`, `splitV_pos`); and every row restricted to `C`, in particular a
  transient one, is the multiple `U_{iC} ν_C` (`apply_eq_splitU_mul_splitV`); at a state of `C`
  the row of `U` is the coordinate row of `C` (`splitU_apply_of_mem`).

The source's limit argument `T_0^m → 0` is replaced by an algebraic maximum principle:
each column of `P` is `P`-harmonic, so its maximum sits on the diagonal
(`apply_le_diag`) and propagates along positive entries. Reachability then collapses to one
step (`transGen_iff`). Nothing is pending.
-/

namespace Surreal.StochasticIdempotent

open Matrix Finset

noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {n : Type*} [Fintype n] [DecidableEq n] {P : Matrix n n K}

/-! ### The maximum principle for a stochastic idempotent -/

omit [LinearOrder K] [IsStrictOrderedRing K] [DecidableEq n] in
/-- Each column of an idempotent is fixed by it. -/
theorem sum_mul_apply (hPP : P * P = P) (i j : n) : ∑ k, P i k * P k j = P i j := by
  rw [← mul_apply, hPP]

/-- Maximum principle: a `P`-harmonic vector takes its maximal value at every state reached
by a positive entry from a maximizer. -/
theorem eq_of_isMax (hP : P ∈ rowStochastic K n) {x : n → K}
    (hx : ∀ i, ∑ k, P i k * x k = x i) {m : n} (hm : ∀ k, x k ≤ x m) {k : n}
    (hk : 0 < P m k) : x k = x m := by
  have hsum : ∑ l, P m l * (x m - x l) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_row_of_mem_rowStochastic hP, one_mul, hx,
      sub_self]
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun l _ =>
    mul_nonneg (nonneg_of_mem_rowStochastic hP) (sub_nonneg.2 (hm l))).1 hsum k (mem_univ k)
  rcases mul_eq_zero.1 hterm with h | h
  · exact absurd h hk.ne'
  · exact (sub_eq_zero.1 h).symm

/-- The maximum of every column of a stochastic idempotent sits on the diagonal. -/
theorem apply_le_diag (hP : P ∈ rowStochastic K n) (hPP : P * P = P) (i j : n) :
    P i j ≤ P j j := by
  haveI : Nonempty n := ⟨i⟩
  obtain ⟨m, hm⟩ := Finite.exists_max fun r => P r j
  by_cases h : 0 < P m j
  · have hj : P j j = P m j :=
      eq_of_isMax hP (x := fun r => P r j) (sum_mul_apply hPP · j) hm h
    exact (hm i).trans hj.ge
  · exact (hm i).trans ((not_lt.1 h).trans (nonneg_of_mem_rowStochastic hP))

/-- A positive entry `P j k` forces `P k j = P j j`. -/
theorem apply_swap_eq (hP : P ∈ rowStochastic K n) (hPP : P * P = P) {j k : n}
    (hjk : 0 < P j k) : P k j = P j j :=
  eq_of_isMax hP (x := fun r => P r j) (sum_mul_apply hPP · j) (apply_le_diag hP hPP · j) hjk

/-- Positive entries compose: `P i k ≥ P i j P j k`. -/
theorem pos_trans (hP : P ∈ rowStochastic K n) (hPP : P * P = P) {i j k : n}
    (hij : 0 < P i j) (hjk : 0 < P j k) : 0 < P i k := by
  rw [← sum_mul_apply hPP i k]
  exact (mul_pos hij hjk).trans_le (Finset.single_le_sum (f := fun m => P i m * P m k)
    (fun m _ => mul_nonneg (nonneg_of_mem_rowStochastic hP) (nonneg_of_mem_rowStochastic hP))
    (mem_univ j))

/-- From a recurrent state, positive entries are symmetric. -/
theorem pos_swap (hP : P ∈ rowStochastic K n) (hPP : P * P = P) {j k : n}
    (hj : 0 < P j j) (hjk : 0 < P j k) : 0 < P k j := by
  rw [apply_swap_eq hP hPP hjk]
  exact hj

/-- On a recurrent row, every positive entry equals the corresponding diagonal entry. -/
theorem apply_eq_diag (hP : P ∈ rowStochastic K n) (hPP : P * P = P) {j k : n}
    (hj : 0 < P j j) (hjk : 0 < P j k) : P j k = P k k :=
  apply_swap_eq hP hPP (pos_swap hP hPP hj hjk)

/-- A state reached by a positive entry from a recurrent state is recurrent. -/
theorem diag_pos_of_pos (hP : P ∈ rowStochastic K n) (hPP : P * P = P) {j k : n}
    (hj : 0 < P j j) (hjk : 0 < P j k) : 0 < P k k := by
  rw [← apply_eq_diag hP hPP hj hjk]
  exact hjk

/-- The column of a state with zero diagonal entry vanishes. -/
theorem apply_eq_zero_of_diag_eq_zero (hP : P ∈ rowStochastic K n) (hPP : P * P = P)
    {j : n} (h : P j j = 0) (i : n) : P i j = 0 :=
  le_antisymm (h ▸ apply_le_diag hP hPP i j) (nonneg_of_mem_rowStochastic hP)

/-- Two recurrent states joined by a positive entry have the same row. -/
theorem row_eq (hP : P ∈ rowStochastic K n) (hPP : P * P = P) {j k : n}
    (hj : 0 < P j j) (hjk : 0 < P j k) : P j = P k := by
  funext l
  have hk := diag_pos_of_pos hP hPP hj hjk
  by_cases hkl : 0 < P k l
  · rw [apply_eq_diag hP hPP hj (pos_trans hP hPP hjk hkl), apply_eq_diag hP hPP hk hkl]
  · have hjl : ¬ 0 < P j l := fun hjl => hkl (pos_trans hP hPP (pos_swap hP hPP hj hjk) hjl)
    rw [le_antisymm (not_lt.1 hjl) (nonneg_of_mem_rowStochastic hP),
      le_antisymm (not_lt.1 hkl) (nonneg_of_mem_rowStochastic hP)]

/-- Every row of a stochastic matrix has a positive entry. -/
theorem exists_pos (hP : P ∈ rowStochastic K n) (i : n) : ∃ k, 0 < P i k := by
  by_contra h
  simp only [not_exists, not_lt] at h
  have hle : ∑ k, P i k ≤ 0 := Finset.sum_nonpos fun k _ => h k
  rw [sum_row_of_mem_rowStochastic hP] at hle
  exact absurd hle (not_le.2 one_pos)

/-! ### Reachability and closed communicating classes -/

/-- Reachability in the directed graph of positive entries: the reflexive-transitive closure
of `0 < P a b`. -/
def Reaches (P : Matrix n n K) : n → n → Prop :=
  Relation.ReflTransGen fun a b => 0 < P a b

/-- A closed communicating class: an equivalence class of mutual reachability from which no
positive entry leads out. -/
def IsClosedCommClass (P : Matrix n n K) (C : Set n) : Prop :=
  (∃ i, C = {k | Reaches P i k ∧ Reaches P k i}) ∧ ∀ i ∈ C, ∀ k, 0 < P i k → k ∈ C

/-- For a stochastic idempotent, a positive path collapses to a single positive entry. -/
theorem transGen_iff (hP : P ∈ rowStochastic K n) (hPP : P * P = P) {i k : n} :
    Relation.TransGen (fun a b => 0 < P a b) i k ↔ 0 < P i k := by
  refine ⟨fun h => ?_, fun h => Relation.TransGen.single h⟩
  induction h with
  | single h => exact h
  | tail _ hbc ih => exact pos_trans hP hPP ih hbc

theorem reaches_iff (hP : P ∈ rowStochastic K n) (hPP : P * P = P) {i k : n} :
    Reaches P i k ↔ k = i ∨ 0 < P i k := by
  rw [Reaches, Relation.reflTransGen_iff_eq_or_transGen, transGen_iff hP hPP]

/-- The support `{k | 0 < P j k}` of row `j`; for a recurrent state it is its closed class. -/
def classOf (P : Matrix n n K) (j : n) : Finset n :=
  univ.filter fun k => 0 < P j k

/-- The closed communicating classes of a stochastic idempotent, computed as the row supports
of the recurrent states `0 < P j j`; see `mem_closedClasses_iff`. -/
def closedClasses (P : Matrix n n K) : Finset (Finset n) :=
  (univ.filter fun j => 0 < P j j).image (classOf P)

omit [IsStrictOrderedRing K] [DecidableEq n] in
theorem mem_classOf {j k : n} : k ∈ classOf P j ↔ 0 < P j k := by
  simp [classOf]

omit [IsStrictOrderedRing K] in
theorem mem_closedClasses {C : Finset n} :
    C ∈ closedClasses P ↔ ∃ j, 0 < P j j ∧ classOf P j = C := by
  simp [closedClasses]

omit [IsStrictOrderedRing K] in
theorem classOf_mem_closedClasses {j : n} (hj : 0 < P j j) : classOf P j ∈ closedClasses P :=
  mem_closedClasses.2 ⟨j, hj, rfl⟩

omit [IsStrictOrderedRing K] [DecidableEq n] in
theorem self_mem_classOf {j : n} (hj : 0 < P j j) : j ∈ classOf P j :=
  mem_classOf.2 hj

theorem classOf_eq (hP : P ∈ rowStochastic K n) (hPP : P * P = P) {j k : n}
    (hj : 0 < P j j) (hjk : 0 < P j k) : classOf P k = classOf P j := by
  simp only [classOf, row_eq hP hPP hj hjk]

/-- Every member of a closed class is recurrent, and its row support is the class. -/
theorem eq_classOf_of_mem (hP : P ∈ rowStochastic K n) (hPP : P * P = P) {C : Finset n}
    (hC : C ∈ closedClasses P) {j : n} (hj : j ∈ C) : 0 < P j j ∧ classOf P j = C := by
  obtain ⟨i, hi, rfl⟩ := mem_closedClasses.1 hC
  have hij : 0 < P i j := mem_classOf.1 hj
  exact ⟨diag_pos_of_pos hP hPP hi hij, classOf_eq hP hPP hi hij⟩

/-- A state is recurrent (`0 < P j j`) exactly when it lies in a closed class. -/
theorem diag_pos_iff (hP : P ∈ rowStochastic K n) (hPP : P * P = P) {j : n} :
    0 < P j j ↔ ∃ C ∈ closedClasses P, j ∈ C :=
  ⟨fun hj => ⟨classOf P j, classOf_mem_closedClasses hj, self_mem_classOf hj⟩,
    fun ⟨_, hC, hjC⟩ => (eq_classOf_of_mem hP hPP hC hjC).1⟩

/-- `closedClasses P` is exactly the set of closed communicating classes of `P`. -/
theorem mem_closedClasses_iff (hP : P ∈ rowStochastic K n) (hPP : P * P = P) {C : Finset n} :
    C ∈ closedClasses P ↔ IsClosedCommClass P (C : Set n) := by
  constructor
  · intro hC
    obtain ⟨j, hj, rfl⟩ := mem_closedClasses.1 hC
    refine ⟨⟨j, ?_⟩, fun i hi k hik => ?_⟩
    · ext k
      simp only [Finset.mem_coe, mem_classOf, Set.mem_setOf_eq, reaches_iff hP hPP]
      constructor
      · intro hjk
        exact ⟨Or.inr hjk, Or.inr (pos_swap hP hPP hj hjk)⟩
      · rintro ⟨rfl | hjk, -⟩
        · exact hj
        · exact hjk
    · rw [Finset.mem_coe, mem_classOf] at hi ⊢
      exact pos_trans hP hPP hi hik
  · rintro ⟨⟨i, hCi⟩, hcl⟩
    have hiC : i ∈ (C : Set n) := by
      rw [hCi]
      exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
    have hii : 0 < P i i := by
      obtain ⟨k, hik⟩ := exists_pos hP i
      have hkC := hcl i hiC k hik
      rw [hCi] at hkC
      rcases (reaches_iff hP hPP).1 hkC.2 with rfl | hki
      · exact hik
      · exact pos_trans hP hPP hik hki
    refine mem_closedClasses.2 ⟨i, hii, ?_⟩
    apply Finset.coe_injective
    ext k
    rw [Finset.mem_coe, mem_classOf]
    constructor
    · exact hcl i hiC k
    · intro hk
      rw [hCi] at hk
      rcases (reaches_iff hP hPP).1 hk.1 with rfl | hik
      · exact hii
      · exact hik

/-- Two closed classes sharing a state coincide. -/
theorem eq_of_mem_of_mem (hP : P ∈ rowStochastic K n) (hPP : P * P = P)
    {C D : Finset n} (hC : C ∈ closedClasses P) (hD : D ∈ closedClasses P) {k : n}
    (hkC : k ∈ C) (hkD : k ∈ D) : C = D :=
  (eq_classOf_of_mem hP hPP hC hkC).2.symm.trans (eq_classOf_of_mem hP hPP hD hkD).2

omit [IsStrictOrderedRing K] in
theorem exists_mem_of_mem_closedClasses {C : Finset n} (hC : C ∈ closedClasses P) :
    ∃ j, j ∈ C := by
  obtain ⟨j, hj, rfl⟩ := mem_closedClasses.1 hC
  exact ⟨j, self_mem_classOf hj⟩

/-- A recurrent row is its diagonal restricted to its class. -/
theorem apply_eq_ite (hP : P ∈ rowStochastic K n) (hPP : P * P = P) {j : n}
    (hj : 0 < P j j) (k : n) : P j k = if k ∈ classOf P j then P k k else 0 := by
  by_cases hjk : 0 < P j k
  · rw [if_pos (mem_classOf.2 hjk), apply_eq_diag hP hPP hj hjk]
  · rw [if_neg (by rwa [mem_classOf]),
      le_antisymm (not_lt.1 hjk) (nonneg_of_mem_rowStochastic hP)]

/-- Each column: `P i k` is the mass of row `i` on the row support of `k` times `P k k`. -/
theorem apply_eq_mass_mul (hP : P ∈ rowStochastic K n) (hPP : P * P = P) (i k : n) :
    P i k = (∑ m ∈ classOf P k, P i m) * P k k := by
  rw [← sum_mul_apply hPP i k, Finset.sum_mul, classOf, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hkm : 0 < P k m
  · rw [if_pos hkm, apply_swap_eq hP hPP hkm]
  · rw [if_neg hkm]
    by_cases hm : 0 < P m m
    · have hmk : ¬ 0 < P m k := fun hmk => hkm (pos_swap hP hPP hm hmk)
      rw [le_antisymm (not_lt.1 hmk) (nonneg_of_mem_rowStochastic hP), mul_zero]
    · rw [apply_eq_zero_of_diag_eq_zero hP hPP
        (le_antisymm (not_lt.1 hm) (nonneg_of_mem_rowStochastic hP)), zero_mul]

/-! ### The canonical splitting -/

/-- The canonical `U`: `U i C = ∑_{k ∈ C} P i k`, the mass that row `i` assigns to the
closed class `C`. -/
def splitU (P : Matrix n n K) : Matrix n (closedClasses P) K :=
  Matrix.of fun i C => ∑ k ∈ (C : Finset n), P i k

/-- The canonical `V`: row `C` is `ν_C(k) = P k k` on `C` and zero elsewhere, the stationary
probability vector of the closed class `C` extended by zero. -/
def splitV (P : Matrix n n K) : Matrix (closedClasses P) n K :=
  Matrix.of fun C k => if k ∈ (C : Finset n) then P k k else 0

omit [IsStrictOrderedRing K] in
theorem splitU_apply (i : n) (C : closedClasses P) :
    splitU P i C = ∑ k ∈ (C : Finset n), P i k :=
  rfl

omit [IsStrictOrderedRing K] in
theorem splitV_apply (C : closedClasses P) (k : n) :
    splitV P C k = if k ∈ (C : Finset n) then P k k else 0 :=
  rfl

theorem splitU_nonneg (hP : P ∈ rowStochastic K n) (i : n) (C : closedClasses P) :
    0 ≤ splitU P i C :=
  Finset.sum_nonneg fun _ _ => nonneg_of_mem_rowStochastic hP

theorem splitV_nonneg (hP : P ∈ rowStochastic K n) (C : closedClasses P) (k : n) :
    0 ≤ splitV P C k := by
  rw [splitV_apply]
  split_ifs
  · exact nonneg_of_mem_rowStochastic hP
  · exact le_rfl

/-- Closed block: every row of a state in the class `C` equals `ν_C`. -/
theorem splitV_apply_eq (hP : P ∈ rowStochastic K n) (hPP : P * P = P) (C : closedClasses P)
    {j : n} (hj : j ∈ (C : Finset n)) (k : n) : splitV P C k = P j k := by
  obtain ⟨hjj, hCj⟩ := eq_classOf_of_mem hP hPP C.2 hj
  rw [apply_eq_ite hP hPP hjj, hCj, splitV_apply]

/-- The closed block `C_a = 𝟙 ν_a`: `P i k = ν_C(k)` for all `i, k ∈ C`. -/
theorem apply_eq_splitV (hP : P ∈ rowStochastic K n) (hPP : P * P = P) (C : closedClasses P)
    {i k : n} (hi : i ∈ (C : Finset n)) (hk : k ∈ (C : Finset n)) : P i k = splitV P C k := by
  rw [splitV_apply, if_pos hk, ← apply_eq_diag hP hPP (eq_classOf_of_mem hP hPP C.2 hi).1]
  rw [← mem_classOf, (eq_classOf_of_mem hP hPP C.2 hi).2]
  exact hk

/-- `ν_C` is positive on `C`. -/
theorem splitV_pos (hP : P ∈ rowStochastic K n) (hPP : P * P = P) (C : closedClasses P)
    {k : n} (hk : k ∈ (C : Finset n)) : 0 < splitV P C k := by
  rw [splitV_apply, if_pos hk]
  exact (eq_classOf_of_mem hP hPP C.2 hk).1

omit [IsStrictOrderedRing K] in
/-- `ν_C` vanishes off `C`. -/
theorem splitV_eq_zero (C : closedClasses P) {k : n} (hk : k ∉ (C : Finset n)) :
    splitV P C k = 0 := by
  rw [splitV_apply, if_neg hk]

/-- `ν_C` is a probability vector. -/
theorem sum_splitV (hP : P ∈ rowStochastic K n) (hPP : P * P = P) (C : closedClasses P) :
    ∑ k, splitV P C k = 1 := by
  obtain ⟨j, hj⟩ := exists_mem_of_mem_closedClasses C.2
  rw [Finset.sum_congr rfl fun k _ => splitV_apply_eq hP hPP C hj k]
  exact sum_row_of_mem_rowStochastic hP j

/-- `ν_C` is stationary: `ν_C P = ν_C`. -/
theorem vecMul_splitV (hP : P ∈ rowStochastic K n) (hPP : P * P = P) (C : closedClasses P) :
    splitV P C ᵥ* P = splitV P C := by
  obtain ⟨j, hj⟩ := exists_mem_of_mem_closedClasses C.2
  have hrow : splitV P C = P j := funext (splitV_apply_eq hP hPP C hj)
  rw [hrow]
  funext k
  simp only [vecMul, dotProduct]
  exact sum_mul_apply hPP j k

/-- `ν_C` is the only stationary vector of total mass one supported in `C`; no sign
condition is needed. -/
theorem eq_splitV_of_stationary (hP : P ∈ rowStochastic K n) (hPP : P * P = P)
    (C : closedClasses P) {x : n → K} (hsupp : ∀ k, k ∉ (C : Finset n) → x k = 0)
    (hsum : ∑ k, x k = 1) (hx : x ᵥ* P = x) : x = splitV P C := by
  funext k
  calc x k = (x ᵥ* P) k := by rw [hx]
    _ = ∑ m, x m * splitV P C k := by
        simp only [vecMul, dotProduct]
        refine Finset.sum_congr rfl fun m _ => ?_
        by_cases hm : m ∈ (C : Finset n)
        · rw [splitV_apply_eq hP hPP C hm]
        · rw [hsupp m hm, zero_mul, zero_mul]
    _ = splitV P C k := by rw [← Finset.sum_mul, hsum, one_mul]

/-- Every row restricted to a closed class `C` (in particular every transient row) is the
multiple `U_{iC} ν_C`. -/
theorem apply_eq_splitU_mul_splitV (hP : P ∈ rowStochastic K n) (hPP : P * P = P)
    (C : closedClasses P) {k : n} (hk : k ∈ (C : Finset n)) (i : n) :
    P i k = splitU P i C * splitV P C k := by
  obtain ⟨hkk, hCk⟩ := eq_classOf_of_mem hP hPP C.2 hk
  rw [apply_eq_mass_mul hP hPP i k, splitU_apply, splitV_apply, if_pos hk, hCk]

/-- Transient states (in no closed class) have vanishing columns; in particular the transient
block `T_0` is zero. -/
theorem apply_eq_zero_of_transient (hP : P ∈ rowStochastic K n) (hPP : P * P = P) {j : n}
    (hj : ∀ C ∈ closedClasses P, j ∉ C) (i : n) : P i j = 0 := by
  refine apply_eq_zero_of_diag_eq_zero hP hPP ?_ i
  refine le_antisymm (not_lt.1 fun hjj => ?_) (nonneg_of_mem_rowStochastic hP)
  exact hj _ (classOf_mem_closedClasses hjj) (self_mem_classOf hjj)

/-- `markov:lem:splitting`, `P = UV` for the canonical choice. -/
theorem splitU_mul_splitV (hP : P ∈ rowStochastic K n) (hPP : P * P = P) :
    splitU P * splitV P = P := by
  ext i k
  rw [mul_apply]
  by_cases hk : 0 < P k k
  · rw [Finset.sum_eq_single ⟨classOf P k, classOf_mem_closedClasses hk⟩]
    · rw [splitU_apply, splitV_apply, if_pos (self_mem_classOf hk),
        apply_eq_mass_mul hP hPP i k]
    · intro D _ hD
      rw [splitV_apply, if_neg, mul_zero]
      intro hkD
      exact hD (Subtype.ext (eq_classOf_of_mem hP hPP D.2 hkD).2.symm)
    · intro h
      exact absurd (mem_univ _) h
  · have hk0 : P k k = 0 := le_antisymm (not_lt.1 hk) (nonneg_of_mem_rowStochastic hP)
    rw [apply_eq_zero_of_diag_eq_zero hP hPP hk0 i]
    refine Finset.sum_eq_zero fun D _ => ?_
    rw [splitV_apply, hk0, ite_self, mul_zero]

/-- The row of `U` at a state of the closed class `C` is the coordinate row of `C`. -/
theorem splitU_apply_of_mem (hP : P ∈ rowStochastic K n) (hPP : P * P = P)
    (C : closedClasses P) {k : n} (hk : k ∈ (C : Finset n)) (D : closedClasses P) :
    splitU P k D = if C = D then 1 else 0 := by
  obtain ⟨hkk, hC⟩ := eq_classOf_of_mem hP hPP C.2 hk
  rw [splitU_apply]
  split_ifs with hCD
  · subst hCD
    rw [← hC, classOf, Finset.sum_filter, ← sum_row_of_mem_rowStochastic hP k]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with h
    · rfl
    · exact (le_antisymm (not_lt.1 h) (nonneg_of_mem_rowStochastic hP)).symm
  · refine Finset.sum_eq_zero fun m hm => ?_
    by_contra hkm
    have hkm' : 0 < P k m := lt_of_le_of_ne (nonneg_of_mem_rowStochastic hP) (Ne.symm hkm)
    apply hCD
    apply Subtype.ext
    rw [← (eq_classOf_of_mem hP hPP D.2 hm).2, ← hC]
    exact (classOf_eq hP hPP hkk hkm').symm

/-- `markov:lem:splitting`, `VU = I` for the canonical choice. -/
theorem splitV_mul_splitU (hP : P ∈ rowStochastic K n) (hPP : P * P = P) :
    splitV P * splitU P = 1 := by
  ext C D
  rw [mul_apply, one_apply]
  have h : ∀ k, splitV P C k * splitU P k D = splitV P C k * (if C = D then 1 else 0) := by
    intro k
    by_cases hk : k ∈ (C : Finset n)
    · rw [splitU_apply_of_mem hP hPP C hk D]
    · rw [splitV_apply, if_neg hk, zero_mul, zero_mul]
  rw [Finset.sum_congr rfl fun k _ => h k, ← Finset.sum_mul, sum_splitV hP hPP, one_mul]

/-- The rows of the canonical `U` sum to one. -/
theorem sum_splitU (hP : P ∈ rowStochastic K n) (hPP : P * P = P) (i : n) :
    ∑ C, splitU P i C = 1 := by
  rw [← sum_row_of_mem_rowStochastic hP i]
  simp only [splitU_apply]
  rw [Finset.sum_congr rfl fun (C : closedClasses P) _ =>
    (Finset.sum_ite_mem_eq (C : Finset n) fun k => P i k).symm,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : 0 < P k k
  · rw [Finset.sum_eq_single ⟨classOf P k, classOf_mem_closedClasses hk⟩]
    · rw [if_pos (self_mem_classOf hk)]
    · intro D _ hD
      rw [if_neg]
      intro hkD
      exact hD (Subtype.ext (eq_classOf_of_mem hP hPP D.2 hkD).2.symm)
    · intro h
      exact absurd (mem_univ _) h
  · rw [apply_eq_zero_of_diag_eq_zero hP hPP
      (le_antisymm (not_lt.1 hk) (nonneg_of_mem_rowStochastic hP)) i]
    simp

/-- `markov:lem:splitting`, rank count: the number of closed classes is `rank P`. -/
theorem card_closedClasses (hP : P ∈ rowStochastic K n) (hPP : P * P = P) :
    (closedClasses P).card = P.rank := by
  apply le_antisymm
  · have h1 : (1 : Matrix (closedClasses P) (closedClasses P) K) = splitV P * P * splitU P :=
      calc (1 : Matrix (closedClasses P) (closedClasses P) K) = splitV P * splitU P :=
            (splitV_mul_splitU hP hPP).symm
        _ = (splitV P * splitU P) * (splitV P * splitU P) := by
            rw [splitV_mul_splitU hP hPP, Matrix.one_mul]
        _ = splitV P * (splitU P * splitV P) * splitU P := by simp only [Matrix.mul_assoc]
        _ = splitV P * P * splitU P := by rw [splitU_mul_splitV hP hPP]
    calc (closedClasses P).card
        = (1 : Matrix (closedClasses P) (closedClasses P) K).rank := by
          rw [rank_one, Fintype.card_coe]
      _ = (splitV P * P * splitU P).rank := by rw [← h1]
      _ ≤ (splitV P * P).rank := rank_mul_le_left _ _
      _ ≤ P.rank := rank_mul_le_right _ _
  · calc P.rank = (splitU P * splitV P).rank := by rw [splitU_mul_splitV hP hPP]
      _ ≤ (splitU P).rank := rank_mul_le_left _ _
      _ ≤ Fintype.card (closedClasses P) := rank_le_card_width _
      _ = (closedClasses P).card := Fintype.card_coe _

/-- `markov:lem:splitting`: a row-stochastic idempotent `P` of rank `p` factors as `P = UV`
with nonnegative row-stochastic `U ∈ K^{n × p}`, `V ∈ K^{p × n}` and `VU = I_p`. The proof
takes the canonical `splitU`, `splitV` reindexed along an ordering of the closed classes. -/
theorem exists_splitting (hP : P ∈ rowStochastic K n) (hPP : P * P = P) :
    ∃ (U : Matrix n (Fin P.rank) K) (V : Matrix (Fin P.rank) n K),
      (∀ i a, 0 ≤ U i a) ∧ (∀ a j, 0 ≤ V a j) ∧ (∀ i, ∑ a, U i a = 1) ∧
      (∀ a, ∑ j, V a j = 1) ∧ P = U * V ∧ V * U = 1 := by
  let e : closedClasses P ≃ Fin P.rank :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, card_closedClasses hP hPP])
  refine ⟨(splitU P).submatrix id e.symm, (splitV P).submatrix e.symm id,
    fun i a => splitU_nonneg hP _ _, fun a j => splitV_nonneg hP _ _, fun i => ?_,
    fun a => sum_splitV hP hPP _, ?_, ?_⟩
  · simp only [submatrix_apply, id]
    rw [e.symm.sum_comp (splitU P i)]
    exact sum_splitU hP hPP i
  · rw [submatrix_mul_equiv, splitU_mul_splitV hP hPP, submatrix_id_id]
  · rw [← submatrix_mul _ _ _ _ _ Function.bijective_id, splitV_mul_splitU hP hPP,
      submatrix_one_equiv]

/-- `markov:lem:splitting`, the canonical choice in one statement. The index set of
`splitU`, `splitV` is exactly the set of closed communicating classes of `P`. Each row `ν_C`
of `splitV` is positive exactly on `C`, is a stationary probability vector, and is the only
stationary vector of mass one supported in `C`. `splitU i C` is the mass that row `i`
assigns to `C`. Both factors are nonnegative and row-stochastic, `P = UV`, `VU = I`, and the
number of classes is `rank P`. -/
theorem canonical_splitting (hP : P ∈ rowStochastic K n) (hPP : P * P = P) :
    (∀ C : Finset n, C ∈ closedClasses P ↔ IsClosedCommClass P (C : Set n)) ∧
    (∀ C : closedClasses P, (∀ k, k ∈ (C : Finset n) ↔ 0 < splitV P C k) ∧
      (∀ k, 0 ≤ splitV P C k) ∧ ∑ k, splitV P C k = 1 ∧ splitV P C ᵥ* P = splitV P C ∧
      ∀ x : n → K, (∀ k, k ∉ (C : Finset n) → x k = 0) → ∑ k, x k = 1 → x ᵥ* P = x →
        x = splitV P C) ∧
    (∀ i (C : closedClasses P), splitU P i C = ∑ k ∈ (C : Finset n), P i k) ∧
    (∀ i C, 0 ≤ splitU P i C) ∧ (∀ i, ∑ C, splitU P i C = 1) ∧
    P = splitU P * splitV P ∧ splitV P * splitU P = 1 ∧ (closedClasses P).card = P.rank := by
  refine ⟨fun C => mem_closedClasses_iff hP hPP, fun C => ⟨fun k => ⟨splitV_pos hP hPP C,
    fun hk => ?_⟩, splitV_nonneg hP C, sum_splitV hP hPP C, vecMul_splitV hP hPP C,
    fun x hsupp hsum hx => eq_splitV_of_stationary hP hPP C hsupp hsum hx⟩,
    splitU_apply, splitU_nonneg hP, sum_splitU hP hPP, (splitU_mul_splitV hP hPP).symm,
    splitV_mul_splitU hP hPP, card_closedClasses hP hPP⟩
  by_contra hkC
  rw [splitV_eq_zero C hkC] at hk
  exact lt_irrefl _ hk

end

end Surreal.StochasticIdempotent
