import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.HahnSeries.Lex
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.Data.Real.Basic
import Surreal.Algebra.MarkovResolvent

/-!
# The directed matrix-forest identity

This file proves `markov:prop:forest` of
`docs/surreal/markov-generators-at-every-scale/article.tex` in full, with all of
`markov:eq:forest-det`, `markov:eq:forest-adj`, `markov:eq:forest-resolvent` and
`markov:eq:forest-rows-trace`.

**Model.** The vertices form a finite type `n`, nonempty for the `D(s)`/`N(s)` forms and the
resolvent statements, and the rates are any matrix `q : n → n → R`. `rowLaplacian q` is the row
Laplacian `markov:eq:laplacian`
(`L_ij = -q_ij` for `i ≠ j`, `L_ii = ∑_{j ≠ i} q_ij`), and the diagonal of `q` is ignored. An
in-forest is a parent map `φ : n → Option n`: `φ i = some j` is the edge `i → j` and
`φ i = none` makes `i` a root. The map must satisfy `IsInForest`, meaning that following
edges from every vertex reaches a root. Then `forests k` is `𝓕_k`, `weight q φ` is `q(f)` and
`IsRootOf φ i j` says `r_f(i) = j`. `forestCoeff`, `forestMatrix`, `forestDenom` and
`forestNumer` are `σ_k`, `F_k`, `D(s)` and `N(s)` of `markov:eq:forest-coefficients`,
`markov:eq:forest-det` and `markov:eq:forest-adj`, with `d = n - 1`. Forests are taken in the
complete directed graph. When `q` vanishes on the non-edges `i ≠ j` of the source's graph `E`,
a forest that uses a missing edge has weight zero, so these sums equal the source's sums over
the forests of `E` (`forestCoeff_eq_sum_subgraph`, `forestMatrix_eq_sum_subgraph`).

**Identities over any commutative ring.** `det_eq_mul_forestDenom` gives `markov:eq:forest-det`,
`det(sI + L) = sD(s)`, and `adjugate_eq_forestNumer` gives `markov:eq:forest-adj`,
`adj(sI + L) = N(s)`. Both hold for every `s` and every family of rates in every commutative
ring. Taking `R` to be a polynomial ring gives the polynomial identities with integer
coefficients of the source, so no characteristic-zero or specialization argument is needed.
The root-count forms are `det_smul_one_add_rowLaplacian` and
`adjugate_smul_one_add_rowLaplacian`. The proof is the cycle-cancellation argument. Row `k` of
`sI + L` is `s e_k + ∑_p q_kp (e_k - e_p)`. Multilinear expansion (`det_of_sum`) turns
`det(sI + L)` into a sum over all parent maps `φ` of `det(I - A_φ)`, which is `1` for an
in-forest (triangular after ordering vertices by depth) and `0` otherwise (the indicator of
the vertices that never reach a root is a kernel vector). For the adjugate, row `j` is
replaced by `e_i`. The determinant is unchanged when the root `j` is reached from `i`, because
the path rows telescope to `e_i - e_j`. It vanishes otherwise, because the indicator of the
tree of `j` is then a kernel vector.

**`markov:eq:forest-rows-trace`.** `F_k𝟙 = σ_k𝟙` (`forestMatrix_mulVec_one`),
`tr F_k = (n - k)σ_k` (`trace_forestMatrix`), `F_0 = I` and `σ_0 = 1`.

**Resolvent.** Over a field, `R_L(s) = N(s)/D(s)` whenever `s ≠ 0` and `D(s) ≠ 0`
(`resolvent_eq_forest`). Over a linearly ordered field with nonnegative off-diagonal rates and
`s > 0`, `D(s) ≥ s^d > 0` (`pow_le_forestDenom`, `forestDenom_pos`), so
`markov:eq:forest-resolvent` holds (`resolvent_eq_div`). There `R_L(s)` is entrywise
nonnegative (`resolvent_nonneg`), row-stochastic (`sum_resolvent`) and has entries in `[0, 1]`
(`resolvent_le_one`), with no irreducibility assumption, as in the remark after the
proposition. Row sums are derived from `L𝟙 = 0`. If the graph of positive rates is strongly
connected, every entry is strictly positive (`resolvent_pos`): a shortest-path parent map is a
spanning in-tree rooted at `j` (`exists_spanning_inTree`), and it contributes to `N(s)_ij`. In
`F = ℝ((t^Γ))`, elements of `[0, 1]` have nonnegative valuation, so the entries lie in `𝒪`
(`orderTop_resolvent_nonneg`). No separate residue lemma is stated: the residue of an element
of `𝒪` is its `t^0` coefficient.

Two points of the prose around the proposition are not stated: that every `σ_k`,
`0 ≤ k ≤ d`, is positive under strong connectivity (not formalized), and the identities as
integer polynomials over `MvPolynomial _ ℤ` (not stated separately; they are the instance of the
ring-generic identities at that ring).

Nothing of `markov:prop:forest` is pending. The results that use it (`markov:thm:leading`,
`markov:prop:remainder`, `markov:thm:stability`, and the `IsCrossover` hypotheses of
`Surreal/Algebra/MarkovEffective.lean`) are not addressed here.
-/

namespace Surreal.MarkovForest

open Matrix Finset

noncomputable section

variable {n : Type*}

section Combinatorics

/-- One step along a parent map `φ : n → Option n`. The value `none` means that a root has
been reached; `φ i = some j` records the edge `i → j`. -/
def step (φ : n → Option n) (o : Option n) : Option n :=
  o.bind φ

/-- Following the edges of `φ` from `i` reaches a root. -/
def Terminates (φ : n → Option n) (i : n) : Prop :=
  ∃ m, (step φ)^[m] (some i) = none

/-- `φ` is an in-forest: every nonroot vertex has exactly one outgoing edge (its parent), and
following outgoing edges from any vertex leads to a root. -/
def IsInForest (φ : n → Option n) : Prop :=
  ∀ i, Terminates φ i

/-- Following the edges of `φ` from `i` passes through `j`. -/
def Reaches (φ : n → Option n) (i j : n) : Prop :=
  ∃ m, (step φ)^[m] (some i) = some j

/-- `j` is the root `r_φ(i)` reached from `i`. -/
def IsRootOf (φ : n → Option n) (i j : n) : Prop :=
  Reaches φ i j ∧ φ j = none

variable {φ : n → Option n}

theorem iterate_step_none (φ : n → Option n) (m : ℕ) : (step φ)^[m] none = none :=
  Function.iterate_fixed rfl m

theorem iterate_succ_step (φ : n → Option n) (m : ℕ) (i : n) :
    (step φ)^[m + 1] (some i) = (step φ)^[m] (φ i) :=
  Function.iterate_succ_apply _ _ _

theorem terminates_of_eq_none {k : n} (hk : φ k = none) : Terminates φ k :=
  ⟨1, hk⟩

theorem terminates_iff {k p : n} (hk : φ k = some p) : Terminates φ k ↔ Terminates φ p := by
  constructor
  · rintro ⟨m, hm⟩
    cases m with
    | zero => exact absurd hm (Option.some_ne_none k)
    | succ m => exact ⟨m, by rwa [iterate_succ_step, hk] at hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨m + 1, by rwa [iterate_succ_step, hk]⟩

theorem reaches_refl (φ : n → Option n) (j : n) : Reaches φ j j :=
  ⟨0, rfl⟩

theorem eq_of_reaches_of_eq_none {k j : n} (hk : φ k = none) (h : Reaches φ k j) : k = j := by
  obtain ⟨m, hm⟩ := h
  cases m with
  | zero => exact Option.some_injective _ hm
  | succ m =>
    rw [iterate_succ_step, hk, iterate_step_none] at hm
    exact absurd hm.symm (Option.some_ne_none j)

theorem reaches_iff {k p j : n} (hk : φ k = some p) (hkj : k ≠ j) :
    Reaches φ k j ↔ Reaches φ p j := by
  constructor
  · rintro ⟨m, hm⟩
    cases m with
    | zero => exact absurd (Option.some_injective _ hm) hkj
    | succ m => exact ⟨m, by rwa [iterate_succ_step, hk] at hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨m + 1, by rwa [iterate_succ_step, hk]⟩

theorem terminates_of_isRootOf {i j : n} (h : IsRootOf φ i j) : Terminates φ i := by
  obtain ⟨⟨m, hm⟩, hj⟩ := h
  exact ⟨m + 1, by rw [Function.iterate_succ_apply', hm]; exact hj⟩

/-- An in-forest has no loops. -/
theorem ne_of_isInForest (hφ : IsInForest φ) {k p : n} (hk : φ k = some p) : k ≠ p := by
  rintro rfl
  obtain ⟨m, hm⟩ := hφ k
  rw [Function.iterate_fixed (f := step φ) (x := some k) hk m] at hm
  exact Option.some_ne_none k hm

/-- A nonempty in-forest has a root. -/
theorem exists_eq_none [Nonempty n] (hφ : IsInForest φ) : ∃ k, φ k = none := by
  by_contra h
  push Not at h
  have key : ∀ m (k : n), (step φ)^[m] (some k) ≠ none := by
    intro m
    induction m with
    | zero => exact fun k => Option.some_ne_none k
    | succ m ih =>
      intro k
      obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp (h k)
      rw [iterate_succ_step, hp]
      exact ih p
  obtain ⟨k⟩ := ‹Nonempty n›
  obtain ⟨m, hm⟩ := hφ k
  exact key m k hm

/-- The empty forest. -/
theorem isInForest_none : IsInForest (fun _ : n => (none : Option n)) :=
  fun _ => ⟨1, rfl⟩

theorem reaches_of_eq_some {k p j : n} (hk : φ k = some p) (h : Reaches φ p j) :
    Reaches φ k j := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m + 1, by rwa [iterate_succ_step, hk]⟩

/-- Every vertex from which a root is reached has a root `r_φ(i)`. -/
theorem exists_isRootOf {i : n} (h : Terminates φ i) : ∃ j, IsRootOf φ i j := by
  obtain ⟨m, hm⟩ := h
  induction m generalizing i with
  | zero => exact absurd hm (Option.some_ne_none i)
  | succ m ih =>
    rw [iterate_succ_step] at hm
    cases hi : φ i with
    | none => exact ⟨i, reaches_refl φ i, hi⟩
    | some p =>
      rw [hi] at hm
      obtain ⟨j, hj, hjn⟩ := ih hm
      exact ⟨j, reaches_of_eq_some hi hj, hjn⟩

/-- The root reached from a vertex is unique. -/
theorem eq_of_isRootOf {i j j' : n} (h : IsRootOf φ i j) (h' : IsRootOf φ i j') : j = j' := by
  obtain ⟨⟨a, ha⟩, hj⟩ := h
  obtain ⟨⟨b, hb⟩, hj'⟩ := h'
  rcases le_total a b with hab | hab
  · refine eq_of_reaches_of_eq_none hj ⟨b - a, ?_⟩
    rw [← ha, ← Function.iterate_add_apply, Nat.sub_add_cancel hab, hb]
  · refine (eq_of_reaches_of_eq_none hj' ⟨a - b, ?_⟩).symm
    rw [← hb, ← Function.iterate_add_apply, Nat.sub_add_cancel hab, ha]

theorem isRootOf_self_iff {i : n} : IsRootOf φ i i ↔ φ i = none :=
  ⟨fun h => h.2, fun h => ⟨reaches_refl φ i, h⟩⟩

/-- Walks of length `m` from a vertex to `j` along a relation `r`. -/
def WalkTo (r : n → n → Prop) (j : n) : ℕ → n → Prop
  | 0, i => i = j
  | m + 1, i => ∃ k, r i k ∧ WalkTo r j m k

theorem exists_walkTo {r : n → n → Prop} {i j : n} (h : Relation.ReflTransGen r i j) :
    ∃ m, WalkTo r j m i := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, rfl⟩
  | head hab _ ih =>
    obtain ⟨m, hm⟩ := ih
    exact ⟨m + 1, _, hab, hm⟩

/-- If every vertex reaches `j` along `r`, then a shortest-path parent map is an in-forest
using only edges of `r` whose only root is `j`: a spanning in-tree rooted at `j`. -/
theorem exists_spanning_inTree {r : n → n → Prop} (j : n)
    (hconn : ∀ i, Relation.ReflTransGen r i j) :
    ∃ φ : n → Option n, IsInForest φ ∧ (∀ i, IsRootOf φ i j) ∧
      ∀ k p, φ k = some p → r k p := by
  classical
  have hw : ∀ i, ∃ m, WalkTo r j m i := fun i => exists_walkTo (hconn i)
  have hpar : ∀ i, i ≠ j → ∃ p, r i p ∧ Nat.find (hw p) < Nat.find (hw i) := by
    intro i hij
    have hspec := Nat.find_spec (hw i)
    obtain ⟨m, hm⟩ : ∃ m, Nat.find (hw i) = m + 1 := Nat.exists_eq_succ_of_ne_zero fun h0 => by
      rw [h0] at hspec
      exact hij hspec
    rw [hm] at hspec
    obtain ⟨p, hp, hpm⟩ := hspec
    exact ⟨p, hp, (Nat.find_min' (hw p) hpm).trans_lt (by omega)⟩
  choose par hpar using hpar
  let φ : n → Option n := fun i => if h : i = j then none else some (par i h)
  have hφj : φ j = none := dif_pos rfl
  have hroot : ∀ d i, Nat.find (hw i) = d → Reaches φ i j := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro i hd
      by_cases hij : i = j
      · subst hij
        exact reaches_refl φ i
      · exact (reaches_iff (dif_neg hij : φ i = some (par i hij)) hij).mpr
          (ih _ ((hpar i hij).2.trans_eq hd) _ rfl)
  refine ⟨φ, fun i => terminates_of_isRootOf ⟨hroot _ i rfl, hφj⟩,
    fun i => ⟨hroot _ i rfl, hφj⟩, fun k p hk => ?_⟩
  by_cases hkj : k = j
  · rw [hkj, hφj] at hk
    exact absurd hk.symm (Option.some_ne_none p)
  · rw [show φ k = some (par k hkj) from dif_neg hkj, Option.some.injEq] at hk
    exact hk ▸ (hpar k hkj).1

end Combinatorics

section Algebra

variable {R : Type*} [CommRing R] [Fintype n] [DecidableEq n] {φ : n → Option n}

/-- The row Laplacian `markov:eq:laplacian`: `L_ij = -q_ij` for `i ≠ j` and
`L_ii = ∑_{j ≠ i} q_ij`. The diagonal rates `q_ii` are never used. -/
def rowLaplacian (q : n → n → R) : Matrix n n R :=
  Matrix.of fun i j => if i = j then ∑ k ∈ univ.erase i, q i k else -q i j

/-- The number of edges of a parent map. -/
def numEdges (φ : n → Option n) : ℕ :=
  (univ.filter fun i => φ i ≠ none).card

/-- The number of roots of a parent map. -/
def numRoots (φ : n → Option n) : ℕ :=
  (univ.filter fun i => φ i = none).card

omit [DecidableEq n] in
theorem numRoots_add_numEdges (φ : n → Option n) : numRoots φ + numEdges φ = Fintype.card n := by
  rw [numRoots, numEdges, card_filter_add_card_filter_not, card_univ]

/-- The forest weight `q(f) = ∏_{e ∈ f} q_e`; the empty forest has weight one. -/
def weight (q : n → n → R) (φ : n → Option n) : R :=
  ∏ i, (φ i).elim 1 (q i)

open Classical in
/-- All in-forests on the vertex set `n`. -/
def allForests : Finset (n → Option n) :=
  univ.filter IsInForest

/-- `𝓕_k`: the in-forests with `k` edges. -/
def forests (k : ℕ) : Finset (n → Option n) :=
  allForests.filter fun φ => numEdges φ = k

/-- The scalar forest coefficient `σ_k = ∑_{f ∈ 𝓕_k} q(f)` of
`markov:eq:forest-coefficients`. -/
def forestCoeff (q : n → n → R) (k : ℕ) : R :=
  ∑ φ ∈ forests k, weight q φ

open Classical in
/-- The matrix forest coefficient `F_k(i,j) = ∑_{f ∈ 𝓕_k, r_f(i) = j} q(f)` of
`markov:eq:forest-coefficients`. -/
def forestMatrix (q : n → n → R) (k : ℕ) : Matrix n n R :=
  Matrix.of fun i j => ∑ φ ∈ (forests k).filter fun φ => IsRootOf φ i j, weight q φ

/-- The forest denominator `D(s) = ∑_{k=0}^{d} σ_k s^{d-k}`, with `d = n - 1`. -/
def forestDenom (q : n → n → R) (s : R) : R :=
  ∑ k ∈ range (Fintype.card n - 1 + 1), forestCoeff q k * s ^ (Fintype.card n - 1 - k)

/-- The forest numerator `N(s) = ∑_{k=0}^{d} F_k s^{d-k}`, with `d = n - 1`. -/
def forestNumer (q : n → n → R) (s : R) : Matrix n n R :=
  ∑ k ∈ range (Fintype.card n - 1 + 1), s ^ (Fintype.card n - 1 - k) • forestMatrix q k

/-- The coefficient of the summand `o` in the expansion of row `k` of `sI + L`. -/
def rowCoeff (s : R) (q : n → n → R) (k : n) (o : Option n) : R :=
  o.elim s (q k)

/-- The vector of the summand `o` in the expansion of row `k` of `sI + L`: `e_k` for
`o = none` and `e_k - e_p` for `o = some p`. -/
def rowVec (k : n) (o : Option n) : n → R :=
  Pi.single k 1 - o.elim 0 fun p => Pi.single p 1

/-- The matrix `I - A_φ` whose row `k` is `rowVec k (φ k)`. -/
def edgeMatrix (φ : n → Option n) : Matrix n n R :=
  Matrix.of fun k => rowVec k (φ k)

/-- Each row of `sI + L` is `s e_k + ∑_p q_kp (e_k - e_p)`. -/
theorem smul_one_add_rowLaplacian (s : R) (q : n → n → R) :
    s • (1 : Matrix n n R) + rowLaplacian q =
      Matrix.of fun k => ∑ o, rowCoeff s q k o • rowVec k o := by
  ext k l
  have hsum : ∑ x, q k x * (Pi.single x (1 : R) : n → R) l = q k l := by
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  by_cases hkl : k = l
  · subst hkl
    simp [rowLaplacian, rowCoeff, rowVec, Fintype.sum_option, mul_sub, Finset.sum_sub_distrib,
      Finset.sum_erase_eq_sub, hsum]
  · simp [rowLaplacian, rowCoeff, rowVec, Fintype.sum_option, hsum, hkl, Ne.symm hkl]

/-- Multilinear expansion of a determinant whose rows are finite sums. -/
theorem det_of_sum (c : n → Option n → R) (v : n → Option n → n → R) :
    (Matrix.of fun k => ∑ o, c k o • v k o).det =
      ∑ φ : n → Option n, (∏ k, c k (φ k)) * (Matrix.of fun k => v k (φ k)).det := by
  change (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R) (fun k => ∑ o, c k o • v k o) =
    ∑ φ : n → Option n, (∏ k, c k (φ k)) *
      (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R) (fun k => v k (φ k))
  rw [← AlternatingMap.coe_multilinearMap, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]

omit [Fintype n] in
theorem edgeMatrix_apply (φ : n → Option n) (k l : n) :
    edgeMatrix (R := R) φ k l = (if k = l then 1 else 0) - if φ k = some l then 1 else 0 := by
  cases h : φ k with
  | none => simp [edgeMatrix, rowVec, h, Pi.single_apply, eq_comm]
  | some p => simp [edgeMatrix, rowVec, h, Pi.single_apply, eq_comm]

theorem edgeMatrix_mulVec (φ : n → Option n) (w : n → R) (k : n) :
    (edgeMatrix φ *ᵥ w) k = w k - (φ k).elim 0 w := by
  change rowVec k (φ k) ⬝ᵥ w = _
  cases φ k with
  | none => simp [rowVec]
  | some p => simp [rowVec, sub_dotProduct]

/-- A kernel vector with a unit coordinate forces a zero determinant, over any commutative
ring. -/
theorem det_eq_zero_of_mulVec_eq_zero {M : Matrix n n R} {w : n → R} (hw : M *ᵥ w = 0) {a : n}
    (ha : w a = 1) : M.det = 0 := by
  have h := congrArg (fun v => (adjugate M *ᵥ v) a) hw
  simp only [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec, Pi.smul_apply, ha,
    mulVec_zero, Pi.zero_apply, smul_eq_mul, mul_one] at h
  exact h

/-- A parent map with a vertex that never reaches a root has `det(I - A_φ) = 0`. -/
theorem det_edgeMatrix_eq_zero (hφ : ¬IsInForest φ) : (edgeMatrix (R := R) φ).det = 0 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, ¬Terminates φ a := by simpa [IsInForest] using hφ
  refine det_eq_zero_of_mulVec_eq_zero (w := fun k => if Terminates φ k then 0 else 1) ?_
    (a := a) (by simp [ha])
  funext k
  rw [edgeMatrix_mulVec, Pi.zero_apply]
  cases hk : φ k with
  | none => simp [terminates_of_eq_none hk]
  | some p => simp [terminates_iff hk]

/-- An in-forest has `det(I - A_φ) = 1`: ordering vertices by depth makes `I - A_φ`
triangular with unit diagonal. -/
theorem det_edgeMatrix_eq_one (hφ : IsInForest φ) : (edgeMatrix (R := R) φ).det = 1 := by
  classical
  let depth : n → ℕ := fun k => Nat.find (show ∃ m, (step φ)^[m] (some k) = none from hφ k)
  have hdepth : ∀ k p, φ k = some p → depth p < depth k := by
    intro k p hk
    have hspec := Nat.find_spec (show ∃ m, (step φ)^[m] (some k) = none from hφ k)
    obtain ⟨m, hm⟩ : ∃ m, depth k = m + 1 := Nat.exists_eq_succ_of_ne_zero fun h0 => by
      rw [show Nat.find _ = depth k from rfl, h0] at hspec
      exact Option.some_ne_none k hspec
    rw [show Nat.find _ = depth k from rfl, hm, iterate_succ_step, hk] at hspec
    exact (Nat.find_min' _ hspec).trans_lt (by omega)
  have htri : (edgeMatrix (R := R) φ).BlockTriangular fun k => OrderDual.toDual (depth k) := by
    intro k l hkl
    rw [OrderDual.toDual_lt_toDual] at hkl
    rw [edgeMatrix_apply, if_neg (by rintro rfl; exact lt_irrefl _ hkl),
      if_neg fun h => (hdepth k l h).not_gt hkl, sub_zero]
  rw [htri.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have hblock : (edgeMatrix (R := R) φ).toSquareBlock (fun k => OrderDual.toDual (depth k)) a
      = 1 := by
    ext ⟨x, hx⟩ ⟨y, hy⟩
    have hxy : depth x = depth y := OrderDual.toDual.injective (hx.trans hy.symm)
    have hne : ¬φ x = some y := fun h => (hdepth x y h).ne hxy.symm
    simp [toSquareBlock_def, edgeMatrix_apply, one_apply, hne]
  rw [hblock, det_one]

/-- Adding another row to row `j` does not change the determinant. -/
theorem det_updateRow_add_row (M : Matrix n n R) {j k : n} (hkj : k ≠ j) (v : n → R) :
    (M.updateRow j (v + M k)).det = (M.updateRow j v).det := by
  rw [det_updateRow_add, add_eq_left]
  exact det_zero_of_row_eq hkj (by rw [updateRow_ne hkj, updateRow_self])

/-- If `j` is a root reached from `i`, replacing row `j` of `I - A_φ` by `e_i` does not change
the determinant: `e_i - e_j` is the sum of the rows along the path from `i` to `j`. -/
theorem det_updateRow_edgeMatrix_of_reaches {i j : n} (hj : φ j = none) (h : Reaches φ i j) :
    ((edgeMatrix (R := R) φ).updateRow j (Pi.single i 1)).det = (edgeMatrix (R := R) φ).det := by
  obtain ⟨m, hm⟩ := h
  induction m generalizing i with
  | zero =>
    obtain rfl := Option.some_injective _ hm
    have hrow : edgeMatrix (R := R) φ i = Pi.single i 1 := by
      funext l
      simp [edgeMatrix, rowVec, hj]
    rw [← hrow, updateRow_eq_self]
  | succ m ih =>
    rw [iterate_succ_step] at hm
    cases hi : φ i with
    | none =>
      rw [hi, iterate_step_none] at hm
      exact absurd hm.symm (Option.some_ne_none j)
    | some p =>
      rw [hi] at hm
      have hij : i ≠ j := by
        rintro rfl
        rw [hj] at hi
        exact Option.some_ne_none p hi.symm
      have hrow : Pi.single i (1 : R) = Pi.single p 1 + edgeMatrix (R := R) φ i := by
        funext l
        simp [edgeMatrix, rowVec, hi]
      rw [hrow, det_updateRow_add_row _ hij, ih hm]

/-- If the root `j` is not reached from `i`, replacing row `j` of `I - A_φ` by `e_i` gives a
singular matrix: the indicator of the tree of `j` is a kernel vector. -/
theorem det_updateRow_edgeMatrix_of_not_reaches {i j : n} (hj : φ j = none)
    (h : ¬Reaches φ i j) : ((edgeMatrix (R := R) φ).updateRow j (Pi.single i 1)).det = 0 := by
  classical
  refine det_eq_zero_of_mulVec_eq_zero (w := fun k => if Reaches φ k j then 1 else 0) ?_
    (a := j) (by simp [reaches_refl])
  funext k
  rw [Pi.zero_apply]
  by_cases hkj : k = j
  · subst hkj
    simp [mulVec, updateRow_self, h]
  · have hk' : ((edgeMatrix (R := R) φ).updateRow j (Pi.single i 1) *ᵥ
        fun k => if Reaches φ k j then 1 else 0) k =
        (edgeMatrix (R := R) φ *ᵥ fun k => if Reaches φ k j then 1 else 0) k := by
      simp only [mulVec, updateRow_ne hkj]
    rw [hk', edgeMatrix_mulVec]
    cases hk : φ k with
    | none =>
      have hnr : ¬Reaches φ k j := fun h' => hkj (eq_of_reaches_of_eq_none hk h')
      simp [hnr]
    | some p => simp [reaches_iff hk hkj]

omit [Fintype n] [DecidableEq n] in
theorem prod_rowCoeff (s : R) (q : n → n → R) (φ : n → Option n) (S : Finset n) :
    ∏ k ∈ S, rowCoeff s q k (φ k) =
      s ^ (S.filter fun k => φ k = none).card * ∏ k ∈ S, (φ k).elim 1 (q k) := by
  rw [← prod_const, prod_filter, ← prod_mul_distrib]
  refine prod_congr rfl fun k _ => ?_
  cases φ k <;> simp [rowCoeff]

theorem mem_allForests : φ ∈ allForests ↔ IsInForest φ := by
  classical
  rw [allForests, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ φ, h⟩⟩

/-- `markov:eq:forest-det` in root-count form: over any commutative ring,
`det(sI + L) = ∑_f q(f) s^{#roots(f)}`, the sum running over all in-forests. -/
theorem det_smul_one_add_rowLaplacian (s : R) (q : n → n → R) :
    (s • (1 : Matrix n n R) + rowLaplacian q).det =
      ∑ φ ∈ allForests, weight q φ * s ^ numRoots φ := by
  classical
  rw [smul_one_add_rowLaplacian, det_of_sum, allForests, sum_filter]
  refine sum_congr rfl fun φ _ => ?_
  rw [show (Matrix.of fun k => rowVec k (φ k)) = edgeMatrix (R := R) φ from rfl, prod_rowCoeff]
  by_cases hφ : IsInForest φ
  · rw [if_pos hφ, det_edgeMatrix_eq_one hφ, mul_one, weight, numRoots, mul_comm]
  · rw [if_neg hφ, det_edgeMatrix_eq_zero hφ, mul_zero]

open Classical in
/-- `markov:eq:forest-adj` in root-count form: over any commutative ring,
`adj(sI + L)_{ij} = ∑_{f : r_f(i) = j} q(f) s^{#roots(f) - 1}`, the sum running over the
in-forests in which the root reached from `i` is `j`. -/
theorem adjugate_smul_one_add_rowLaplacian (s : R) (q : n → n → R) (i j : n) :
    adjugate (s • (1 : Matrix n n R) + rowLaplacian q) i j =
      ∑ φ ∈ allForests.filter fun φ => IsRootOf φ i j, weight q φ * s ^ (numRoots φ - 1) := by
  have hrows : (s • (1 : Matrix n n R) + rowLaplacian q).updateRow j (Pi.single i 1) =
      Matrix.of fun k => ∑ o, (if k = j then (if o = none then 1 else 0) else rowCoeff s q k o) •
        (if k = j then Pi.single i 1 else rowVec k o) := by
    rw [smul_one_add_rowLaplacian]
    ext k l
    by_cases hkj : k = j
    · subst hkj
      simp [Fintype.sum_option]
    · simp [hkj]
  rw [adjugate_apply, hrows, det_of_sum, allForests, filter_filter, sum_filter]
  refine sum_congr rfl fun φ _ => ?_
  have hmat : (Matrix.of fun k => if k = j then Pi.single i (1 : R) else rowVec k (φ k)) =
      (edgeMatrix (R := R) φ).updateRow j (Pi.single i 1) := by
    ext k l
    by_cases hkj : k = j
    · subst hkj
      simp
    · simp [hkj, edgeMatrix]
  rw [hmat, ← mul_prod_erase univ _ (mem_univ j), if_pos (rfl : j = j)]
  by_cases hj : φ j = none
  · rw [if_pos hj, one_mul, prod_congr rfl fun k hk => if_neg (ne_of_mem_erase hk),
      prod_rowCoeff]
    have hcard : ((univ.erase j).filter fun k => φ k = none).card = numRoots φ - 1 := by
      rw [filter_erase, card_erase_of_mem (mem_filter.mpr ⟨mem_univ j, hj⟩), numRoots]
    have hw : ∏ k ∈ univ.erase j, (φ k).elim 1 (q k) = weight q φ := by
      rw [weight, ← mul_prod_erase univ _ (mem_univ j), hj]
      exact (one_mul _).symm
    rw [hcard, hw]
    by_cases hr : Reaches φ i j
    · rw [det_updateRow_edgeMatrix_of_reaches hj hr]
      by_cases hφ : IsInForest φ
      · rw [det_edgeMatrix_eq_one hφ, mul_one, if_pos ⟨hφ, (⟨hr, hj⟩ : IsRootOf φ i j)⟩,
          mul_comm]
      · rw [det_edgeMatrix_eq_zero hφ, mul_zero, if_neg fun h => hφ h.1]
    · rw [det_updateRow_edgeMatrix_of_not_reaches hj hr, mul_zero,
        if_neg fun h => hr (show IsRootOf φ i j from h.2).1]
  · rw [if_neg hj, zero_mul, zero_mul, if_neg fun h => hj (show IsRootOf φ i j from h.2).2]

omit [DecidableEq n] in
/-- A nonempty in-forest has at most `d = n - 1` edges. -/
theorem numEdges_lt_card [Nonempty n] (hφ : IsInForest φ) : numEdges φ < Fintype.card n := by
  obtain ⟨k, hk⟩ := exists_eq_none hφ
  have h1 : 0 < numRoots φ := card_pos.mpr ⟨k, mem_filter.mpr ⟨mem_univ k, hk⟩⟩
  have h2 := numRoots_add_numEdges φ
  omega

theorem numEdges_mem_range [Nonempty n] (hφ : φ ∈ allForests) :
    numEdges φ ∈ range (Fintype.card n - 1 + 1) := by
  have := numEdges_lt_card (mem_allForests.mp hφ)
  rw [mem_range]
  omega

/-- `markov:eq:forest-det`: `det(sI + L) = s D(s)` with `D(s) = ∑_{k=0}^{d} σ_k s^{d-k}`, for
all rates and `s` in any commutative ring (a polynomial identity when `R` is a polynomial
ring). -/
theorem det_eq_mul_forestDenom [Nonempty n] (s : R) (q : n → n → R) :
    (s • (1 : Matrix n n R) + rowLaplacian q).det = s * forestDenom q s := by
  rw [det_smul_one_add_rowLaplacian, forestDenom, mul_sum,
    ← sum_fiberwise_of_maps_to fun φ hφ => numEdges_mem_range hφ]
  refine sum_congr rfl fun k _ => ?_
  rw [forestCoeff, forests, sum_mul, mul_sum]
  refine sum_congr rfl fun φ hφ => ?_
  obtain ⟨hφA, hk⟩ := mem_filter.mp hφ
  subst hk
  have h1 := numRoots_add_numEdges φ
  have h2 := numEdges_lt_card (mem_allForests.mp hφA)
  rw [show numRoots φ = Fintype.card n - 1 - numEdges φ + 1 by omega, pow_succ]
  ring

/-- `markov:eq:forest-adj`: `adj(sI + L) = N(s)` with `N(s) = ∑_{k=0}^{d} F_k s^{d-k}`, for
all rates and `s` in any commutative ring (a polynomial identity when `R` is a polynomial
ring). -/
theorem adjugate_eq_forestNumer [Nonempty n] (s : R) (q : n → n → R) :
    adjugate (s • (1 : Matrix n n R) + rowLaplacian q) = forestNumer q s := by
  classical
  ext i j
  rw [adjugate_smul_one_add_rowLaplacian, forestNumer, Matrix.sum_apply,
    ← sum_fiberwise_of_maps_to fun φ hφ => numEdges_mem_range (mem_filter.mp hφ).1]
  refine sum_congr rfl fun k _ => ?_
  rw [Matrix.smul_apply, forestMatrix, of_apply, smul_eq_mul, mul_sum, forests, filter_comm]
  refine sum_congr rfl fun φ hφ => ?_
  have hk : numEdges φ = k := by
    simp only [mem_filter] at hφ
    tauto
  subst hk
  have := numRoots_add_numEdges φ
  rw [show numRoots φ - 1 = Fintype.card n - 1 - numEdges φ by omega, mul_comm]

/-- The row Laplacian has zero row sums: `L𝟙 = 0`. -/
theorem rowLaplacian_mulVec_one (q : n → n → R) : rowLaplacian q *ᵥ (fun _ => 1) = 0 := by
  funext k
  simp only [mulVec, dotProduct, mul_one, Pi.zero_apply, rowLaplacian, of_apply]
  rw [← add_sum_erase univ _ (mem_univ k), if_pos (rfl : k = k),
    sum_congr rfl fun l hl => if_neg (ne_of_mem_erase hl).symm, sum_neg_distrib, add_neg_cancel]

omit [DecidableEq n] in
theorem numEdges_eq_zero_iff : numEdges φ = 0 ↔ φ = fun _ => none := by
  rw [numEdges, card_eq_zero, filter_eq_empty_iff]
  simp [funext_iff]

theorem forests_zero : forests (n := n) 0 = {fun _ => none} := by
  ext φ
  rw [forests, mem_filter, mem_allForests, numEdges_eq_zero_iff, mem_singleton]
  constructor
  · exact fun h => h.2
  · rintro rfl
    exact ⟨isInForest_none, rfl⟩

/-- `σ_0 = 1` (`markov:eq:forest-rows-trace`): only the empty forest has no edges. -/
theorem forestCoeff_zero (q : n → n → R) : forestCoeff q 0 = 1 := by
  rw [forestCoeff, forests_zero, sum_singleton, weight]
  exact prod_eq_one fun _ _ => rfl

/-- `F_0 = I` (`markov:eq:forest-rows-trace`). -/
theorem forestMatrix_zero (q : n → n → R) : forestMatrix q 0 = 1 := by
  ext i j
  have hroot : IsRootOf (fun _ : n => (none : Option n)) i j ↔ i = j :=
    ⟨fun h => eq_of_reaches_of_eq_none rfl h.1, fun h => h ▸ ⟨reaches_refl _ i, rfl⟩⟩
  have hw : weight q (fun _ : n => (none : Option n)) = 1 := prod_eq_one fun _ _ => rfl
  rw [forestMatrix, of_apply, forests_zero, one_apply, filter_singleton]
  by_cases hij : i = j
  · subst hij
    rw [if_pos (hroot.mpr rfl), sum_singleton, hw, if_pos rfl]
  · simp [hroot, hij]

/-- `markov:eq:forest-rows-trace`: every row of `F_k` sums to `σ_k`, since each forest has
exactly one root reached from `i`. -/
theorem forestMatrix_mulVec_one (q : n → n → R) (k : ℕ) :
    forestMatrix q k *ᵥ (fun _ => 1) = forestCoeff q k • fun _ => 1 := by
  classical
  funext i
  simp only [mulVec, dotProduct, mul_one, forestMatrix, of_apply, Pi.smul_apply, smul_eq_mul,
    forestCoeff]
  simp_rw [sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun φ hφ => ?_
  have hφ' : IsInForest φ := mem_allForests.mp (mem_filter.mp hφ).1
  obtain ⟨r, hr⟩ := exists_isRootOf (hφ' i)
  rw [sum_eq_single r (fun j _ hj => if_neg fun h => hj (eq_of_isRootOf h hr))
    (fun h => absurd (mem_univ r) h), if_pos hr]

/-- `markov:eq:forest-rows-trace`: `tr F_k = (n - k) σ_k`, since every forest in `𝓕_k` has
`n - k` roots. -/
theorem trace_forestMatrix (q : n → n → R) (k : ℕ) :
    (forestMatrix q k).trace = ((Fintype.card n - k : ℕ) : R) * forestCoeff q k := by
  classical
  simp only [Matrix.trace, diag_apply, forestMatrix, of_apply, forestCoeff]
  simp_rw [sum_filter]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun φ hφ => ?_
  have hk : numEdges φ = k := (mem_filter.mp hφ).2
  have hroots : numRoots φ = Fintype.card n - k := by
    have := numRoots_add_numEdges φ
    omega
  simp_rw [isRootOf_self_iff]
  rw [← sum_filter, sum_const, nsmul_eq_mul, ← hroots, numRoots]

omit [DecidableEq n] in
/-- A parent map using an edge outside a graph `E` off which `q` vanishes has weight zero. -/
theorem weight_eq_zero_of_not_subgraph {E : n → n → Prop} {q : n → n → R}
    (hq : ∀ i j, ¬E i j → q i j = 0) (h : ¬∀ i p, φ i = some p → E i p) : weight q φ = 0 := by
  push Not at h
  obtain ⟨i, p, hi, hE⟩ := h
  exact prod_eq_zero (mem_univ i) (by rw [hi]; exact hq i p hE)

omit [DecidableEq n] in
/-- An in-forest using an edge outside a graph `E` has weight zero as soon as `q` vanishes on
the non-edges `i ≠ j` of `E`; the diagonal rates are unconstrained, since forests have no
loops. -/
theorem weight_eq_zero_of_isInForest_of_not_subgraph {E : n → n → Prop} {q : n → n → R}
    (hq : ∀ i j, i ≠ j → ¬E i j → q i j = 0) (hφ : IsInForest φ)
    (h : ¬∀ i p, φ i = some p → E i p) : weight q φ = 0 := by
  push Not at h
  obtain ⟨i, p, hi, hE⟩ := h
  exact prod_eq_zero (mem_univ i) (by rw [hi]; exact hq i p (ne_of_isInForest hφ hi) hE)

open Classical in
/-- If `q` vanishes on the non-edges `i ≠ j` of the graph `E` of allowed edges, then `σ_k` is
the sum over the in-forests of `E` with `k` edges, as in the source. -/
theorem forestCoeff_eq_sum_subgraph {E : n → n → Prop} {q : n → n → R}
    (hq : ∀ i j, i ≠ j → ¬E i j → q i j = 0) (k : ℕ) :
    forestCoeff q k =
      ∑ φ ∈ (forests k).filter fun φ => ∀ i p, φ i = some p → E i p, weight q φ := by
  rw [forestCoeff, sum_filter]
  refine sum_congr rfl fun φ hφ => ?_
  split_ifs with h
  · rfl
  · exact weight_eq_zero_of_isInForest_of_not_subgraph hq
      (mem_allForests.mp (mem_filter.mp hφ).1) h

open Classical in
/-- If `q` vanishes on the non-edges `i ≠ j` of the graph `E` of allowed edges, then `F_k(i,j)`
is the sum over the in-forests of `E` with `k` edges and `r_f(i) = j`, as in the source. -/
theorem forestMatrix_eq_sum_subgraph {E : n → n → Prop} {q : n → n → R}
    (hq : ∀ i j, i ≠ j → ¬E i j → q i j = 0) (k : ℕ) (i j : n) :
    forestMatrix q k i j = ∑ φ ∈ ((forests k).filter fun φ => IsRootOf φ i j).filter
      fun φ => ∀ i p, φ i = some p → E i p, weight q φ := by
  rw [forestMatrix, of_apply, sum_filter (s := (forests k).filter fun φ => IsRootOf φ i j)]
  refine sum_congr rfl fun φ hφ => ?_
  split_ifs with h
  · rfl
  · exact weight_eq_zero_of_isInForest_of_not_subgraph hq
      (mem_allForests.mp (mem_filter.mp (mem_filter.mp hφ).1).1) h

end Algebra

section Field

variable {K : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- `markov:eq:forest-resolvent`: whenever `s ≠ 0` and `D(s) ≠ 0`, the normalized resolvent is
`R_L(s) = N(s)/D(s)`. -/
theorem resolvent_eq_forest [Nonempty n] (q : n → n → K) {s : K} (hs : s ≠ 0)
    (hD : forestDenom q s ≠ 0) :
    Markov.resolvent (rowLaplacian q) s = (forestDenom q s)⁻¹ • forestNumer q s := by
  apply Markov.resolvent_eq_of_mul_eq hs
  rw [Matrix.mul_smul, ← adjugate_eq_forestNumer, mul_adjugate, det_eq_mul_forestDenom,
    smul_smul, mul_comm s, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]

/-- Row sums of the normalized resolvent are one whenever it is defined. -/
theorem resolvent_mulVec_one (q : n → n → K) {s : K}
    (hdet : IsUnit (s • (1 : Matrix n n K) + rowLaplacian q).det) :
    Markov.resolvent (rowLaplacian q) s *ᵥ (fun _ => 1) = fun _ => 1 := by
  have hM : (s • (1 : Matrix n n K) + rowLaplacian q) *ᵥ (fun _ => (1 : K)) = s • fun _ => 1 := by
    rw [add_mulVec, rowLaplacian_mulVec_one, add_zero, smul_mulVec, one_mulVec]
  have h := congrArg ((s • (1 : Matrix n n K) + rowLaplacian q)⁻¹ *ᵥ ·) hM
  simp only [mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec, mulVec_smul] at h
  rw [Markov.resolvent, smul_mulVec]
  exact h.symm

end Field

section Ordered

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Fintype n]
  [DecidableEq n] {q : n → n → K} {φ : n → Option n}

omit [DecidableEq n] in
theorem weight_nonneg (hq : ∀ i j, i ≠ j → 0 ≤ q i j) (hφ : IsInForest φ) :
    0 ≤ weight q φ := by
  refine prod_nonneg fun k _ => ?_
  cases hk : φ k with
  | none => exact zero_le_one
  | some p => exact hq k p (ne_of_isInForest hφ hk)

theorem forestCoeff_nonneg (hq : ∀ i j, i ≠ j → 0 ≤ q i j) (k : ℕ) : 0 ≤ forestCoeff q k :=
  sum_nonneg fun _ hφ => weight_nonneg hq (mem_allForests.mp (mem_filter.mp hφ).1)

theorem forestMatrix_nonneg (hq : ∀ i j, i ≠ j → 0 ≤ q i j) (k : ℕ) (i j : n) :
    0 ≤ forestMatrix q k i j := by
  classical
  rw [forestMatrix, of_apply]
  exact sum_nonneg fun _ hφ =>
    weight_nonneg hq (mem_allForests.mp (mem_filter.mp (mem_filter.mp hφ).1).1)

/-- For nonnegative off-diagonal rates and `s ≥ 0`, `D(s) ≥ s^d`: the `k = 0` term of `D(s)` is
`s^d` and the other terms are nonnegative. -/
theorem pow_le_forestDenom (hq : ∀ i j, i ≠ j → 0 ≤ q i j) {s : K} (hs : 0 ≤ s) :
    s ^ (Fintype.card n - 1) ≤ forestDenom q s := by
  rw [forestDenom]
  calc s ^ (Fintype.card n - 1) = forestCoeff q 0 * s ^ (Fintype.card n - 1 - 0) := by
        rw [forestCoeff_zero, one_mul, Nat.sub_zero]
    _ ≤ _ := single_le_sum (f := fun k => forestCoeff q k * s ^ (Fintype.card n - 1 - k))
        (fun k _ => mul_nonneg (forestCoeff_nonneg hq k) (pow_nonneg hs _)) (by simp)

/-- For nonnegative off-diagonal rates and `s > 0`, the forest denominator is positive (its
`k = 0` term is `s^d`). -/
theorem forestDenom_pos [Nonempty n] (hq : ∀ i j, i ≠ j → 0 ≤ q i j) {s : K} (hs : 0 < s) :
    0 < forestDenom q s := by
  refine sum_pos' (fun k _ => mul_nonneg (forestCoeff_nonneg hq k) (pow_nonneg hs.le _))
    ⟨0, by simp, ?_⟩
  rw [forestCoeff_zero, one_mul]
  exact pow_pos hs _

theorem forestNumer_nonneg (hq : ∀ i j, i ≠ j → 0 ≤ q i j) {s : K} (hs : 0 ≤ s) (i j : n) :
    0 ≤ forestNumer q s i j := by
  rw [forestNumer, Matrix.sum_apply]
  exact sum_nonneg fun k _ => by
    rw [Matrix.smul_apply, smul_eq_mul]
    exact mul_nonneg (pow_nonneg hs _) (forestMatrix_nonneg hq k i j)

theorem isUnit_det_smul_one_add_rowLaplacian [Nonempty n] (hq : ∀ i j, i ≠ j → 0 ≤ q i j)
    {s : K} (hs : 0 < s) : IsUnit (s • (1 : Matrix n n K) + rowLaplacian q).det := by
  rw [det_eq_mul_forestDenom]
  exact (mul_pos hs (forestDenom_pos hq hs)).ne'.isUnit

/-- `markov:eq:forest-resolvent` for nonnegative off-diagonal rates and every `s > 0`. -/
theorem resolvent_eq_div [Nonempty n] (hq : ∀ i j, i ≠ j → 0 ≤ q i j) {s : K} (hs : 0 < s) :
    Markov.resolvent (rowLaplacian q) s = (forestDenom q s)⁻¹ • forestNumer q s :=
  resolvent_eq_forest q hs.ne' (forestDenom_pos hq hs).ne'

/-- `markov:prop:forest`: for nonnegative off-diagonal rates and `s > 0`, `R_L(s)` is entrywise
nonnegative, with no irreducibility assumption. -/
theorem resolvent_nonneg [Nonempty n] (hq : ∀ i j, i ≠ j → 0 ≤ q i j) {s : K} (hs : 0 < s)
    (i j : n) : 0 ≤ Markov.resolvent (rowLaplacian q) s i j := by
  rw [resolvent_eq_div hq hs, Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr (forestDenom_pos hq hs).le) (forestNumer_nonneg hq hs.le i j)

/-- `markov:prop:forest`: for nonnegative off-diagonal rates and `s > 0`, every row of `R_L(s)`
sums to one. -/
theorem sum_resolvent [Nonempty n] (hq : ∀ i j, i ≠ j → 0 ≤ q i j) {s : K} (hs : 0 < s)
    (i : n) : ∑ j, Markov.resolvent (rowLaplacian q) s i j = 1 := by
  have h := congrFun (resolvent_mulVec_one q (isUnit_det_smul_one_add_rowLaplacian hq hs)) i
  simpa [mulVec, dotProduct] using h

/-- For nonnegative off-diagonal rates and `s > 0`, every entry of `R_L(s)` is at most one. -/
theorem resolvent_le_one [Nonempty n] (hq : ∀ i j, i ≠ j → 0 ≤ q i j) {s : K} (hs : 0 < s)
    (i j : n) : Markov.resolvent (rowLaplacian q) s i j ≤ 1 := by
  rw [← sum_resolvent hq hs i]
  exact single_le_sum (fun l _ => resolvent_nonneg hq hs i l) (mem_univ j)

/-- If the graph of positive rates is strongly connected, then for nonnegative off-diagonal
rates and `s > 0` every entry of `N(s)` is positive: a spanning in-tree rooted at `j`
contributes to column `j`. -/
theorem forestNumer_pos [Nonempty n] (hq : ∀ i j, i ≠ j → 0 ≤ q i j)
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => 0 < q a b) i j) {s : K} (hs : 0 < s)
    (i j : n) : 0 < forestNumer q s i j := by
  classical
  rw [← adjugate_eq_forestNumer, adjugate_smul_one_add_rowLaplacian]
  obtain ⟨ψ, hψ, hroot, hedge⟩ := exists_spanning_inTree j fun i => hconn i j
  refine sum_pos' (fun φ hφ => mul_nonneg
    (weight_nonneg hq (mem_allForests.mp (mem_filter.mp hφ).1)) (pow_nonneg hs.le _))
    ⟨ψ, mem_filter.mpr ⟨mem_allForests.mpr hψ, hroot i⟩, mul_pos ?_ (pow_pos hs _)⟩
  refine prod_pos fun k _ => ?_
  cases hk : ψ k with
  | none => exact zero_lt_one
  | some p => exact hedge k p hk

/-- `markov:prop:forest`, strict positivity: if the graph of positive rates is strongly
connected, then for nonnegative off-diagonal rates and `s > 0` every entry of `R_L(s)` is
positive. -/
theorem resolvent_pos [Nonempty n] (hq : ∀ i j, i ≠ j → 0 ≤ q i j)
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => 0 < q a b) i j) {s : K} (hs : 0 < s)
    (i j : n) : 0 < Markov.resolvent (rowLaplacian q) s i j := by
  rw [resolvent_eq_div hq hs, Matrix.smul_apply, smul_eq_mul]
  exact mul_pos (inv_pos.mpr (forestDenom_pos hq hs)) (forestNumer_pos hq hconn hs i j)

end Ordered

section Hahn

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ]

open HahnSeries in
/-- In `ℝ((t^Γ))`, an element of `[0, 1]` has nonnegative valuation, so it lies in the
valuation ring `𝒪 = {x : v(x) ≥ 0}`. -/
theorem orderTop_nonneg_of_nonneg_of_le_one {x : Lex (HahnSeries Γ ℝ)} (h0 : 0 ≤ x)
    (h1 : x ≤ 1) : 0 ≤ (ofLex x).orderTop := by
  by_contra hneg
  rw [not_le] at hneg
  have hx : ofLex x ≠ 0 := fun h => by simp [h] at hneg
  obtain ⟨g, hg⟩ : ∃ g : Γ, (ofLex x).orderTop = g :=
    ⟨_, (WithTop.coe_untop _ (orderTop_ne_top.mpr hx)).symm⟩
  have hg0 : g < 0 := by
    rw [hg] at hneg
    exact_mod_cast hneg
  have hpos : 0 < (ofLex x).coeff g := by
    have hlt : 0 < x := lt_of_le_of_ne h0 fun h => hx (by rw [← h]; rfl)
    have := leadingCoeff_pos_iff.mpr hlt
    rwa [leadingCoeff_of_ne_zero hx, show (ofLex x).orderTop.untop (orderTop_ne_top.mpr hx) = g
      from (WithTop.untop_eq_iff _).mpr hg] at this
  refine absurd h1 (not_le.mpr ((lt_iff _ _).mpr ⟨g, fun j hj => ?_, ?_⟩))
  · rw [coeff_eq_zero_of_lt_orderTop (x := ofLex x) (by rw [hg]; exact WithTop.coe_lt_coe.mpr hj)]
    simp [coeff_one, (hj.trans hg0).ne]
  · simpa [coeff_one, hg0.ne] using hpos

variable [IsOrderedAddMonoid Γ] [Fintype n] [DecidableEq n]

/-- `markov:prop:forest`, last clause: over `F = ℝ((t^Γ))`, for nonnegative off-diagonal rates
and every `s > 0`, each entry of `R_L(s)` has nonnegative valuation, that is, lies in the
valuation ring `𝒪`, because it lies in `[0, 1]` (`resolvent_nonneg`, `resolvent_le_one`). -/
theorem orderTop_resolvent_nonneg [Nonempty n] {q : n → n → Lex (HahnSeries Γ ℝ)}
    (hq : ∀ i j, i ≠ j → 0 ≤ q i j) {s : Lex (HahnSeries Γ ℝ)} (hs : 0 < s) (i j : n) :
    0 ≤ (ofLex (Markov.resolvent (rowLaplacian q) s i j)).orderTop :=
  orderTop_nonneg_of_nonneg_of_le_one (resolvent_nonneg hq hs i j) (resolvent_le_one hq hs i j)

end Hahn

end

end Surreal.MarkovForest
