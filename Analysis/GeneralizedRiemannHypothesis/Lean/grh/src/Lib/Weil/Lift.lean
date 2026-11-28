import Lib.Adelic.AutomorphicForms.Cuspidality
import Lib.DiscreteSeries.Theta.BlockRule
import Lib.DiscreteSeries.Theta.LocalCorrespondence
import Lib.Weil.DualPair.ThetaLiftConvergence

/-!
# Theta lifts of forms: products of minors, edges, arrows between spaces of forms

This file studies theta lifts between spaces of automorphic forms on unitary groups. Over the reals,
`Ω` assigns operators on a Fock space to the points of a pair of real unitary groups, and `e`, `e'`
are kernels on the two groups; the forms of parameter `l` are those of type `New.typeKernel l s`. A
half edge relates `e` to `e'` through a Fock vector `Φ` and its lifts; an edge does so in both
directions. Edges together with finite data give arrows, data for which the global lift sends forms
to forms. The lift is equivariant under the finite points. The transposed lift is the lift for the
swapped kernel, and the descent `y' ↦ conj (transposed lift of conj y')` is the adjoint of the lift.

## Main definitions and results

* `New.isJointHighest_prod_det_pow_staircaseWeight`: a product of powers of nested minors, one nest
  for each sign, is nonzero, harmonic for both groups, and a highest weight vector for the rows and
  for the columns.
* `New.ParamsCorrespond`, `New.jointHarmonic`: parameters `l`, `l'` that correspond at every
  infinite place, and a chosen product of joint harmonics (`New.IsJointHarmonic`) for them.
* `New.IsHalfEdge`, `New.IsEdge`: `e` is a cusp kernel, and the integral of `⟨Φ, Ω (x, 1) Φ⟩`
  against `conj e` is not zero. The lift with `Φ` of a form of type `e` is a form of type `e'` once
  it has a level. The lift with each polynomial Fock vector is a real convolution of it. An edge has
  this both ways.
* `New.ParamsCorrespond.isEdge_jointHarmonic`: for corresponding parameters the chosen product is
  an edge for the real Weil representation.
* `New.formLift`, `New.IsArrow`: the lift on forms, and the data φ for which it sends forms of type
  e to forms of type e'.
* `New.IsEdge.isArrow`, `New.IsEdge.isForm_star_lift_swap`: an edge tensored with any finite datum
  gives arrows in both directions, and the descent sends forms of type e' to forms of type e.

Notions from other files:
* `New.Space`, `New.Space.lift`: a hermitian space with a point, given by a matrix J over E and x in
  GL_n(𝔸) with xᴴJx equal to diag(s) at the infinite places and 1 at the finite places; the theta
  lift h ↦ ∫_{[S]} θ(ω(g, h)φ) y(g) dg of y with datum φ.
* `New.Space.IsForm`, `New.typeKernel`: a form of type e is a bounded automorphic function that
  right convolution (`New.realConv`) with e fixes; `typeKernel l s` is the product over the infinite
  places of the kernels `dsKernel` with parameters l.
* `New.Fock.fockSpace`, `New.Fock.polyVector`, `New.Fock.piTensor`: the Fock space on ℂ^ι with its
  L¹ norm, the vector (polynomial times Gaussian) of a polynomial, and the product of Fock vectors
  in separate variables.
* `New.integratedRep`: for a representation π of U(diag ε) by bounded operators and a function f,
  the operator π(f) with π(f)x = ∫ f(g)π(g)x dg, when such a bounded operator exists.

## Relation to the literature

Known result: Joint harmonics and global theta lifts between discrete series types. Here the
parameter has large gaps, and the types are given by integrable projector kernels. The lift is shown
to carry forms fixed by one kernel to forms fixed by the other, in both directions, without Howe
duality. Source: J.-S. Li, Theta lifting for unitary representations with nonzero cohomology, Duke
Math. J. 61 (1990); Howe, JAMS 2 (1989); A. Ichino, arXiv 2002.09148, Lemma 7.8.
-/

noncomputable section

/-!
## Products of minors

Explicit harmonic highest vectors in the polynomial (Fock) model: polynomials in variables
`X (a, c)`, with rows `a : n`, all of sign `1`, and columns `c : r` of signs `s c`.
-/

section Staircase

open Finset Function Fin Equiv Fintype

/-- The weight at the column `c` of the staircase with `k η j` minors of size `j` and sign `η`,
where `o c` is the place of `c` among the columns of its sign. The first term is the weight of
the vacuum for the columns; it equals `γ + card n` if `s c = -1` and `γ` if `s c = 1`. The sum
counts the minors of sign `s c` and size `j < card n` that contain the column `c`, those with
`o c < j`. -/
def New.staircaseWeight (n : Type) [Fintype n] {r : Type} (s : r → ℤˣ) (o : r → ℕ)
    (k : ℤˣ → ℕ → ℕ) (γ : ℤ) (c : r) : ℤ :=
  (FockDualPair.std (R := n) 1 s 0 γ).swap.vacuumWeight (s c) -
    s c * ∑ j ∈ Ioo (o c) (Fintype.card n), k (s c) j

/-- The matrix of variables on the first `p` rows and columns for the sign `η`. Its entry `(i, j)`
is the sum of the `X (a, c)` over the rows `a` at place `i` in the decreasing order of `η • l'` and
the columns `c` of sign `η` with `o c = j`. There is at most one such pair `(a, c)` if `l'` is
injective and `o` is injective on the columns of sign `η`. -/
def New.staircaseBlock {r n : Type} [Fintype r] [Fintype n] (s : r → ℤˣ) (o : r → ℕ) (l' : n → ℤ)
    (η : ℤˣ) (p : ℕ) : Matrix (Fin p) (Fin p) (MvPolynomial (n × r) ℂ) :=
  Matrix.of fun i j : Fin p ↦ ∑ a : n, ∑ c : r,
    if decreasingPosition (η.val • l') a = i ∧ s c = η ∧ o c = j.val then .X (a, c) else 0

/-- Counting layers. For each sign `η` and size `p < N` take `k η p` layers, with places
`0, …, p - 1`. The layers of sign `η` that have the place `m η` are those of size `p > m η`. So the
sum of a weight `w η` over all such layers is the sum of `w η` times their number. -/
theorem New.sum_sigma_filter_eq_sum_mul_sum_Ioo (N : ℕ) (k : ℤˣ → ℕ → ℕ) (m : ℤˣ → ℕ) (w : ℤˣ → ℤ) :
    ∑ t : (Σ η : ℤˣ, Σ p : Fin N, Fin (k η p)), ∑ i : Fin t.2.1 with m t.1 = i.val, w t.1 =
      ∑ η : ℤˣ, w η * ∑ j ∈ Ioo (m η) N, k η j := by
  have h_card (a p : ℕ) : #{i : Fin p | a = i.val} = if a < p then 1 else 0 := by
    simpa using Fin.sum_univ_eq_sum_range (fun i ↦ if a = i then (1 : ℕ) else 0) p
  have h_Ioo (a : ℕ) : Ioo a N = map valEmbedding {j : Fin N | a < j} := by
    simp [Finset.ext_iff, exists_iff]
  simp only [Fintype.sum_sigma, Finset.sum_const, h_card, h_Ioo]
  simp [sum_filter, mul_sum, mul_comm]

/-- For injective `l`, number the columns `c` of sign `η` by decreasing `η * l c`: the number `o c`
of columns of the same sign that come before `c` is a bijection onto an initial segment of `ℕ`. -/
theorem New.exists_equiv_fin_eq_card_filter_lt {r : Type} [Fintype r] [DecidableEq r] {s : r → ℤˣ}
    {l : r → ℤ} (hl : Injective l) {o : r → ℕ}
    (ho : ∀ c : r, o c = #{d : r | s d = s c ∧ s c * l c < s c * l d}) (η : ℤˣ) :
    ∃ f : {c : r // s c = η} ≃ Fin (card {c : r // s c = η}),
      ∀ c : {c : r // s c = η}, f c = o c := by
  have h_inj : Injective fun c : {c : r // s c = η} ↦ η * l c :=
    (mul_right_injective₀ η.ne_zero).comp (hl.comp Subtype.val_injective)
  refine (exists_equiv_decreasingPosition h_inj).imp fun f hf c ↦ ?_
  rw [← (hf c).left, ho, decreasingPosition, ← card_map (.subtype _)]
  exact congrArg Finset.card (Finset.ext fun d ↦ by simp [c.prop, and_comm])

/-- For injective `l` and a sign `η`, the position of a row in the decreasing order of `η • l` is a
bijection onto `Fin (card n)`, and the position for `-η` is the reversed one. -/
theorem New.exists_equiv_decreasingPosition_smul {n : Type} [Fintype n] [DecidableEq n] {l : n → ℤ}
    (hl : Injective l) (η : ℤˣ) :
    ∃ u : n ≃ Fin (Fintype.card n), ∀ a : n,
      decreasingPosition (η.val • l) a = u a ∧ decreasingPosition ((-η).val • l) a = (u a).rev := by
  rw [Units.val_neg, neg_smul]
  exact exists_equiv_decreasingPosition fun a b h ↦ hl (mul_left_cancel₀ η.ne_zero h)

/-- Layers of opposite signs share no row. Let `x η` be the place of a row among `N` places in the
order of sign `η`, the order for `-η` being the reverse. Assume that `k 1 i = 0` or `k (-1) j = 0`
whenever `N < i + j`. If `k η p ≠ 0`, `k μ q ≠ 0`, `x η < p` and `x μ < q`, then `η = μ`. -/
theorem New.sign_eq_of_ne_zero_of_lt {N : ℕ} {k : ℤˣ → ℕ → ℕ}
    (hk_fit : ∀ i j : ℕ, N < i + j → k 1 i = 0 ∨ k (-1) j = 0) {x : ℤˣ → Fin N}
    (hx : ∀ η : ℤˣ, x (-η) = (x η).rev) {η μ : ℤˣ} {p q : ℕ} (hp : k η p ≠ 0) (hq : k μ q ≠ 0)
    (hxp : x η < p) (hxq : x μ < q) : η = μ := by
  -- For opposite signs the two places add up to `N - 1`, so `N < p + q`.
  have h_sum : (x (-1) : ℕ) + x 1 + 1 = N := by grind
  rcases Int.units_eq_one_or η with rfl | rfl <;> rcases Int.units_eq_one_or μ with rfl | rfl <;>
    grind

/-- Order the rows by decreasing `η • l'` and the columns of sign `η` by decreasing `η • l` (`l`,
`l'` injective); `decreasingPosition (η • l') a` is the place of the row `a` and `o c` the place of
the column `c`. Take the product over `η = ±1` and `p < card n` of the `k η p`-th power of the minor
on the first `p` rows and columns for `η`. Assume that `k η p = 0` if there are fewer than `p`
columns of sign `η` and `p < card n`, and that `k 1 i = 0` or `k (-1) j = 0` whenever
`i + j > card n`. Let `ν a` be the weight of the vacuum at the rows plus the sum over `η` of `η`
times the number of minors of sign `η` that contain the row `a`. `FockDualPair.std 1 s γ γ'` has
rows `n`, columns `r` of signs `s`, and shifts `γ`, `γ' + card n`. `staircaseWeight` at `c` combines
the column vacuum weight (`γ' + card n` if `s c = -1`, else `γ'`) with the count of minors of sign
`s c` containing `c`. Then the product satisfies `New.FockDualPair.IsJointHighest`: it is nonzero,
harmonic for both groups, highest of weight `ν` for the rows, ordered by `l'`, and highest of weight
`New.staircaseWeight` for the columns, ordered by `-l`. -/
theorem New.isJointHighest_prod_det_pow_staircaseWeight {r n : Type} [Fintype r] [DecidableEq r]
    [Fintype n] [DecidableEq n] {s : r → ℤˣ} {γ γ' : ℤ} {ν : n → ℤ} {l : r → ℤ} {l' : n → ℤ}
    (hl : Injective l) (hl' : Injective l') {o : r → ℕ}
    (ho : ∀ c : r, o c = #{d : r | s d = s c ∧ s c * l c < s c * l d}) (k : ℤˣ → ℕ → ℕ)
    (hk_cols : ∀ (η : ℤˣ) (i : ℕ), card {c : r // s c = η} < i → i < card n → k η i = 0)
    (hk_fit : ∀ i j : ℕ, card n < i + j → k 1 i = 0 ∨ k (-1) j = 0)
    (hν : ∀ a : n, ν a = (FockDualPair.std (R := n) 1 s γ γ').vacuumWeight 1 +
      ∑ η : ℤˣ, η.val * ∑ j ∈ Ioo (decreasingPosition (η.val • l') a) (card n), k η j) :
    (FockDualPair.std 1 s γ γ').IsJointHighest l' (-l)
      (∏ η : ℤˣ, ∏ p : Fin (card n), (staircaseBlock s o l' η p).det ^ k η p)
      ν (staircaseWeight n s o k γ') := by
  -- The product runs over layers `t = (η, p, copy)`; `IsLayering.isJointHighest_of_eq_prod_det`
  -- applies once the rows and the columns both satisfy `IsLayering`.
  -- `u η` numbers the rows in the order of `η • l'`, and `f η` the columns of sign `η` by `o`.
  have h_number_rows (η : ℤˣ) : ∃ u : n ≃ Fin (card n), ∀ a : n,
      decreasingPosition (η.val • l') a = u a ∧ decreasingPosition ((-η).val • l') a = (u a).rev :=
    exists_equiv_decreasingPosition_smul hl' η
  have h_number_cols (η : ℤˣ) : ∃ f : {c : r // s c = η} ≃ Fin (card {c : r // s c = η}),
      ∀ c : {c : r // s c = η}, f c = o c := exists_equiv_fin_eq_card_filter_lt hl ho η
  choose u hu hu_neg using h_number_rows
  choose f hf using h_number_cols
  have hu_rev (a : n) (η : ℤˣ) : u (-η) a = (u η a).rev := Fin.ext (by rw [← hu, hu_neg])
  -- Row `i` and column `i` of a layer of sign `η` are those at place `i` in the two orders. Place
  -- `i < p` exists among the columns of sign `η` by `hk_cols`, as `k η p ≠ 0` for a layer.
  have h_place (t : Σ η : ℤˣ, Σ p : Fin (card n), Fin (k η p)) (i : Fin t.2.1) : ∃ (a : n) (c : r),
      (∀ b : n, a = b ↔ u t.1 b = i.val) ∧ ∀ d : r, c = d ↔ s d = t.1 ∧ o d = i := by
    obtain ⟨η, p, copy⟩ := t
    have hp : p ≤ card {c : r // s c = η} := not_lt.1 fun h ↦ copy.pos.ne' (hk_cols η p h p.is_lt)
    refine ⟨(u η).symm ⟨i, i.is_lt.trans p.is_lt⟩, (f η).symm ⟨i, i.is_lt.trans_le hp⟩,
      fun b ↦ by rw [symm_apply_eq, Fin.ext_iff, eq_comm], fun d ↦ ?_⟩
    simp only [Subtype.coe_eq_iff, symm_apply_eq, Fin.ext_iff, hf, exists_prop, eq_comm (a := o d)]
  choose ρ κ hρ hκ using h_place
  have h_at (t : Σ η : ℤˣ, Σ p : Fin (card n), Fin (k η p)) (i : Fin t.2.1) :
      u t.1 (ρ t i) = i.val ∧ s (κ t i) = t.1 ∧ o (κ t i) = i := by simp [← hρ, ← hκ]
  have h_rows : IsLayering (FockDualPair.std 1 s γ γ') l' ν ρ κ := by
    refine ⟨fun t i j h_row ↦ ?_, ?_, fun t i a _ h_out ↦ ?_, fun a ↦ ?_⟩
    · exact Fin.ext (by rw [← (h_at t i).left, h_row, (h_at t j).left])
    · -- Layers that share a row have the same sign.
      rintro ⟨η, p, copy⟩ ⟨μ, q, copy'⟩ i j i' j' h_row
      set a : n := ρ ⟨η, p, copy⟩ i
      have h_lt : u η a < p.val := ((hρ _ i a).1 rfl).trans_lt i.is_lt
      have h_lt' : u μ a < q.val := ((hρ _ j a).1 h_row.symm).trans_lt j.is_lt
      simpa [h_at] using
        sign_eq_of_ne_zero_of_lt (x := (u · a)) hk_fit (hu_rev a) copy.pos.ne' copy'.pos.ne' h_lt
          h_lt'
    · -- A row further out has a smaller place, so it is in the layer too.
      have h_lt : t.1 * l' (ρ t i) < t.1 * l' a := by simpa [h_at, mul_sub, pairSign] using h_out
      have h_le : (u t.1 a : ℕ) ≤ u t.1 (ρ t i) := by
        simpa only [← hu, decreasingPosition] using card_le_card fun b ↦ by simpa using h_lt.trans
      exact ⟨⟨u t.1 a, (h_le.trans_eq (h_at t i).left).trans_lt i.is_lt⟩, (hρ t _ a).2 rfl⟩
    · -- The row `a` lies in the layers of sign `η` that have the place `u η a`.
      simp_rw [hν, hu, ← sum_sigma_filter_eq_sum_mul_sum_Ioo, hρ, FockDualPair.varSign, pairSign,
        h_at]
      simp
  -- The same for the columns; the condition on signs is trivial, as all rows have sign `1`.
  have h_cols :
      IsLayering (FockDualPair.std 1 s γ γ').swap (-l) (staircaseWeight n s o k γ') κ ρ := by
    refine ⟨fun t i j h_col ↦ ?_, by simp, fun t i c h_sign h_out ↦ ?_, fun c ↦ ?_⟩
    · exact Fin.ext (by rw [← (h_at t i).right.right, h_col, (h_at t j).right.right])
    · obtain ⟨-, h_sign_layer, h_place_layer⟩ := h_at t i
      have h_lt : s c * l (κ t i) < s c * l c := by simpa [h_sign, mul_add, pairSign] using h_out
      have h_le : o c ≤ o (κ t i) := by
        simpa only [ho] using card_le_card (monotone_filter_right _ (by grind))
      exact ⟨⟨o c, by lia⟩, (hκ t _ c).2 ⟨h_sign.trans h_sign_layer, rfl⟩⟩
    · -- Only the layers of sign `s c` contain the column `c`, each with the sign `-s c`.
      have h_count : -(s c * ∑ j ∈ Ioo (o c) (card n), k (s c) j : ℤ) =
          ∑ η : ℤˣ, (if s c = η then -(s c).val else 0) * ∑ j ∈ Ioo (o c) (card n), k η j := by
        simp only [ite_mul, zero_mul, Fintype.sum_ite_eq, neg_mul]
      rw [staircaseWeight, sub_eq_add_neg, h_count,
        ← sum_sigma_filter_eq_sum_mul_sum_Ioo _ k fun _ ↦ o c]
      refine congrArg _ (sum_congr rfl fun t _ ↦ ?_)
      by_cases h_sign : s c = t.1 <;> simp [hκ, h_sign, pairSign]
  refine h_rows.isJointHighest_of_eq_prod_det h_cols ?_
  -- The `(i, j)` entry of the block of `t` is the variable at row `ρ t i` and column `κ t j`.
  simp_rw [staircaseBlock, ← Fin.prod_const, ← Fintype.prod_sigma', hu, ← hρ, ← hκ]
  simp only [ite_and, sum_ite_irrel, sum_const_zero, Fintype.sum_ite_eq, refl_apply]

end Staircase

namespace New

/-!
## Edges: archimedean data for theta lifts

* `New.isHalfEdge_of_oscillatorPair`: a tensor product of joint harmonics for oscillator pairs is a
  half edge.
-/

section Edge

open NumberField MeasureTheory Matrix ComplexConjugate MvPolynomial Fock Fintype Norms.L2Operator
  Complex CompactlySupported Set Heisenberg.IsVacuum

variable {E n n' ι : Type} [Field E] [CMType E] [WeilData E]
  [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype ι] [DecidableEq ι]
  {s : n → ℤˣ} {t : n' → ℤˣ} (γ γ' : InfinitePlace E → ℤ) (l : InfinitePlace E → n → ℤ)
  (l' : InfinitePlace E → n' → ℤ) {η : ι → ℤˣ}
  (Ω : GInf E s × GInf E t → fockSpace (realSigns E η) →L[ℂ] fockSpace (realSigns E η))
  (e : GInf E s → ℂ) (e' : GInf E t → ℂ) (Φ : fockSpace (realSigns E η))

/-! ### Corresponding parameters and the chosen joint harmonic -/

/-- `-l` if `d` is true and `l` otherwise: the parameter of the forms of type `l`, or, if `d` is
true, of their conjugates. -/
abbrev negIf {α : Type*} [Neg α] (d : Bool) (l : α) : α := match d with
  | true => -l
  | false => l

theorem negIf_true {α : Type*} [Neg α] (l : α) : negIf true l = -l := rfl

theorem negIf_false {α : Type*} [Neg α] (l : α) : negIf false l = l := rfl

/-- The doubled parameters l for the signs s : n → ℤˣ and l' for the signs t : n' → ℤˣ correspond:
at each infinite place w they satisfy the block rule (`New.IsBlockRule`) for the weights γ w and γ'
w. -/
def ParamsCorrespond (s : n → ℤˣ) (t : n' → ℤˣ) : Prop :=
  ∀ w : InfinitePlace E, IsBlockRule (γ w) (γ' w) (toHCParam s (l w)) (toHCParam t (l' w))

/-- A chosen joint harmonic polynomial at the place `w` for the signs `t`, `s`, the weights `γ w`,
`-γ' w` and the parameters `l' w`, `-l w`; an arbitrary polynomial if none exists. See
`isJointHarmonic_jointHarmonicAt`. -/
def jointHarmonicAt (s : n → ℤˣ) (t : n' → ℤˣ) (w : InfinitePlace E) : MvPolynomial (n' × n) ℂ :=
  Classical.epsilon (IsJointHarmonic (.std t s (γ w) (-γ' w)) (l' w) (-l w))

/-- The product over the infinite places `w` of the chosen polynomials `jointHarmonicAt`, each in
the variables of `w`. -/
def jointHarmonic {E : Type} [Field E] [NumberField E] (γ γ' : InfinitePlace E → ℤ)
    (l : InfinitePlace E → n → ℤ) (l' : InfinitePlace E → n' → ℤ)
    (s : n → ℤˣ) (t : n' → ℤˣ) : MvPolynomial (InfinitePlace E × n' × n) ℂ :=
  ∏ w : InfinitePlace E, rename (w, ·) (jointHarmonicAt γ γ' l l' s t w)

variable {γ γ' l l'}

section Correspond

omit [CMType E] [WeilData E]

section

omit [DecidableEq n] [DecidableEq n']

/-- If the parameters `l` (signs `s`) and `l'` (signs `t`) correspond for the weights `γ`, `γ'`,
then `l' w` and `-l w` match (`New.IsMatch`) for the standard dual pair data at each place `w`. -/
theorem ParamsCorrespond.isMatch (h_corr : ParamsCorrespond γ γ' l l' s t) (w : InfinitePlace E) :
    IsMatch (.std t s (γ w) (-γ' w)) (l' w) (-l w) := isBlockRule_iff_isMatch.1 (h_corr w)

/-- The correspondence of parameters is symmetric: if `l`, `l'` correspond for the signs `s`, `t`
and the weights `γ`, `γ'`, then `l'`, `l` correspond for `t`, `s` and `γ'`, `γ`. -/
theorem ParamsCorrespond.symm (h_corr : ParamsCorrespond γ γ' l l' s t) :
    ParamsCorrespond γ' γ l' l t s := fun w ↦ (h_corr w).symm

/-- If `l`, `l'` correspond for the signs `s`, `t` and the weights `γ`, `γ'`, then `-l`, `-l'`
correspond for the signs `-s`, `t` and the weights `card n - γ`, `card n' - γ'`. -/
theorem ParamsCorrespond.neg (h_corr : ParamsCorrespond γ γ' l l' s t) :
    ParamsCorrespond (card n - γ ·) (card n' - γ' ·) (-l) (-l') (-s) t := fun w ↦ (h_corr w).neg

end

/-- Let `w` be an infinite place of `E`. Suppose the doubled parameters `l' w` and `-l w` match
(`New.IsMatch`) for the standard dual pair datum `.std t s (γ w) (-γ' w)`, which has rows with signs
`t`, columns with signs `s`, and weights `γ w` and `-γ' w`. Then the chosen polynomial
`jointHarmonicAt γ γ' l l' s t w` is a joint harmonic for this datum (`New.IsJointHarmonic`): it is
nonzero, highest for the row and column actions with the weights of the two lowest `K`-types, and
termwise harmonic for the datum and for its swap. -/
theorem isJointHarmonic_jointHarmonicAt {w : InfinitePlace E}
    (h_match : IsMatch (.std t s (γ w) (-γ' w)) (l' w) (-l w)) :
    IsJointHarmonic (.std t s (γ w) (-γ' w)) (l' w) (-l w) (jointHarmonicAt γ γ' l l' s t w) :=
  Classical.epsilon_spec h_match.exists_isJointHarmonic

end Correspond

variable {E : Type} [Field E] [NumberField E] {γ γ' : InfinitePlace E → ℤ}
  {l : InfinitePlace E → n → ℤ} {l' : InfinitePlace E → n' → ℤ} in
/-- Let the doubled parameters `l` (for the signs `s`) and `l'` (for the signs `t`) correspond for
the weights `γ`, `γ'`. For each infinite place w, let `P w` be a joint harmonic for the standard
dual pair `.std t s (γ w) (-γ' w)` with parameters `l' w` and `-l w`. Then the product over w of the
`P w`, with the variables of `P w` renamed to those of the place w, is a scalar multiple of
`jointHarmonic γ γ' l l' s t`. -/
theorem ParamsCorrespond.prod_eq_smul_jointHarmonic (h_corr : ParamsCorrespond γ γ' l l' s t)
    (P : InfinitePlace E → MvPolynomial (n' × n) ℂ)
    (hP : ∀ w : InfinitePlace E, IsJointHarmonic (.std t s (γ w) (-γ' w)) (l' w) (-l w) (P w)) :
    ∃ c : ℂ, ∏ w : InfinitePlace E, rename (Prod.mk w) (P w) = c • jointHarmonic γ γ' l l' s t := by
  have h_local (w : InfinitePlace E) : ∃ c : ℂ, P w = c • jointHarmonicAt γ γ' l l' s t w := by
    obtain ⟨-, ⟨-, h_cols⟩, h_harm, h_rows, h_harm_swap⟩ := (hP w).isJointHighest
    exact (isJointHarmonic_jointHarmonicAt (h_corr.isMatch w)).exists_eq_smul_of_row_weight h_harm
      h_harm_swap h_rows h_cols
  choose c hc using h_local
  exact ⟨∏ w, c w, by simp [jointHarmonic, hc, map_smul, Finset.prod_smul]⟩

/-- The real points of the two groups act through `Ω` on the real vector `v` of a datum
`V.integrated v f` and leave its finite part `f` alone. -/
def ThetaKernel.HasRealPart {V : Space E ι η} {S : Space E n s} {T : Space E n' t}
    (Θ : ThetaKernel (𝒮 V) S T)
    (Ω : GInf E s × GInf E t → fockSpace (realSigns E η) →L[ℂ] fockSpace (realSigns E η)) : Prop :=
  ∀ (x : GInf E s) (y : GInf E t) (v : fockSpace (realSigns E η)) (f : 𝒮 V),
    Θ.ω ((x, 1), (y, 1)) (V.integrated v f) = V.integrated (Ω (x, y) v) f

/-- Half an edge from `e` to `e'`: `e` is a cusp kernel of order `0`, and the integral of
`⟨Φ, Ω (x, 1) Φ⟩` against `conj e / e 1` is not zero. For a theta kernel whose real points act
through `Ω` (`ThetaKernel.HasRealPart`) and a form of type `e`, the lift with `Φ`
is a form of type `e'` as soon as it has a level. For each polynomial Fock vector `v` there is one
continuous `α` of compact support such that, for all these kernels and forms, the lift with `v` is
the real convolution with `α` of the lift with `Φ`. -/
structure IsHalfEdge : Prop where
  /-- `e` is a cusp kernel of order `0`. -/
  isCuspKernel_source : IsCuspKernel 0 e
  /-- The zeta integral of `Φ` against `conj e`, normalised by `e 1`, is not zero. -/
  zetaIntegral_ne_zero : ∫ x : GInf E s, fockInner Φ (Ω (x, 1) Φ) * (conj (e x) / e 1) ≠ 0
  /-- The lift with `Φ` of a form `y` of type `e` is a form of type `e'` if it has a level. -/
  isForm_lift {V : Space E ι η} {S : Space E n s} {T : Space E n' t} {y : G E s → ℂ} {f : 𝒮 V}
    (Θ : ThetaKernel (𝒮 V) S T) (hΘ : Θ.HasRealPart Ω) (hy : S.IsForm e y)
    (K : OpenSubgroup (Gf E n')) (h_level : HasLevel (S.lift Θ (V.integrated Φ f) y) K) :
    T.IsForm e' (S.lift Θ (V.integrated Φ f) y)
  /-- Every Fock polynomial `v` has a continuous function `α` of compact support such that the lift
  with `v` of any form `y` of type `e` is the convolution with `α` of the lift with `Φ`. -/
  exists_lift_eq_realConv (v : fockSpace (realSigns E η))
    (hv : v ∈ range (polyVector (realSigns E η))) :
    ∃ α : C_c(GInf E t, ℂ), ∀ {V : Space E ι η} {S : Space E n s} {T : Space E n' t}
      {y : G E s → ℂ} {f : 𝒮 V} (Θ : ThetaKernel (𝒮 V) S T), Θ.HasRealPart Ω → S.IsForm e y →
      S.lift Θ (V.integrated v f) y = realConv α (S.lift Θ (V.integrated Φ f) y)

variable {Ω e e' Φ} in
/-- Let `Φ` be a half edge for `Ω` from `e` to `e'`, and let `v` be a polynomial Fock vector. There
is one compactly supported `α` on `GInf E t` with the following property. Take any spaces `V`, `S`,
`T`, any theta kernel `Θ` with `Θ.ω ((x, 1), (x', 1))` acting on `V.integrated u f'` as `Ω (x, x')`
acts on `u`, any `f`, and any form `y` of type `e` (bounded automorphic, fixed by convolution with
`e` if `e` is integrable). Then the lift `F` of `y` with `V.integrated Φ f` is a form of type `e'`
if it has a level, and the lift with `V.integrated v f` is `realConv α F`. -/
theorem IsHalfEdge.lift_isForm_and_eq_realConv (h_edge : IsHalfEdge Ω e e' Φ)
    (v : fockSpace (realSigns E η)) (hv : v ∈ range (polyVector (realSigns E η))) :
    ∃ α : C_c(GInf E t, ℂ), ∀ {V : Space E ι η} {S : Space E n s} {T : Space E n' t}
      {y : G E s → ℂ} {f : 𝒮 V} (Θ : ThetaKernel (𝒮 V) S T),
      (∀ (x : GInf E s) (x' : GInf E t) (u : fockSpace (realSigns E η)) (f' : 𝒮 V),
        Θ.ω ((x, 1), (x', 1)) (V.integrated u f') = V.integrated (Ω (x, x') u) f') →
      S.IsForm e y →
      let F : G E t → ℂ := S.lift Θ (V.integrated Φ f) y
      (∀ K : OpenSubgroup (Gf E n'), HasLevel F K → T.IsForm e' F) ∧
        S.lift Θ (V.integrated v f) y = realConv α F := by
  obtain ⟨α, hα⟩ := h_edge.exists_lift_eq_realConv v hv
  exact ⟨α, fun Θ hΘ hy ↦ ⟨h_edge.isForm_lift Θ hΘ hy, hα Θ hΘ hy⟩⟩

/-- Φ is a half edge for Ω with kernels e, e', and also for Ω with its two groups exchanged with
kernels conj(e'), conj(e). -/
structure IsEdge extends IsHalfEdge Ω e e' Φ where
  /-- With the two groups exchanged, `Φ` is a half edge from `conj e'` to `conj e`. -/
  swapped : IsHalfEdge (Ω ·.swap) (Star.star e') (Star.star e) Φ

variable {Ω}

/-! ### Products of joint harmonics are edges -/

section Oscillator

variable {π : InfinitePlace E → USign s →* fockSpace η →L[ℂ] fockSpace η}
  {π' : InfinitePlace E → USign t →* fockSpace η →L[ℂ] fockSpace η}
  {Φ : InfinitePlace E → MvPolynomial ι ℂ} [Nonempty n]

section

omit [WeilData E]

/-- Let `π w` be unitary representations of growth `A` of the unitary group of signs `s : n → ℤˣ` on
the Fock space of signs `η : ι → ℤˣ`, let `k w` be continuous functions with integrable moment of
order `A`, and let `T` be a continuous linear map from `fockSpace (realSigns E η)` to a Banach space
`X`, and let `v w` be vectors of `fockSpace η`. The integral over the real points `x : GInf E s` of
the image under `T` of the pure tensor (`piTensor`) of the vectors `k w (x w) • π w (x w) (v w)`
converges, and equals the image under `T` of the pure tensor of the local integrals
`integratedRep (π w) (k w) (v w)`. -/
theorem integral_piTensor_eq_integratedRep {A : ℕ}
    (hπ : ∀ w : InfinitePlace E, IsUnitaryRep A (π w) fockInner)
    (k : InfinitePlace E → USign s → ℂ) (k_cont : ∀ w : InfinitePlace E, Continuous (k w))
    (hk : ∀ w : InfinitePlace E, Integrable fun g : USign s ↦ k w g * ‖(g : Matrix n n ℂ)‖ ^ A)
    (v : InfinitePlace E → fockSpace η) {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [CompleteSpace X] (T : fockSpace (realSigns E η) →L[ℂ] X) :
    let F (x : GInf E s) : X := T (piTensor fun w : InfinitePlace E ↦ k w (x w) • π w (x w) (v w))
    Integrable F ∧ ∫ x : GInf E s, F x =
      T (piTensor fun w : InfinitePlace E ↦ integratedRep (π w) (k w) (v w)) := by
  -- Bound the integrand by a product of integrable functions of one place each; then evaluate at a
  -- point `z`, where the integral of a product over the places is the product of the integrals.
  have π_cont (w : InfinitePlace E) (x : fockSpace η) : Continuous (π w · x) := (hπ w).continuous x
  let F₀ (x : GInf E s) : fockSpace (realSigns E η) := piTensor fun w ↦ k w (x w) • π w (x w) (v w)
  have h_factor (w : InfinitePlace E) : Integrable fun g : USign s ↦ ‖k w g • π w g (v w)‖ :=
    (integrable_smul_rep (hπ w) (hk w) (v w)).norm
  have F₀_int : Integrable F₀ := ((Integrable.fintype_prod h_factor).const_mul _).mono'
    (by fun_prop) (.of_forall fun _ ↦ piTensor.le_opNorm _)
  have F₀_eq : ∫ x, F₀ x = piTensor fun w ↦ integratedRep (π w) (k w) (v w) := ext fun z ↦ by
    -- the value of `piTensor` at `z` is the product of the values of its factors
    let ev (w : InfinitePlace E) : fockSpace η →L[ℂ] ℂ := valueAt fun i ↦ z (w, i)
    calc (∫ x, F₀ x) z = ∫ x : GInf E s, ∏ w, k w (x w) • ev w (π w (x w) (v w)) :=
        ((valueAt z).integral_comp_comm F₀_int).symm
      _ = ∏ w, ∫ g, k w g • ev w (π w g (v w)) :=
        integral_fintype_prod_eq_prod fun w g ↦ k w g • ev w (π w g (v w))
      _ = ∏ w, ev w (integratedRep (π w) (k w) (v w)) := by
        simp only [map_integratedRep (hπ _) (hk _)]
  exact ⟨T.integrable_comp F₀_int, (T.integral_comp_comm F₀_int).trans (congrArg T F₀_eq)⟩

/-- Let `Ω (x, 1)` act on pure tensors place by place through the oscillator pairs `π w`, `π' w` for
the dual pair data `T w`, and let joint harmonics `Φ w` for the parameters `l w`, `l' w` exist. Here
`typeKernel l s` is the product over the places of the kernels `dsKernel (l w)`, each the formal
degree times the conjugate discrete series coefficient. For a continuous linear `L`,
`x ↦ typeKernel l s x • L (Ω (x, 1) v)` is integrable at a pure tensor `v`, and its integral is `L`
of the tensor of the vectors `π w (dsKernel (l w)) (v w)`, where `π w (f)` is the operator
`∫ f(g) π w g dg`. -/
theorem integral_typeKernel_smul_piTensor {T : InfinitePlace E → FockDualPair s t ι}
    (hp : ∀ w : InfinitePlace E, OscillatorPair (T w) (π w) (π' w))
    (hΦ : ∀ w : InfinitePlace E, IsJointHarmonic (T w) (l w) (l' w) (Φ w))
    (hΩ_left : ∀ (v : InfinitePlace E → fockSpace η) (x : GInf E s),
      Ω (x, 1) (piTensor v) = piTensor fun w : InfinitePlace E ↦ π w (x w) (v w))
    (v : InfinitePlace E → fockSpace η) {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [CompleteSpace X] (L : fockSpace (realSigns E η) →L[ℂ] X) :
    Integrable (fun x : GInf E s ↦ typeKernel l s x • L (Ω (x, 1) (piTensor v))) ∧
      ∫ x : GInf E s, typeKernel l s x • L (Ω (x, 1) (piTensor v)) =
        L (piTensor fun w : InfinitePlace E ↦ integratedRep (π w) (dsKernel (l w)) (v w)) := by
  have h_moment (w : InfinitePlace E) :
      Integrable fun g : USign s ↦ dsKernel (l w) g * ‖(g : Matrix n n ℂ)‖ ^ card ι :=
    ((hΦ w).hasLargeGap le_rfl).integrable_dsKernel_mul_norm_pow _ (Nat.le_succ _)
  -- `typeKernel l s x` is the product of the scalars `dsKernel (l w) (x w)`.
  simpa [← hΩ_left, ContinuousMultilinearMap.map_smul_univ] using
    integral_piTensor_eq_integratedRep (fun w ↦ (hp w).unitary_rep) _ (by fun_prop) h_moment v L

omit [DecidableEq ι] in
/-- If the parameters `l w`, `l' w` have joint harmonics, the kernel of type `-l` is a cusp
kernel. -/
theorem isCuspKernel_typeKernel_neg_of_isJointHarmonic {T : InfinitePlace E → FockDualPair s t ι}
    (hΦ : ∀ w : InfinitePlace E, IsJointHarmonic (T w) (l w) (l' w) (Φ w)) :
    IsCuspKernel 0 (typeKernel (-l) s) :=
  isCuspKernel_typeKernel (l := -l) fun w ↦ ((hΦ w).hasLargeGap (Nat.zero_le _)).neg

end

/-- The lift of a form of type `-l` sees only the part of type `l` of the real vector. Here
`Ω (x, 1)` acts on pure tensors through the oscillator pairs `π w`, `π' w`, joint harmonics for
`l w`, `l' w` exist, and the real points act through `Ω` on the theta kernel: the lift with a pure
tensor is unchanged when each factor is replaced by its projection `π w (dsKernel (l w))`. -/
theorem lift_piTensor_integratedRep {T : InfinitePlace E → FockDualPair s t ι}
    (hp : ∀ w : InfinitePlace E, OscillatorPair (T w) (π w) (π' w))
    (hΦ : ∀ w : InfinitePlace E, IsJointHarmonic (T w) (l w) (l' w) (Φ w))
    (hΩ_left : ∀ (v : InfinitePlace E → fockSpace η) (x : GInf E s),
      Ω (x, 1) (piTensor v) = piTensor fun w : InfinitePlace E ↦ π w (x w) (v w))
    {V : Space E ι η} {S : Space E n s} {S' : Space E n' t} {y : G E s → ℂ}
    (Θ : ThetaKernel (𝒮 V) S S') (hΘ : Θ.HasRealPart Ω) (hy : S.IsForm (typeKernel (-l) s) y)
    (v : InfinitePlace E → fockSpace η) (f : 𝒮 V) (g : G E t) :
    S.lift Θ (V.integrated (piTensor
      fun w : InfinitePlace E ↦ integratedRep (π w) (dsKernel (l w)) (v w)) f) y g =
      S.lift Θ (V.integrated (piTensor v) f) y g := by
  -- Insert `y = realConv e y` for `e = typeKernel (-l) s` and move the real variable to the datum.
  let e : GInf E s → ℂ := typeKernel (-l) s
  let φ : 𝒮 V := V.integrated (piTensor v) f
  have cusp : IsCuspKernel 0 e := isCuspKernel_typeKernel_neg_of_isJointHarmonic hΦ
  have y_cont : Continuous y := hy.continuous
  have e_inv (x : GInf E s) : typeKernel l s x⁻¹ = e x := by
    simp [e, typeKernel, ((hΦ _).hasLargeGap le_rfl).isIdempotentKernel_dsKernel.apply_inv,
      ← conj_dsKernel_neg (hΦ _).hasGap_row]
  have h_real (x : GInf E s) : V.integrated (Ω (x, 1) (piTensor v)) f = Θ.ω ((x, 1), 1) φ :=
    (hΘ x 1 (piTensor v) f).symm
  -- At each point the lift is a continuous functional `L g` of the datum, with bounded integrand.
  obtain ⟨L, hL⟩ : ∃ L : G E t → 𝒮 V →L[ℂ] ℂ, ∀ (ψ : 𝒮 V) (g : G E t), S.lift Θ ψ y g = L g ψ :=
    Θ.exists_clm_lift (hy.mem_rapidFunctions cusp)
  obtain ⟨C, A, hC⟩ : ∃ (C : ℝ) (A : ℕ), ∀ (ψ : 𝒮 V) (a : G E s) (g : G E t),
      ‖Θ.θ (Θ.ω (a, g) ψ) * y a‖ ≤ S'.height g ^ A * |C| * ‖ψ‖ :=
    Θ.exists_norm_theta_mul_le (hy.mem_rapidFunctions cusp)
  -- The double integral converges absolutely, as `typeKernel l s x • ω (x, 1) φ` is integrable.
  have h_orbit : Integrable fun x : GInf E s ↦ typeKernel l s x • Θ.ω ((x, 1), 1) φ := by
    simpa only [ContinuousLinearMap.flip_apply, h_real] using
      (integral_typeKernel_smul_piTensor hp hΦ hΩ_left v (V.integrated.flip f)).1
  let F (x : GInf E s) (a : G E s) : ℂ := e x * (Θ.θ (Θ.ω (a, g) φ) * y (a * (x, 1)))
  have h_bound (x : GInf E s) (a : G E s) :
      ‖F x a‖ ≤ S'.height g ^ A * |C| * ‖typeKernel l s x⁻¹ • Θ.ω ((x⁻¹, 1), 1) φ‖ := by
    refine (hC _ (a * (x, 1)) g).trans' ?_
    simp [F, e_inv, Prod.mk_one_one, rep_apply_apply, mul_assoc]
  have h_int : Integrable F.uncurry (volume.prod S.quotMeasure) :=
    ((h_orbit.norm.comp_inv.const_mul _).comp_fst _).mono' (by fun_prop)
      (.of_forall fun p ↦ h_bound p.1 p.2)
  calc _ = ∫ x : GInf E s, typeKernel l s x * S.lift Θ (Θ.ω ((x, 1), 1) φ) y g := by
        simpa [hL, h_real] using
          (integral_typeKernel_smul_piTensor hp hΦ hΩ_left v (L g ∘L V.integrated.flip f)).2.symm
    _ = ∫ x : GInf E s, ∫ a : G E s, F x a ∂S.quotMeasure := by
        -- substitute `x⁻¹` for `x`, then move `(x⁻¹, 1)` from the datum to `y`
        rw [← integral_inv_eq_self]
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        have h_move : S.lift Θ (Θ.ω ((x⁻¹, 1), 1) φ) y = S.lift Θ φ fun a ↦ y (a * (x, 1)) := by
          simp [Θ.lift_omega_left hy.toIsAutomorphic]
        simp only [F, e_inv, h_move]
        simp only [Space.lift, integral_const_mul]
    _ = ∫ a : G E s, (∫ x : GInf E s, F x a) ∂S.quotMeasure := integral_integral_swap h_int
    _ = S.lift Θ φ (realConv e y) g := by
        simp only [F, Space.lift, realConv, ← integral_const_mul, mul_left_comm]
    _ = S.lift Θ φ y g := by rw [hy.realConv_eq cusp.integrable]

variable [Nonempty n']

/-- Let `Ω` act on pure tensors through the oscillator pairs `π w`, `π' w` and on the theta kernel
through its real points, let `y` be a form of type `-l`, and write `p w = π w (dsKernel (l w))`. Let
`k w` be continuous, with integrable moment of order `card ι`, and
`π' w (k w) (p w (Φ w)) = p w (v w)`. Fix a finite datum `f`. If `F` is the lift of `y` with
`V.integrated Φ₀ f`, where `Φ₀` is the tensor of the Fock vectors of the joint harmonics `Φ w`, then
`x ↦ (∏ w, k w (x w)) * F (g * (x, 1))` is integrable, and its integral is the lift of `y` with the
tensor of the `v w`, at `g`. -/
theorem integral_mul_lift_eq_lift_piTensor {T : InfinitePlace E → FockDualPair s t ι}
    (hp : ∀ w : InfinitePlace E, OscillatorPair (T w) (π w) (π' w))
    (hΦ : ∀ w : InfinitePlace E, IsJointHarmonic (T w) (l w) (l' w) (Φ w))
    (hΩ_left : ∀ (v : InfinitePlace E → fockSpace η) (x : GInf E s),
      Ω (x, 1) (piTensor v) = piTensor fun w : InfinitePlace E ↦ π w (x w) (v w))
    (hΩ_right : ∀ (v : InfinitePlace E → fockSpace η) (y : GInf E t),
      Ω (1, y) (piTensor v) = piTensor fun w : InfinitePlace E ↦ π' w (y w) (v w))
    {V : Space E ι η} {S : Space E n s} {S' : Space E n' t} {y : G E s → ℂ} {f : 𝒮 V}
    (Θ : ThetaKernel (𝒮 V) S S') (hΘ : Θ.HasRealPart Ω) (hy : S.IsForm (typeKernel (-l) s) y)
    {k : InfinitePlace E → USign t → ℂ} {v : InfinitePlace E → fockSpace η}
    (k_cont : ∀ w : InfinitePlace E, Continuous (k w))
    (k_int : ∀ w : InfinitePlace E,
      Integrable fun g : USign t ↦ k w g * ‖(g : Matrix n' n' ℂ)‖ ^ card ι)
    (hk_proj : ∀ w : InfinitePlace E, integratedRep (π' w) (k w)
      (integratedRep (π w) (dsKernel (l w)) (polyVector η (Φ w))) =
        integratedRep (π w) (dsKernel (l w)) (v w)) (g : G E t) :
    let F : G E t → ℂ :=
      S.lift Θ (V.integrated (piTensor fun w : InfinitePlace E ↦ polyVector η (Φ w)) f) y
    Integrable (fun x : GInf E t ↦ (∏ w : InfinitePlace E, k w (x w)) * F (g * (x, 1))) ∧
      ∫ x : GInf E t, (∏ w : InfinitePlace E, k w (x w)) * F (g * (x, 1)) =
        S.lift Θ (V.integrated (piTensor v) f) y g := by
  -- The lift sees only the projected vector, so this is the local identity under the lift.
  intro F
  let p (w : InfinitePlace E) : fockSpace η →L[ℂ] fockSpace η :=
    integratedRep (π w) (dsKernel (l w))
  obtain ⟨L, hL⟩ : ∃ L : G E t → 𝒮 V →L[ℂ] ℂ, ∀ (φ : 𝒮 V) (g : G E t), S.lift Θ φ y g = L g φ :=
    Θ.exists_clm_lift (hy.mem_rapidFunctions (isCuspKernel_typeKernel_neg_of_isJointHarmonic hΦ))
  let pΦ : fockSpace (realSigns E η) := piTensor fun w ↦ p w (polyVector η (Φ w))
  let M (x : GInf E t) : ℂ := (∏ w, k w (x w)) * L g (V.integrated (Ω (1, x) pΦ) f)
  have h_mean : Integrable M ∧ ∫ x, M x = L g (V.integrated (piTensor fun w ↦ p w (v w)) f) := by
    simpa [M, pΦ, p, hk_proj, hΩ_right, ContinuousMultilinearMap.map_smul_univ] using
      integral_piTensor_eq_integratedRep (fun w ↦ (hp w).column_rep.unitary_rep) k k_cont k_int
        (fun w ↦ p w (polyVector η (Φ w))) (L g ∘L V.integrated.flip f)
  -- Translating the lift by `(x, 1)` is acting on the real vector by `Ω (1, x)`.
  have h_translate (x : GInf E t) : F (g * (x, 1)) = L g (V.integrated (Ω (1, x) pΦ) f) :=
    calc F (g * (x, 1)) = S.lift Θ (V.integrated pΦ f) y (g * (x, 1)) :=
          (lift_piTensor_integratedRep hp hΦ hΩ_left Θ hΘ hy _ f _).symm
      _ = L g (V.integrated (Ω (1, x) pΦ) f) := by
          rw [lift_mul_right, ← hL, ← hΘ 1 x pΦ f, Prod.mk_one_one]
  have h_target : S.lift Θ (V.integrated (piTensor v) f) y g =
      L g (V.integrated (piTensor fun w ↦ p w (v w)) f) := by
    rw [← hL, lift_piTensor_integratedRep hp hΦ hΩ_left Θ hΘ hy]
  simpa only [h_translate, h_target] using h_mean

omit [WeilData E] in
/-- Let `s`, `t` be the signs of two real unitary groups over the infinite places of `E`. At each
place `w`, let `π w`, `π' w` be commuting oscillator representations of `U(diag s)`, `U(diag t)` on
the rows and columns of the dual pair data `T w`, and let `Φ w` be a joint harmonic for `T w` of
parameters `l w`, `l' w`. If `Ω (x, 1)` maps each pure tensor `⊗ v w` to `⊗ π w (x w) (v w)`, then
for `Φ₀ = ⊗ polyVector η (Φ w)` the integral over `GInf E s` of `⟨Φ₀, Ω (x, 1) Φ₀⟩ * conj
(typeKernel (-l) s x) / typeKernel (-l) s 1` is not zero. -/
theorem integral_fockInner_mul_typeKernel_ne_zero {T : InfinitePlace E → FockDualPair s t ι}
    (hp : ∀ w : InfinitePlace E, OscillatorPair (T w) (π w) (π' w))
    (hΦ : ∀ w : InfinitePlace E, IsJointHarmonic (T w) (l w) (l' w) (Φ w))
    (hΩ_left : ∀ (v : InfinitePlace E → fockSpace η) (x : GInf E s),
      Ω (x, 1) (piTensor v) = piTensor fun w : InfinitePlace E ↦ π w (x w) (v w)) :
    let Φ₀ : fockSpace (realSigns E η) := piTensor fun w : InfinitePlace E ↦ polyVector η (Φ w)
    ∫ x : GInf E s, fockInner Φ₀ (Ω (x, 1) Φ₀) *
      (conj (typeKernel (-l) s x) / typeKernel (-l) s 1) ≠ 0 := by
  -- Up to the normalisation, it is a product of local pairings, each with positive real part.
  intro Φ₀
  let pΦ (w : InfinitePlace E) : fockSpace η :=
    integratedRep (π w) (dsKernel (l w)) (polyVector η (Φ w))
  have h_conj (x : GInf E s) : conj (typeKernel (-l) s x) = typeKernel l s x := by
    simp [typeKernel, conj_dsKernel_neg (hΦ _).hasGap_row]
  have h_pairing : ∫ x : GInf E s, fockInner Φ₀ (Ω (x, 1) Φ₀) * typeKernel l s x =
      ∏ w, fockInner (polyVector η (Φ w)) (pΦ w) := by
    simpa only [smul_eq_mul, mul_comm, Φ₀, fockInner_piTensor] using
      (integral_typeKernel_smul_piTensor hp hΦ hΩ_left _ (fockInner Φ₀)).right
  simp_rw [h_conj, ← mul_div_assoc, integral_div, h_pairing]
  refine div_ne_zero (Finset.prod_ne_zero_iff.2 fun w _ ↦ ?_)
    (isCuspKernel_typeKernel_neg_of_isJointHarmonic hΦ).apply_one_ne_zero
  exact ne_zero_of_re_pos ((hp w).re_inner_integratedRep_pos (hΦ w))

/-- If `Ω` acts on pure tensors place by place through oscillator pairs (commuting oscillator
representations of the two groups), the tensor product of the Fock vectors of joint harmonics `Φ w`
for the parameters `l w`, `l' w` (nonzero polynomials, harmonic and highest for both groups) is a
half edge from the kernel of type `-l` to the kernel of type `l'`. -/
theorem isHalfEdge_of_oscillatorPair {T : InfinitePlace E → FockDualPair s t ι}
    (hp : ∀ w : InfinitePlace E, OscillatorPair (T w) (π w) (π' w))
    (hΦ : ∀ w : InfinitePlace E, IsJointHarmonic (T w) (l w) (l' w) (Φ w))
    (hΩ_left : ∀ (v : InfinitePlace E → fockSpace η) (x : GInf E s),
      Ω (x, 1) (piTensor v) = piTensor fun w : InfinitePlace E ↦ π w (x w) (v w))
    (hΩ_right : ∀ (v : InfinitePlace E → fockSpace η) (y : GInf E t),
      Ω (1, y) (piTensor v) = piTensor fun w : InfinitePlace E ↦ π' w (y w) (v w)) :
    IsHalfEdge Ω (typeKernel (-l) s) (typeKernel l' t)
      (piTensor fun w : InfinitePlace E ↦ polyVector η (Φ w)) := by
  -- Let `p w` be the projection by the kernel of `l w`, which is `conj` of the kernel of `-l w`.
  -- Local identities `π' (k) p Φ = p v` make the lift with `v` the mean against `k` of the lift
  -- with `Φ` (`integral_mul_lift_eq_lift_piTensor`), so all reduces to local facts.
  let p (w : InfinitePlace E) : fockSpace η →L[ℂ] fockSpace η :=
    integratedRep (π w) (dsKernel (l w))
  have cusp : IsCuspKernel 0 (typeKernel (-l) s) :=
    isCuspKernel_typeKernel_neg_of_isJointHarmonic hΦ
  refine ⟨cusp, integral_fockInner_mul_typeKernel_ne_zero hp hΦ hΩ_left, ?_, ?_⟩
  · -- the kernel of `l'` fixes `p Φ`, hence the lift `F`, so `F` is a form of that type
    intro V S S' y f Θ hΘ hy K hK
    set F : G E t → ℂ := S.lift Θ (V.integrated (piTensor fun w ↦ polyVector η (Φ w)) f) y
    have h_gap (w : InfinitePlace E) : (toHCParam t (l' w)).HasLargeGap (card ι) :=
      (hΦ w).swap.hasLargeGap le_rfl
    have h_moment (w : InfinitePlace E) :
        Integrable fun g : USign t ↦ dsKernel (l' w) g * ‖(g : Matrix n' n' ℂ)‖ ^ card ι :=
      (h_gap w).integrable_dsKernel_mul_norm_pow (card ι) (Nat.le_succ _)
    have h_fix (g : G E t) : Integrable (fun x : GInf E t ↦ typeKernel l' t x * F (g * (x, 1))) ∧
        ∫ x : GInf E t, typeKernel l' t x * F (g * (x, 1)) = F g :=
      integral_mul_lift_eq_lift_piTensor hp hΦ hΩ_left hΩ_right Θ hΘ hy (by fun_prop) h_moment
        (fun w ↦ (hp w).integratedRep_integratedRep_eq_self (hΦ w) (h_moment w)
          (h_gap w).isIdempotentKernel_dsKernel.convolution_self) g
    have F_eq : realConv (typeKernel l' t) F = F := funext fun g ↦ (h_fix g).right
    rw [← F_eq]
    exact S'.isForm_realConv (isCuspKernel_typeKernel h_gap)
      ⟨Θ.continuous_lift (hy.mem_rapidFunctions cusp), Θ.fixesLeft_lift, K, hK⟩
      fun g ↦ (h_fix g).left
  · -- local bumps `g ↦ α a w g⁻¹` carry `p Φ` to `p` of the factor `v a w` of the monomial `a`
    let v (a : InfinitePlace E × ι →₀ ℕ) (w : InfinitePlace E) : fockSpace η :=
      polyVector η (monomial (a.curry w) 1)
    have local_bump (a : InfinitePlace E × ι →₀ ℕ) (w : InfinitePlace E) :
        ∃ α : DiscreteSeries.Bumps t,
        p w (v a w) = integratedRep (π' w) (fun g ↦ α.1.1 g⁻¹) (p w (polyVector η (Φ w))) :=
      (hp w).exists_bump_integratedRep_eq (hΦ w) _
    choose α hα using local_bump
    rintro _ ⟨P, rfl⟩
    refine ⟨∑ a ∈ P.support, P.coeff a • bumpProduct (α a),
      fun {V S S' y f} Θ hΘ hy ↦ funext fun g ↦ ?_⟩
    obtain ⟨L, hL⟩ : ∃ L : G E t → 𝒮 V →L[ℂ] ℂ, ∀ (φ : 𝒮 V) (g : G E t), S.lift Θ φ y g = L g φ :=
      Θ.exists_clm_lift (hy.mem_rapidFunctions cusp)
    let F : G E t → ℂ := S.lift Θ (V.integrated (piTensor fun w ↦ polyVector η (Φ w)) f) y
    have h_bump (a : InfinitePlace E × ι →₀ ℕ) :
        Integrable (fun x : GInf E t ↦ bumpProduct (α a) x * F (g * (x, 1))) ∧
        ∫ x : GInf E t, bumpProduct (α a) x * F (g * (x, 1)) =
          S.lift Θ (V.integrated (piTensor (v a)) f) y g :=
      integral_mul_lift_eq_lift_piTensor hp hΦ hΩ_left hΩ_right Θ hΘ hy (by fun_prop)
        (fun w ↦ DiscreteSeries.integrable_bump_inv_smul _ (α a w)) (fun w ↦ (hα a w).symm) g
    -- a monomial is a pure tensor, and both sides are linear in `P`
    calc S.lift Θ (V.integrated (polyVector (realSigns E η) P) f) y g
        = ∑ a ∈ P.support, P.coeff a * S.lift Θ (V.integrated (piTensor (v a)) f) y g := by
          conv_lhs => rw [P.as_sum]
          simp [v, hL, piTensor_polyVector, monomial_eq, C_mul', prod_prod_type]
      _ = realConv ⇑(∑ a ∈ P.support, P.coeff a • bumpProduct (α a)) F g := by
          simp [realConv, Finset.sum_mul, mul_assoc, integral_finsetSum, Integrable.const_mul,
            h_bump, integral_const_mul]

end Oscillator

/-- Let `s : n → ℤˣ`, `t : n' → ℤˣ` be the signs of two real unitary groups. At each infinite place
`w`, let `Φ w` be a joint harmonic for `FockDualPair.std t s (γ w) (-γ' w)` with parameters `l' w`,
`-l w`: a nonzero polynomial in variables indexed by `n' × n`, harmonic for both groups and, for
each group, highest of the weight of its lowest `K`-type. Then the Fock vector of the product of the
`Φ w`, each in the variables of `w`, is an edge for `realPairWeil γ γ'` from `typeKernel l s` to
`typeKernel l' t`. This means it is a half edge (`New.IsHalfEdge`, requiring in particular that the
integral of `⟨Φ, Ω (x, 1) Φ⟩` against `conj e / e 1` be nonzero) for these kernels, and also, with
the two groups exchanged, for their conjugates. -/
theorem isEdge_of_isJointHarmonic {Φ : InfinitePlace E → MvPolynomial (n' × n) ℂ}
    [Nonempty n] [Nonempty n']
    (hΦ : ∀ w : InfinitePlace E, IsJointHarmonic (.std t s (γ w) (-γ' w)) (l' w) (-l w) (Φ w)) :
    IsEdge (realPairWeil γ γ') (typeKernel l s) (typeKernel l' t)
      ↑(∏ w : InfinitePlace E, rename (w, ·) (Φ w)) := by
  -- On pure tensors the two groups act place by place, through the oscillator pairs `π' w`, `π w`.
  let π (w : InfinitePlace E) :
      USign s →* fockSpace (homSigns s t) →L[ℂ] fockSpace (homSigns s t) :=
    detTwist ((pairHom t s).comp (MonoidHom.inl (USign s) (USign t))) (-γ' w)
  let π' (w : InfinitePlace E) :
      USign t →* fockSpace (homSigns s t) →L[ℂ] fockSpace (homSigns s t) :=
    detTwist ((pairHom t s).comp (MonoidHom.inr (USign s) (USign t))) (γ w)
  have h_pair (w : InfinitePlace E) : OscillatorPair (.std t s (γ w) (-γ' w)) (π' w) (π w) :=
    oscillatorPair_detTwist
  have hπ (v : InfinitePlace E → fockSpace (homSigns s t)) (x : GInf E s) :
      realPairWeil γ γ' (x, 1) (piTensor v) = piTensor fun w ↦ π w (x w) (v w) := by
    simp [π, realPairWeil, pairHomInf, realWeil_piTensor, ContinuousMultilinearMap.map_smul_univ]
  have hπ' (v : InfinitePlace E → fockSpace (homSigns s t)) (y : GInf E t) :
      realPairWeil γ γ' (1, y) (piTensor v) = piTensor fun w ↦ π' w (y w) (v w) := by
    simp [π', realPairWeil, pairHomInf, realWeil_piTensor, ContinuousMultilinearMap.map_smul_univ]
  rw [← piTensor_polyVector Φ]
  constructor
  · -- the half edge from `l` to `l'` comes from the swapped pair
    rw [← neg_neg l]
    exact isHalfEdge_of_oscillatorPair (fun w ↦ (h_pair w).swap) (fun w ↦ (hΦ w).swap) hπ hπ'
  · -- for the reverse one, conjugation changes the sign of the parameters
    have h_conj : Star.star (typeKernel l s) = typeKernel (-l) s :=
      funext fun x ↦ by simp [typeKernel, ← conj_dsKernel_neg (hΦ _).hasGap_column]
    have h_conj' : Star.star (typeKernel l' t) = typeKernel (-l') t :=
      funext fun y ↦ by simp [typeKernel, ← conj_dsKernel_neg (hΦ _).hasGap_row]
    rw [h_conj, h_conj']
    exact isHalfEdge_of_oscillatorPair h_pair hΦ hπ' hπ

/-- If `l`, `l'` correspond (the block rule holds at every infinite place), the Fock vector
`jointHarmonic` is an edge for the real Weil representation `realPairWeil γ γ'` from
`typeKernel l s` to `typeKernel l' t`. Here `jointHarmonic` is the product over places `w` of the
chosen polynomials `jointHarmonicAt`. Being an edge means a half edge for these kernels, and also
for the representation with its groups exchanged and the conjugate kernels in reverse order.
`typeKernel l s` is ∏_w (formal degree)·conj(discrete series coefficient) on U(diag s). -/
theorem ParamsCorrespond.isEdge_jointHarmonic [Nonempty n] [Nonempty n']
    (h_corr : ParamsCorrespond γ γ' l l' s t) :
    IsEdge (realPairWeil γ γ') (typeKernel l s) (typeKernel l' t) (jointHarmonic γ γ' l l' s t) :=
  isEdge_of_isJointHarmonic fun w ↦ isJointHarmonic_jointHarmonicAt (h_corr.isMatch w)

end Edge

/-!
## Arrows: the theta lift on forms, equivariance and adjoints

The theta lift as a linear map between spaces of forms. A theta kernel K for spaces S and T
(`New.ThetaKernel`) consists of a representation ω of the pair of their adelic unitary groups and a
functional θ, and `New.Space.lift` integrates a function on the first group against the kernel
θ(ω(g, h)φ). `New.Space.Form S e` is the space of forms of type e on S (`New.Space.IsForm`), and
`New.ThetaKernel.swap` exchanges the two groups, so that its lifts are the transposed lifts.
-/

section Arrow

open ComplexConjugate Space InnerProductSpace Submodule LinearMap

variable {E n n' : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] {s : n → ℤˣ} {t : n' → ℤˣ}
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {S : Space E n s} {T : Space E n' t} (K : ThetaKernel X S T) (e : GInf E s → ℂ)
  (e' : GInf E t → ℂ) {φ φ' : X}

/-- A chosen bilinear map (φ, y) ↦ L_φ y from data and forms of type e on S to forms of type e' on T
that agrees with the theta lift `New.Space.lift` whenever y is of rapid decay and its lift is such a
form. It is built from left inverses of the inclusions of these spaces of functions. -/
def formLift : X →ₗ[ℂ] S.Form e →ₗ[ℂ] T.Form e' :=
  (K.liftBilin.compl₂ (S.rapidFunctions.toSubmodule.subtype.leftInverse ∘ₗ
    (S.formSubmodule e).subtype)).compr₂ (T.formSubmodule e').subtype.leftInverse

/-- The datum φ is an arrow e → e' for the theta kernel K: forms of type e on S are rapid, and their
lifts by φ are forms of type e' on T. -/
def IsArrow (φ : X) : Prop :=
  ∀ y : S.Form e, y.val ∈ S.rapidFunctions ∧ T.IsForm e' (lift K φ y)

variable {K e e'}

/-- Complex conjugation F ↦ conj(F), as a conjugate-linear map from forms of type e to forms of
type e', when e' is the conjugate of e. -/
def conjForm {e' : GInf E s → ℂ} (h : e' = star e) : S.Form e →ₗ⋆[ℂ] S.Form e' :=
  (starLinearEquiv ℂ).toLinearMap.restrict fun F hF ↦ by
    subst h
    exact hF.conj

/-- `conjForm h y` is the pointwise complex conjugate of `y`. -/
@[simp]
lemma coe_conjForm {e' : GInf E s → ℂ} (he' : e' = star e) (y : S.Form e) :
    (conjForm he' y : S.Form e') = fun g : G E s ↦ conj (y g) := rfl

/-- Let Φ be an edge e → e' for the real Weil representation `realPairWeil γ γ'`. This means Φ is a
half edge from e to e', and also, with the two groups exchanged, from ē' to ē. A half edge requires
that e is a cusp kernel of order 0, that ∫⟨Φ, Ω(x,1)Φ⟩·conj e(x)/e(1) dx ≠ 0, and that lifts with Φ
of forms of type e are of type e' once they have a level. Let a, b be automorphic characters of
weights γ, γ' with tame parts ψ, ψ', and let f lie in the finite part of the data space of
`S.hom T`. Then for the theta kernel `pairThetaKer S T a b`, the datum
Φ ⊗ f = `integrated (S.hom T) Φ f` is an arrow e → e' (forms of type e are rapid and lift to forms
of type e'), and for the swapped kernel it is an arrow ē' → ē. -/
lemma IsEdge.isArrow [WeilData E] {γ γ' : NumberField.InfinitePlace E → ℤ}
    {Φ : Fock.fockSpace (realSigns E (homSigns s t))}
    {ψ ψ' : (w : FinPlace E) → MulChar (ResField w) ℂ} {f : 𝒮 (S.hom T)}
    (hΦ : IsEdge (realPairWeil γ γ') e e' Φ) (a b : AutChar E) [a.HasWeight γ ψ] [b.HasWeight γ' ψ']
    (hf : f ∈ (S.hom T).finitePart) :
    IsArrow (pairThetaKer S T a b) e e' (integrated (S.hom T) Φ f) ∧
      IsArrow (pairThetaKer S T a b).swap (star e') (star e) (integrated (S.hom T) Φ f) := by
  -- `f`, hence the datum, is fixed by a level `U × U'`, and real points act on the real vector
  -- only. Under these two conditions `IsHalfEdge.isForm_lift` says that the lift is a form.
  obtain ⟨U, U', h_fix⟩ : ∃ (U : OpenSubgroup (Gf E n)) (U' : OpenSubgroup (Gf E n')),
      ∀ k ∈ U, ∀ k' ∈ U', pairWeil S T a b ((1, k), 1, k') f = f := exists_level_pairWeil a b hf
  let Θ : ThetaKernel (𝒮 (S.hom T)) S T := pairThetaKer S T a b
  have h_real : Θ.HasRealPart (realPairWeil γ γ') := pairWeil_integrated S T a b
  have h_real_swap : Θ.swap.HasRealPart (realPairWeil γ γ' ·.swap) := by
    simp [Θ, ThetaKernel.HasRealPart, pairWeil_integrated]
  have h_level (y : G E s → ℂ) : HasLevel (lift Θ (integrated (S.hom T) Φ f) y) U' := by
    simp +contextual [Θ, h_fix, lift_mul_right, ← Prod.mk_one_one]
  have h_level_swap (y : G E t → ℂ) : HasLevel (lift Θ.swap (integrated (S.hom T) Φ f) y) U := by
    simp +contextual [Θ, h_fix, lift_mul_right, ← Prod.mk_one_one]
  constructor
  · exact fun y ↦ ⟨y.prop.mem_rapidFunctions hΦ.isCuspKernel_source,
      hΦ.isForm_lift Θ h_real y.prop U' (h_level y)⟩
  · exact fun y ↦ ⟨y.prop.mem_rapidFunctions hΦ.swapped.isCuspKernel_source,
      hΦ.swapped.isForm_lift Θ.swap h_real_swap y.prop U (h_level_swap y)⟩

/-- Let Φ be an edge e → e' for `realPairWeil γ γ'`. This means Φ is a half edge from e to e', and
also, with the two groups exchanged, from ē' to ē. A half edge requires that e is a cusp kernel of
order 0, that ∫⟨Φ, Ω(x,1)Φ⟩·conj e(x)/e(1) dx ≠ 0, and that lifts with Φ of forms of type e are of
type e' once they have a level. Let a, b be automorphic characters of weights γ, γ' with tame parts
ψ, ψ', and let f lie in the finite part of `S.hom T`. Then for every form y' of type e' on T, the
descent by Φ ⊗ f is a form of type e on S. Here the descent is the conjugate of the lift of ȳ' by
Φ ⊗ f for the swapped kernel of `pairThetaKer S T a b`. -/
lemma IsEdge.isForm_star_lift_swap [WeilData E] {γ γ' : NumberField.InfinitePlace E → ℤ}
    {Φ : Fock.fockSpace (realSigns E (homSigns s t))}
    {ψ ψ' : (w : FinPlace E) → MulChar (ResField w) ℂ} {f : 𝒮 (S.hom T)}
    (hΦ : IsEdge (realPairWeil γ γ') e e' Φ) (a b : AutChar E) [a.HasWeight γ ψ] [b.HasWeight γ' ψ']
    (hf : f ∈ (S.hom T).finitePart) (y' : T.Form e') :
    S.IsForm e
      (star (lift (pairThetaKer S T a b).swap (integrated (S.hom T) Φ f) (star y'.val))) := by
  have h_swap : IsArrow (pairThetaKer S T a b).swap (star e') (star e) (integrated (S.hom T) Φ f) :=
    (hΦ.isArrow a b hf).right
  have h_conj : S.IsForm (star (star e))
      (star (lift (pairThetaKer S T a b).swap (integrated (S.hom T) Φ f) (star y'.val))) :=
    (h_swap (conjForm rfl y')).right.conj
  rwa [star_star] at h_conj

open MvPolynomial NumberField CompactlySupported in
/-- Let Φ be an edge e → e' for the real Weil representation of weights γ, γ'; that is, Φ is a half
edge e → e', and also conj e' → conj e with the groups exchanged. There is a linear form κ on
polynomials with the following property for all spaces S, T of signs s, t, all characters a, b of
these weights, all f in the finite part of `S.hom T` (spanned by the finite Heisenberg translates of
the vacuum), all polynomials P and all forms y, y' of types e, e'. With the theta kernel
`pairThetaKer S T a b`, the Petersson product of y' with the lift of y by v_P ⊗ f is κ(P) times that
with the lift by Φ ⊗ f, and likewise for the product of ȳ with the transposed lift of ȳ'. Here v_P
is the Fock vector of P, v ⊗ f is `integrated (S.hom T) v f`, the transposed lift is the lift for
`K.swap`, and ȳ is the complex conjugate of y. -/
lemma IsEdge.exists_petersson_lift_eq_mul [WeilData E] {γ γ' : InfinitePlace E → ℤ}
    {Φ : Fock.fockSpace (realSigns E (homSigns s t))} (hΦ : IsEdge (realPairWeil γ γ') e e' Φ) :
    ∃ κ : MvPolynomial (InfinitePlace E × n' × n) ℂ →ₗ[ℂ] ℂ,
      ∀ {S : Space E n s} {T : Space E n' t} {ψ ψ' : (w : FinPlace E) → MulChar (ResField w) ℂ}
        (a b : AutChar E) [a.HasWeight γ ψ] [b.HasWeight γ' ψ'] {f : 𝒮 (S.hom T)},
        f ∈ (S.hom T).finitePart →
        ∀ (P : MvPolynomial (InfinitePlace E × n' × n) ℂ) (y : S.Form e) (y' : T.Form e'),
        let K : ThetaKernel (𝒮 (S.hom T)) S T := pairThetaKer S T a b
        let φ : 𝒮 (S.hom T) :=
          integrated (S.hom T) (Fock.polyVector (realSigns E (homSigns s t)) P) f
        let φ₀ : 𝒮 (S.hom T) := integrated (S.hom T) Φ f
        T.petersson y' (lift K φ y) = κ P * T.petersson y' (lift K φ₀ y) ∧
        S.petersson (star y.val) (lift K.swap φ (star y'.val)) =
          κ P * S.petersson (star y.val) (lift K.swap φ₀ (star y'.val)) := by
  -- The lift by a monomial `m` is the convolution of the form `lift K φ₀ y` with a continuous
  -- function `α m` of compact support. As `y'` and that form have type `e'`, this scales their
  -- product by a number `c m`. Extend these numbers linearly.
  have he' : IsCuspKernel 0 e' := by simpa using hΦ.swapped.isCuspKernel_source.star
  have h_conv (m : InfinitePlace E × n' × n →₀ ℕ) : ∃ α : C_c(GInf E t, ℂ),
      ∀ {V : Space E (n' × n) (homSigns s t)} {S : Space E n s} {T : Space E n' t} {y : G E s → ℂ}
        {f : 𝒮 V} (Θ : ThetaKernel (𝒮 V) S T), Θ.HasRealPart (realPairWeil γ γ') → S.IsForm e y →
        lift Θ (integrated V (Fock.polyVector (realSigns E (homSigns s t)) (monomial m 1)) f) y =
          realConv α (lift Θ (integrated V Φ f) y) :=
    hΦ.exists_lift_eq_realConv _ ⟨monomial m 1, rfl⟩
  choose α hα using h_conv
  let c (m : InfinitePlace E × n' × n →₀ ℕ) : ℂ := ∫ x : GInf E t, α m x * (conj (e' x) / e' 1)
  let κ : MvPolynomial (InfinitePlace E × n' × n) ℂ →ₗ[ℂ] ℂ := (basisMonomials _ ℂ).constr ℂ c
  refine ⟨κ, fun {S T ψ ψ'} a b _ _ f hf P y y' ↦ ?_⟩
  intro K φ φ₀
  obtain ⟨hy, h_form⟩ : y.val ∈ S.rapidFunctions ∧ T.IsForm e' (lift K φ₀ y) :=
    (hΦ.isArrow a b hf).left y
  have hy' : y'.val ∈ T.rapidFunctions := y'.prop.mem_rapidFunctions he'
  let L : MvPolynomial (InfinitePlace E × n' × n) ℂ →ₗ[ℂ] ℂ :=
    (K.isLinearMap_petersson_lift hy hy').mk' _ ∘ₗ ((integrated (S.hom T)).flip f).toLinearMap ∘ₗ
      Fock.polyVector _
  have h_L (Q : MvPolynomial (InfinitePlace E × n' × n) ℂ) :
      L Q = T.petersson y' (lift K (integrated (S.hom T) (Fock.polyVector _ Q) f) y) := rfl
  have h_monomial (m : InfinitePlace E × n' × n →₀ ℕ) :
      L (monomial m 1) = c m * T.petersson y' (lift K φ₀ y) := by
    -- convolve with `α m`, then move the real translation to `y'`
    rw [h_L, hα m K (pairWeil_integrated S T a b) y.prop, petersson_realConv_right
      h_form.isBoundedMeasurable (α m).integrable y'.prop.isBoundedMeasurable]
    simp only [c, ← MeasureTheory.integral_mul_const, y'.prop.petersson_real_translate he' h_form,
      mul_assoc]
  have h_eq : L = κ.smulRight (T.petersson y' (lift K φ₀ y)) := (basisMonomials _ ℂ).ext fun m ↦ by
    rw [smulRight_apply, Module.Basis.constr_basis, coe_basisMonomials, h_monomial, smul_eq_mul]
  have h_lift : T.petersson y' (lift K φ y) = κ P * T.petersson y' (lift K φ₀ y) := by
    rw [← h_L, h_eq, LinearMap.smulRight_apply, smul_eq_mul]
  -- Lift and transposed lift give the same integral.
  have h_transpose (χ : 𝒮 (S.hom T)) :
      S.petersson (star y.val) (lift K.swap χ (star y'.val)) = T.petersson y' (lift K χ y) := by
    simpa only [petersson, starRingEnd_apply, Pi.star_apply, star_star] using
      (K.integral_mul_lift_eq_integral_mul_lift_swap hy (star_mem_rapidFunctions hy')).symm
  exact ⟨h_lift, by rw [h_transpose, h_transpose, h_lift]⟩

namespace IsArrow

/-- If some datum φ is an arrow e → e', then for any datum φ' a form z of type e' whose underlying
function is the lift of y by φ' is the value of `New.formLift` at φ' and y. -/
lemma eq_formLift_of_coe_eq (hφ : IsArrow K e e' φ) {y : S.Form e} (z : T.Form e')
    (hz : z.val = lift K φ' y.val) : z = formLift K e e' φ' y := by
  -- Each of the two left inverses in `formLift` undoes the inclusion of its submodule: `y` is
  -- rapid, and `z` is a form of type `e'`.
  let R : Submodule ℂ (G E s → ℂ) := S.rapidFunctions.toSubmodule
  have h_rapid : R.subtype.leftInverse y.val = ⟨y.val, (hφ y).left⟩ :=
    leftInverse_apply_of_inj (ker_subtype R) ⟨y.val, (hφ y).left⟩
  have h_lift : z.val = K.liftBilin φ' (R.subtype.leftInverse y.val) := by rwa [h_rapid]
  exact (leftInverse_apply_of_inj (ker_subtype _) z).symm.trans (congrArg _ h_lift)

attribute [irreducible] formLift

/-- If the datum φ is an arrow from type e to type e' (forms of type e are rapid and lift to forms
of type e'), then the function underlying `formLift K e e' φ y` is the theta lift of y by φ. -/
lemma coe_formLift (hφ : IsArrow K e e' φ) (y : S.Form e) : formLift K e e' φ y = lift K φ y :=
  congrArg Subtype.val (hφ.eq_formLift_of_coe_eq ⟨lift K φ y, (hφ y).right⟩ rfl).symm

/-- If φ is an arrow e → e', then for k, k' in the finite groups of S, T and a form y of type e,
the right translate by k' of the lift of y by φ is the lift by ω(k, k')φ of the right translate of
y by k. -/
lemma formRep_formLift (hφ : IsArrow K e e' φ) (k : Gf E n) (k' : Gf E n') (y : S.Form e) :
    T.formRep e' k' (formLift K e e' φ y) =
      formLift K e e' (K.ω ((1, k), 1, k') φ) (S.formRep e k y) := by
  refine hφ.eq_formLift_of_coe_eq _ (funext fun g ↦ ?_)
  rw [formRep_apply, hφ.coe_formLift]
  exact K.lift_equivariant y.prop.toIsAutomorphic φ (1, k) (1, k') g

/-- Let φ be an arrow and k, k' finite points with ω(k, k')φ = cφ'. Then the translate by k' of
the lift of a form y by φ is c times the lift by φ' of the translate of y by k. -/
lemma formRep_formLift_of_eq_smul (hφ : IsArrow K e e' φ) {k : Gf E n} {k' : Gf E n'} {c : ℂ}
    (hω : K.ω ((1, k), 1, k') φ = c • φ') (y : S.Form e) :
    T.formRep e' k' (formLift K e e' φ y) = c • formLift K e e' φ' (S.formRep e k y) := by
  simp [hφ.formRep_formLift k, hω]

/-- If φ is an arrow e → e' and, for the swapped kernel, an arrow ε' → ε, then
∫_{[T]} z·L_φ y = ∫_{[S]} y·Lᵗ_φ z for forms y of type e and z of type ε', where L_φ is the lift and
Lᵗ_φ the transposed lift by φ. -/
lemma integral_mul_formLift_swap (hφ : IsArrow K e e' φ) {ε : GInf E s → ℂ} {ε' : GInf E t → ℂ}
    (h_swap : IsArrow K.swap ε' ε φ) (y : S.Form e) (z : T.Form ε') :
    ∫ g : G E t, z g * formLift K e e' φ y g ∂T.quotMeasure =
      ∫ g : G E s, y g * formLift K.swap ε' ε φ z g ∂S.quotMeasure := by
  simpa only [hφ.coe_formLift, h_swap.coe_formLift] using
    K.integral_mul_lift_eq_integral_mul_lift_swap (hφ y).left (h_swap z).left

/-- If φ is an arrow e → e' and, for the swapped kernel, an arrow between the conjugate types, then
⟨L_φ y, x⟩ = ⟨y, conj(Lᵗ_φ conj(x))⟩, where L_φ is the lift and Lᵗ_φ the transposed lift by φ. So
the adjoint of the lift is the descent x ↦ conj(Lᵗ_φ conj(x)). -/
lemma inner_formLift_adjoint (hφ : IsArrow K e e' φ) {ε : GInf E s → ℂ} {ε' : GInf E t → ℂ}
    (h_swap : IsArrow K.swap ε' ε φ) (hε' : ε' = star e') (he : e = star ε) (x : T.Form e')
    (y : S.Form e) :
    ⟪formLift K e e' φ y, x⟫_ℂ = ⟪y, conjForm he (formLift K.swap ε' ε φ (conjForm hε' x))⟫_ℂ := by
  have hx_conj : star x.val ∈ T.rapidFunctions := (h_swap (conjForm hε' x)).left
  have h_descent : (conjForm he (formLift K.swap ε' ε φ (conjForm hε' x))).val =
      star (lift K.swap φ (star x.val)) := congrArg star (h_swap.coe_formLift (conjForm hε' x))
  rw [inner_eq_petersson, inner_eq_petersson, hφ.coe_formLift, h_descent, ← conj_petersson,
    K.petersson_lift_eq_petersson_descent (hφ y).left
      (by simpa using star_mem_rapidFunctions hx_conj), conj_petersson]

end IsArrow

end Arrow

end New

end
