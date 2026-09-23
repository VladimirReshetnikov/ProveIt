import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Lex
import Mathlib.Data.Complex.BigOperators
import Surreal.HahnSeries.RowColumnFinite
import Surreal.HahnSeries.ComplexNumbers
import Surreal.HahnSeries.StrongMeasure

/-!
# The Hahn inner product on row-finite Hahn vectors

This file formalizes `ihs:rf:prop:inner` (with both formulas of `ihs:rf:eq:inner`),
`ihs:rf:lem:strongaction` and the example `ihs:rf:prop:degenerate` of
`docs/surcomplex/infinite-dimensional-hahn-spectral-theory/article.tex` (Part II). It builds on
`Surreal.HahnSeries.RowColumnFinite`, which provides `R_I = rcf k I`, `𝒜_rf = (rcf k I)⟦Γ⟧`
with its coefficientwise involution, and the convolution action of `𝒜_rf` on
`ℋ_rf = V_I((t^Γ))`, `V_I = I →₀ k`.

`ihs:rf:prop:inner`. Take any commutative semiring `k` with a `StarRing` structure (the source's
`ℂ`), any index type `I`, and exponents in any partially ordered cancellative commutative monoid
`Γ`; divisibility is never used.
* `hahnInner x y = ∑_{α, β} ⟨x_α, y_β⟩ t^{α + β}` is defined coefficientwise by the finite sum
  over the pairs of support exponents with `α + β = γ` (`coeff_hahnInner`). The family
  `innerFamily x y : i ↦ conj(x_i) y_i` of coordinate products is strongly summable (a Mathlib
  `SummableFamily`), and its Hahn sum is `hahnInner x y` (`hsum_innerFamily`): this is the second
  formula of `ihs:rf:eq:inner`.
* It is additive in both arguments, linear over `K = k((t^Γ))` in the second argument and
  conjugate-linear in the first (`hahnInner_smul_right`, `hahnInner_smul_left`, for the
  `HahnModule Γ k` action of `K`), and Hermitian: `conj ⟨x, y⟩ = ⟨y, x⟩` (`hahnStar_hahnInner`).
* Adjoint relation: `⟨Xx, y⟩ = ⟨x, X*y⟩` for every `X ∈ 𝒜_rf` (`hahnInner_rcf_smul_left`). The
  proof regroups triple sums over support exponents (`sum_antidiagonal_assoc`) and applies the
  finite adjoint identity `finInner_smul_left` of `ihs:rf:lem:rcf` coefficientwise.
* For linearly ordered `Γ`, the coefficients of `⟨x, x⟩` below `2 v(x)` vanish and its
  coefficient at `2 v(x)` is `⟨x_{v(x)}, x_{v(x)}⟩` (`coeff_hahnInner_self_of_lt`,
  `coeff_hahnInner_self_order`). Hence `v(⟨x, x⟩) = 2 v(x)`, with `v = orderTop`, whenever the
  finite form is anisotropic (`orderTop_hahnInner_self`), in particular over `ℂ`
  (`orderTop_hahnInner_self_complex`).
* Over `k = ℂ`, for `x ≠ 0`, `⟨x, x⟩` is the image of a real series `r ∈ F = ℝ((t^Γ))` with
  `0 < r` in the lexicographic order of `F` (a nonzero real series is positive exactly when its
  leading coefficient is), `v(r) = 2 v(x)` and `r_{2 v(x)} = ∑_i |(x_{v(x)})_i|² > 0`
  (`hahnInner_self_pos`). No square roots are used.

`ihs:rf:lem:strongaction`, for the same `k`, `I`, `Γ` and any index type of the families:
* a strongly summable family `(x_a)` in `ℋ_rf` and `X ∈ 𝒜_rf` give a strongly summable `(X x_a)`
  with `∑^H X x_a = X (∑^H x_a)` (`exists_summable_rcf_smul`); likewise a strongly summable
  `(X_a)` in `𝒜_rf` acting on a fixed vector (`exists_summable_smul_rcf`);
* multiplication of a strongly summable family in `𝒜_rf` by a fixed element, on either side
  (`exists_summable_mul_left`, `exists_summable_mul_right`);
* the inner product with a fixed vector, in either argument: the families `a ↦ ⟨x, y_a⟩` and
  `a ↦ ⟨x_a, y⟩` are strongly summable, with `⟨x, ∑^H y_a⟩ = ∑^H ⟨x, y_a⟩` and
  `⟨∑^H x_a, y⟩ = ∑^H ⟨x_a, y⟩` (`hsum_innerRightFamily`, `hsum_innerLeftFamily`).
The operator clauses restate Mathlib's `SummableFamily.hsum_smul_module`, `smul_hsum`,
`hsum_smul` and `hsum_mul` for `𝒜_rf` and `ℋ_rf`.

`ihs:rf:prop:degenerate`, for `k = ℂ`, `I = ℤ` and any linearly ordered cancellative
commutative monoid `Γ`. The bilateral adjacency operator `(Tx)_n = x_{n-1} + x_{n+1}` is an
element `adjacency` of `R_ℤ = RCF_ℤ(ℂ)` with `T* = T` (`star_adjacency`) and no eigenvector in
`ℂ^(ℤ)` for any eigenvalue in `ℂ` (`adjacency_smul_ne_smul`); in particular `T` has trivial
kernel on `ℂ^(ℤ)` (`adjacency_smul_ne_zero`). For `η ∈ Γ`, the operator
`A = Id + t^η T ∈ 𝒜_rf` (`degenerateOp η`) satisfies:
* `A* = A` (`star_degenerateOp`), hence `⟨Ax, y⟩ = ⟨x, Ay⟩`
  (`hahnInner_degenerateOp_smul_left`);
* for `η > 0` and `x ≠ 0`, `⟨x, Ax⟩` is the image of a real series `r` with `0 < r` in the
  lexicographic order, `v(r) = 2 v(x)` and the same coefficient `∑_i |(x_{v(x)})_i|²` at
  `2 v(x)` as `⟨x, x⟩` (`hahnInner_degenerateOp_pos`);
* for every `η` (positivity of `η` is not needed here), every `z ∈ K` and every `x ≠ 0`,
  `Ax ≠ zx`, where `zx` is the `K`-vector-space action (`degenerateOp_smul_ne_smul`), so `A` has
  no eigenvalue in `K`.

All clauses of `ihs:rf:prop:inner`, `ihs:rf:lem:strongaction` and `ihs:rf:prop:degenerate` are
proved; positivity is stated for `k = ℂ`, as in the source. The remark `ihs:rf:rem:nodiv`
(including its square root of the squared length) is not formalized here.
-/

open scoped HahnSeries Pointwise

namespace Surreal.RowFiniteInner

open Finsupp Surreal.RowColumnFinite

noncomputable section

section Antidiagonal

variable {Γ : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]

/-- Enlarging the index sets of an antidiagonal sum does not change it when the summand
vanishes off the original sets. -/
theorem sum_antidiagonal_mono {M : Type*} [AddCommMonoid M] {s t s' t' : Set Γ}
    (hs : s.IsPWO) (ht : t.IsPWO) (hs' : s'.IsPWO) (ht' : t'.IsPWO) (hss : s ⊆ s')
    (htt : t ⊆ t') (f : Γ → Γ → M) (hf : ∀ i j, ¬ (i ∈ s ∧ j ∈ t) → f i j = 0) (a : Γ) :
    ∑ p ∈ Finset.antidiagonal hs ht a, f p.1 p.2 =
      ∑ p ∈ Finset.antidiagonal hs' ht' a, f p.1 p.2 := by
  refine Finset.sum_subset (fun p hp => ?_) (fun p hp hpn => hf _ _ fun h => hpn ?_)
  · rw [Finset.mem_antidiagonal] at hp ⊢
    exact ⟨hss hp.1, htt hp.2.1, hp.2.2⟩
  · rw [Finset.mem_antidiagonal] at hp ⊢
    exact ⟨h.1, h.2, hp.2.2⟩

/-- Antidiagonal sums can be read with the two factors interchanged. -/
theorem sum_antidiagonal_swap {M : Type*} [AddCommMonoid M] {s t : Set Γ} (hs : s.IsPWO)
    (ht : t.IsPWO) (f : Γ → Γ → M) (a : Γ) :
    ∑ p ∈ Finset.antidiagonal hs ht a, f p.1 p.2 =
      ∑ p ∈ Finset.antidiagonal ht hs a, f p.2 p.1 :=
  Finset.sum_equiv (Equiv.prodComm Γ Γ) (fun _ => Finset.swap_mem_antidiagonal.symm)
    fun _ _ => rfl

/-- Reassociation of iterated antidiagonal sums: both sides are the sum of `f i j l` over the
triples in `s × t × u` with `i + j + l = a`. -/
theorem sum_antidiagonal_assoc {M : Type*} [AddCommMonoid M] {s t u : Set Γ} (hs : s.IsPWO)
    (ht : t.IsPWO) (hu : u.IsPWO) (f : Γ → Γ → Γ → M) (a : Γ) :
    ∑ p ∈ Finset.antidiagonal (hs.add ht) hu a,
        ∑ q ∈ Finset.antidiagonal hs ht p.1, f q.1 q.2 p.2 =
      ∑ p ∈ Finset.antidiagonal hs (ht.add hu) a,
        ∑ q ∈ Finset.antidiagonal ht hu p.2, f p.1 q.1 q.2 := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ ↦ ⟨(k, l + j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ ↦ ⟨(i + k, l), (i, k)⟩) <;>
    aesop (add safe Set.add_mem_add) (add simp [add_assoc])

/-- An antidiagonal over `s` and `t` is empty at points outside `s + t`. -/
theorem antidiagonal_eq_empty {s t : Set Γ} (hs : s.IsPWO) (ht : t.IsPWO) {a : Γ}
    (ha : a ∉ s + t) : Finset.antidiagonal hs ht a = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun p hp => ha ?_
  rw [Finset.mem_antidiagonal] at hp
  exact ⟨p.1, hp.1, p.2, hp.2.1, hp.2.2⟩

/-- The coefficients of `c • y` in a Hahn module, summed over any enlarged index sets. -/
theorem coeff_of_symm_smul {R V : Type*} [Zero R] [AddCommMonoid V] [SMulWithZero R V]
    (c : R⟦Γ⟧) (y : V⟦Γ⟧) {s t : Set Γ} (hs : s.IsPWO) (ht : t.IsPWO) (hcs : c.support ⊆ s)
    (hyt : y.support ⊆ t) (b : Γ) :
    ((HahnModule.of R).symm (c • HahnModule.of R y)).coeff b =
      ∑ p ∈ Finset.antidiagonal hs ht b, c.coeff p.1 • y.coeff p.2 := by
  rw [HahnModule.coeff_smul]
  refine sum_antidiagonal_mono c.isPWO_support y.isPWO_support hs ht hcs hyt
    (fun i j => c.coeff i • y.coeff j) (fun i j h => ?_) b
  rw [not_and_or, HahnSeries.mem_support, HahnSeries.mem_support, not_not, not_not] at h
  rcases h with h | h
  · rw [h, zero_smul]
  · rw [h, smul_zero]

/-- The support of `c • y` lies in `supp c + supp y`. -/
theorem support_of_symm_smul_subset {R V : Type*} [Zero R] [AddCommMonoid V]
    [SMulWithZero R V] (c : R⟦Γ⟧) (y : V⟦Γ⟧) :
    ((HahnModule.of R).symm (c • HahnModule.of R y)).support ⊆ c.support + y.support :=
  fun b hb => by
    by_contra h
    apply hb
    rw [coeff_of_symm_smul c y c.isPWO_support y.isPWO_support subset_rfl subset_rfl,
      antidiagonal_eq_empty _ _ h, Finset.sum_empty]

end Antidiagonal

section Generic

variable {Γ : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
  {k I : Type*} [CommSemiring k] [StarRing k]

/-- The finite-support inner product is additive over finite sums in its first argument. -/
theorem finInner_sum_left {ι : Type*} (s : Finset ι) (v : ι → I →₀ k) (w : I →₀ k) :
    finInner (∑ q ∈ s, v q) w = ∑ q ∈ s, finInner (v q) w := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, finInner_zero_left]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, finInner_add_left, ih]

/-- The finite-support inner product is additive over finite sums in its second argument. -/
theorem finInner_sum_right {ι : Type*} (s : Finset ι) (v : I →₀ k) (w : ι → I →₀ k) :
    finInner v (∑ q ∈ s, w q) = ∑ q ∈ s, finInner v (w q) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, finInner_zero_right]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, finInner_add_right, ih]

/-- The finite-support inner product is Hermitian. -/
theorem star_finInner (v w : I →₀ k) : star (finInner v w) = finInner w v := by
  induction v using Finsupp.induction_linear with
  | zero => rw [finInner_zero_left, finInner_zero_right, star_zero]
  | add v v' hv hv' => rw [finInner_add_left, finInner_add_right, star_add, hv, hv']
  | single j a => rw [finInner_single_left, finInner_single_right, star_mul, star_star]

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
/-- The finite inner product of two coefficients vanishes unless both exponents lie in the
supports. -/
theorem finInner_coeff_eq_zero (x y : (I →₀ k)⟦Γ⟧) {i j : Γ}
    (h : ¬ (i ∈ x.support ∧ j ∈ y.support)) : finInner (x.coeff i) (y.coeff j) = 0 := by
  rw [not_and_or, HahnSeries.mem_support, HahnSeries.mem_support, not_not, not_not] at h
  rcases h with h | h
  · rw [h, finInner_zero_left]
  · rw [h, finInner_zero_right]

/-- `ihs:rf:eq:inner`, first form: the `K`-valued inner product
`⟨x, y⟩ = ∑_{α, β} ⟨x_α, y_β⟩ t^{α + β}` on `ℋ_rf = V_I((t^Γ))`. Its coefficient at `γ` is the
finite sum over the pairs of support exponents with `α + β = γ`. -/
def hahnInner (x y : (I →₀ k)⟦Γ⟧) : k⟦Γ⟧ where
  coeff a := ∑ p ∈ Finset.antidiagonal x.isPWO_support y.isPWO_support a,
    finInner (x.coeff p.1) (y.coeff p.2)
  isPWO_support' := (x.isPWO_support.add y.isPWO_support).mono fun a ha => by
    by_contra h
    exact ha (by dsimp only; rw [antidiagonal_eq_empty _ _ h, Finset.sum_empty])

/-- The coefficient of `⟨x, y⟩` at `a`: the sum of `⟨x_α, y_β⟩` over the pairs of support
exponents with `α + β = a`. -/
theorem coeff_hahnInner (x y : (I →₀ k)⟦Γ⟧) (a : Γ) :
    (hahnInner x y).coeff a = ∑ p ∈ Finset.antidiagonal x.isPWO_support y.isPWO_support a,
      finInner (x.coeff p.1) (y.coeff p.2) := rfl

/-- The coefficients of `⟨x, y⟩`, summed over any enlarged index sets. -/
theorem coeff_hahnInner_of_subset {x y : (I →₀ k)⟦Γ⟧} {s t : Set Γ} (hs : s.IsPWO)
    (ht : t.IsPWO) (hxs : x.support ⊆ s) (hyt : y.support ⊆ t) (a : Γ) :
    (hahnInner x y).coeff a = ∑ p ∈ Finset.antidiagonal hs ht a,
      finInner (x.coeff p.1) (y.coeff p.2) :=
  sum_antidiagonal_mono _ _ hs ht hxs hyt (fun i j => finInner (x.coeff i) (y.coeff j))
    (fun _ _ h => finInner_coeff_eq_zero x y h) a

/-- The support of `⟨x, y⟩` lies in `supp x + supp y`. -/
theorem support_hahnInner_subset (x y : (I →₀ k)⟦Γ⟧) :
    (hahnInner x y).support ⊆ x.support + y.support := fun a ha => by
  by_contra h
  exact ha (by rw [coeff_hahnInner, antidiagonal_eq_empty _ _ h, Finset.sum_empty])

/-- `⟨0, y⟩ = 0`. -/
@[simp] theorem hahnInner_zero_left (y : (I →₀ k)⟦Γ⟧) : hahnInner 0 y = 0 := by
  ext a
  simp [coeff_hahnInner]

/-- `⟨x, 0⟩ = 0`. -/
@[simp] theorem hahnInner_zero_right (x : (I →₀ k)⟦Γ⟧) : hahnInner x 0 = 0 := by
  ext a
  simp [coeff_hahnInner]

/-- `ihs:rf:prop:inner`, additivity in the first argument. -/
theorem hahnInner_add_left (x x' y : (I →₀ k)⟦Γ⟧) :
    hahnInner (x + x') y = hahnInner x y + hahnInner x' y := by
  ext a
  have hs := x.isPWO_support.union x'.isPWO_support
  rw [HahnSeries.coeff_add,
    coeff_hahnInner_of_subset hs y.isPWO_support (HahnSeries.support_add_subset x x') subset_rfl,
    coeff_hahnInner_of_subset hs y.isPWO_support Set.subset_union_left subset_rfl,
    coeff_hahnInner_of_subset hs y.isPWO_support Set.subset_union_right subset_rfl,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [HahnSeries.coeff_add, finInner_add_left]

/-- `ihs:rf:prop:inner`, additivity in the second argument. -/
theorem hahnInner_add_right (x y y' : (I →₀ k)⟦Γ⟧) :
    hahnInner x (y + y') = hahnInner x y + hahnInner x y' := by
  ext a
  have ht := y.isPWO_support.union y'.isPWO_support
  rw [HahnSeries.coeff_add,
    coeff_hahnInner_of_subset x.isPWO_support ht subset_rfl (HahnSeries.support_add_subset y y'),
    coeff_hahnInner_of_subset x.isPWO_support ht subset_rfl Set.subset_union_left,
    coeff_hahnInner_of_subset x.isPWO_support ht subset_rfl Set.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [HahnSeries.coeff_add, finInner_add_right]

/-- `ihs:rf:prop:inner`, Hermitian symmetry: `⟨y, x⟩ = conj ⟨x, y⟩`, with the coefficientwise
conjugation of `K`. -/
theorem hahnStar_hahnInner (x y : (I →₀ k)⟦Γ⟧) : hahnStar (hahnInner x y) = hahnInner y x := by
  ext a
  rw [coeff_hahnStar, coeff_hahnInner, coeff_hahnInner, star_sum]
  simp_rw [star_finInner]
  exact sum_antidiagonal_swap _ _ (fun i j => finInner (y.coeff j) (x.coeff i)) a

/-- The coordinate series `x_i ∈ K = k((t^Γ))` of a Hahn vector `x ∈ V_I((t^Γ))`. -/
def coord (x : (I →₀ k)⟦Γ⟧) (i : I) : k⟦Γ⟧ :=
  x.map (Finsupp.applyAddHom i)

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [StarRing k] in
/-- The coefficient of the coordinate series `x_i` at `g` is the `i`-th entry of `x_g`. -/
@[simp] theorem coeff_coord (x : (I →₀ k)⟦Γ⟧) (i : I) (g : Γ) :
    (coord x i).coeff g = x.coeff g i := rfl

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [StarRing k] in
/-- Each coordinate series `x_i` is supported in `supp x`. -/
theorem support_coord_subset (x : (I →₀ k)⟦Γ⟧) (i : I) : (coord x i).support ⊆ x.support := by
  intro g hg
  rw [HahnSeries.mem_support] at hg ⊢
  contrapose hg
  rw [coeff_coord, hg, Finsupp.zero_apply]

/-- The coefficient of `conj(x_i) y_i` at `g`, as a sum over the pairs of support exponents of
`x` and `y` with sum `g`. -/
theorem coeff_hahnStar_coord_mul (x y : (I →₀ k)⟦Γ⟧) (i : I) (g : Γ) :
    (hahnStar (coord x i) * coord y i).coeff g =
      ∑ p ∈ Finset.antidiagonal x.isPWO_support y.isPWO_support g,
        star (x.coeff p.1 i) * y.coeff p.2 i := by
  rw [HahnSeries.coeff_mul]
  refine sum_antidiagonal_mono _ _ _ _ ?_ (support_coord_subset y i)
    (fun a b => star (x.coeff a i) * y.coeff b i) (fun a b h => ?_) g
  · rw [support_hahnStar]
    exact support_coord_subset x i
  · simp only [HahnSeries.mem_support, coeff_hahnStar, coeff_coord, not_and_or, not_not,
      star_eq_zero] at h
    rcases h with h | h <;> simp [h]

/-- `ihs:rf:eq:inner`, second form: the family `i ↦ conj(x_i) y_i` over `I`. It is strongly
summable: the supports lie in `supp x + supp y`, and at each exponent only finitely many
`i` contribute. -/
def innerFamily (x y : (I →₀ k)⟦Γ⟧) : _root_.HahnSeries.SummableFamily Γ k I where
  toFun i := hahnStar (coord x i) * coord y i
  isPWO_iUnion_support' := (x.isPWO_support.add y.isPWO_support).mono <|
    Set.iUnion_subset fun i => HahnSeries.support_mul_subset.trans
      (Set.add_subset_add (by rw [support_hahnStar]; exact support_coord_subset x i)
        (support_coord_subset y i))
  finite_co_support' g := by
    classical
    refine ((Finset.antidiagonal x.isPWO_support y.isPWO_support g).biUnion
      fun p => (y.coeff p.2).support).finite_toSet.subset fun i hi => ?_
    rw [Set.mem_setOf_eq, coeff_hahnStar_coord_mul] at hi
    obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
    exact Finset.mem_coe.2 (Finset.mem_biUnion.2
      ⟨p, hp, Finsupp.mem_support_iff.2 (right_ne_zero_of_mul hne)⟩)

/-- The member of `innerFamily x y` at `i` is `conj(x_i) y_i`. -/
@[simp] theorem innerFamily_apply (x y : (I →₀ k)⟦Γ⟧) (i : I) :
    innerFamily x y i = hahnStar (coord x i) * coord y i := rfl

/-- `ihs:rf:eq:inner`: the two formulas agree, `∑_{α, β} ⟨x_α, y_β⟩ t^{α + β}` is the strong
sum `∑^H_{i ∈ I} conj(x_i) y_i`. -/
theorem hsum_innerFamily (x y : (I →₀ k)⟦Γ⟧) : (innerFamily x y).hsum = hahnInner x y := by
  ext g
  rw [HahnSeries.SummableFamily.coeff_hsum, coeff_hahnInner]
  simp_rw [innerFamily_apply, coeff_hahnStar_coord_mul]
  rw [finsum_sum_comm]
  · exact Finset.sum_congr rfl fun p _ => (finInner_eq_finsum _ _).symm
  · intro p _
    exact Set.Finite.subset (y.coeff p.2).hasFiniteSupport fun i hi => right_ne_zero_of_mul hi

omit [StarRing k] in
/-- The `K`-vector-space action on `V_I((t^Γ))` is coordinatewise multiplication. -/
theorem coord_smul (c : k⟦Γ⟧) (y : (I →₀ k)⟦Γ⟧) (i : I) :
    coord ((HahnModule.of k).symm (c • HahnModule.of k y)) i = c * coord y i := by
  ext g
  rw [coeff_coord, coeff_of_symm_smul c y c.isPWO_support y.isPWO_support subset_rfl subset_rfl,
    HahnSeries.coeff_mul_right' y.isPWO_support (support_coord_subset y i),
    Finsupp.finsetSum_apply]
  rfl

/-- `ihs:rf:prop:inner`, linearity over `K` in the second argument: `⟨x, c y⟩ = c ⟨x, y⟩`. -/
theorem hahnInner_smul_right (c : k⟦Γ⟧) (x y : (I →₀ k)⟦Γ⟧) :
    hahnInner x ((HahnModule.of k).symm (c • HahnModule.of k y)) = c * hahnInner x y := by
  have h : innerFamily x ((HahnModule.of k).symm (c • HahnModule.of k y)) =
      c • innerFamily x y := by
    ext i : 1
    rw [HahnSeries.SummableFamily.smul_apply, HahnSeries.of_symm_smul_of_eq_mul,
      innerFamily_apply, innerFamily_apply, coord_smul, mul_left_comm]
  rw [← hsum_innerFamily, h, HahnSeries.SummableFamily.hsum_smul, hsum_innerFamily]

/-- `ihs:rf:prop:inner`, conjugate-linearity over `K` in the first argument:
`⟨c x, y⟩ = conj(c) ⟨x, y⟩`, with the coefficientwise conjugation of `K`. -/
theorem hahnInner_smul_left (c : k⟦Γ⟧) (x y : (I →₀ k)⟦Γ⟧) :
    hahnInner ((HahnModule.of k).symm (c • HahnModule.of k x)) y =
      hahnStar c * hahnInner x y := by
  have h : innerFamily ((HahnModule.of k).symm (c • HahnModule.of k x)) y =
      hahnStar c • innerFamily x y := by
    ext i : 1
    rw [HahnSeries.SummableFamily.smul_apply, HahnSeries.of_symm_smul_of_eq_mul,
      innerFamily_apply, innerFamily_apply, coord_smul, hahnStar_mul, mul_comm (hahnStar _),
      mul_assoc]
  rw [← hsum_innerFamily, h, HahnSeries.SummableFamily.hsum_smul, hsum_innerFamily]

/-- `ihs:rf:prop:inner`, adjoint relation: `⟨X x, y⟩ = ⟨x, X* y⟩` for `X ∈ 𝒜_rf = R_I((t^Γ))`
acting on `ℋ_rf = V_I((t^Γ))` by convolution, where `X*` is the coefficientwise conjugate
transpose. Both sides are the sum of `⟨x_ν, X_μ* y_β⟩` over the triples of support exponents
with `μ + ν + β` fixed. -/
theorem hahnInner_rcf_smul_left (X : (rcf k I)⟦Γ⟧) (x y : (I →₀ k)⟦Γ⟧) :
    hahnInner ((HahnModule.of (rcf k I)).symm (X • HahnModule.of (rcf k I) x)) y =
      hahnInner x ((HahnModule.of (rcf k I)).symm (star X • HahnModule.of (rcf k I) y)) := by
  ext a
  have hX := X.isPWO_support
  have hx := x.isPWO_support
  have hy := y.isPWO_support
  have hsX : (star X).support ⊆ X.support := by
    rw [show (star X).support = (hahnStar X).support from rfl, support_hahnStar]
  rw [coeff_hahnInner_of_subset (hx.add hX) hy
      ((support_of_symm_smul_subset X x).trans (add_comm X.support x.support).le) subset_rfl,
    coeff_hahnInner_of_subset hx (hX.add hy) subset_rfl
      ((support_of_symm_smul_subset (star X) y).trans (Set.add_subset_add_right hsX))]
  calc ∑ p ∈ Finset.antidiagonal (hx.add hX) hy a,
        finInner (((HahnModule.of (rcf k I)).symm (X • HahnModule.of (rcf k I) x)).coeff p.1)
          (y.coeff p.2)
      = ∑ p ∈ Finset.antidiagonal (hx.add hX) hy a, ∑ q ∈ Finset.antidiagonal hx hX p.1,
          finInner (x.coeff q.1) (star (X.coeff q.2) • y.coeff p.2) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [coeff_of_symm_smul X x hX hx subset_rfl subset_rfl, finInner_sum_left]
        refine (sum_antidiagonal_swap hX hx
          (fun i j => finInner (X.coeff i • x.coeff j) (y.coeff p.2)) p.1).trans ?_
        exact Finset.sum_congr rfl fun q _ => finInner_smul_left _ _ _
    _ = ∑ p ∈ Finset.antidiagonal hx (hX.add hy) a, ∑ q ∈ Finset.antidiagonal hX hy p.2,
          finInner (x.coeff p.1) (star (X.coeff q.1) • y.coeff q.2) :=
        sum_antidiagonal_assoc hx hX hy
          (fun i j l => finInner (x.coeff i) (star (X.coeff j) • y.coeff l)) a
    _ = _ := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [coeff_of_symm_smul (star X) y hX hy hsX subset_rfl, finInner_sum_right]
        rfl

end Generic

section StrongSums

open _root_.HahnSeries

variable {Γ : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
  {k I α : Type*} [CommSemiring k]

/-- `ihs:rf:lem:strongaction`, operators on vectors: if `(x_a)` is strongly summable in `ℋ_rf`
and `X ∈ 𝒜_rf`, then `(X x_a)` is strongly summable and `∑^H X x_a = X (∑^H x_a)`. -/
theorem exists_summable_rcf_smul (X : (rcf k I)⟦Γ⟧) (s : SummableFamily Γ (I →₀ k) α) :
    ∃ t : SummableFamily Γ (I →₀ k) α,
      (∀ a, t a = (HahnModule.of (rcf k I)).symm (X • HahnModule.of (rcf k I) (s a))) ∧
        t.hsum = (HahnModule.of (rcf k I)).symm (X • HahnModule.of (rcf k I) s.hsum) :=
  ⟨X • s, fun _ => rfl, SummableFamily.hsum_smul_module⟩

/-- `ihs:rf:lem:strongaction`, a strongly summable family `(X_a)` in `𝒜_rf` acting on a fixed
vector `x`: `(X_a x)` is strongly summable and `∑^H X_a x = (∑^H X_a) x`. -/
theorem exists_summable_smul_rcf (s : SummableFamily Γ (rcf k I) α) (x : (I →₀ k)⟦Γ⟧) :
    ∃ t : SummableFamily Γ (I →₀ k) α,
      (∀ a, t a = (HahnModule.of (rcf k I)).symm (s a • HahnModule.of (rcf k I) x)) ∧
        t.hsum = (HahnModule.of (rcf k I)).symm (s.hsum • HahnModule.of (rcf k I) x) := by
  refine ⟨.Equiv (Equiv.prodPUnit α) (s.smul (.const Unit x)), fun _ => rfl, ?_⟩
  rw [SummableFamily.hsum_equiv, SummableFamily.smul_hsum,
    SummableFamily.hsum_unique (SummableFamily.const Unit x)]
  rfl

/-- `ihs:rf:lem:strongaction`, left multiplication in `𝒜_rf` by a fixed element. -/
theorem exists_summable_mul_left (X : (rcf k I)⟦Γ⟧) (s : SummableFamily Γ (rcf k I) α) :
    ∃ t : SummableFamily Γ (rcf k I) α, (∀ a, t a = X * s a) ∧ t.hsum = X * s.hsum :=
  ⟨X • s, fun _ => rfl, SummableFamily.hsum_smul⟩

/-- `ihs:rf:lem:strongaction`, right multiplication in `𝒜_rf` by a fixed element. -/
theorem exists_summable_mul_right (X : (rcf k I)⟦Γ⟧) (s : SummableFamily Γ (rcf k I) α) :
    ∃ t : SummableFamily Γ (rcf k I) α, (∀ a, t a = s a * X) ∧ t.hsum = s.hsum * X := by
  refine ⟨.Equiv (Equiv.prodPUnit α) (s.mul (.const Unit X)), fun _ => rfl, ?_⟩
  rw [SummableFamily.hsum_equiv, SummableFamily.hsum_mul,
    SummableFamily.hsum_unique (SummableFamily.const Unit X)]
  rfl

variable [StarRing k]

/-- The family `a ↦ ⟨x, y_a⟩` of inner products of a fixed vector with a strongly summable
family. -/
def innerRightFamily (x : (I →₀ k)⟦Γ⟧) (s : SummableFamily Γ (I →₀ k) α) :
    SummableFamily Γ k α where
  toFun a := hahnInner x (s a)
  isPWO_iUnion_support' := (x.isPWO_support.add s.isPWO_iUnion_support).mono <|
    Set.iUnion_subset fun a => (support_hahnInner_subset x (s a)).trans
      (Set.add_subset_add_left (Set.subset_iUnion (fun a => (s a).support) a))
  finite_co_support' g := by
    classical
    refine ((Finset.antidiagonal x.isPWO_support s.isPWO_iUnion_support g).biUnion
      fun p => (s.finite_co_support p.2).toFinset).finite_toSet.subset fun a ha => ?_
    rw [Set.mem_setOf_eq, coeff_hahnInner_of_subset x.isPWO_support s.isPWO_iUnion_support
      subset_rfl (Set.subset_iUnion (fun a => (s a).support) a)] at ha
    obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
    refine Finset.mem_coe.2 (Finset.mem_biUnion.2
      ⟨p, hp, (s.finite_co_support p.2).mem_toFinset.2 fun h => hne ?_⟩)
    rw [show (s a).coeff p.2 = 0 from h, finInner_zero_right]

/-- The member of `innerRightFamily x s` at `a` is `⟨x, s a⟩`. -/
@[simp] theorem innerRightFamily_apply (x : (I →₀ k)⟦Γ⟧) (s : SummableFamily Γ (I →₀ k) α)
    (a : α) : innerRightFamily x s a = hahnInner x (s a) := rfl

/-- `ihs:rf:lem:strongaction`, inner product with a fixed vector (second argument):
`⟨x, ∑^H y_a⟩ = ∑^H ⟨x, y_a⟩`. -/
theorem hsum_innerRightFamily (x : (I →₀ k)⟦Γ⟧) (s : SummableFamily Γ (I →₀ k) α) :
    (innerRightFamily x s).hsum = hahnInner x s.hsum := by
  ext g
  have hU := s.isPWO_iUnion_support
  rw [SummableFamily.coeff_hsum, coeff_hahnInner_of_subset x.isPWO_support hU subset_rfl
    SummableFamily.support_hsum_subset]
  simp_rw [innerRightFamily_apply]
  rw [finsum_congr fun a => coeff_hahnInner_of_subset x.isPWO_support hU subset_rfl
    (Set.subset_iUnion (fun a => (s a).support) a) g, finsum_sum_comm]
  · refine Finset.sum_congr rfl fun p _ => ?_
    have ht := s.finite_co_support p.2
    rw [SummableFamily.coeff_hsum, finsum_eq_sum_of_support_subset (s := ht.toFinset),
      finsum_eq_sum_of_support_subset (s := ht.toFinset), finInner_sum_right]
    · intro a ha
      rw [Set.Finite.coe_toFinset]
      exact ha
    · intro a ha
      rw [Set.Finite.coe_toFinset]
      intro h
      apply ha
      dsimp only at h ⊢
      rw [h, finInner_zero_right]
  · intro p _
    refine (s.finite_co_support p.2).subset fun a ha h => ha ?_
    dsimp only at h ⊢
    rw [h, finInner_zero_right]

/-- The family `a ↦ ⟨x_a, y⟩` of inner products of a strongly summable family with a fixed
vector. -/
def innerLeftFamily (s : SummableFamily Γ (I →₀ k) α) (y : (I →₀ k)⟦Γ⟧) :
    SummableFamily Γ k α where
  toFun a := hahnInner (s a) y
  isPWO_iUnion_support' := (s.isPWO_iUnion_support.add y.isPWO_support).mono <|
    Set.iUnion_subset fun a => (support_hahnInner_subset (s a) y).trans
      (Set.add_subset_add_right (Set.subset_iUnion (fun a => (s a).support) a))
  finite_co_support' g := by
    classical
    refine ((Finset.antidiagonal s.isPWO_iUnion_support y.isPWO_support g).biUnion
      fun p => (s.finite_co_support p.1).toFinset).finite_toSet.subset fun a ha => ?_
    rw [Set.mem_setOf_eq, coeff_hahnInner_of_subset s.isPWO_iUnion_support y.isPWO_support
      (Set.subset_iUnion (fun a => (s a).support) a) subset_rfl] at ha
    obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
    refine Finset.mem_coe.2 (Finset.mem_biUnion.2
      ⟨p, hp, (s.finite_co_support p.1).mem_toFinset.2 fun h => hne ?_⟩)
    rw [show (s a).coeff p.1 = 0 from h, finInner_zero_left]

/-- The member of `innerLeftFamily s y` at `a` is `⟨s a, y⟩`. -/
@[simp] theorem innerLeftFamily_apply (s : SummableFamily Γ (I →₀ k) α) (y : (I →₀ k)⟦Γ⟧)
    (a : α) : innerLeftFamily s y a = hahnInner (s a) y := rfl

/-- `ihs:rf:lem:strongaction`, inner product with a fixed vector (first argument):
`⟨∑^H x_a, y⟩ = ∑^H ⟨x_a, y⟩`. -/
theorem hsum_innerLeftFamily (s : SummableFamily Γ (I →₀ k) α) (y : (I →₀ k)⟦Γ⟧) :
    (innerLeftFamily s y).hsum = hahnInner s.hsum y := by
  ext g
  have hU := s.isPWO_iUnion_support
  rw [SummableFamily.coeff_hsum, coeff_hahnInner_of_subset hU y.isPWO_support
    SummableFamily.support_hsum_subset subset_rfl]
  simp_rw [innerLeftFamily_apply]
  rw [finsum_congr fun a => coeff_hahnInner_of_subset hU y.isPWO_support
    (Set.subset_iUnion (fun a => (s a).support) a) subset_rfl g, finsum_sum_comm]
  · refine Finset.sum_congr rfl fun p _ => ?_
    have ht := s.finite_co_support p.1
    rw [SummableFamily.coeff_hsum, finsum_eq_sum_of_support_subset (s := ht.toFinset),
      finsum_eq_sum_of_support_subset (s := ht.toFinset), finInner_sum_left]
    · intro a ha
      rw [Set.Finite.coe_toFinset]
      exact ha
    · intro a ha
      rw [Set.Finite.coe_toFinset]
      intro h
      apply ha
      dsimp only at h ⊢
      rw [h, finInner_zero_left]
  · intro p _
    refine (s.finite_co_support p.1).subset fun a ha h => ha ?_
    dsimp only at h ⊢
    rw [h, finInner_zero_left]

end StrongSums

section Order

variable {Γ : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  {k I : Type*} [CommSemiring k] [StarRing k]

/-- `ihs:rf:prop:inner`, no smaller exponent: every coefficient of `⟨x, x⟩` below `2 v(x)`
vanishes. -/
theorem coeff_hahnInner_self_of_lt (x : (I →₀ k)⟦Γ⟧) {b : Γ} (hb : b < x.order + x.order) :
    (hahnInner x x).coeff b = 0 := by
  rw [coeff_hahnInner]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  exact absurd hp.2.2 (lt_of_lt_of_le hb (add_le_add (HahnSeries.order_le_of_coeff_ne_zero hp.1)
    (HahnSeries.order_le_of_coeff_ne_zero hp.2.1))).ne'

/-- `ihs:rf:prop:inner`, leading coefficient: the coefficient of `⟨x, x⟩` at `2 v(x)` is
`⟨x_{v(x)}, x_{v(x)}⟩`, because `(v(x), v(x))` is the only pair of support exponents with that
sum. -/
theorem coeff_hahnInner_self_order (x : (I →₀ k)⟦Γ⟧) :
    (hahnInner x x).coeff (x.order + x.order) =
      finInner (x.coeff x.order) (x.coeff x.order) := by
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [coeff_hahnInner, HahnSeries.order_of_ne hx,
      Finset.antidiagonal_min_add_min x.isWF_support x.isWF_support, Finset.sum_singleton]

/-- `ihs:rf:prop:inner`, valuation formula `v(⟨x, x⟩) = 2 v(x)` (with `v = orderTop`), for
every coefficient semiring on which the finite-support form is anisotropic (`hk`), as it is for
`ℂ`. -/
theorem orderTop_hahnInner_self (hk : ∀ v : I →₀ k, v ≠ 0 → finInner v v ≠ 0)
    (x : (I →₀ k)⟦Γ⟧) : (hahnInner x x).orderTop = x.orderTop + x.orderTop := by
  by_cases hx : x = 0
  · subst hx
    simp
  · have hne : (hahnInner x x).coeff (x.order + x.order) ≠ 0 := by
      rw [coeff_hahnInner_self_order]
      exact hk _ fun h => hx (HahnSeries.coeff_order_eq_zero.1 h)
    rw [HahnSeries.orderTop_eq_of_le ((HahnSeries.mem_support _ _).2 hne) fun g hg =>
        not_lt.1 fun hlt => hg (coeff_hahnInner_self_of_lt x hlt),
      ← HahnSeries.order_eq_orderTop_of_ne_zero hx, WithTop.coe_add]

end Order

section Complex

variable {Γ : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] {I : Type*}

/-- Over `ℂ`, `⟨v, v⟩ = ∑_i |v_i|²` for a finitely supported vector. -/
theorem finInner_self_complex (v : I →₀ ℂ) :
    finInner v v = ((∑ i ∈ v.support, Complex.normSq (v i) : ℝ) : ℂ) := by
  rw [finInner, Finsupp.sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_conj_mul_self, starRingEnd_apply]

/-- Over `ℂ`, `∑_i |v_i|² > 0` for a nonzero finitely supported vector. -/
theorem sum_normSq_pos {v : I →₀ ℂ} (hv : v ≠ 0) : 0 < ∑ i ∈ v.support, Complex.normSq (v i) :=
  Finset.sum_pos (fun _ hi => Complex.normSq_pos.2 (Finsupp.mem_support_iff.1 hi))
    (Finsupp.support_nonempty_iff.2 hv)

/-- Over `ℂ`, the finite-support form is anisotropic: `⟨v, v⟩ ≠ 0` for `v ≠ 0`. -/
theorem finInner_self_ne_zero_complex {v : I →₀ ℂ} (hv : v ≠ 0) : finInner v v ≠ 0 := by
  rw [finInner_self_complex, Complex.ofReal_ne_zero]
  exact (sum_normSq_pos hv).ne'

/-- `ihs:rf:prop:inner`, valuation formula over `K = ℂ((t^Γ))`: `v(⟨x, x⟩) = 2 v(x)`. -/
theorem orderTop_hahnInner_self_complex (x : (I →₀ ℂ)⟦Γ⟧) :
    (hahnInner x x).orderTop = x.orderTop + x.orderTop :=
  orderTop_hahnInner_self (fun _ hv => finInner_self_ne_zero_complex hv) x

/-- A complex Hahn series fixed by the coefficientwise conjugation lies in the real subfield
`F = ℝ((t^Γ))`. -/
theorem eq_complexRealEmbedding_of_hahnStar_eq {P : ℂ⟦Γ⟧} (hP : hahnStar P = P) :
    P = Surreal.HahnSeries.complexRealEmbedding (P.map Complex.reAddGroupHom) := by
  ext g
  have h := congrArg (fun z => z.coeff g) hP
  simp only [coeff_hahnStar, ← starRingEnd_apply] at h
  exact (Complex.conj_eq_iff_re.1 h).symm

/-- A self-conjugate complex Hahn series whose coefficients vanish below `g` and whose
coefficient at `g` is a positive real number `s` is the image of a positive element `r` of
`F = ℝ((t^Γ))` with `v(r) = g` and `r_g = s`. -/
theorem exists_pos_of_hahnStar_eq {P : ℂ⟦Γ⟧} (hP : hahnStar P = P) {g : Γ}
    (hlow : ∀ j < g, P.coeff j = 0) {s : ℝ} (hs : 0 < s) (hg : P.coeff g = s) :
    ∃ r : ℝ⟦Γ⟧, P = Surreal.HahnSeries.complexRealEmbedding r ∧ 0 < toLex r ∧
      r.orderTop = g ∧ r.coeff g = s := by
  set r : ℝ⟦Γ⟧ := P.map Complex.reAddGroupHom with hr
  have hlead : r.coeff g = s := by
    rw [hr, HahnSeries.map_coeff, hg]
    exact Complex.ofReal_re s
  have hlow' : ∀ j < g, r.coeff j = 0 := fun j hj => by
    rw [hr, HahnSeries.map_coeff, hlow j hj, map_zero]
  have hpos : 0 < r.coeff g := hlead ▸ hs
  refine ⟨r, eq_complexRealEmbedding_of_hahnStar_eq hP,
    Surreal.HahnSeries.pos_of_coeff hlow' hpos, ?_, hlead⟩
  exact HahnSeries.orderTop_eq_of_le ((HahnSeries.mem_support _ _).2 hpos.ne') fun j hj =>
    not_lt.1 fun hlt => hj (hlow' j hlt)

/-- Over `ℂ`, `⟨x, x⟩` lies in the real subfield `F = ℝ((t^Γ))`: its coefficients are fixed by
conjugation, by Hermitian symmetry. -/
theorem hahnInner_self_eq_complexRealEmbedding (x : (I →₀ ℂ)⟦Γ⟧) :
    hahnInner x x = Surreal.HahnSeries.complexRealEmbedding
      ((hahnInner x x).map Complex.reAddGroupHom) :=
  eq_complexRealEmbedding_of_hahnStar_eq (hahnStar_hahnInner x x)

/-- `ihs:rf:prop:inner`, positivity and valuation over `K = ℂ((t^Γ))`: for `x ≠ 0` the square
`⟨x, x⟩` is the image of an element `r` of `F = ℝ((t^Γ))` with `0 < r` in the lexicographic
order of `F` (where a nonzero series is positive exactly when its leading coefficient is);
`v(r) = 2 v(x)`, so `v(⟨x, x⟩) = 2 v(x)`; and the coefficient of `r` at `2 v(x)` is
`∑_i |(x_{v(x)})_i|² > 0`. No divisibility of `Γ` and no square roots are used. -/
theorem hahnInner_self_pos {x : (I →₀ ℂ)⟦Γ⟧} (hx : x ≠ 0) :
    ∃ r : ℝ⟦Γ⟧, hahnInner x x = Surreal.HahnSeries.complexRealEmbedding r ∧ 0 < toLex r ∧
      r.orderTop = x.orderTop + x.orderTop ∧
      r.coeff (x.order + x.order) =
        ∑ i ∈ (x.coeff x.order).support, Complex.normSq (x.coeff x.order i) ∧
      0 < r.coeff (x.order + x.order) := by
  have hs := sum_normSq_pos (v := x.coeff x.order) fun h =>
    hx (HahnSeries.coeff_order_eq_zero.1 h)
  obtain ⟨r, hr, hpos, hord, hlead⟩ := exists_pos_of_hahnStar_eq (hahnStar_hahnInner x x)
    (g := x.order + x.order) (fun j hj => coeff_hahnInner_self_of_lt x hj) hs
    (by rw [coeff_hahnInner_self_order, finInner_self_complex])
  exact ⟨r, hr, hpos, by rw [hord, ← HahnSeries.order_eq_orderTop_of_ne_zero hx, WithTop.coe_add],
    hlead, hlead ▸ hs⟩

end Complex

section Adjacency

/-- The shift `(x_n)_n ↦ (x_{n-1})_n` of `ℂ^(ℤ)`. -/
def shiftUp : Module.End ℂ (ℤ →₀ ℂ) :=
  (Finsupp.domLCongr (Equiv.addRight (1 : ℤ))).toLinearMap

/-- The shift `(x_n)_n ↦ (x_{n+1})_n` of `ℂ^(ℤ)`. -/
def shiftDown : Module.End ℂ (ℤ →₀ ℂ) :=
  (Finsupp.domLCongr (Equiv.addRight (1 : ℤ)).symm).toLinearMap

/-- Coordinates of the upward shift. -/
theorem shiftUp_apply (x : ℤ →₀ ℂ) (n : ℤ) : shiftUp x n = x (n - 1) := by
  rw [sub_eq_add_neg]
  rfl

/-- Coordinates of the downward shift. -/
theorem shiftDown_apply (x : ℤ →₀ ℂ) (n : ℤ) : shiftDown x n = x (n + 1) :=
  rfl

/-- The entries of the bilateral adjacency matrix: `T_{ij} = [j = i - 1] + [j = i + 1]`, so
`T_{ij} = 1` when `|i - j| = 1` and `T_{ij} = 0` otherwise. -/
theorem entry_shiftUp_add_shiftDown (i j : ℤ) :
    entry ℂ ℤ (shiftUp + shiftDown) i j =
      (if j = i - 1 then 1 else 0) + (if j = i + 1 then 1 else 0) := by
  rw [entry_apply, LinearMap.add_apply, Finsupp.add_apply, shiftUp_apply, shiftDown_apply,
    Finsupp.single_apply, Finsupp.single_apply]

/-- `ihs:rf:prop:degenerate`: the bilateral adjacency operator `(Tx)_n = x_{n-1} + x_{n+1}` on
`ℂ^(ℤ)`, an element of `R_ℤ = RCF_ℤ(ℂ)`: row `i` of its matrix is supported on `{i - 1, i + 1}`
(columns of endomorphisms of `ℂ^(ℤ)` are always finite). -/
def adjacency : rcf ℂ ℤ :=
  ⟨shiftUp + shiftDown, fun i => (Set.toFinite ({i - 1, i + 1} : Set ℤ)).subset fun j hj => by
    by_contra h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h
    apply hj
    rw [entry_shiftUp_add_shiftDown, if_neg h.1, if_neg h.2, add_zero]⟩

/-- `(Tv)_n = v_{n-1} + v_{n+1}`. -/
theorem adjacency_smul_apply (v : ℤ →₀ ℂ) (n : ℤ) :
    (adjacency • v) n = v (n - 1) + v (n + 1) := by
  rw [rcf_smul_def]
  exact congrArg₂ (· + ·) (shiftUp_apply v n) (shiftDown_apply v n)

/-- `ihs:rf:prop:degenerate`: the bilateral adjacency matrix is real symmetric, `T* = T`. -/
theorem star_adjacency : star adjacency = adjacency := by
  refine rcf_ext ?_
  rw [entry_star]
  ext i j
  rw [Matrix.conjTranspose_apply]
  change star (entry ℂ ℤ (shiftUp + shiftDown) j i) = entry ℂ ℤ (shiftUp + shiftDown) i j
  rw [entry_shiftUp_add_shiftDown, entry_shiftUp_add_shiftDown]
  split_ifs <;> first | omega | simp

/-- `ihs:rf:prop:degenerate`: a nonzero finite-support vector is never an eigenvector of the
bilateral adjacency operator, for any eigenvalue `c ∈ ℂ`. At the index just above the largest
nonzero coordinate, `Tv` is nonzero while `cv` vanishes. -/
theorem adjacency_smul_ne_smul {v : ℤ →₀ ℂ} (hv : v ≠ 0) (c : ℂ) : adjacency • v ≠ c • v := by
  intro h
  have hne := Finsupp.support_nonempty_iff.2 hv
  have hm : v (v.support.max' hne) ≠ 0 := Finsupp.mem_support_iff.1 (Finset.max'_mem _ _)
  have hgt : ∀ n, v.support.max' hne < n → v n = 0 := fun n hn =>
    Finsupp.notMem_support_iff.1 fun hn' => absurd (Finset.le_max' _ n hn') (not_le.2 hn)
  have h1 := congrArg (fun w : ℤ →₀ ℂ => w (v.support.max' hne + 1)) h
  simp only [adjacency_smul_apply, Finsupp.smul_apply, smul_eq_mul, add_sub_cancel_right] at h1
  rw [hgt (v.support.max' hne + 1 + 1) (by omega), hgt (v.support.max' hne + 1) (by omega),
    add_zero, mul_zero] at h1
  exact hm h1

/-- The bilateral adjacency operator has trivial kernel on `ℂ^(ℤ)` (the case `c = 0` of
`adjacency_smul_ne_smul`); this is the injectivity of `T` used for `ihs:rf:prop:degenerate`. -/
theorem adjacency_smul_ne_zero {v : ℤ →₀ ℂ} (hv : v ≠ 0) : adjacency • v ≠ 0 := by
  have := adjacency_smul_ne_smul hv 0
  rwa [zero_smul] at this

/-- The bilateral adjacency operator is nonzero. -/
theorem adjacency_ne_zero : adjacency ≠ 0 := fun h =>
  adjacency_smul_ne_smul (v := Finsupp.single 0 1) (Finsupp.single_ne_zero.2 one_ne_zero) 0
    (by rw [h, zero_smul ℂ]; rfl)

end Adjacency

section Degenerate

variable {Γ : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]

/-- The coefficients of `c • y` in a Hahn module vanish below `v(c) + v(y)`. -/
theorem coeff_of_symm_smul_of_lt {R V : Type*} [Zero R] [AddCommMonoid V] [SMulWithZero R V]
    (c : R⟦Γ⟧) (y : V⟦Γ⟧) {b : Γ} (hb : b < c.order + y.order) :
    ((HahnModule.of R).symm (c • HahnModule.of R y)).coeff b = 0 := by
  rw [coeff_of_symm_smul c y c.isPWO_support y.isPWO_support subset_rfl subset_rfl]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  exact absurd hp.2.2 (lt_of_lt_of_le hb (add_le_add (HahnSeries.order_le_of_coeff_ne_zero hp.1)
    (HahnSeries.order_le_of_coeff_ne_zero hp.2.1))).ne'

/-- The coefficient of `c • y` at `v(c) + v(y)` is the product of the leading coefficients. -/
theorem coeff_of_symm_smul_order_add_order {R V : Type*} [Zero R] [AddCommMonoid V]
    [SMulWithZero R V] (c : R⟦Γ⟧) (y : V⟦Γ⟧) :
    ((HahnModule.of R).symm (c • HahnModule.of R y)).coeff (c.order + y.order) =
      c.leadingCoeff • y.leadingCoeff := by
  simpa only [Equiv.symm_apply_apply] using
    HahnModule.coeff_smul_order_add_order c (HahnModule.of R y)

/-- `ihs:rf:prop:degenerate`: the operator `A = Id + t^η T ∈ 𝒜_rf = RCF_ℤ(ℂ)((t^Γ))`. -/
def degenerateOp (η : Γ) : (rcf ℂ ℤ)⟦Γ⟧ :=
  1 + HahnSeries.single η adjacency

/-- `ihs:rf:prop:degenerate`, self-adjointness: `A* = A`. -/
theorem star_degenerateOp (η : Γ) : star (degenerateOp η) = degenerateOp η := by
  have h : star (HahnSeries.single η adjacency : (rcf ℂ ℤ)⟦Γ⟧) =
      HahnSeries.single η adjacency := by
    ext g
    rw [coeff_star_hahn]
    by_cases hg : g = η
    · rw [hg, HahnSeries.coeff_single_same, star_adjacency]
    · rw [HahnSeries.coeff_single_of_ne hg, star_zero]
  rw [degenerateOp, star_add, star_one, h]

/-- `ihs:rf:prop:degenerate`, self-adjointness for the inner product: `⟨Ax, y⟩ = ⟨x, Ay⟩`. -/
theorem hahnInner_degenerateOp_smul_left (η : Γ) (x y : (ℤ →₀ ℂ)⟦Γ⟧) :
    hahnInner ((HahnModule.of (rcf ℂ ℤ)).symm (degenerateOp η • HahnModule.of (rcf ℂ ℤ) x)) y =
      hahnInner x
        ((HahnModule.of (rcf ℂ ℤ)).symm (degenerateOp η • HahnModule.of (rcf ℂ ℤ) y)) := by
  rw [hahnInner_rcf_smul_left, star_degenerateOp]

/-- `A x = x + t^η T x`. -/
theorem degenerateOp_smul (η : Γ) (x : (ℤ →₀ ℂ)⟦Γ⟧) :
    (HahnModule.of (rcf ℂ ℤ)).symm (degenerateOp η • HahnModule.of (rcf ℂ ℤ) x) =
      x + (HahnModule.of (rcf ℂ ℤ)).symm
        (HahnSeries.single η adjacency • HahnModule.of (rcf ℂ ℤ) x) := by
  rw [degenerateOp, HahnModule.add_smul fun r s u => add_smul r s u, HahnModule.one_smul',
    HahnModule.of_symm_add, Equiv.symm_apply_apply]

/-- The coefficient of `t^η T x` at `η + g` is `T x_g`. -/
theorem coeff_single_adjacency_smul (η : Γ) (x : (ℤ →₀ ℂ)⟦Γ⟧) (g : Γ) :
    ((HahnModule.of (rcf ℂ ℤ)).symm
      (HahnSeries.single η adjacency • HahnModule.of (rcf ℂ ℤ) x)).coeff (η + g) =
        adjacency • x.coeff g := by
  simpa only [vadd_eq_add, Equiv.symm_apply_apply] using
    HahnModule.coeff_single_smul_vadd (r := adjacency) (x := HahnModule.of (rcf ℂ ℤ) x) (a := g)
      (b := η)

/-- The perturbation `⟨x, t^η T x⟩` has no exponent below `v(x) + (η + v(x))`. -/
theorem coeff_hahnInner_single_adjacency_of_lt (η : Γ) (x : (ℤ →₀ ℂ)⟦Γ⟧) {j : Γ}
    (hj : j < x.order + (η + x.order)) :
    (hahnInner x ((HahnModule.of (rcf ℂ ℤ)).symm
      (HahnSeries.single η adjacency • HahnModule.of (rcf ℂ ℤ) x))).coeff j = 0 := by
  rw [coeff_hahnInner]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  have h2 : η + x.order ≤ p.2 := not_lt.1 fun hlt => hp.2.1 (by
    refine coeff_of_symm_smul_of_lt (HahnSeries.single η adjacency) x ?_
    rwa [HahnSeries.order_single adjacency_ne_zero])
  exact absurd hp.2.2 (lt_of_lt_of_le hj (add_le_add
    (HahnSeries.order_le_of_coeff_ne_zero hp.1) h2)).ne'

/-- `ihs:rf:prop:degenerate`, positivity: for `η > 0` and `x ≠ 0`, `⟨x, Ax⟩` is the image of an
element `r` of `F = ℝ((t^Γ))` with `0 < r` in the lexicographic order of `F` and
`v(r) = 2 v(x)`, whose coefficient at `2 v(x)` is `∑_i |(x_{v(x)})_i|²`, the leading coefficient
of `⟨x, x⟩` (`hahnInner_self_pos`). The proof: `⟨x, t^η T x⟩` has no exponent below
`2 v(x) + η`, and `⟨x, Ax⟩` is real because `A` is self-adjoint. -/
theorem hahnInner_degenerateOp_pos {η : Γ} (hη : 0 < η) {x : (ℤ →₀ ℂ)⟦Γ⟧} (hx : x ≠ 0) :
    ∃ r : ℝ⟦Γ⟧, hahnInner x ((HahnModule.of (rcf ℂ ℤ)).symm
        (degenerateOp η • HahnModule.of (rcf ℂ ℤ) x)) =
          Surreal.HahnSeries.complexRealEmbedding r ∧
      0 < toLex r ∧ r.orderTop = x.orderTop + x.orderTop ∧
      r.coeff (x.order + x.order) =
        ∑ i ∈ (x.coeff x.order).support, Complex.normSq (x.coeff x.order i) := by
  have h2 : x.order + x.order < x.order + (η + x.order) :=
    add_lt_add_of_le_of_lt le_rfl (lt_add_of_pos_left _ hη)
  have hP := congrArg (hahnInner x) (degenerateOp_smul η x)
  rw [hahnInner_add_right] at hP
  have hreal : hahnStar (hahnInner x ((HahnModule.of (rcf ℂ ℤ)).symm
      (degenerateOp η • HahnModule.of (rcf ℂ ℤ) x))) = hahnInner x ((HahnModule.of (rcf ℂ ℤ)).symm
        (degenerateOp η • HahnModule.of (rcf ℂ ℤ) x)) := by
    rw [hahnStar_hahnInner, hahnInner_rcf_smul_left, star_degenerateOp]
  obtain ⟨r, hr, hpos, hord, hlead⟩ := exists_pos_of_hahnStar_eq hreal (g := x.order + x.order)
    (fun j hj => by
      rw [hP, HahnSeries.coeff_add, coeff_hahnInner_self_of_lt x hj,
        coeff_hahnInner_single_adjacency_of_lt η x (hj.trans h2), add_zero])
    (sum_normSq_pos (v := x.coeff x.order) fun h => hx (HahnSeries.coeff_order_eq_zero.1 h))
    (by rw [hP, HahnSeries.coeff_add, coeff_hahnInner_self_order, finInner_self_complex,
      coeff_hahnInner_single_adjacency_of_lt η x h2, add_zero])
  exact ⟨r, hr, hpos, by rw [hord, ← HahnSeries.order_eq_orderTop_of_ne_zero hx, WithTop.coe_add],
    hlead⟩

/-- `ihs:rf:prop:degenerate`, no eigenvalue: for every `η` (positivity of `η` is not needed),
every `z ∈ K = ℂ((t^Γ))` and every nonzero `x ∈ ℂ^(ℤ)((t^Γ))`, `Ax ≠ zx`, where `zx` is the
`K`-vector-space action. If `Ax = zx`, then `t^η T x = (z - 1) x`. Since `T x_{v(x)} ≠ 0`
(`adjacency_smul_ne_zero`), comparing coefficients at `η + v(x)` and `v(z - 1) + v(x)` rules out
`z = 1` and `v(z - 1) ≠ η`, and leaves `T x_{v(x)} = c x_{v(x)}` for the leading coefficient `c`
of `z - 1`, a finite-support eigenvector of `T`. -/
theorem degenerateOp_smul_ne_smul (η : Γ) (z : ℂ⟦Γ⟧) {x : (ℤ →₀ ℂ)⟦Γ⟧} (hx : x ≠ 0) :
    (HahnModule.of (rcf ℂ ℤ)).symm (degenerateOp η • HahnModule.of (rcf ℂ ℤ) x) ≠
      (HahnModule.of ℂ).symm (z • HahnModule.of ℂ x) := by
  intro h
  rw [degenerateOp_smul] at h
  have hS : (HahnModule.of (rcf ℂ ℤ)).symm
      (HahnSeries.single η adjacency • HahnModule.of (rcf ℂ ℤ) x) =
        (HahnModule.of ℂ).symm ((z - 1) • HahnModule.of ℂ x) := by
    have hz : (HahnModule.of ℂ).symm (z • HahnModule.of ℂ x) =
        (HahnModule.of ℂ).symm ((z - 1) • HahnModule.of ℂ x) + x := by
      conv_lhs => rw [← sub_add_cancel z 1]
      rw [HahnModule.add_smul fun r s u => add_smul r s u, HahnModule.one_smul',
        HahnModule.of_symm_add, Equiv.symm_apply_apply]
    rw [hz] at h
    exact (add_sub_cancel_left x _).symm.trans
      ((congrArg (· - x) h).trans (add_sub_cancel_right _ x))
  have hv : x.leadingCoeff ≠ 0 := HahnSeries.leadingCoeff_ne_zero.2 hx
  have hTv : adjacency • x.leadingCoeff ≠ 0 := adjacency_smul_ne_zero hv
  have hb1 : ((HahnModule.of ℂ).symm ((z - 1) • HahnModule.of ℂ x)).coeff (η + x.order) =
      adjacency • x.leadingCoeff := by
    rw [← hS, coeff_single_adjacency_smul, HahnSeries.leadingCoeff_eq]
  by_cases hw : z - 1 = 0
  · rw [hw, HahnModule.zero_smul', HahnModule.of_symm_zero, HahnSeries.coeff_zero] at hb1
    exact hTv hb1.symm
  have hc : (z - 1).leadingCoeff ≠ 0 := HahnSeries.leadingCoeff_ne_zero.2 hw
  have hb2 := coeff_of_symm_smul_order_add_order (z - 1) x
  rcases lt_trichotomy (η + x.order) ((z - 1).order + x.order) with hlt | heq | hgt
  · rw [coeff_of_symm_smul_of_lt (z - 1) x hlt] at hb1
    exact hTv hb1.symm
  · rw [heq, hb2] at hb1
    exact adjacency_smul_ne_smul hv _ hb1.symm
  · rw [← hS, coeff_of_symm_smul_of_lt (HahnSeries.single η adjacency) x
      (by rwa [HahnSeries.order_single adjacency_ne_zero])] at hb2
    exact smul_ne_zero hc hv hb2.symm

end Degenerate

end

end Surreal.RowFiniteInner
