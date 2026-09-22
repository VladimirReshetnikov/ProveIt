import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.PowerSeries.Derivative
import Surreal.HahnSeries.Evaluation

/-!
# Escape chains and the evaluation exclusion criterion

This file formalizes the finite-step escape mechanism of
`docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/article.tex`.

The exponent group `Γ` is an arbitrary linearly ordered abelian group; divisibility is not
assumed (`hol:conv:group`). The coefficient field `ℂ` of the source is generalized to any
semiring without zero divisors for the escape results, and to any field of characteristic
zero for the formal exponential. The valuation `v` is Mathlib's `HahnSeries.order`; its junk
value `order 0 = 0` never matters, since every order occurring in a hypothesis or conclusion
below is that of an element assumed nonzero, or sits in a disjunct next to `x = 0`.

* `StronglySummable`, `strongDomain` and `IsStronglyEntire` are `hol:def:entire`, with
  strong summability encoded, as elsewhere in the project, by a `SummableFamily` whose terms
  are the given family; `stronglySummable_iff` and `stronglySummable_iff_isWF` unfold it to
  the two clauses of the source. The domain and entireness are defined for univariate power
  series; the `d`-variable clause is represented only through `StronglySummable` over an
  arbitrary index type.
  `IsOrderUnit` is `hol:def:orderunit`, recorded here as shared vocabulary only.
* `not_stronglySummable_of_antitone_order` is `hol:lem:nonincreasing`. Only the members of the
  infinite subsequence are required to be nonzero, so the lemma applies to evaluation families
  containing zero members, which is how the source uses it.
* `exists_escape_step` and `exists_escape_chain` are `hol:lem:escape`, including `1 ≤ s`.
* `not_stronglySummable_of_escape` and `eq_zero_of_stronglySummable_escape` are
  `hol:thm:escapeexclusion`, with the weak inequality `hol:eq:boundincrements`;
  `not_mem_strongDomain_of_escape` restates it for the domain of a power series.
* `eq_zero_of_boundedCost`, `single_neg_witness` and `eq_zero_of_boundedCost_single` are
  `hol:cor:boundedcost`.
* `derivative_formalExp` and `strongDomain_formalExp` are `hol:prop:expdomain`; the domain is
  derived from `stronglySummable_single_mul_pow_iff`, the exact domain of
  `(c_n y^n)` for nonzero scalar coefficients. Finally `escapeBound_formalExp_iff` and
  `not_mem_strongDomain_formalExp_iff_escapeBound` record the remark after
  `hol:prop:expdomain`: for the first-order recurrence of `E_η`, the region excluded by
  `hol:thm:escapeexclusion` is exactly the complement of the domain, boundary included.

The refined periodic threshold `hol:cor:periodic`, which needs divisibility, and the
certificate lemmas `hol:lem:support` and `hol:lem:certificate` are not formalized here.
-/

namespace Surreal.Holonomic

open _root_.HahnSeries

noncomputable section

section Vocabulary

variable {Γ R : Type*}

section Summable

variable [PartialOrder Γ] [AddCommMonoid R]

/-- `hol:def:entire`: a family of Hahn series is strongly summable if it is the family of
terms of a Mathlib `SummableFamily`, that is, the union of its supports is partially well
ordered and every exponent lies in the supports of only finitely many members. -/
def StronglySummable {ι : Type*} (b : ι → R⟦Γ⟧) : Prop :=
  ∃ s : SummableFamily Γ R ι, ∀ i, s i = b i

/-- The two clauses of strong summability in `hol:def:entire`. -/
theorem stronglySummable_iff {ι : Type*} (b : ι → R⟦Γ⟧) :
    StronglySummable b ↔
      (⋃ i, (b i).support).IsPWO ∧ ∀ g : Γ, {i | (b i).coeff g ≠ 0}.Finite := by
  constructor
  · rintro ⟨s, hs⟩
    have hb : b = fun i => s i := funext fun i => (hs i).symm
    subst hb
    exact ⟨s.isPWO_iUnion_support, s.finite_co_support⟩
  · rintro ⟨hpwo, hfin⟩
    exact ⟨⟨b, hpwo, hfin⟩, fun _ => rfl⟩

end Summable

/-- `hol:def:entire` verbatim for a linearly ordered exponent group: the union of the supports
is well ordered and each exponent lies in only finitely many supports. -/
theorem stronglySummable_iff_isWF [LinearOrder Γ] [AddCommMonoid R] {ι : Type*}
    (b : ι → R⟦Γ⟧) :
    StronglySummable b ↔
      (⋃ i, (b i).support).IsWF ∧ ∀ g : Γ, {i | (b i).coeff g ≠ 0}.Finite := by
  rw [stronglySummable_iff, Set.isPWO_iff_isWF]

section Domain

variable [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ] [Semiring R]

/-- `hol:def:entire`: the strong evaluation domain of a formal power series with Hahn
coefficients is the set of arguments `x` at which the family `(a_n x^n)` is strongly
summable, before any cancellation between different indices. -/
def strongDomain (f : PowerSeries R⟦Γ⟧) : Set R⟦Γ⟧ :=
  {x | StronglySummable fun n => PowerSeries.coeff n f * x ^ n}

/-- `hol:def:entire`: a formal power series is (strongly) entire if its strong evaluation
domain is the whole Hahn field. -/
def IsStronglyEntire (f : PowerSeries R⟦Γ⟧) : Prop :=
  strongDomain f = Set.univ

end Domain

/-- `hol:def:orderunit`: a positive `μ` is an order unit if every `|γ|` is bounded by some
ordinary multiple of `μ`. -/
def IsOrderUnit [AddCommGroup Γ] [LinearOrder Γ] (μ : Γ) : Prop :=
  0 < μ ∧ ∀ γ : Γ, ∃ N : ℕ, |γ| ≤ N • μ

end Vocabulary

section Nonincreasing

variable {Γ R ι : Type*} [LinearOrder Γ] [Zero Γ] [AddCommMonoid R]

/-- `hol:lem:nonincreasing`: a family possessing nonzero members at pairwise distinct indices,
forming an infinite sequence whose leading exponents are nonincreasing, is not strongly
summable. Other members of the family may vanish. The proof handles both failure modes at
once: a monotone subsequence of the leading exponents, supplied by partial well-ordering of
the union of supports, must be constant, and then one exponent lies in infinitely many
supports. -/
theorem not_stronglySummable_of_antitone_order {b : ι → R⟦Γ⟧} {idx : ℕ → ι}
    (hidx : Function.Injective idx) (hne : ∀ r, b (idx r) ≠ 0)
    (hanti : Antitone fun r => (b (idx r)).order) : ¬ StronglySummable b := by
  rintro ⟨s, hs⟩
  have hmem : ∀ r, (b (idx r)).order ∈ ⋃ i, (s i).support := fun r =>
    Set.mem_iUnion.mpr ⟨idx r, by
      rw [hs]
      exact (mem_support _ _).mpr (coeff_order_eq_zero.not.mpr (hne r))⟩
  obtain ⟨g, hg⟩ := s.isPWO_iUnion_support.exists_monotone_subseq hmem
  have hconst : ∀ n, (b (idx (g n))).order = (b (idx (g 0))).order := fun n =>
    le_antisymm (hanti (g.monotone (Nat.zero_le n))) (hg (Nat.zero_le n))
  have hinf : {i | (s i).coeff (b (idx (g 0))).order ≠ 0}.Infinite := by
    refine Set.infinite_of_injective_forall_mem (f := fun n => idx (g n))
      (hidx.comp g.injective) fun n => ?_
    change (s (idx (g n))).coeff (b (idx (g 0))).order ≠ 0
    rw [hs, ← hconst n]
    exact coeff_order_eq_zero.not.mpr (hne _)
  exact hinf (s.finite_co_support _)

/-- `hol:lem:nonincreasing`, with the nonincreasing condition stated step by step. -/
theorem not_stronglySummable_of_order_succ_le {b : ι → R⟦Γ⟧} {idx : ℕ → ι}
    (hidx : Function.Injective idx) (hne : ∀ r, b (idx r) ≠ 0)
    (hsucc : ∀ r, (b (idx (r + 1))).order ≤ (b (idx r)).order) : ¬ StronglySummable b :=
  not_stronglySummable_of_antitone_order hidx hne (antitone_nat_of_succ_le hsucc)

end Nonincreasing

section Escape

variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Semiring R] [NoZeroDivisors R]

/-- One step of `hol:lem:escape`: at an index where the recurrence holds with `c₀(n) ≠ 0` and
`a_n ≠ 0`, some shift `j ∈ {1, …, s}` has `c_j(n) a_{n+j} ≠ 0` and satisfies the escape
inequality `hol:eq:escapeineq`. Otherwise the leading monomial of `c₀(n) a_n` could not
cancel. -/
theorem exists_escape_step {a : ℕ → R⟦Γ⟧} {c : ℕ → ℕ → R⟦Γ⟧} {s n : ℕ}
    (hrec : c 0 n * a n + ∑ j ∈ Finset.Icc 1 s, c j n * a (n + j) = 0)
    (hc0 : c 0 n ≠ 0) (ha : a n ≠ 0) :
    ∃ j ∈ Finset.Icc 1 s, c j n ≠ 0 ∧ a (n + j) ≠ 0 ∧
      (a (n + j)).order - (a n).order ≤ (c 0 n).order - (c j n).order := by
  have h0 : c 0 n * a n ≠ 0 := mul_ne_zero hc0 ha
  obtain ⟨j, hj, hne, hle⟩ : ∃ j ∈ Finset.Icc 1 s, c j n * a (n + j) ≠ 0 ∧
      (c j n * a (n + j)).order ≤ (c 0 n * a n).order := by
    by_contra hcon
    have hlt : ∀ j ∈ Finset.Icc 1 s, c j n * a (n + j) ≠ 0 →
        (c 0 n * a n).order < (c j n * a (n + j)).order :=
      fun j hj hz => not_le.mp fun hle => hcon ⟨j, hj, hz, hle⟩
    have hsum : (∑ j ∈ Finset.Icc 1 s, c j n * a (n + j)).coeff (c 0 n * a n).order = 0 := by
      rw [coeff_sum]
      refine Finset.sum_eq_zero fun j hj => ?_
      by_cases hz : c j n * a (n + j) = 0
      · rw [hz, coeff_zero]
      · exact coeff_eq_zero_of_lt_order (hlt j hj hz)
    have hcoeff := congrArg (fun y => y.coeff (c 0 n * a n).order) hrec
    simp only [coeff_add, hsum, add_zero, coeff_zero] at hcoeff
    exact coeff_order_eq_zero.not.mpr h0 hcoeff
  have hcj : c j n ≠ 0 := left_ne_zero_of_mul hne
  have haj : a (n + j) ≠ 0 := right_ne_zero_of_mul hne
  refine ⟨j, hj, hcj, haj, ?_⟩
  rw [order_mul hcj haj, order_mul hc0 ha] at hle
  rw [sub_le_sub_iff, add_comm (a (n + j)).order]
  exact hle

/-- `hol:lem:escape`: if the recurrence `hol:eq:generalrecurrence` holds with `c₀(n) ≠ 0` for
all `n ≥ N`, and `a_{n₀} ≠ 0` for some `n₀ ≥ N`, then `s ≥ 1` and there is an infinite chain
`n₀ < n₁ < ⋯` with jumps `j_r = n_{r+1} - n_r ∈ {1, …, s}`, `a_{n_r} ≠ 0`, `c_{j_r}(n_r) ≠ 0`,
and the escape inequality `hol:eq:escapeineq`. -/
theorem exists_escape_chain {a : ℕ → R⟦Γ⟧} {c : ℕ → ℕ → R⟦Γ⟧} {s N : ℕ}
    (hrec : ∀ n, N ≤ n → c 0 n * a n + ∑ j ∈ Finset.Icc 1 s, c j n * a (n + j) = 0)
    (hc0 : ∀ n, N ≤ n → c 0 n ≠ 0) {n₀ : ℕ} (hn₀ : N ≤ n₀) (ha : a n₀ ≠ 0) :
    1 ≤ s ∧ ∃ ch jmp : ℕ → ℕ, ch 0 = n₀ ∧ StrictMono ch ∧ ∀ r, N ≤ ch r ∧
      jmp r ∈ Finset.Icc 1 s ∧ ch (r + 1) = ch r + jmp r ∧ a (ch r) ≠ 0 ∧
      c (jmp r) (ch r) ≠ 0 ∧ (a (ch (r + 1))).order - (a (ch r)).order ≤
        (c 0 (ch r)).order - (c (jmp r) (ch r)).order := by
  let T := {n : ℕ // N ≤ n ∧ a n ≠ 0}
  have hstep : ∀ t : T, ∃ j ∈ Finset.Icc 1 s, c j t.1 ≠ 0 ∧ a (t.1 + j) ≠ 0 ∧
      (a (t.1 + j)).order - (a t.1).order ≤ (c 0 t.1).order - (c j t.1).order := fun t =>
    exists_escape_step (hrec t.1 t.2.1) (hc0 t.1 t.2.1) t.2.2
  choose jmp' hjmp' hc' ha' hle' using hstep
  let next : T → T := fun t => ⟨t.1 + jmp' t, le_trans t.2.1 (Nat.le_add_right _ _), ha' t⟩
  let t₀ : T := ⟨n₀, hn₀, ha⟩
  have hsucc : ∀ r, (next^[r + 1] t₀).1 = (next^[r] t₀).1 + jmp' (next^[r] t₀) := fun r => by
    rw [Function.iterate_succ_apply']
  have hpos : ∀ t, 1 ≤ jmp' t := fun t => (Finset.mem_Icc.mp (hjmp' t)).1
  refine ⟨le_trans (hpos t₀) (Finset.mem_Icc.mp (hjmp' t₀)).2,
    fun r => (next^[r] t₀).1, fun r => jmp' (next^[r] t₀), rfl, ?_, fun r => ?_⟩
  · refine strictMono_nat_of_lt_succ fun r => ?_
    rw [hsucc r]
    have := hpos (next^[r] t₀)
    omega
  · refine ⟨(next^[r] t₀).2.1, hjmp' _, hsucc r, (next^[r] t₀).2.2, hc' _, ?_⟩
    beta_reduce
    rw [hsucc r]
    exact hle' _

/-- `hol:thm:escapeexclusion`: in the situation of `hol:lem:escape`, if `x ≠ 0` satisfies the
weak bound `hol:eq:boundincrements` `v(c₀(n)) - v(c_j(n)) + j v(x) ≤ 0` for every `n ≥ N` and
every `j ∈ {1, …, s}` with `c_j(n) ≠ 0`, and `a_{n₀} ≠ 0` for some `n₀ ≥ N`, then the
evaluation family `(a_n x^n)` is not strongly summable. -/
theorem not_stronglySummable_of_escape {a : ℕ → R⟦Γ⟧} {c : ℕ → ℕ → R⟦Γ⟧} {s N : ℕ}
    (hrec : ∀ n, N ≤ n → c 0 n * a n + ∑ j ∈ Finset.Icc 1 s, c j n * a (n + j) = 0)
    (hc0 : ∀ n, N ≤ n → c 0 n ≠ 0) {x : R⟦Γ⟧} (hx : x ≠ 0)
    (hbound : ∀ n, N ≤ n → ∀ j ∈ Finset.Icc 1 s, c j n ≠ 0 →
      (c 0 n).order - (c j n).order + j • x.order ≤ 0)
    {n₀ : ℕ} (hn₀ : N ≤ n₀) (ha : a n₀ ≠ 0) :
    ¬ StronglySummable fun n => a n * x ^ n := by
  obtain ⟨-, ch, jmp, -, hmono, hch⟩ := exists_escape_chain hrec hc0 hn₀ ha
  have hord : ∀ m, a m ≠ 0 → (a m * x ^ m).order = (a m).order + m • x.order := fun m hm => by
    rw [order_mul hm (pow_ne_zero _ hx), order_pow]
  refine not_stronglySummable_of_order_succ_le hmono.injective
    (fun r => mul_ne_zero (hch r).2.2.2.1 (pow_ne_zero _ hx)) fun r => ?_
  obtain ⟨hN, hj, hsucc, har, hcj, hle⟩ := hch r
  have har' : a (ch (r + 1)) ≠ 0 := (hch (r + 1)).2.2.2.1
  have key : (a (ch (r + 1))).order + jmp r • x.order ≤ (a (ch r)).order := by
    have h := (add_le_add hle (le_refl (jmp r • x.order))).trans (hbound _ hN _ hj hcj)
    rwa [sub_add_eq_add_sub, sub_nonpos] at h
  rw [hord _ har', hord _ har,
    show ch (r + 1) • x.order = ch r • x.order + jmp r • x.order by rw [hsucc, add_nsmul]]
  calc (a (ch (r + 1))).order + (ch r • x.order + jmp r • x.order)
      = ((a (ch (r + 1))).order + jmp r • x.order) + ch r • x.order := by abel
    _ ≤ (a (ch r)).order + ch r • x.order := add_le_add key le_rfl

/-- `hol:thm:escapeexclusion` for a formal power series `f = ∑ a_n z^n`: under the escape
bound, a single nonzero coefficient `a_{n₀}` with `n₀ ≥ N` puts `x` outside `Dom(f)`. -/
theorem not_mem_strongDomain_of_escape {f : PowerSeries R⟦Γ⟧} {c : ℕ → ℕ → R⟦Γ⟧} {s N : ℕ}
    (hrec : ∀ n, N ≤ n → c 0 n * PowerSeries.coeff n f +
      ∑ j ∈ Finset.Icc 1 s, c j n * PowerSeries.coeff (n + j) f = 0)
    (hc0 : ∀ n, N ≤ n → c 0 n ≠ 0) {x : R⟦Γ⟧} (hx : x ≠ 0)
    (hbound : ∀ n, N ≤ n → ∀ j ∈ Finset.Icc 1 s, c j n ≠ 0 →
      (c 0 n).order - (c j n).order + j • x.order ≤ 0)
    {n₀ : ℕ} (hn₀ : N ≤ n₀) (ha : PowerSeries.coeff n₀ f ≠ 0) : x ∉ strongDomain f :=
  not_stronglySummable_of_escape (a := fun n => PowerSeries.coeff n f) hrec hc0 hx hbound hn₀ ha

/-- `hol:thm:escapeexclusion`, equivalent form: strong summability of `(a_n x^n)` forces
`a_n = 0` for every `n ≥ N`. -/
theorem eq_zero_of_stronglySummable_escape {a : ℕ → R⟦Γ⟧} {c : ℕ → ℕ → R⟦Γ⟧} {s N : ℕ}
    (hrec : ∀ n, N ≤ n → c 0 n * a n + ∑ j ∈ Finset.Icc 1 s, c j n * a (n + j) = 0)
    (hc0 : ∀ n, N ≤ n → c 0 n ≠ 0) {x : R⟦Γ⟧} (hx : x ≠ 0)
    (hbound : ∀ n, N ≤ n → ∀ j ∈ Finset.Icc 1 s, c j n ≠ 0 →
      (c 0 n).order - (c j n).order + j • x.order ≤ 0)
    (hs : StronglySummable fun n => a n * x ^ n) : ∀ n, N ≤ n → a n = 0 :=
  fun _ hn => by_contra fun ha => not_stronglySummable_of_escape hrec hc0 hx hbound hn ha hs

/-- `hol:cor:boundedcost`: if a single `B` bounds `v(c₀(n)) - v(c_j(n))` for all `n ≥ N` and
all shifts with `c_j(n) ≠ 0`, then strong summability of `(a_n x^n)` at any `x ≠ 0` with
`v(x) ≤ -max B 0` forces `a_n = 0` for all `n ≥ N`. No divisibility is used. -/
theorem eq_zero_of_boundedCost {a : ℕ → R⟦Γ⟧} {c : ℕ → ℕ → R⟦Γ⟧} {s N : ℕ}
    (hrec : ∀ n, N ≤ n → c 0 n * a n + ∑ j ∈ Finset.Icc 1 s, c j n * a (n + j) = 0)
    (hc0 : ∀ n, N ≤ n → c 0 n ≠ 0) (B : Γ)
    (hB : ∀ n, N ≤ n → ∀ j ∈ Finset.Icc 1 s, c j n ≠ 0 → (c 0 n).order - (c j n).order ≤ B)
    {x : R⟦Γ⟧} (hx : x ≠ 0) (hxB : x.order ≤ -max B 0)
    (hs : StronglySummable fun n => a n * x ^ n) : ∀ n, N ≤ n → a n = 0 := by
  refine eq_zero_of_stronglySummable_escape hrec hc0 hx (fun n hn j hj hcj => ?_) hs
  have hv : x.order ≤ 0 := hxB.trans (neg_nonpos.mpr (le_max_right B 0))
  have hvB : x.order ≤ -B := hxB.trans (neg_le_neg (le_max_left B 0))
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by have := (Finset.mem_Icc.mp hj).1; omega⟩
  have hjv : (k + 1) • x.order ≤ x.order := by
    rw [succ_nsmul]
    exact add_le_of_nonpos_left (nsmul_nonpos hv k)
  calc (c 0 n).order - (c (k + 1) n).order + (k + 1) • x.order ≤ B + -B :=
        add_le_add (hB n hn _ hj hcj) (hjv.trans hvB)
    _ = 0 := add_neg_cancel B

omit [NoZeroDivisors R] in
/-- `hol:cor:boundedcost`, existence clause: for every `δ ≥ max B 0` the monomial `t^{-δ}` is
a nonzero argument with `v(t^{-δ}) ≤ -max B 0`; `δ = max B 0` gives `t^{-B⁺}`. -/
theorem single_neg_witness [Nontrivial R] (B δ : Γ) (hδ : max B 0 ≤ δ) :
    single (-δ) (1 : R) ≠ 0 ∧ (single (-δ) (1 : R)).order ≤ -max B 0 :=
  ⟨single_ne_zero one_ne_zero, by rw [order_single one_ne_zero]; exact neg_le_neg hδ⟩

/-- `hol:cor:boundedcost` at the explicit arguments `x = t^{-δ}`, `δ ≥ max B 0`. -/
theorem eq_zero_of_boundedCost_single [Nontrivial R] {a : ℕ → R⟦Γ⟧} {c : ℕ → ℕ → R⟦Γ⟧}
    {s N : ℕ}
    (hrec : ∀ n, N ≤ n → c 0 n * a n + ∑ j ∈ Finset.Icc 1 s, c j n * a (n + j) = 0)
    (hc0 : ∀ n, N ≤ n → c 0 n ≠ 0) (B : Γ)
    (hB : ∀ n, N ≤ n → ∀ j ∈ Finset.Icc 1 s, c j n ≠ 0 → (c 0 n).order - (c j n).order ≤ B)
    {δ : Γ} (hδ : max B 0 ≤ δ)
    (hs : StronglySummable fun n => a n * single (-δ) (1 : R) ^ n) : ∀ n, N ≤ n → a n = 0 :=
  eq_zero_of_boundedCost hrec hc0 B hB (single_neg_witness B δ hδ).1
    (single_neg_witness B δ hδ).2 hs

end Escape

section FormalExponential

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field K]

/-- The exact strong domain of `(c_n y^n)` for nonzero scalar coefficients: strong
summability holds exactly when `y` has positive order, including `y = 0`. For `c_n = 1/n!`
and `y = t^γ` this specializes to `hol:eq:monomialexp`. -/
theorem stronglySummable_single_mul_pow_iff {c : ℕ → K} (hc : ∀ n, c n ≠ 0) (y : K⟦Γ⟧) :
    StronglySummable (fun n => single 0 (c n) * y ^ n) ↔ 0 < y.orderTop := by
  constructor
  · intro hs
    by_contra hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hy (by simp)
    have hv : y.order ≤ 0 := by
      rw [not_lt, ← order_eq_orderTop_of_ne_zero hy0] at hy
      exact_mod_cast hy
    have hne : ∀ n, single 0 (c n) * y ^ n ≠ 0 := fun n =>
      mul_ne_zero (single_ne_zero (hc n)) (pow_ne_zero n hy0)
    refine not_stronglySummable_of_order_succ_le (idx := id) Function.injective_id hne
      (fun n => ?_) hs
    simp only [id, order_mul (single_ne_zero (hc _)) (pow_ne_zero _ hy0), order_single (hc _),
      order_pow, zero_add, succ_nsmul]
    exact add_le_of_nonpos_right hv
  · intro hy
    obtain ⟨s, hs⟩ := Surreal.HahnSeries.summable_coeff_mul_powers y hy c
    exact ⟨s, hs⟩

/-- The formal exponential `E_η(z) = ∑ t^{nη} z^n / n!` of `hol:prop:expdomain`. -/
def formalExp (η : Γ) : PowerSeries K⟦Γ⟧ :=
  PowerSeries.mk fun n => single (n • η) ((n.factorial : K)⁻¹)

theorem coeff_formalExp (η : Γ) (n : ℕ) :
    PowerSeries.coeff n (formalExp η : PowerSeries K⟦Γ⟧) = single (n • η) ((n.factorial : K)⁻¹) :=
  PowerSeries.coeff_mk _ _

/-- An ordinary positive integer `n + 1` is the constant Hahn series `n + 1`. -/
theorem natCast_add_one_eq_single (n : ℕ) : ((n : K⟦Γ⟧) + 1) = single 0 ((n : K) + 1) := by
  rw [← C_apply, map_add, map_natCast, map_one]

/-- The coefficient recurrence `(n+1) a_{n+1} = t^η a_n` of `E_η`. -/
theorem coeff_succ_formalExp_mul [CharZero K] (η : Γ) (n : ℕ) :
    PowerSeries.coeff (n + 1) (formalExp η : PowerSeries K⟦Γ⟧) * ((n : K⟦Γ⟧) + 1) =
      single η (1 : K) * PowerSeries.coeff n (formalExp η) := by
  rw [coeff_formalExp, coeff_formalExp, natCast_add_one_eq_single, single_mul_single,
    single_mul_single, add_zero, succ_nsmul', one_mul, Nat.factorial_succ, Nat.cast_mul,
    mul_inv, Nat.cast_succ, mul_comm, ← mul_assoc, mul_inv_cancel₀ (Nat.cast_add_one_ne_zero n),
    one_mul]

/-- `hol:prop:expdomain`, differential identity: `D_z E_η = t^η E_η`. -/
theorem derivative_formalExp [CharZero K] (η : Γ) :
    PowerSeries.derivative K⟦Γ⟧ (formalExp η) = single η (1 : K) • formalExp η := by
  ext n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_smul, smul_eq_mul,
    coeff_succ_formalExp_mul]

/-- The evaluation terms of `E_η` at `x` are `(t^η x)^n / n!`. -/
theorem coeff_formalExp_mul_pow (η : Γ) (x : K⟦Γ⟧) (n : ℕ) :
    PowerSeries.coeff n (formalExp η : PowerSeries K⟦Γ⟧) * x ^ n =
      single 0 ((n.factorial : K)⁻¹) * (single η (1 : K) * x) ^ n := by
  rw [coeff_formalExp, mul_pow, single_pow, one_pow, ← mul_assoc, single_mul_single, zero_add,
    mul_one]

/-- `hol:prop:expdomain`, pointwise form: `x ∈ Dom(E_η)` exactly when `x = 0` or
`v(x) > -η`. -/
theorem mem_strongDomain_formalExp_iff [CharZero K] (η : Γ) (x : K⟦Γ⟧) :
    x ∈ strongDomain (formalExp η) ↔ x = 0 ∨ -η < x.order := by
  have hterms : (fun n => PowerSeries.coeff n (formalExp η : PowerSeries K⟦Γ⟧) * x ^ n) =
      fun n => single 0 ((n.factorial : K)⁻¹) * (single η (1 : K) * x) ^ n :=
    funext (coeff_formalExp_mul_pow η x)
  have hfac : ∀ n : ℕ, ((n.factorial : K)⁻¹) ≠ 0 := fun n =>
    inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
  change StronglySummable _ ↔ _
  rw [hterms, stronglySummable_single_mul_pow_iff hfac, orderTop_mul,
    orderTop_single one_ne_zero]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [← order_eq_orderTop_of_ne_zero hx, ← WithTop.coe_add, WithTop.coe_pos,
      neg_lt_iff_pos_add, add_comm η]
    simp [hx]

/-- `hol:prop:expdomain`, equation `hol:eq:expdomain`:
`Dom(E_η) = {0} ∪ {x ∈ K^× : v(x) > -η}`. -/
theorem strongDomain_formalExp [CharZero K] (η : Γ) :
    strongDomain (formalExp η : PowerSeries K⟦Γ⟧) = {0} ∪ {x | x ≠ 0 ∧ -η < x.order} := by
  ext x
  rw [mem_strongDomain_formalExp_iff, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
  tauto

/-- `hol:prop:expdomain`: a nonzero `x` lies outside the domain of `E_η` exactly on the closed
region `v(x) ≤ -η`. -/
theorem not_mem_strongDomain_formalExp_iff [CharZero K] (η : Γ) {x : K⟦Γ⟧} (hx : x ≠ 0) :
    x ∉ strongDomain (formalExp η : PowerSeries K⟦Γ⟧) ↔ x.order ≤ -η := by
  rw [mem_strongDomain_formalExp_iff]
  simp [hx]

/-- The recurrence coefficients of `E_η` in the shape `hol:eq:generalrecurrence`, with the
single shift `s = 1`: `c₀(n) = -t^η` and `c_j(n) = n + 1` for `j ≥ 1`. -/
def expRecCoeff (η : Γ) (j n : ℕ) : K⟦Γ⟧ :=
  if j = 0 then -single η 1 else (n : K⟦Γ⟧) + 1

/-- The coefficients of `E_η` satisfy `hol:eq:generalrecurrence` with `s = 1`, `N = 0`. -/
theorem formalExp_recurrence [CharZero K] (η : Γ) (n : ℕ) :
    expRecCoeff η 0 n * PowerSeries.coeff n (formalExp η : PowerSeries K⟦Γ⟧) +
      ∑ j ∈ Finset.Icc 1 1, expRecCoeff η j n * PowerSeries.coeff (n + j) (formalExp η) =
      0 := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  simp only [expRecCoeff, one_ne_zero, if_false, if_true]
  rw [mul_comm ((n : K⟦Γ⟧) + 1), coeff_succ_formalExp_mul, neg_mul, neg_add_cancel]

omit [IsOrderedAddMonoid Γ] in
/-- The leading recurrence coefficient `c₀(n) = -t^η` of `E_η` never vanishes. -/
theorem expRecCoeff_zero_ne_zero (η : Γ) (n : ℕ) : expRecCoeff (K := K) η 0 n ≠ 0 := by
  simp [expRecCoeff]

/-- For the recurrence of `E_η`, the hypothesis `hol:eq:boundincrements` of
`hol:thm:escapeexclusion` holds exactly on the closed region `v(x) ≤ -η`. This is a formal
equivalence of orders; it is used only for `x ≠ 0`, where `x.order` is the valuation. -/
theorem escapeBound_formalExp_iff [CharZero K] (η : Γ) (x : K⟦Γ⟧) :
    (∀ n, 0 ≤ n → ∀ j ∈ Finset.Icc 1 1, expRecCoeff (K := K) η j n ≠ 0 →
      (expRecCoeff (K := K) η 0 n).order - (expRecCoeff (K := K) η j n).order + j • x.order ≤ 0)
      ↔ x.order ≤ -η := by
  have h0 : ∀ n, (expRecCoeff (K := K) η 0 n).order = η := fun n => by
    simp [expRecCoeff]
  have h1 : ∀ n, (expRecCoeff (K := K) η 1 n).order = 0 := fun n => by
    simp only [expRecCoeff, one_ne_zero, if_false]
    rw [natCast_add_one_eq_single, order_single (Nat.cast_add_one_ne_zero n)]
  have hne : ∀ n, expRecCoeff (K := K) η 1 n ≠ 0 := fun n => by
    simp only [expRecCoeff, one_ne_zero, if_false]
    rw [natCast_add_one_eq_single]
    exact single_ne_zero (Nat.cast_add_one_ne_zero n)
  constructor
  · intro h
    have := h 0 le_rfl 1 (Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩) (hne 0)
    rw [h0, h1, sub_zero, one_nsmul] at this
    exact le_neg_iff_add_nonpos_left.mpr this
  · intro hx n _ j hj _
    obtain rfl : j = 1 := by have := Finset.mem_Icc.mp hj; omega
    rw [h0, h1, sub_zero, one_nsmul]
    exact le_neg_iff_add_nonpos_left.mp hx

/-- The remark after `hol:prop:expdomain`: for nonzero `x`, the region excluded from
`Dom(E_η)` by `hol:thm:escapeexclusion` applied to the recurrence of `E_η` is exactly the
complement of the domain, boundary included. The implication from the escape bound to
exclusion is proved by the escape criterion itself, not by the domain computation. -/
theorem not_mem_strongDomain_formalExp_iff_escapeBound [CharZero K] (η : Γ) {x : K⟦Γ⟧}
    (hx : x ≠ 0) :
    x ∉ strongDomain (formalExp η : PowerSeries K⟦Γ⟧) ↔
      ∀ n, 0 ≤ n → ∀ j ∈ Finset.Icc 1 1, expRecCoeff (K := K) η j n ≠ 0 →
        (expRecCoeff (K := K) η 0 n).order - (expRecCoeff (K := K) η j n).order +
          j • x.order ≤ 0 := by
  constructor
  · intro h
    exact (escapeBound_formalExp_iff η x).mpr ((not_mem_strongDomain_formalExp_iff η hx).mp h)
  · intro hbound
    have ha : PowerSeries.coeff 0 (formalExp η : PowerSeries K⟦Γ⟧) ≠ 0 := by
      rw [coeff_formalExp]
      simp
    exact not_mem_strongDomain_of_escape (fun n _ => formalExp_recurrence η n)
      (fun n _ => expRecCoeff_zero_ne_zero η n) hx hbound le_rfl ha

end FormalExponential

end

end Surreal.Holonomic
