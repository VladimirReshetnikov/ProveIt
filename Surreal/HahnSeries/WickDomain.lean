import Surreal.Algebra.StrictAlternative
import Surreal.Algebra.WickQuartic
import Surreal.HahnSeries.MvEvaluation

/-!
# The exact diagramwise Hahn domain of a Wick expansion

This file proves `wick:thm:main` (the finite-certificate summability theorem) and
`wick:cor:obstruction` of `docs/surcomplex/wick-summability-certificates/article.tex`,
together with `wick:cor:robustness` and the exact leading-exponent identity `wick:eq:leading`.

**Setting.** `Γ` is a nonzero ordered `ℚ`-vector space, that is, a nonzero divisible ordered
abelian group, and the coefficient field `R` is any field of characteristic zero; the source
takes `R = ℂ`, so that `R((t^Γ))` is its field `K`. The interaction has vertex types `a ∈ A`
with exponent vectors `αᵃ ∈ ℕ^V` and nonzero couplings `gₐ`. The covariance is given by a
finite edge type `E` with endpoints `ends e = (i, j)` and nonzero entries `Cₑ`. Count vectors
`q = (m, k)` are functions `A ⊕ E → ℕ`. The incidence map `q ↦ Am - Dk` (`incidence`) has the
rows `(Aᵀ; -Dᵀ)` of `wick:eq:wickM`, with `D_e = 2e_i` for a loop and `e_i + e_j` otherwise.
The sector `Q_β = {Am + β = Dk}` of `wick:eq:incidence` is `sector α ends β`
(`mem_sector_iff`), and `S = Q_0`. The atom `T_β(m, k) = W(Am + β, k) / ∏ₐ mₐ! · g^m C^k` of
`wick:eq:atom` is `atom`, with `W` given by the closed formula `wick:eq:W` (`wickW`); only
`W > 0` is used. `StronglySummable` is `wick:def:strong` (`stronglySummable_iff_isWF`), and the
weight `L(m, k) = ∑ₐ mₐ v(gₐ) + ∑ₑ kₑ v(Cₑ)` of `wick:eq:weight` is `wickWeight`.

**Main results.**
* `order_atom`: `v(T_β(q)) = L(q)`, which is `wick:eq:leading`.
* `main_tfae`: the five conditions (i)–(v) of `wick:thm:main` are equivalent: (i) the vacuum
  atom family is strongly summable; (ii) `L > 0` on `S ∖ {0}`; (iii) `L > 0` on the finite
  Hilbert basis of `S` (`Surreal.Wick.hilbertBasis`, finite by
  `Surreal.Wick.finite_hilbertBasis`); (iv) the balancing system `wick:eq:balance` has a
  solution `p ∈ Γ^V`; (v) every sector family is strongly summable.
* `stronglySummable_atom_iff_vacuum`: the last assertion of `wick:thm:main`; for one nonempty
  sector, summability in that sector is equivalent to these conditions.
  `stronglySummable_atom_iff` is the sector criterion, which also covers empty sectors.
* `main_tfae_matrix`: the theorem for the source's data, a covariance matrix `C` with edge set
  `E = {(i, j) : i ≤ j, C_ij ≠ 0}`. Only the entries with `i ≤ j` enter, so no symmetry of `C`
  is assumed, and `C` may be singular.
* `exists_hilbertBasis_obstruction` and `not_stronglySummable_atom_multiples`:
  `wick:cor:obstruction`.
* `stronglySummable_atom_congr_order` (equal valuations) and `stronglySummable_atom_scale_iff`
  (diagonal monomial rescaling by an arbitrary `p`): `wick:cor:robustness`;
  `stronglySummable_atom_matrix_congr_order` is its first part for two covariance matrices with
  the same nonzero pattern on `i ≤ j`.

**Proof.** It follows the source. Necessity (`not_stronglySummable_of_order`,
`forall_pos_of_stronglySummable`): the multiples `q₀ + n q` of a kernel element of weight
`≤ 0` give strictly descending leading exponents, or infinitely many atoms with the same
leading exponent. (ii) ⟺ (iii) is `Surreal.Wick.forall_kernel_pos_iff_forall_hilbertBasis_pos`.
(ii) ⟹ (iv) is `Surreal.Alternative.feasible_iff_forall_pos` (`wick:thm:alternative`) after
clearing denominators (`exists_balance_of_forall_pos`). (iv) ⟹ (v) substitutes the
positive-order rescaled entries `uⱼ = xⱼ t^{bⱼ ⬝ p}` into `Surreal.HahnSeries.mvPowerFamily`
(`wick:cor:substitution`), restricts to the fiber `{q | ∑ⱼ qⱼ bⱼ = γ}` and multiplies by the
fixed monomial `t^{-γ ⬝ p}` (`stronglySummable_of_balance`); for the Wick sector `Q_β`, the fiber
over `γ = -β`, this is the factor `t^{p⬝β}` of `wick:eq:scaledatom`. These steps are proved for
an arbitrary integer count matrix `b` and arbitrary nonzero coefficients
(`stronglySummable_fiber_iff`, `tfae_of_countWeight`) and then specialized to the Wick data.

**Generality.** The source's standing conventions `d, s ≥ 1`, `αᵃ ≠ 0` and "duplicate monomials
combined" are not needed, and the abstract edge type allows parallel edges. Nothing of
`wick:thm:main`, `wick:cor:obstruction` or `wick:cor:robustness` is pending. The counting
statement `wick:lem:wickcount` (that `W(M, k)` is the number of pairings, hence an integer) is
not formalized here and is not needed.
-/

namespace Surreal.WickDomain

open _root_.HahnSeries Surreal.HahnSeries Surreal.Wick Surreal.Alternative

noncomputable section

/-! ### Strong summability -/

section Summable

variable {Γ R : Type*} [PartialOrder Γ] [AddCommMonoid R]

/-- `wick:def:strong`: a family of Hahn series is strongly summable if it is the family of
members of a Mathlib `SummableFamily`, that is, the union of the supports is partially well
ordered and every exponent lies in the supports of only finitely many members. -/
def StronglySummable {ι : Type*} (f : ι → R⟦Γ⟧) : Prop :=
  ∃ s : SummableFamily Γ R ι, ∀ i, s i = f i

/-- The two clauses of strong summability in `wick:def:strong`. -/
theorem stronglySummable_iff {ι : Type*} (f : ι → R⟦Γ⟧) :
    StronglySummable f ↔
      (⋃ i, (f i).support).IsPWO ∧ ∀ g : Γ, {i | (f i).coeff g ≠ 0}.Finite := by
  constructor
  · rintro ⟨s, hs⟩
    have hf : f = fun i => s i := funext fun i => (hs i).symm
    subst hf
    exact ⟨s.isPWO_iUnion_support, s.finite_co_support⟩
  · rintro ⟨hpwo, hfin⟩
    exact ⟨⟨f, hpwo, hfin⟩, fun _ => rfl⟩

/-- A family with an empty index type is strongly summable. -/
theorem stronglySummable_of_isEmpty {ι : Type*} [IsEmpty ι] (f : ι → R⟦Γ⟧) :
    StronglySummable f :=
  ⟨0, fun i => isEmptyElim i⟩

end Summable

/-- `wick:def:strong` verbatim for a linearly ordered exponent group: the union of the supports
is well ordered and each exponent lies in only finitely many supports. -/
theorem stronglySummable_iff_isWF {Γ R : Type*} [LinearOrder Γ] [AddCommMonoid R] {ι : Type*}
    (f : ι → R⟦Γ⟧) :
    StronglySummable f ↔
      (⋃ i, (f i).support).IsWF ∧ ∀ g : Γ, {i | (f i).coeff g ≠ 0}.Finite := by
  rw [stronglySummable_iff, Set.isPWO_iff_isWF]

/-! ### The descent obstruction -/

section Descent

variable {Γ R : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [AddCommMonoid R]

/-- The necessity mechanism in the proof of `wick:thm:main`: if infinitely many distinct
members of a family are nonzero with leading exponents `a + n c`, `c ≤ 0`, the family is not
strongly summable. For `c < 0` the exponents descend forever inside the union of supports; for
`c = 0` the exponent `a` lies in infinitely many supports. -/
theorem not_stronglySummable_of_order {ι : Type*} (f : ι → R⟦Γ⟧) (φ : ℕ → ι)
    (hφ : Function.Injective φ) (a c : Γ) (hc : c ≤ 0) (hne : ∀ n, f (φ n) ≠ 0)
    (hord : ∀ n, (f (φ n)).order = a + n • c) : ¬ StronglySummable f := by
  rw [stronglySummable_iff]
  rintro ⟨hpwo, hfin⟩
  have hmem : ∀ n, (f (φ n)).coeff (a + n • c) ≠ 0 := fun n => by
    rw [← hord n]
    exact coeff_order_eq_zero.not.2 (hne n)
  rcases hc.lt_or_eq with hlt | rfl
  · obtain ⟨m, n, hmn, hle⟩ := Set.PartiallyWellOrderedOn.exists_lt hpwo
      (f := fun n => a + n • c)
      (fun n => Set.mem_iUnion.2 ⟨φ n, (mem_support _ _).2 (hmem n)⟩)
    have hle' : m • c ≤ n • c := le_of_add_le_add_left hle
    have hsplit : n • c = m • c + (n - m) • c := by
      rw [← add_nsmul, Nat.add_sub_cancel' hmn.le]
    have hneg : (n - m) • c < 0 := nsmul_neg hlt (Nat.sub_ne_zero_of_lt hmn)
    rw [hsplit] at hle'
    exact absurd hle' (not_le.2 (add_lt_of_neg_right _ hneg))
  · apply Set.infinite_range_of_injective hφ
    refine (hfin a).subset ?_
    rintro _ ⟨n, rfl⟩
    simpa using hmem n

end Descent

/-! ### Monomials, weights and fibers -/

section Weight

variable {Γ R σ : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [Zero R] [Fintype σ]

/-- The valuation weight `L(q) = ∑ⱼ qⱼ v(xⱼ)` of `wick:eq:weight`. -/
def valWeight (x : σ → R⟦Γ⟧) : (σ → ℕ) →+ Γ :=
  countWeight fun j => (x j).order

theorem valWeight_apply (x : σ → R⟦Γ⟧) (q : σ → ℕ) :
    valWeight x q = ∑ j, q j • (x j).order :=
  rfl

end Weight

section Monomial

variable {Γ R σ : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing R] [IsDomain R] [Fintype σ]

/-- The monomial `x^q = ∏ⱼ xⱼ^{qⱼ}` attached to a count vector `q`. -/
def countMonomial (x : σ → R⟦Γ⟧) (q : σ → ℕ) : R⟦Γ⟧ :=
  ∏ j, x j ^ q j

theorem countMonomial_ne_zero {x : σ → R⟦Γ⟧} (hx : ∀ j, x j ≠ 0) (q : σ → ℕ) :
    countMonomial x q ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (hx j)

/-- The leading exponent of a monomial with nonzero entries is its valuation weight. -/
theorem order_countMonomial {x : σ → R⟦Γ⟧} (hx : ∀ j, x j ≠ 0) (q : σ → ℕ) :
    (countMonomial x q).order = valWeight x q := by
  classical
  rw [valWeight_apply, countMonomial]
  suffices h : ∀ t : Finset σ, (∏ j ∈ t, x j ^ q j).order = ∑ j ∈ t, q j • (x j).order from
    h Finset.univ
  intro t
  induction t using Finset.induction_on with
  | empty => simp
  | insert j t hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj,
      order_mul (pow_ne_zero _ (hx j))
        (Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hx i)),
      order_pow, ih]

/-- A nonzero scalar multiple of a nonzero Hahn series is nonzero and has the same order. -/
theorem smul_ne_zero_and_order {c : R} (hc : c ≠ 0) {y : R⟦Γ⟧} (hy : y ≠ 0) :
    c • y ≠ 0 ∧ (c • y).order = y.order := by
  rw [← single_zero_mul_eq_smul]
  have hs : single (0 : Γ) c ≠ 0 := single_ne_zero hc
  refine ⟨mul_ne_zero hs hy, ?_⟩
  rw [order_mul hs hy, order_single hc, zero_add]

/-- Multiplying the entries by monomials `t^{sⱼ}` shifts the valuation weight by `∑ⱼ qⱼ sⱼ`. -/
theorem valWeight_mul_single {x : σ → R⟦Γ⟧} (hx : ∀ j, x j ≠ 0) (s : σ → Γ) (q : σ → ℕ) :
    valWeight (fun j => x j * single (s j) (1 : R)) q = valWeight x q + ∑ j, q j • s j := by
  simp only [valWeight_apply, order_mul (hx _) (single_ne_zero one_ne_zero),
    order_single one_ne_zero, smul_add, Finset.sum_add_distrib]

omit [IsDomain R] [Fintype σ] in
/-- A finite product of monomials `t^{cⱼ}` is the monomial `t^{∑ cⱼ}`. -/
theorem prod_single_one (t : Finset σ) (c : σ → Γ) :
    ∏ j ∈ t, single (c j) (1 : R) = single (∑ j ∈ t, c j) 1 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert j t hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, single_mul_single, mul_one]

end Monomial

section Fiber

variable {σ G : Type*} [AddCommMonoid G]

/-- The fiber `{q | f q = β}` of a count map. For the Wick incidence map this is the observable
sector `Q_β` of `wick:eq:incidence`. -/
def fiber (f : (σ → ℕ) →+ G) (β : G) : Set (σ → ℕ) :=
  {q | f q = β}

theorem mem_fiber {f : (σ → ℕ) →+ G} {β : G} {q : σ → ℕ} : q ∈ fiber f β ↔ f q = β :=
  Iff.rfl

end Fiber

/-! ### Necessity: summability forces positivity on the kernel -/

section Necessity

variable {Γ R σ G : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [AddCommMonoid R] [AddCommGroup G]

/-- `wick:thm:main`, (i) ⟹ (ii) and the necessity half of the sector statement: if a family on
a nonempty fiber `f⁻¹(β)` has nonzero members whose orders are given by an additive weight `L`,
and it is strongly summable, then `L q > 0` for every nonzero `q` in the kernel `S = f⁻¹(0)`.
The proof uses the members indexed by `q₀ + n q`, which stay in the fiber. -/
theorem forall_pos_of_stronglySummable (f : (σ → ℕ) →+ G) (L : (σ → ℕ) →+ Γ) {β : G}
    (F : fiber f β → R⟦Γ⟧) (hF0 : ∀ q, F q ≠ 0) (hFord : ∀ q, (F q).order = L q.1)
    {q₀ : σ → ℕ} (hq₀ : q₀ ∈ fiber f β) (hs : StronglySummable F) :
    ∀ q, f q = 0 → q ≠ 0 → 0 < L q := by
  intro q hq hq0
  by_contra hle
  have hmem : ∀ n : ℕ, q₀ + n • q ∈ fiber f β := fun n => by
    rw [mem_fiber, map_add, map_nsmul, hq, nsmul_zero, add_zero]
    exact hq₀
  refine not_stronglySummable_of_order F (fun n => ⟨q₀ + n • q, hmem n⟩) ?_ (L q₀) (L q)
    (not_lt.1 hle) (fun n => hF0 _) (fun n => ?_) hs
  · intro m n hmn
    have h1 : q₀ + m • q = q₀ + n • q := congrArg Subtype.val hmn
    have h2 : m • q = n • q := add_left_cancel h1
    obtain ⟨j, hj⟩ : ∃ j, q j ≠ 0 := by
      by_contra! h
      exact hq0 (funext h)
    have h3 := congrFun h2 j
    simp only [Pi.smul_apply, smul_eq_mul] at h3
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hj) h3
  · rw [hFord, map_add, map_nsmul]

/-- `wick:cor:obstruction`, last sentence: the multiples of a count vector of nonpositive
weight index a family that is not strongly summable, as soon as its members are nonzero with
orders given by the weight. -/
theorem not_stronglySummable_multiples (L : (σ → ℕ) →+ Γ) {q : σ → ℕ} (hL : L q ≤ 0)
    (F : ℕ → R⟦Γ⟧) (hF0 : ∀ n, F n ≠ 0) (hFord : ∀ n, (F n).order = L (n • q)) :
    ¬ StronglySummable F :=
  not_stronglySummable_of_order F id Function.injective_id 0 (L q) hL hF0 fun n => by
    rw [id, hFord, map_nsmul, zero_add]

end Necessity

/-! ### Hilbert-basis obstructions -/

section Hilbert

variable {ι G Γ : Type*} [Finite ι] [AddCommGroup G] [AddCommMonoid Γ] [LinearOrder Γ]
  [IsOrderedCancelAddMonoid Γ]

/-- `wick:cor:obstruction`, second sentence: if a nonzero kernel element `q` has nonpositive
weight, some Hilbert-basis element `h` of nonpositive weight occurs in a decomposition of `q`,
namely `q = h + r` with `r` in the kernel (and `r` is itself a sum of Hilbert-basis elements by
`Surreal.Wick.mem_closure_hilbertBasis`). -/
theorem exists_hilbertBasis_summand_nonpos (f : (ι → ℕ) →+ G) (L : (ι → ℕ) →+ Γ)
    {q : ι → ℕ} (hq : f q = 0) (hq0 : q ≠ 0) (hL : L q ≤ 0) :
    ∃ h ∈ hilbertBasis f, L h ≤ 0 ∧ ∃ r, f r = 0 ∧ q = h + r := by
  have hker : AddSubmonoid.closure (hilbertBasis f) ≤ AddMonoidHom.mker f :=
    AddSubmonoid.closure_le.2 fun h hh => hh.1.1
  have key : ∀ y ∈ AddSubmonoid.closure (hilbertBasis f),
      y = 0 ∨ 0 < L y ∨ ∃ h ∈ hilbertBasis f, L h ≤ 0 ∧ ∃ r, f r = 0 ∧ y = h + r := by
    intro y hy
    induction hy using AddSubmonoid.closure_induction with
    | mem y hy =>
      by_cases hLy : 0 < L y
      · exact Or.inr (Or.inl hLy)
      · exact Or.inr (Or.inr ⟨y, hy, not_lt.1 hLy, 0, map_zero f, (add_zero y).symm⟩)
    | zero => exact Or.inl rfl
    | add y z hy hz ihy ihz =>
      have hfy : f y = 0 := AddMonoidHom.mem_mker.1 (hker hy)
      have hfz : f z = 0 := AddMonoidHom.mem_mker.1 (hker hz)
      rcases ihy with rfl | hLy | ⟨h, hh, hLh, r, hr, rfl⟩
      · rw [zero_add]
        exact ihz
      · rcases ihz with rfl | hLz | ⟨h, hh, hLh, r, hr, rfl⟩
        · rw [add_zero]
          exact Or.inr (Or.inl hLy)
        · exact Or.inr (Or.inl (by rw [map_add]; exact add_pos hLy hLz))
        · refine Or.inr (Or.inr ⟨h, hh, hLh, y + r, ?_, add_left_comm y h r⟩)
          rw [map_add, hfy, hr, add_zero]
      · refine Or.inr (Or.inr ⟨h, hh, hLh, r + z, ?_, add_assoc h r z⟩)
        rw [map_add, hr, hfz, add_zero]
  rcases key q (mem_closure_hilbertBasis f hq) with h0 | hpos | hex
  · exact absurd h0 hq0
  · exact absurd hpos (not_lt.2 hL)
  · exact hex

end Hilbert

/-! ### The strict alternative for count maps -/

section Balance

variable {Γ σ V : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Fintype σ] [Fintype V]

omit [LinearOrder Γ] [IsOrderedAddMonoid Γ] in
/-- Exchanging the order of summation in `∑ⱼ qⱼ (bⱼ ⬝ p) = (∑ⱼ qⱼ bⱼ) ⬝ p`. -/
theorem sum_nsmul_sum_zsmul (b : σ → V → ℤ) (p : V → Γ) (q : σ → ℕ) :
    ∑ j, q j • ∑ i, b j i • p i = ∑ i, countWeight b q i • p i := by
  simp only [countWeight_apply, Finset.sum_apply, Pi.smul_apply, Finset.sum_smul,
    Finset.smul_sum, smul_assoc]
  exact Finset.sum_comm

/-- `wick:thm:main`, (iv) ⟹ (ii): a balancing vector makes the weight positive on every
nonzero element of the kernel. -/
theorem forall_pos_of_balance (b : σ → V → ℤ) (w : σ → Γ) {p : V → Γ}
    (hp : ∀ j, 0 < w j + ∑ i, b j i • p i) {q : σ → ℕ} (hq : countWeight b q = 0)
    (hq0 : q ≠ 0) : 0 < countWeight w q := by
  have key : ∑ j, q j • (w j + ∑ i, b j i • p i) = countWeight w q := by
    rw [countWeight_apply]
    simp only [smul_add, Finset.sum_add_distrib]
    rw [sum_nsmul_sum_zsmul, hq]
    simp
  rw [← key]
  obtain ⟨j, hj⟩ : ∃ j, q j ≠ 0 := by
    by_contra! h
    exact hq0 (funext h)
  exact Finset.sum_pos' (fun i _ => nsmul_nonneg (hp i).le _)
    ⟨j, Finset.mem_univ _, nsmul_pos (hp j) hj⟩

/-- `wick:thm:main`, (ii) ⟹ (iv), via `wick:thm:alternative`: if an additive weight is positive
on every nonzero element of the nonnegative integer kernel of `q ↦ ∑ⱼ qⱼ bⱼ`, then there is a
balancing vector `p` with `wⱼ + bⱼ ⬝ p > 0` for every `j`. A rational obstruction is turned into
an integer kernel element by clearing denominators. -/
theorem exists_balance_of_forall_pos [Module ℚ Γ] [Nontrivial Γ] (b : σ → V → ℤ) (w : σ → Γ)
    (h : ∀ q, countWeight b q = 0 → q ≠ 0 → 0 < countWeight w q) :
    ∃ p : V → Γ, ∀ j, 0 < w j + ∑ i, b j i • p i := by
  obtain ⟨p, hp⟩ := (feasible_iff_forall_pos (fun j i => (b j i : ℚ)) w).2 fun r hr0 hrne hrM => by
    obtain ⟨D, m, hD, hm⟩ := exists_int_multiple r
    have hm0 : ∀ j, 0 ≤ m j := fun j => by
      have : (0 : ℚ) ≤ m j := by
        rw [hm j]
        exact mul_nonneg hD.le (hr0 j)
      exact_mod_cast this
    let q : σ → ℕ := fun j => (m j).toNat
    have hqm : ∀ j, ((q j : ℕ) : ℚ) = m j := fun j => by
      have : ((q j : ℕ) : ℤ) = m j := Int.toNat_of_nonneg (hm0 j)
      exact_mod_cast this
    have hq : countWeight b q = 0 := by
      funext i
      have hi : ((countWeight b q i : ℤ) : ℚ) = D * ∑ j, r j * (b j i : ℚ) := by
        rw [countWeight_apply, Finset.sum_apply, Int.cast_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Pi.smul_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, hqm, hm, mul_assoc]
      have h0 : ∑ j, r j * (b j i : ℚ) = 0 := hrM i
      rw [h0, mul_zero] at hi
      exact_mod_cast hi
    have hq0 : q ≠ 0 := by
      obtain ⟨j, hj⟩ := Function.ne_iff.1 hrne
      have hrj : 0 < r j := lt_of_le_of_ne (hr0 j) (Ne.symm hj)
      intro hq0
      have h0 : ((q j : ℕ) : ℚ) = 0 := by
        rw [hq0]
        simp
      rw [hqm, hm] at h0
      exact (mul_pos hD hrj).ne' h0
    have e : ∑ j, r j • w j = D⁻¹ • countWeight w q := by
      rw [countWeight_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, hqm, hm, inv_mul_cancel_left₀ hD.ne']
    rw [e]
    exact qsmul_pos (inv_pos.2 hD) (h q hq hq0)
  refine ⟨p, fun j => ?_⟩
  have := hp j
  simp only [Int.cast_smul_eq_zsmul] at this
  rwa [add_comm]

end Balance

/-! ### Sufficiency: balanced substitution -/

section Substitution

variable {Γ R σ V : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [CommRing R] [IsDomain R] [Fintype σ] [Fintype V]

omit [IsDomain R] in
/-- The compensation identity behind `wick:eq:scaledatom`: rescaling `xⱼ` by `t^{bⱼ ⬝ p}`
multiplies `x^q` by `t^{(∑ⱼ qⱼ bⱼ) ⬝ p}`. -/
theorem countMonomial_mul_single_sum (b : σ → V → ℤ) (p : V → Γ) (x : σ → R⟦Γ⟧)
    (q : σ → ℕ) :
    countMonomial (fun j => x j * single (∑ i, b j i • p i) (1 : R)) q =
      countMonomial x q * single (∑ i, countWeight b q i • p i) 1 := by
  simp only [countMonomial, mul_pow, Finset.prod_mul_distrib, single_pow, one_pow]
  rw [prod_single_one, sum_nsmul_sum_zsmul]

/-- `wick:thm:main`, (iv) ⟹ (v): if `p` balances the data, every fiber family
`(c_q x^q)` over `{q | ∑ⱼ qⱼ bⱼ = β}` is strongly summable, for arbitrary coefficients `c_q`.
The rescaled entries `uⱼ = xⱼ t^{bⱼ ⬝ p}` have positive order, so all monomials `u^q` form a
strongly summable family (`wick:cor:substitution`); on the fiber `x^q = t^{-β ⬝ p} u^q`. For a
Wick sector the fiber value is `-β`, so the factor is `t^{p⬝β}` as in `wick:eq:scaledatom`. -/
theorem stronglySummable_of_balance (b : σ → V → ℤ) {x : σ → R⟦Γ⟧} (hx : ∀ j, x j ≠ 0)
    {p : V → Γ} (hp : ∀ j, 0 < (x j).order + ∑ i, b j i • p i) (β : V → ℤ)
    (c : fiber (countWeight b) β → R) :
    StronglySummable fun q : fiber (countWeight b) β => c q • countMonomial x q.1 := by
  let u : σ → R⟦Γ⟧ := fun j => x j * single (∑ i, b j i • p i) (1 : R)
  have hu : ∀ j, 0 < (u j).orderTop := fun j => by
    change 0 < (x j * single (∑ i, b j i • p i) (1 : R)).orderTop
    rw [orderTop_mul, orderTop_single one_ne_zero, ← order_eq_orderTop_of_ne_zero (hx j),
      ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_lt_coe]
    exact hp j
  refine ⟨single (-∑ i, β i • p i) (1 : R) • SummableFamily.smulFamily c
    (restrict (SummableFamily.Equiv Finsupp.equivFunOnFinite (mvPowerFamily u hu))
      (fiber (countWeight b) β)), fun q => ?_⟩
  change single (-∑ i, β i • p i) (1 : R) *
    (c q • mvPowerFamily u hu (Finsupp.equivFunOnFinite.symm q.1)) = c q • countMonomial x q.1
  rw [mvPowerFamily_apply, mul_smul_comm]
  congr 1
  have hq : countWeight b q.1 = β := q.2
  have e1 : ∏ j, u j ^ (Finsupp.equivFunOnFinite.symm q.1) j =
      countMonomial x q.1 * single (∑ i, β i • p i) 1 := by
    have h := countMonomial_mul_single_sum b p x q.1
    rw [hq] at h
    exact h
  rw [e1, mul_left_comm, single_mul_single, neg_add_cancel, mul_one, single_zero_one, mul_one]

/-- `wick:thm:main` for an arbitrary integer count matrix `b`, in the form used for single
sectors: a fiber family `(c_q x^q)` with nonzero coefficients is strongly summable iff either the
fiber is empty or the weight is positive on every nonzero kernel element. -/
theorem stronglySummable_fiber_iff [Module ℚ Γ] [Nontrivial Γ] (b : σ → V → ℤ)
    {x : σ → R⟦Γ⟧} (hx : ∀ j, x j ≠ 0) (β : V → ℤ) (c : fiber (countWeight b) β → R)
    (hc : ∀ q, c q ≠ 0) :
    StronglySummable (fun q : fiber (countWeight b) β => c q • countMonomial x q.1) ↔
      ((fiber (countWeight b) β).Nonempty →
        ∀ q, countWeight b q = 0 → q ≠ 0 → 0 < valWeight x q) := by
  constructor
  · rintro hs ⟨q₀, hq₀⟩
    exact forall_pos_of_stronglySummable (countWeight b) (valWeight x) _
      (fun q => (smul_ne_zero_and_order (hc q) (countMonomial_ne_zero hx _)).1)
      (fun q => (smul_ne_zero_and_order (hc q) (countMonomial_ne_zero hx _)).2.trans
        (order_countMonomial hx _)) hq₀ hs
  · intro h
    by_cases hne : (fiber (countWeight b) β).Nonempty
    · obtain ⟨p, hp⟩ := exists_balance_of_forall_pos b (fun j => (x j).order) (h hne)
      exact stronglySummable_of_balance b hx hp β c
    · haveI : IsEmpty (fiber (countWeight b) β) :=
        Set.isEmpty_coe_sort.2 (Set.not_nonempty_iff_eq_empty.1 hne)
      exact stronglySummable_of_isEmpty _

/-- `wick:thm:main` for an arbitrary integer count matrix `b : σ → V → ℤ` (columns `bⱼ`), nonzero
entries `xⱼ` and arbitrary nonzero coefficients `c_β(q)`. The following are equivalent:
(i) the vacuum family on `S = {q | ∑ⱼ qⱼ bⱼ = 0}` is strongly summable; (ii) `L(q) > 0` on
`S ∖ {0}`; (iii) `L(h) > 0` on the Hilbert basis of `S`; (iv) some `p` has
`v(xⱼ) + bⱼ ⬝ p > 0` for every `j`; (v) every fiber family is strongly summable. -/
theorem tfae_of_countWeight [Module ℚ Γ] [Nontrivial Γ] (b : σ → V → ℤ) {x : σ → R⟦Γ⟧}
    (hx : ∀ j, x j ≠ 0) (c : (β : V → ℤ) → fiber (countWeight b) β → R)
    (hc : ∀ β q, c β q ≠ 0) :
    List.TFAE [StronglySummable fun q : fiber (countWeight b) 0 => c 0 q • countMonomial x q.1,
      ∀ q, countWeight b q = 0 → q ≠ 0 → 0 < valWeight x q,
      ∀ h ∈ hilbertBasis (countWeight b), 0 < valWeight x h,
      ∃ p : V → Γ, ∀ j, 0 < (x j).order + ∑ i, b j i • p i,
      ∀ β, StronglySummable fun q : fiber (countWeight b) β => c β q • countMonomial x q.1] := by
  have h0 : (fiber (countWeight b) 0).Nonempty := ⟨0, map_zero _⟩
  tfae_have 1 ↔ 2 :=
    (stronglySummable_fiber_iff b hx 0 (c 0) (hc 0)).trans ⟨fun h => h h0, fun h _ => h⟩
  tfae_have 2 ↔ 3 := forall_kernel_pos_iff_forall_hilbertBasis_pos _ _
  tfae_have 2 → 4 := exists_balance_of_forall_pos b _
  tfae_have 4 → 2 := fun ⟨_, hp⟩ _ hq hq0 => forall_pos_of_balance b _ hp hq hq0
  tfae_have 2 → 5 := fun h β =>
    (stronglySummable_fiber_iff b hx β (c β) (hc β)).2 fun _ => h
  tfae_have 5 → 1 := fun h => h 0
  tfae_finish

end Substitution

/-! ### Wick data -/

section WickData

variable {V A E : Type*} [Fintype V] [DecidableEq V] [Fintype A] [Fintype E]

/-- The incidence column `D_e` of an edge `e = (i, j)`: `2 e_i` for a loop and `e_i + e_j`
otherwise. -/
def edgeVec (ends : E → V × V) (e : E) : V → ℕ :=
  Pi.single (ends e).1 1 + Pi.single (ends e).2 1

omit [Fintype E] in
/-- Pairing `D_e` with `p` gives `p_i + p_j`. -/
theorem sum_edgeVec_smul {M : Type*} [AddCommMonoid M] (ends : E → V × V) (e : E)
    (p : V → M) : ∑ i, edgeVec ends e i • p i = p (ends e).1 + p (ends e).2 := by
  simp [edgeVec, add_smul, Finset.sum_add_distrib, Pi.single_apply, ite_smul]

/-- The rows of the matrix `M = (Aᵀ; -Dᵀ)` of `wick:eq:wickM`, indexed by vertex types `a` and
edges `e`. -/
def wickMatrix (α : A → V → ℕ) (ends : E → V × V) : A ⊕ E → V → ℤ :=
  Sum.elim (fun a i => (α a i : ℤ)) fun e i => -(edgeVec ends e i : ℤ)

/-- The incidence map `q = (m, k) ↦ Am - Dk`. -/
def incidence (α : A → V → ℕ) (ends : E → V × V) : (A ⊕ E → ℕ) →+ (V → ℤ) :=
  countWeight (wickMatrix α ends)

/-- The count `(Am)_i = ∑ₐ mₐ αᵃᵢ` of vertex half-edges of color `i`. -/
def vertexCount (α : A → V → ℕ) (q : A ⊕ E → ℕ) : V → ℕ :=
  fun i => ∑ a, q (Sum.inl a) * α a i

/-- The count `(Dk)_i = ∑ₑ kₑ (D_e)ᵢ` of contracted slots of color `i`. -/
def edgeCount (ends : E → V × V) (q : A ⊕ E → ℕ) : V → ℕ :=
  fun i => ∑ e, q (Sum.inr e) * edgeVec ends e i

/-- The observable sector `Q_β = {(m, k) : Am + β = Dk}` of `wick:eq:incidence`, as the fiber of
the incidence map over `-β`; `S = Q_0`. -/
def sector (α : A → V → ℕ) (ends : E → V × V) (β : V → ℕ) : Set (A ⊕ E → ℕ) :=
  fiber (incidence α ends) fun i => -(β i : ℤ)

variable {α : A → V → ℕ} {ends : E → V × V}

omit [Fintype V] in
/-- The `i`-th coordinate of the incidence map is `(Am)_i - (Dk)_i`. -/
theorem incidence_apply (q : A ⊕ E → ℕ) (i : V) :
    incidence α ends q i = (vertexCount α q i : ℤ) - edgeCount ends q i := by
  simp only [incidence, countWeight_apply, Finset.sum_apply, Pi.smul_apply,
    Fintype.sum_sum_type, wickMatrix, Sum.elim_inl, Sum.elim_inr]
  simp only [vertexCount, edgeCount, nsmul_eq_mul, mul_neg, Finset.sum_neg_distrib, Nat.cast_sum,
    Nat.cast_mul, sub_eq_add_neg]

omit [Fintype V] in
/-- Membership in `Q_β` is the color-balance equation `Am + β = Dk` of `wick:eq:incidence`. -/
theorem mem_sector_iff {β : V → ℕ} {q : A ⊕ E → ℕ} :
    q ∈ sector α ends β ↔ vertexCount α q + β = edgeCount ends q := by
  simp only [sector, mem_fiber, funext_iff, incidence_apply, Pi.add_apply]
  refine forall_congr' fun i => ?_
  omega

omit [Fintype V] in
/-- The vacuum sector `S = Q_0` is the kernel of the incidence map. -/
theorem mem_sector_zero_iff {q : A ⊕ E → ℕ} :
    q ∈ sector α ends 0 ↔ incidence α ends q = 0 := by
  simp only [sector, mem_fiber, Pi.zero_apply, Nat.cast_zero, neg_zero]
  exact Iff.rfl

omit [Fintype V] in
/-- `S` is closed under multiples. -/
theorem nsmul_mem_sector_zero {q : A ⊕ E → ℕ} (hq : q ∈ sector α ends 0) (n : ℕ) :
    n • q ∈ sector α ends 0 := by
  rw [mem_sector_zero_iff] at hq ⊢
  rw [map_nsmul, hq, nsmul_zero]

variable (α ends)

/-- The closed formula `wick:eq:W` for `W(M, k)`: the product of the `M_i!` divided by
`2^{k_ii} k_ii!` for loops and by `k_ij!` for the other edges. It is the colored matching
multiplicity of `wick:lem:wickcount` when `E` has no parallel edges; that counting statement is
not formalized, and only the positivity `wickW_pos` is used here. -/
def wickW (M : V → ℕ) (k : E → ℕ) : ℚ :=
  (∏ i, ((M i).factorial : ℚ)) /
    ∏ e, ((if (ends e).1 = (ends e).2 then (2 : ℚ) ^ k e else 1) * ((k e).factorial : ℚ))

omit [Fintype A] in
/-- `W(M, k)` is a positive rational. -/
theorem wickW_pos (M : V → ℕ) (k : E → ℕ) : 0 < wickW ends M k := by
  unfold wickW
  positivity

/-- The rational multiplier `W(Am + β, k) / ∏ₐ mₐ!` of the atom `T_β(m, k)` in
`wick:eq:atom`. -/
def atomCoeff (β : V → ℕ) (q : A ⊕ E → ℕ) : ℚ :=
  wickW ends (vertexCount α q + β) (fun e => q (Sum.inr e)) /
    ∏ a, ((q (Sum.inl a)).factorial : ℚ)

theorem atomCoeff_pos (β : V → ℕ) (q : A ⊕ E → ℕ) : 0 < atomCoeff α ends β q :=
  div_pos (wickW_pos ends _ _) (Finset.prod_pos fun a _ => by positivity)

end WickData

/-! ### The Wick atoms and the main theorem -/

section Wick

variable {Γ R V A E : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field R] [Fintype V] [DecidableEq V] [Fintype A] [Fintype E]
  (α : A → V → ℕ) (ends : E → V × V) (g : A → R⟦Γ⟧) (C : E → R⟦Γ⟧)

/-- The Wick atom `T_β(m, k) = W(Am + β, k) / ∏ₐ mₐ! · g^m C^k` of `wick:eq:atom`, for
`(m, k) ∈ Q_β`. -/
def atom (β : V → ℕ) (q : sector α ends β) : R⟦Γ⟧ :=
  ((atomCoeff α ends β q.1 : ℚ) : R) •
    ((∏ a, g a ^ q.1 (Sum.inl a)) * ∏ e, C e ^ q.1 (Sum.inr e))

/-- The weight `L(m, k) = ∑ₐ mₐ λₐ + ∑ₑ kₑ cₑ` of `wick:eq:weight`, with `λₐ = v(gₐ)` and
`cₑ = v(Cₑ)`. -/
def wickWeight : (A ⊕ E → ℕ) →+ Γ :=
  valWeight (Sum.elim g C)

omit [IsOrderedAddMonoid Γ] in
theorem wickWeight_apply (q : A ⊕ E → ℕ) :
    wickWeight g C q = ∑ a, q (Sum.inl a) • (g a).order + ∑ e, q (Sum.inr e) • (C e).order := by
  simp only [wickWeight, valWeight_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

theorem atom_eq (β : V → ℕ) (q : sector α ends β) :
    atom α ends g C β q =
      ((atomCoeff α ends β q.1 : ℚ) : R) • countMonomial (Sum.elim g C) q.1 := by
  simp only [atom, countMonomial, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]

variable {g C}

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [Fintype A] [Fintype E] in
theorem sumElim_ne_zero (hg : ∀ a, g a ≠ 0) (hC : ∀ e, C e ≠ 0) :
    ∀ j, Sum.elim g C j ≠ 0 := by
  rintro (a | e)
  · exact hg a
  · exact hC e

theorem atom_ne_zero_and_order [CharZero R] (hg : ∀ a, g a ≠ 0) (hC : ∀ e, C e ≠ 0)
    (β : V → ℕ) (q : sector α ends β) :
    atom α ends g C β q ≠ 0 ∧ (atom α ends g C β q).order = wickWeight g C q.1 := by
  have hc : ((atomCoeff α ends β q.1 : ℚ) : R) ≠ 0 :=
    Rat.cast_ne_zero.2 (atomCoeff_pos α ends β q.1).ne'
  have hx := sumElim_ne_zero hg hC
  rw [atom_eq]
  exact ⟨(smul_ne_zero_and_order hc (countMonomial_ne_zero hx _)).1,
    (smul_ne_zero_and_order hc (countMonomial_ne_zero hx _)).2.trans
      (order_countMonomial hx _)⟩

/-- Every Wick atom is nonzero. -/
theorem atom_ne_zero [CharZero R] (hg : ∀ a, g a ≠ 0) (hC : ∀ e, C e ≠ 0) (β : V → ℕ)
    (q : sector α ends β) : atom α ends g C β q ≠ 0 :=
  (atom_ne_zero_and_order α ends hg hC β q).1

/-- `wick:eq:leading`: the leading exponent of the atom `T_β(m, k)` is exactly `L(m, k)`,
whatever the higher Hahn terms of the couplings and covariances. -/
theorem order_atom [CharZero R] (hg : ∀ a, g a ≠ 0) (hC : ∀ e, C e ≠ 0) (β : V → ℕ)
    (q : sector α ends β) : (atom α ends g C β q).order = wickWeight g C q.1 :=
  (atom_ne_zero_and_order α ends hg hC β q).2

variable (g C)

omit [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Fintype A] [Fintype E] in
theorem sum_wickMatrix_inl (p : V → Γ) (a : A) :
    ∑ i, wickMatrix α ends (Sum.inl a) i • p i = ∑ i, α a i • p i := by
  simp only [wickMatrix, Sum.elim_inl, natCast_zsmul]

omit [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Fintype A] [Fintype E] in
theorem sum_wickMatrix_inr (p : V → Γ) (e : E) :
    ∑ i, wickMatrix α ends (Sum.inr e) i • p i = -(p (ends e).1 + p (ends e).2) := by
  simp only [wickMatrix, Sum.elim_inr, neg_smul, Finset.sum_neg_distrib, natCast_zsmul,
    sum_edgeVec_smul]

omit [IsOrderedAddMonoid Γ] [Fintype A] [Fintype E] in
/-- The balancing system `wick:eq:balance` is the strict system `M p + b > 0` for
`M = (Aᵀ; -Dᵀ)` and `b = (λ, c)` of `wick:eq:wickM`. -/
theorem balance_iff (p : V → Γ) :
    (∀ j, 0 < (Sum.elim g C j).order + ∑ i, wickMatrix α ends j i • p i) ↔
      (∀ a, 0 < (g a).order + ∑ i, α a i • p i) ∧
        ∀ e, 0 < (C e).order - p (ends e).1 - p (ends e).2 := by
  rw [Sum.forall]
  simp only [Sum.elim_inl, Sum.elim_inr, sum_wickMatrix_inl, sum_wickMatrix_inr,
    ← sub_eq_add_neg, sub_sub]

variable {g C}

/-- `wick:thm:main`, sector form: for every `β ∈ ℕ^V`, the atom family on `Q_β` is strongly
summable iff `Q_β` is empty or `L(q) > 0` for every `q ∈ S ∖ {0}`. -/
theorem stronglySummable_atom_iff [CharZero R] [Module ℚ Γ] [Nontrivial Γ]
    (hg : ∀ a, g a ≠ 0) (hC : ∀ e, C e ≠ 0) (β : V → ℕ) :
    StronglySummable (atom α ends g C β) ↔
      ((sector α ends β).Nonempty → ∀ q ∈ sector α ends 0, q ≠ 0 → 0 < wickWeight g C q) := by
  have e : atom α ends g C β =
      fun q => ((atomCoeff α ends β q.1 : ℚ) : R) • countMonomial (Sum.elim g C) q.1 :=
    funext (atom_eq α ends g C β)
  rw [e]
  refine (stronglySummable_fiber_iff (wickMatrix α ends) (sumElim_ne_zero hg hC)
    (fun i => -(β i : ℤ)) (fun q => ((atomCoeff α ends β q.1 : ℚ) : R))
    fun q => Rat.cast_ne_zero.2 (atomCoeff_pos α ends β q.1).ne').trans
    (imp_congr Iff.rfl (forall_congr' fun q => ?_))
  rw [mem_sector_zero_iff]
  exact Iff.rfl

/-- **Exact diagramwise Hahn domain** (`wick:thm:main`). Let `Γ` be a nonzero divisible ordered
abelian group (a nonzero ordered `ℚ`-vector space) and `R` a field of characteristic zero (the
source takes `R = ℂ`). Fix exponent vectors `αᵃ ∈ ℕ^V`, nonzero couplings `gₐ ∈ R((t^Γ))`, and
edges `e` with endpoints `ends e` and nonzero covariance entries `Cₑ`. The following are
equivalent:
(i) the vacuum Wick atom family is strongly summable;
(ii) `L(q) > 0` for every `q ∈ S ∖ {0}`;
(iii) `L(h) > 0` for every element `h` of the finite Hilbert basis of `S`;
(iv) some `p ∈ Γ^V` has `λₐ + αᵃ ⬝ p > 0` for all `a` and `c_ij - p_i - p_j > 0` for all edges;
(v) for every `β ∈ ℕ^V`, the Wick atom family on `Q_β` is strongly summable. -/
theorem main_tfae [CharZero R] [Module ℚ Γ] [Nontrivial Γ] (hg : ∀ a, g a ≠ 0)
    (hC : ∀ e, C e ≠ 0) :
    List.TFAE [StronglySummable (atom α ends g C 0),
      ∀ q ∈ sector α ends 0, q ≠ 0 → 0 < wickWeight g C q,
      ∀ h ∈ hilbertBasis (incidence α ends), 0 < wickWeight g C h,
      ∃ p : V → Γ, (∀ a, 0 < (g a).order + ∑ i, α a i • p i) ∧
        ∀ e, 0 < (C e).order - p (ends e).1 - p (ends e).2,
      ∀ β : V → ℕ, StronglySummable (atom α ends g C β)] := by
  have h0 : (sector α ends 0).Nonempty := ⟨0, mem_sector_zero_iff.2 (map_zero _)⟩
  tfae_have 1 ↔ 2 :=
    (stronglySummable_atom_iff α ends hg hC 0).trans ⟨fun h => h h0, fun h _ => h⟩
  tfae_have 2 ↔ 3 := by
    refine Iff.trans ?_
      (forall_kernel_pos_iff_forall_hilbertBasis_pos (incidence α ends) (wickWeight g C))
    exact forall_congr' fun q => by rw [mem_sector_zero_iff]
  tfae_have 2 → 4 := fun h => by
    obtain ⟨p, hp⟩ := exists_balance_of_forall_pos (wickMatrix α ends)
      (fun j => (Sum.elim g C j).order) fun q hq hq0 => h q (mem_sector_zero_iff.2 hq) hq0
    exact ⟨p, (balance_iff α ends g C p).1 hp⟩
  tfae_have 4 → 2 := fun ⟨p, hp⟩ q hq hq0 =>
    forall_pos_of_balance (wickMatrix α ends) (fun j => (Sum.elim g C j).order)
      ((balance_iff α ends g C p).2 hp) (mem_sector_zero_iff.1 hq) hq0
  tfae_have 2 → 5 := fun h β => (stronglySummable_atom_iff α ends hg hC β).2 fun _ => h
  tfae_have 5 → 1 := fun h => h 0
  tfae_finish

/-- `wick:thm:main`, last assertion: for any single `β` with `Q_β` nonempty, strong summability
in that sector is equivalent to strong summability of the vacuum family (hence to all the
conditions of `main_tfae`). -/
theorem stronglySummable_atom_iff_vacuum [CharZero R] [Module ℚ Γ] [Nontrivial Γ]
    (hg : ∀ a, g a ≠ 0) (hC : ∀ e, C e ≠ 0) {β : V → ℕ} (hβ : (sector α ends β).Nonempty) :
    StronglySummable (atom α ends g C β) ↔ StronglySummable (atom α ends g C 0) := by
  rw [stronglySummable_atom_iff α ends hg hC β, stronglySummable_atom_iff α ends hg hC 0]
  exact ⟨fun h _ => h hβ, fun h _ => h ⟨0, mem_sector_zero_iff.2 (map_zero _)⟩⟩

/-- **A computable obstruction pattern** (`wick:cor:obstruction`). If the balancing system
fails, there is `q ∈ S ∖ {0}` with `L(q) ≤ 0`, and some Hilbert-basis element `h` with
`L(h) ≤ 0` occurs in a decomposition `q = h + r`, `r ∈ S`. -/
theorem exists_hilbertBasis_obstruction [Module ℚ Γ] [Nontrivial Γ]
    (h : ¬ ∃ p : V → Γ, (∀ a, 0 < (g a).order + ∑ i, α a i • p i) ∧
      ∀ e, 0 < (C e).order - p (ends e).1 - p (ends e).2) :
    ∃ q ∈ sector α ends 0, q ≠ 0 ∧ wickWeight g C q ≤ 0 ∧
      ∃ h ∈ hilbertBasis (incidence α ends), wickWeight g C h ≤ 0 ∧
        ∃ r ∈ sector α ends 0, q = h + r := by
  have hq : ∃ q, incidence α ends q = 0 ∧ q ≠ 0 ∧ wickWeight g C q ≤ 0 := by
    by_contra! hneg
    obtain ⟨p, hp⟩ := exists_balance_of_forall_pos (wickMatrix α ends)
      (fun j => (Sum.elim g C j).order) hneg
    exact h ⟨p, (balance_iff α ends g C p).1 hp⟩
  obtain ⟨q, hq, hq0, hL⟩ := hq
  obtain ⟨h', hh', hLh, r, hr, rfl⟩ :=
    exists_hilbertBasis_summand_nonpos (incidence α ends) (wickWeight g C) hq hq0 hL
  exact ⟨h' + r, mem_sector_zero_iff.2 hq, hq0, hL, h', hh', hLh, r,
    mem_sector_zero_iff.2 hr, rfl⟩

/-- `wick:cor:obstruction`, last sentence: the vacuum atoms at the multiples `n h` of a kernel
element `h` of nonpositive weight form a family that is not strongly summable. -/
theorem not_stronglySummable_atom_multiples [CharZero R] (hg : ∀ a, g a ≠ 0)
    (hC : ∀ e, C e ≠ 0) {h : A ⊕ E → ℕ} (hh : h ∈ sector α ends 0)
    (hL : wickWeight g C h ≤ 0) :
    ¬ StronglySummable fun n : ℕ => atom α ends g C 0 ⟨n • h, nsmul_mem_sector_zero hh n⟩ :=
  not_stronglySummable_multiples (wickWeight g C) hL _ (fun _ => atom_ne_zero α ends hg hC 0 _)
    fun _ => order_atom α ends hg hC 0 _

/-- **Valuation robustness** (`wick:cor:robustness`, first part). Replacing couplings and
covariance entries by other nonzero Hahn series with the same valuations, keeping the incidence
pattern, does not change strong summability in any sector. Here both families share the edge type
`E`. For two covariance matrices `C`, `C'` with the same nonzero pattern the edge types
`MatrixEdge C` and `MatrixEdge C'` are only propositionally equal; the matrix form is
`stronglySummable_atom_matrix_congr_order`, which takes `E = MatrixEdge C` with the entries
`C'_ij` on it and reindexes along the equal edge sets. -/
theorem stronglySummable_atom_congr_order [CharZero R] [Module ℚ Γ] [Nontrivial Γ]
    {g' : A → R⟦Γ⟧} {C' : E → R⟦Γ⟧} (hg : ∀ a, g a ≠ 0) (hC : ∀ e, C e ≠ 0)
    (hg' : ∀ a, g' a ≠ 0) (hC' : ∀ e, C' e ≠ 0) (hgo : ∀ a, (g' a).order = (g a).order)
    (hCo : ∀ e, (C' e).order = (C e).order) (β : V → ℕ) :
    StronglySummable (atom α ends g C β) ↔ StronglySummable (atom α ends g' C' β) := by
  have hw : wickWeight g' C' = wickWeight g C :=
    AddMonoidHom.ext fun q => by simp only [wickWeight_apply, hgo, hCo]
  rw [stronglySummable_atom_iff α ends hg hC, stronglySummable_atom_iff α ends hg' hC', hw]

variable (g C)

/-- The rescaled couplings `uₐ = gₐ t^{αᵃ ⬝ p}` of `wick:eq:scaleddata`. -/
def scaleCoupling (p : V → Γ) : A → R⟦Γ⟧ :=
  fun a => g a * single (∑ i, α a i • p i) 1

/-- The rescaled covariances `w_ij = C_ij t^{-p_i-p_j}` of `wick:eq:scaleddata`. -/
def scaleCov (p : V → Γ) : E → R⟦Γ⟧ :=
  fun e => C e * single (-(p (ends e).1 + p (ends e).2)) 1

variable {g C}

/-- **Diagonal invariance** (`wick:cor:robustness`, second part). The diagonal monomial
transformation `wick:eq:scaleddata`, for an arbitrary `p ∈ Γ^V` (the rescaled entries need not
have positive valuation), does not change strong summability in any sector. -/
theorem stronglySummable_atom_scale_iff [CharZero R] [Module ℚ Γ] [Nontrivial Γ]
    (hg : ∀ a, g a ≠ 0) (hC : ∀ e, C e ≠ 0) (p : V → Γ) (β : V → ℕ) :
    StronglySummable (atom α ends g C β) ↔
      StronglySummable (atom α ends (scaleCoupling α g p) (scaleCov ends C p) β) := by
  have hg' : ∀ a, scaleCoupling α g p a ≠ 0 := fun a =>
    mul_ne_zero (hg a) (single_ne_zero one_ne_zero)
  have hC' : ∀ e, scaleCov ends C p e ≠ 0 := fun e =>
    mul_ne_zero (hC e) (single_ne_zero one_ne_zero)
  have hel : Sum.elim (scaleCoupling α g p) (scaleCov ends C p) =
      fun j => Sum.elim g C j * single (∑ i, wickMatrix α ends j i • p i) (1 : R) := by
    funext j
    rcases j with a | e
    · simp only [Sum.elim_inl, scaleCoupling, sum_wickMatrix_inl]
    · simp only [Sum.elim_inr, scaleCov, sum_wickMatrix_inr]
  have hw : ∀ q, wickWeight (scaleCoupling α g p) (scaleCov ends C p) q =
      wickWeight g C q + ∑ i, incidence α ends q i • p i := by
    intro q
    rw [wickWeight, hel, valWeight_mul_single (sumElim_ne_zero hg hC), sum_nsmul_sum_zsmul]
    rfl
  rw [stronglySummable_atom_iff α ends hg hC, stronglySummable_atom_iff α ends hg' hC']
  refine imp_congr Iff.rfl (forall₂_congr fun q hq => ?_)
  rw [hw, mem_sector_zero_iff.1 hq]
  simp

end Wick

/-! ### The source's matrix setting -/

section Matrix

variable {Γ R V A : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field R] [Fintype V] [LinearOrder V] [Fintype A]

/-- The edge set `E = {(i, j) : i ≤ j, C_ij ≠ 0}` of a covariance matrix `C`
(`wick:sec:wick`). -/
abbrev MatrixEdge (C : Matrix V V R⟦Γ⟧) : Type _ :=
  {e : V × V // e.1 ≤ e.2 ∧ C e.1 e.2 ≠ 0}

/-- The edge set of a covariance matrix is finite. The instance is `Fintype.ofFinite`, hence
noncomputable; `Fintype` is a subsingleton, so it agrees propositionally with any other
instance, such as `Subtype.fintype` under classical decidability. -/
noncomputable instance (C : Matrix V V R⟦Γ⟧) : Fintype (MatrixEdge C) :=
  Fintype.ofFinite _

/-- The covariance entry `C_ij` carried by an edge `(i, j) ∈ E`. -/
def matrixCov (C : Matrix V V R⟦Γ⟧) : MatrixEdge C → R⟦Γ⟧ :=
  fun e => C e.1.1 e.1.2

/-- **Exact diagramwise Hahn domain** (`wick:thm:main`) in the source's setting: a covariance
matrix `C` over `R((t^Γ))` (possibly singular, and only its entries `C_ij`, `i ≤ j`, are used,
so no symmetry assumption is needed), with edge set `E = {(i, j) : i ≤ j, C_ij ≠ 0}`. -/
theorem main_tfae_matrix [CharZero R] [Module ℚ Γ] [Nontrivial Γ] (α : A → V → ℕ)
    {g : A → R⟦Γ⟧} (hg : ∀ a, g a ≠ 0) (C : Matrix V V R⟦Γ⟧) :
    List.TFAE [StronglySummable (atom α Subtype.val g (matrixCov C) 0),
      ∀ q ∈ sector α (Subtype.val : MatrixEdge C → V × V) 0, q ≠ 0 →
        0 < wickWeight g (matrixCov C) q,
      ∀ h ∈ hilbertBasis (incidence α (Subtype.val : MatrixEdge C → V × V)),
        0 < wickWeight g (matrixCov C) h,
      ∃ p : V → Γ, (∀ a, 0 < (g a).order + ∑ i, α a i • p i) ∧
        ∀ i j, i ≤ j → C i j ≠ 0 → 0 < (C i j).order - p i - p j,
      ∀ β : V → ℕ, StronglySummable (atom α Subtype.val g (matrixCov C) β)] := by
  have key : (∃ p : V → Γ, (∀ a, 0 < (g a).order + ∑ i, α a i • p i) ∧
        ∀ e : MatrixEdge C, 0 < (matrixCov C e).order - p e.1.1 - p e.1.2) ↔
      ∃ p : V → Γ, (∀ a, 0 < (g a).order + ∑ i, α a i • p i) ∧
        ∀ i j, i ≤ j → C i j ≠ 0 → 0 < (C i j).order - p i - p j :=
    exists_congr fun p => and_congr Iff.rfl
      ⟨fun h i j hij hC => h ⟨(i, j), hij, hC⟩, fun h e => h _ _ e.2.1 e.2.2⟩
  rw [← key]
  exact main_tfae α Subtype.val hg fun e => e.2.2

/-- Reindexing `stronglySummable_atom_congr_order` along equal edge sets: for edge types given
as subtypes `{e // P e}` and `{e // P' e}` of `V × V` with `P = P'`, nonzero couplings and
covariance entries with the same valuations give the same strong summability in every sector. -/
theorem stronglySummable_atom_subtype_congr_order [CharZero R] [Module ℚ Γ] [Nontrivial Γ]
    (α : A → V → ℕ) {P P' : V × V → Prop} [i₁ : Fintype (Subtype P)]
    [i₂ : Fintype (Subtype P')] (hP : P = P') {g g' : A → R⟦Γ⟧} {c : Subtype P → R⟦Γ⟧}
    {c' : Subtype P' → R⟦Γ⟧} (hg : ∀ a, g a ≠ 0) (hc : ∀ e, c e ≠ 0) (hg' : ∀ a, g' a ≠ 0)
    (hc' : ∀ e, c' e ≠ 0) (hgo : ∀ a, (g' a).order = (g a).order)
    (hco : ∀ e (he : P e) (he' : P' e), (c' ⟨e, he'⟩).order = (c ⟨e, he⟩).order)
    (β : V → ℕ) :
    StronglySummable (atom α Subtype.val g c β) ↔
      StronglySummable (atom α Subtype.val g' c' β) := by
  subst hP
  obtain rfl := Subsingleton.elim i₁ i₂
  exact stronglySummable_atom_congr_order α Subtype.val hg hc hg' hc' hgo
    (fun e => hco e.1 e.2 e.2) β

/-- **Valuation robustness** (`wick:cor:robustness`, first part) in the source's matrix setting
of `main_tfae_matrix`. Replace the couplings `g` by nonzero couplings `g'` with the same
valuations, and the covariance matrix `C` by a matrix `C'` with the same nonzero pattern on the
entries `i ≤ j` and the same valuations at the nonzero ones. Strong summability of the Wick atom
family in the sector `Q_β` does not change, for every `β`. -/
theorem stronglySummable_atom_matrix_congr_order [CharZero R] [Module ℚ Γ] [Nontrivial Γ]
    (α : A → V → ℕ) {g g' : A → R⟦Γ⟧} (hg : ∀ a, g a ≠ 0) (hg' : ∀ a, g' a ≠ 0)
    (hgo : ∀ a, (g' a).order = (g a).order) {C C' : Matrix V V R⟦Γ⟧}
    (hpat : ∀ i j, i ≤ j → (C i j ≠ 0 ↔ C' i j ≠ 0))
    (hCo : ∀ i j, i ≤ j → C i j ≠ 0 → (C' i j).order = (C i j).order) (β : V → ℕ) :
    StronglySummable (atom α Subtype.val g (matrixCov C) β) ↔
      StronglySummable (atom α Subtype.val g' (matrixCov C') β) := by
  refine stronglySummable_atom_subtype_congr_order α ?_ hg (fun e => e.2.2) hg'
    (fun e => e.2.2) hgo (fun e he _ => hCo e.1 e.2 he.1 he.2) β
  funext e
  exact propext (and_congr_right fun h => hpat e.1 e.2 h)

end Matrix

end

end Surreal.WickDomain
