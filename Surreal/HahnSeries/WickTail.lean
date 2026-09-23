import Surreal.HahnSeries.SignCoherentSums
import Surreal.HahnSeries.ExponentialLogarithm

/-!
# Finite substitution, truncated Wick sums and the vacuum logarithm

This file proves `wick:cor:substitution` and `wick:prop:tail` (with `wick:eq:tail`) of
`docs/surcomplex/wick-summability-certificates/article.tex`, together with the first sentence of
`wick:prop:connectedlog` (`Z = 1 + z` with `z = 0` or `v(z) > 0`, and `log Z` of `wick:eq:log`
is a well-defined strong sum) and the remark of `wick:sec:observables` that `Z` is invertible
with inverse the strongly summable geometric series `∑ₙ (-z)ⁿ`.

**Setting.** As in `Surreal.WickDomain`: couplings `gₐ` and edge covariances `Cₑ` are nonzero
Hahn series over a field `R` (the source's `K = ℂ((t^Γ))`), the atoms `T_β(m, k)` of
`wick:eq:atom` are `Surreal.WickDomain.atom`, the sector `Q_β` is `Surreal.WickDomain.sector`,
and strong summability is `Surreal.WickDomain.StronglySummable` (`wick:def:strong`).
The diagramwise Wick sum `𝒵_β` is `wickSum` (the strong sum of the atom family when it is
strongly summable, `wickSum_eq_hsum`, `coeff_wickSum`; for an empty sector it is `0`, as in the
source, `wickSum_eq_zero_of_sector_eq_empty`), `Z = 𝒵₀`, and the truncation `𝒵_{β,≤N}` is
`truncSum`, the finite sum of the atoms over `truncFinset` (the count vectors with `|m| ≤ N`,
finite by `finite_truncSet`). It is the sum of the first `N + 1` order blocks of
`wick:prop:signcoherent` (`truncSum_eq_sum_orderBlock`).

**Main results.**
* `stronglySummable_substitution`, `exists_evaluation`, and their specializations
  `stronglySummable_substitution_complex` and `exists_evaluation_complex` to `R = ℂ`:
  `wick:cor:substitution`. For finitely many inputs
  `uⱼ` of positive valuation and arbitrary coefficients `aₙ` (no growth bound), the family
  `(aₙ u^n)_{n ∈ ℕ^r}` is strongly summable, and `Surreal.HahnSeries.mvEvaluate` is an
  `R`-algebra homomorphism `R[[U]] → R((t^Γ))` with `Uⱼ ↦ uⱼ` whose values are these strong
  sums. This holds over any commutative ring and any ordered cancellative exponent monoid.
* `sum_nsmul_add_le_wickWeight` and `le_orderTop_atom`: for any `p` and `η` with
  `η ≤ λₐ + αᵃ ⬝ p = v(uₐ)` and `η ≤ c_ij - p_i - p_j = v(w_ij)`, every atom of `Q_β` has
  valuation at least `p ⬝ β + (|m| + |k|) η` (the scaled form `wick:eq:scaledatom`).
* `le_orderTop_wickSum_sub_truncSum`: **`wick:prop:tail`**,
  `v(𝒵_β - 𝒵_{β,≤N}) ≥ p ⬝ β + (N + 1) η` for every `β` and `N` (a zero tail has
  `orderTop = ⊤`). `le_orderTop_wickSum_sub_truncSum_scaled` states the hypothesis literally
  on the scaled entries `uₐ = gₐ t^{αᵃ⬝p}`, `w_e = C_e t^{-p_i-p_j}` of `wick:eq:scaleddata`,
  and `le_orderTop_wickSum_sub_truncSum_matrix` is the source's covariance-matrix setting.
* `orderTop_wickSum_zero_sub_one_pos_of_stronglySummable` (condition (i) of `wick:thm:main`,
  characteristic zero), `orderTop_wickSum_zero_sub_one_pos_of_forall_pos` (condition (ii)) and
  `orderTop_wickSum_zero_sub_one_pos_of_hilbertBasis` (condition (iii)), the latter two for a
  nonzero divisible `Γ` and characteristic zero, and `orderTop_wickSum_zero_sub_one_pos_of_balance`
  (condition (iv), no further assumption): `0 < v(Z - 1)`, the first sentence of
  `wick:prop:connectedlog`. Condition (v) gives (i) at `β = 0`.
* `isUnit_wickSum_zero`, `wickSum_zero_ne_zero` and `exists_inv_wickSum_zero`: `Z` is a unit, so
  `Z ≠ 0`, and `Z⁻¹` is the strong sum of the geometric family `((-z)ⁿ)ₙ`
  (`wick:sec:observables`).
* `vacuumLog`, `exists_vacuumLog_family` and `infExp_vacuumLog`: `log Z` of `wick:eq:log` is the
  strong sum of `((-1)^{n+1} zⁿ / n)_{n ≥ 1}`, and its exponential is `Z`.

**Generality.** `wick:prop:tail`, the summability `stronglySummable_atom_of_balance` and the
balance form of the vacuum clause need neither characteristic zero nor divisibility of `Γ`: a
balancing vector is part of their hypotheses, so `wick:thm:main` is not invoked. The
summability form of the vacuum clause uses characteristic zero (for `wick:eq:leading`); the
forms under (ii) and (iii) also use a nonzero divisible `Γ`, through `wick:thm:main`
(`Surreal.WickDomain.stronglySummable_atom_iff` and `Surreal.WickDomain.main_tfae`); and the
logarithm uses characteristic zero for the coefficients `1 / n`.

**Pending.** The identification in `wick:prop:connectedlog` of `log Z` with the strongly summed
connected vacuum Wick family, which needs a model of pairings and connected diagrams, the
counting lemma `wick:lem:wickcount` and the exponential formula; none of these is formalized.
`wick:prop:embedding` is not restated here; its content is `Surreal.Surcomplex.hahnEmbedding`
with `hahnEmbedding_injective`, `hahnEmbedding_single` and `strongSum_hahnEmbedding`.
-/

namespace Surreal.WickTail

open _root_.HahnSeries Surreal.HahnSeries Surreal.WickDomain Surreal.SignCoherent Surreal.Wick

noncomputable section

/-! ### Finite infinitesimal substitution -/

section Substitution

variable {Γ R σ : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing R] [Fintype σ]

/-- **Finite infinitesimal substitution** (`wick:cor:substitution`, summability). If
`u₁, …, u_r` have positive valuation, then for every family of coefficients `(aₙ)_{n ∈ ℕ^r}`,
with no bound on their size, the family `(aₙ u₁^{n₁} ⋯ u_r^{n_r})` is strongly summable. -/
theorem stronglySummable_substitution (u : σ → R⟦Γ⟧) (hu : ∀ j, 0 < (u j).orderTop)
    (a : (σ → ℕ) → R) : StronglySummable fun n : σ → ℕ => a n • ∏ j, u j ^ n j := by
  refine ⟨SummableFamily.smulFamily a
    (SummableFamily.Equiv Finsupp.equivFunOnFinite (mvPowerFamily u hu)), fun n => ?_⟩
  rw [SummableFamily.smulFamily_toFun, SummableFamily.Equiv_toFun, mvPowerFamily_apply]
  rfl

/-- **Finite infinitesimal substitution** (`wick:cor:substitution`, evaluation homomorphism).
For inputs of positive valuation there is an `R`-algebra homomorphism `R[[U]] → R((t^Γ))`
taking `Uⱼ` to `uⱼ`, whose value at `F` is the strong sum of `(coeff_n F • u^n)ₙ`. Being an
algebra homomorphism, it respects addition and multiplication (the Cauchy product). -/
theorem exists_evaluation (u : σ → R⟦Γ⟧) (hu : ∀ j, 0 < (u j).orderTop) :
    ∃ φ : MvPowerSeries σ R →ₐ[R] R⟦Γ⟧, (∀ j, φ (MvPowerSeries.X j) = u j) ∧
      ∀ F, ∃ s : SummableFamily Γ R (σ →₀ ℕ),
        (∀ n, s n = MvPowerSeries.coeff n F • ∏ j, u j ^ n j) ∧ φ F = s.hsum :=
  ⟨mvEvaluate u hu, mvEvaluate_X u hu, fun F =>
    ⟨mvEvaluationFamily u hu F, mvEvaluationFamily_apply u hu F, mvEvaluate_apply u hu F⟩⟩

end Substitution

/-- `wick:cor:substitution` in the source's form: `K = ℂ((t^Γ))`, inputs `u₁, …, u_r` of
positive valuation and an arbitrary complex family `(aₙ)_{n ∈ ℕ^r}`. -/
theorem stronglySummable_substitution_complex {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] {r : ℕ} (u : Fin r → ℂ⟦Γ⟧) (hu : ∀ j, 0 < (u j).orderTop)
    (a : (Fin r → ℕ) → ℂ) : StronglySummable fun n : Fin r → ℕ => a n • ∏ j, u j ^ n j :=
  stronglySummable_substitution u hu a

/-- The evaluation homomorphism of `wick:cor:substitution` in the source's form: for inputs
`u₁, …, u_r ∈ ℂ((t^Γ))` of positive valuation there is a `ℂ`-algebra homomorphism
`ℂ[[U₁, …, U_r]] → ℂ((t^Γ))` with `Uⱼ ↦ uⱼ`, whose value at `F` is the strong sum of
`(coeff_n F • u^n)ₙ` (`exists_evaluation` with `R = ℂ` and `σ = Fin r`). -/
theorem exists_evaluation_complex {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] {r : ℕ} (u : Fin r → ℂ⟦Γ⟧) (hu : ∀ j, 0 < (u j).orderTop) :
    ∃ φ : MvPowerSeries (Fin r) ℂ →ₐ[ℂ] ℂ⟦Γ⟧, (∀ j, φ (MvPowerSeries.X j) = u j) ∧
      ∀ F, ∃ s : SummableFamily Γ ℂ (Fin r →₀ ℕ),
        (∀ n, s n = MvPowerSeries.coeff n F • ∏ j, u j ^ n j) ∧ φ F = s.hsum :=
  exists_evaluation u hu

/-- A Hahn series whose coefficients vanish at all exponents `≤ a` has `orderTop > a`. -/
theorem lt_orderTop_of_forall_coeff_eq_zero {Γ R : Type*} [Zero Γ] [LinearOrder Γ] [Zero R]
    {x : R⟦Γ⟧} {a : Γ} (h : ∀ γ ≤ a, x.coeff γ = 0) : (a : WithTop Γ) < x.orderTop := by
  by_cases hx : x = 0
  · rw [hx, orderTop_zero]
    exact WithTop.coe_lt_top a
  · rw [← order_eq_orderTop_of_ne_zero hx, WithTop.coe_lt_coe]
    by_contra hle
    exact hx (coeff_order_eq_zero.1 (h _ (not_lt.1 hle)))

/-! ### Wick sums and their truncations -/

section Wick

variable {Γ R V A E : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field R] [Fintype V] [DecidableEq V] [Fintype A] [Fintype E]
  (α : A → V → ℕ) (ends : E → V × V) (g : A → R⟦Γ⟧) (C : E → R⟦Γ⟧)

/-- The diagramwise Wick sum `𝒵_β` (definition after `wick:eq:atom`): the strong sum of the
atom family of `Q_β` when that family is strongly summable. It is `0` otherwise; for an empty
sector the family is strongly summable with sum `0`, the source's convention `𝒵_β = 0`
(`wickSum_eq_zero_of_sector_eq_empty`). -/
def wickSum (β : V → ℕ) : R⟦Γ⟧ := by
  classical
  exact if h : StronglySummable (atom α ends g C β) then (Classical.choose h).hsum else 0

variable {α ends g C}

/-- The Wick sum is the sum of every summable family realizing the atom family. -/
theorem wickSum_eq_hsum {β : V → ℕ} (s : SummableFamily Γ R (sector α ends β))
    (hs : ∀ q, s q = atom α ends g C β q) : wickSum α ends g C β = s.hsum := by
  have h : StronglySummable (atom α ends g C β) := ⟨s, hs⟩
  unfold wickSum
  rw [dif_pos h]
  ext γ
  rw [SummableFamily.coeff_hsum, SummableFamily.coeff_hsum]
  exact finsum_congr fun q => by rw [Classical.choose_spec h q, hs q]

/-- The coefficients of a Wick sum are the finite sums of the atom coefficients. -/
theorem coeff_wickSum {β : V → ℕ} (h : StronglySummable (atom α ends g C β)) (γ : Γ) :
    (wickSum α ends g C β).coeff γ = ∑ᶠ q, (atom α ends g C β q).coeff γ := by
  obtain ⟨s, hs⟩ := h
  rw [wickSum_eq_hsum s hs, SummableFamily.coeff_hsum]
  exact finsum_congr fun q => by rw [hs q]

/-- The source's convention `𝒵_β = 0` for an empty sector `Q_β = ∅`. -/
theorem wickSum_eq_zero_of_sector_eq_empty {β : V → ℕ} (h : sector α ends β = ∅) :
    wickSum α ends g C β = 0 :=
  (wickSum_eq_hsum 0 fun q => (Set.eq_empty_iff_forall_notMem.1 h q.1 q.2).elim).trans
    SummableFamily.hsum_zero

variable (α ends g C)

omit [Fintype V] in
/-- Only finitely many count vectors `(m, k) ∈ Q_β` have `|m| ≤ N`. -/
theorem finite_truncSet (β : V → ℕ) (N : ℕ) :
    {q : sector α ends β | interactionOrder q.1 ≤ N}.Finite :=
  (Set.finite_Iic N).preimage' (f := fun q : sector α ends β => interactionOrder q.1)
    fun n _ => finite_orderFiber α ends β n

/-- The finite index set `{(m, k) ∈ Q_β : |m| ≤ N}` of `𝒵_{β,≤N}`. -/
def truncFinset (β : V → ℕ) (N : ℕ) : Finset (sector α ends β) :=
  (finite_truncSet α ends β N).toFinset

omit [Fintype V] in
@[simp]
theorem mem_truncFinset {β : V → ℕ} {N : ℕ} {q : sector α ends β} :
    q ∈ truncFinset α ends β N ↔ interactionOrder q.1 ≤ N := by
  rw [truncFinset, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

/-- The truncated Wick sum `𝒵_{β,≤N}` of `wick:sec:observables`: the finite sum of the atoms
`T_β(m, k)` with `|m| ≤ N`. -/
def truncSum (β : V → ℕ) (N : ℕ) : R⟦Γ⟧ :=
  ∑ q ∈ truncFinset α ends β N, atom α ends g C β q

/-- The truncation `𝒵_{β,≤N}` is the sum of the order blocks `n = 0, …, N` of
`wick:prop:signcoherent`. -/
theorem truncSum_eq_sum_orderBlock (β : V → ℕ) (N : ℕ) :
    truncSum α ends g C β N = ∑ n ∈ Finset.range (N + 1), orderBlock α ends g C β n := by
  classical
  have e : truncFinset α ends β N = (Finset.range (N + 1)).biUnion
      fun n => (finite_orderFiber α ends β n).toFinset := by
    ext q
    simp
  rw [truncSum, e, Finset.sum_biUnion]
  · rfl
  · intro m _ n _ hmn
    exact Finset.disjoint_left.2 fun q hm hn =>
      hmn (((mem_orderFinset α ends).1 hm).symm.trans ((mem_orderFinset α ends).1 hn))

/-! ### Valuation bounds for the atoms -/

variable {α ends g C}

/-- The balancing computation behind `wick:eq:scaledatom`: if `η` is at most every
`λₐ + αᵃ ⬝ p` and every `c_ij - p_i - p_j`, then every `q = (m, k) ∈ Q_β` has weight
`L(m, k) ≥ p ⬝ β + (|m| + |k|) η`. -/
theorem sum_nsmul_add_le_wickWeight {p : V → Γ} {η : Γ}
    (hu : ∀ a, η ≤ (g a).order + ∑ i, α a i • p i)
    (hw : ∀ e, η ≤ (C e).order - p (ends e).1 - p (ends e).2) {β : V → ℕ}
    {q : A ⊕ E → ℕ} (hq : q ∈ sector α ends β) :
    ∑ i, β i • p i + (∑ j, q j) • η ≤ wickWeight g C q := by
  have hwj : ∀ j, η ≤ (Sum.elim g C j).order + ∑ i, wickMatrix α ends j i • p i := by
    rintro (a | e)
    · rw [Sum.elim_inl, sum_wickMatrix_inl]
      exact hu a
    · rw [Sum.elim_inr, sum_wickMatrix_inr, ← sub_eq_add_neg, ← sub_sub]
      exact hw e
  have hq' : countWeight (wickMatrix α ends) q = fun i => -(β i : ℤ) := hq
  have key : ∑ j, q j • ((Sum.elim g C j).order + ∑ i, wickMatrix α ends j i • p i) =
      wickWeight g C q - ∑ i, β i • p i := by
    rw [wickWeight, valWeight_apply]
    simp only [smul_add, Finset.sum_add_distrib]
    rw [sum_nsmul_sum_zsmul, hq']
    simp only [neg_smul, natCast_zsmul, Finset.sum_neg_distrib, ← sub_eq_add_neg]
  have h1 : (∑ j, q j) • η ≤ wickWeight g C q - ∑ i, β i • p i := by
    rw [← key, Finset.sum_smul]
    exact Finset.sum_le_sum fun j _ => nsmul_le_nsmul_right (hwj j) (q j)
  rw [add_comm]
  exact le_sub_iff_add_le.1 h1

/-- `wick:eq:leading` as a lower bound, with no characteristic assumption: the valuation of
the atom `T_β(q)` is at least `L(q)`. -/
theorem wickWeight_le_orderTop_atom (hg : ∀ a, g a ≠ 0) (hC : ∀ e, C e ≠ 0) (β : V → ℕ)
    (q : sector α ends β) :
    (wickWeight g C q.1 : WithTop Γ) ≤ (atom α ends g C β q).orderTop := by
  rw [atom_eq]
  refine le_trans ?_ (not_lt.1 (orderTop_smul_not_lt _ _))
  rw [← order_eq_orderTop_of_ne_zero (countMonomial_ne_zero (sumElim_ne_zero hg hC) _),
    order_countMonomial (sumElim_ne_zero hg hC)]
  exact le_rfl

/-- The proof of `wick:prop:tail`, first step: in the scaled form `wick:eq:scaledatom`, every
atom `T_β(m, k)` has valuation at least `p ⬝ β + (|m| + |k|) η`. -/
theorem le_orderTop_atom (hg : ∀ a, g a ≠ 0) (hC : ∀ e, C e ≠ 0) {p : V → Γ} {η : Γ}
    (hu : ∀ a, η ≤ (g a).order + ∑ i, α a i • p i)
    (hw : ∀ e, η ≤ (C e).order - p (ends e).1 - p (ends e).2) {β : V → ℕ}
    (q : sector α ends β) :
    ((∑ i, β i • p i + (∑ j, q.1 j) • η : Γ) : WithTop Γ) ≤ (atom α ends g C β q).orderTop :=
  (WithTop.coe_le_coe.2 (sum_nsmul_add_le_wickWeight hu hw q.2)).trans
    (wickWeight_le_orderTop_atom hg hC β q)

/-- `wick:thm:main`, (iv) ⟹ (v), with no divisibility or characteristic assumption: a
balancing vector makes every sector family strongly summable. -/
theorem stronglySummable_atom_of_balance (hg : ∀ a, g a ≠ 0) (hC : ∀ e, C e ≠ 0)
    {p : V → Γ} (hu : ∀ a, 0 < (g a).order + ∑ i, α a i • p i)
    (hw : ∀ e, 0 < (C e).order - p (ends e).1 - p (ends e).2) (β : V → ℕ) :
    StronglySummable (atom α ends g C β) := by
  have e : atom α ends g C β =
      fun q => ((atomCoeff α ends β q.1 : ℚ) : R) • countMonomial (Sum.elim g C) q.1 :=
    funext (atom_eq α ends g C β)
  rw [e]
  exact stronglySummable_of_balance (wickMatrix α ends) (sumElim_ne_zero hg hC)
    ((balance_iff α ends g C p).2 ⟨hu, hw⟩) (fun i => -(β i : ℤ))
    fun q => ((atomCoeff α ends β q.1 : ℚ) : R)

/-! ### The valuation error estimate -/

/-- **A valuation error estimate** (`wick:prop:tail`, `wick:eq:tail`). Let `η > 0` be at most
the valuations `λₐ + αᵃ ⬝ p` of the scaled couplings `uₐ` and `c_ij - p_i - p_j` of the scaled
covariances `w_ij` (so `p` is a balancing vector and every sector family is strongly summable).
Then for every `β` and `N`, `v(𝒵_β - 𝒵_{β,≤N}) ≥ p ⬝ β + (N + 1) η`, where a zero tail has
valuation `⊤`. -/
theorem le_orderTop_wickSum_sub_truncSum (hg : ∀ a, g a ≠ 0) (hC : ∀ e, C e ≠ 0)
    {p : V → Γ} {η : Γ} (hη : 0 < η) (hu : ∀ a, η ≤ (g a).order + ∑ i, α a i • p i)
    (hw : ∀ e, η ≤ (C e).order - p (ends e).1 - p (ends e).2) (β : V → ℕ) (N : ℕ) :
    ((∑ i, β i • p i + (N + 1) • η : Γ) : WithTop Γ) ≤
      (wickSum α ends g C β - truncSum α ends g C β N).orderTop := by
  have hS := stronglySummable_atom_of_balance hg hC (fun a => hη.trans_le (hu a))
    (fun e => hη.trans_le (hw e)) β
  rw [le_orderTop_iff_forall]
  intro γ hγ
  rw [coeff_sub, coeff_wickSum hS, truncSum, coeff_sum, sub_eq_zero]
  apply finsum_eq_sum_of_support_subset
  intro q hq
  rw [Function.mem_support] at hq
  rw [Finset.mem_coe, mem_truncFinset]
  by_contra hN
  apply hq
  apply coeff_eq_zero_of_lt_orderTop
  refine lt_of_lt_of_le hγ ((WithTop.coe_le_coe.2 ?_).trans (le_orderTop_atom hg hC hu hw q))
  refine add_le_add le_rfl (nsmul_le_nsmul_left hη.le ?_)
  have h1 : interactionOrder q.1 ≤ ∑ j, q.1 j := by
    rw [Fintype.sum_sum_type]
    exact Nat.le_add_right _ _
  omega

/-- `wick:prop:tail` with its hypothesis stated literally on the scaled entries
`uₐ = gₐ t^{αᵃ⬝p}` and `w_e = C_e t^{-p_i-p_j}` of `wick:eq:scaleddata`: if `0 < η ≤ v(uₐ)` and
`η ≤ v(w_e)` for all `a` and `e`, then `v(𝒵_β - 𝒵_{β,≤N}) ≥ p ⬝ β + (N + 1) η`. -/
theorem le_orderTop_wickSum_sub_truncSum_scaled (hg : ∀ a, g a ≠ 0) (hC : ∀ e, C e ≠ 0)
    {p : V → Γ} {η : Γ} (hη : 0 < η)
    (hu : ∀ a, (η : WithTop Γ) ≤ (scaleCoupling α g p a).orderTop)
    (hw : ∀ e, (η : WithTop Γ) ≤ (scaleCov ends C p e).orderTop) (β : V → ℕ) (N : ℕ) :
    ((∑ i, β i • p i + (N + 1) • η : Γ) : WithTop Γ) ≤
      (wickSum α ends g C β - truncSum α ends g C β N).orderTop := by
  refine le_orderTop_wickSum_sub_truncSum hg hC hη (fun a => ?_) (fun e => ?_) β N
  · have h := hu a
    rw [scaleCoupling, orderTop_mul, orderTop_single one_ne_zero,
      ← order_eq_orderTop_of_ne_zero (hg a), ← WithTop.coe_add, WithTop.coe_le_coe] at h
    exact h
  · have h := hw e
    rw [scaleCov, orderTop_mul, orderTop_single one_ne_zero,
      ← order_eq_orderTop_of_ne_zero (hC e), ← WithTop.coe_add, WithTop.coe_le_coe,
      ← sub_eq_add_neg, ← sub_sub] at h
    exact h

/-! ### The vacuum sum `Z = 1 + z` -/

omit [Fintype V] in
variable (α ends) in
/-- The empty vacuum diagram `(m, k) = (0, 0)` lies in `S = Q_0`. -/
theorem zero_mem_sector : (0 : A ⊕ E → ℕ) ∈ sector α ends 0 :=
  mem_sector_zero_iff.2 (map_zero _)

variable (α ends g C) in
/-- The atom of the empty vacuum diagram is `1`. -/
theorem atom_zero_eq_one : atom α ends g C 0 ⟨0, zero_mem_sector α ends⟩ = 1 := by
  simp [atom, atomCoeff, wickW, vertexCount]

/-- The first sentence of `wick:prop:connectedlog`, core form: if the vacuum family is strongly
summable and `L > 0` on `S ∖ {0}`, then `Z = 1 + z` with `z = 0` or `v(z) > 0`. -/
theorem orderTop_wickSum_zero_sub_one_pos (hg : ∀ a, g a ≠ 0) (hC : ∀ e, C e ≠ 0)
    (hS : StronglySummable (atom α ends g C 0))
    (hpos : ∀ q ∈ sector α ends 0, q ≠ 0 → 0 < wickWeight g C q) :
    0 < (wickSum α ends g C 0 - 1).orderTop := by
  rw [← WithTop.coe_zero]
  apply lt_orderTop_of_forall_coeff_eq_zero
  intro γ hγ
  rw [coeff_sub, coeff_wickSum hS, finsum_eq_single _ ⟨0, zero_mem_sector α ends⟩,
    atom_zero_eq_one, sub_self]
  intro q hq
  apply coeff_eq_zero_of_lt_orderTop
  have hq0 : q.1 ≠ 0 := fun h => hq (Subtype.ext h)
  exact lt_of_lt_of_le (WithTop.coe_lt_coe.2 (hγ.trans_lt (hpos q.1 q.2 hq0)))
    (wickWeight_le_orderTop_atom hg hC 0 q)

/-- The first sentence of `wick:prop:connectedlog` under condition (i) of `wick:thm:main`: if
the vacuum Wick family is strongly summable (characteristic zero), then `z = Z - 1` is `0` or has
positive valuation. -/
theorem orderTop_wickSum_zero_sub_one_pos_of_stronglySummable [CharZero R]
    (hg : ∀ a, g a ≠ 0) (hC : ∀ e, C e ≠ 0) (hS : StronglySummable (atom α ends g C 0)) :
    0 < (wickSum α ends g C 0 - 1).orderTop :=
  orderTop_wickSum_zero_sub_one_pos hg hC hS fun q hq hq0 =>
    forall_pos_of_stronglySummable (incidence α ends) (wickWeight g C) (atom α ends g C 0)
      (atom_ne_zero α ends hg hC 0) (order_atom α ends hg hC 0) (zero_mem_sector α ends) hS q
      (mem_sector_zero_iff.1 hq) hq0

/-- The first sentence of `wick:prop:connectedlog` under condition (iv) of `wick:thm:main` (a
balancing vector), with no characteristic or divisibility assumption: `z = Z - 1` is `0` or has
positive valuation. -/
theorem orderTop_wickSum_zero_sub_one_pos_of_balance (hg : ∀ a, g a ≠ 0) (hC : ∀ e, C e ≠ 0)
    {p : V → Γ} (hu : ∀ a, 0 < (g a).order + ∑ i, α a i • p i)
    (hw : ∀ e, 0 < (C e).order - p (ends e).1 - p (ends e).2) :
    0 < (wickSum α ends g C 0 - 1).orderTop :=
  orderTop_wickSum_zero_sub_one_pos hg hC (stronglySummable_atom_of_balance hg hC hu hw 0)
    fun _ hq hq0 => forall_pos_of_balance (wickMatrix α ends) (fun j => (Sum.elim g C j).order)
      ((balance_iff α ends g C p).2 ⟨hu, hw⟩) (mem_sector_zero_iff.1 hq) hq0

/-- The first sentence of `wick:prop:connectedlog` under condition (ii) of `wick:thm:main`
(`L(q) > 0` for every `q ∈ S ∖ {0}`), for a nonzero divisible `Γ` and characteristic zero:
`z = Z - 1` is `0` or has positive valuation. -/
theorem orderTop_wickSum_zero_sub_one_pos_of_forall_pos [CharZero R] [Module ℚ Γ]
    [Nontrivial Γ] (hg : ∀ a, g a ≠ 0) (hC : ∀ e, C e ≠ 0)
    (hpos : ∀ q ∈ sector α ends 0, q ≠ 0 → 0 < wickWeight g C q) :
    0 < (wickSum α ends g C 0 - 1).orderTop :=
  orderTop_wickSum_zero_sub_one_pos hg hC
    ((stronglySummable_atom_iff α ends hg hC 0).2 fun _ => hpos) hpos

/-- The first sentence of `wick:prop:connectedlog` under condition (iii) of `wick:thm:main`
(`L(h) > 0` on the Hilbert basis of `S`), for a nonzero divisible `Γ` and characteristic zero:
`z = Z - 1` is `0` or has positive valuation. -/
theorem orderTop_wickSum_zero_sub_one_pos_of_hilbertBasis [CharZero R] [Module ℚ Γ]
    [Nontrivial Γ] (hg : ∀ a, g a ≠ 0) (hC : ∀ e, C e ≠ 0)
    (hpos : ∀ h ∈ hilbertBasis (incidence α ends), 0 < wickWeight g C h) :
    0 < (wickSum α ends g C 0 - 1).orderTop :=
  orderTop_wickSum_zero_sub_one_pos_of_stronglySummable hg hC
    (((main_tfae α ends hg hC).out 0 2).2 hpos)

/-- `Z` is a unit on the diagramwise admissible domain (`wick:sec:observables`). -/
theorem isUnit_wickSum_zero (h : 0 < (wickSum α ends g C 0 - 1).orderTop) :
    IsUnit (wickSum α ends g C 0) :=
  isUnit_of_orderTop_pos h

/-- `Z` is never zero on the diagramwise admissible domain (`wick:sec:observables`). -/
theorem wickSum_zero_ne_zero (h : 0 < (wickSum α ends g C 0 - 1).orderTop) :
    wickSum α ends g C 0 ≠ 0 :=
  (isUnit_wickSum_zero h).ne_zero

/-- `wick:sec:observables`: the inverse of `Z = 1 + z` is the strong sum of the geometric
family `((-z)ⁿ)_{n ≥ 0}`. (That `Z ≠ 0` follows from `Z * s.hsum = 1`; it is stated as
`wickSum_zero_ne_zero`.) -/
theorem exists_inv_wickSum_zero (h : 0 < (wickSum α ends g C 0 - 1).orderTop) :
    ∃ s : SummableFamily Γ R ℕ, (∀ n, s n = (-(wickSum α ends g C 0 - 1)) ^ n) ∧
      wickSum α ends g C 0 * s.hsum = 1 ∧ (wickSum α ends g C 0)⁻¹ = s.hsum := by
  have hx : 0 < (-(wickSum α ends g C 0 - 1)).orderTop := by
    rw [orderTop_neg]
    exact h
  have hmul : wickSum α ends g C 0 *
      (SummableFamily.powers (-(wickSum α ends g C 0 - 1))).hsum = 1 := by
    have := SummableFamily.one_sub_self_mul_hsum_powers hx
    rwa [sub_neg_eq_add, add_sub_cancel] at this
  exact ⟨SummableFamily.powers _, SummableFamily.powers_of_orderTop_pos hx, hmul,
    inv_eq_of_mul_eq_one_right hmul⟩

variable [CharZero R]

variable (α ends g C) in
/-- The vacuum logarithm `log Z = ∑_{n ≥ 1} (-1)^{n+1} zⁿ / n` of `wick:eq:log`, for
`z = Z - 1` of positive valuation. -/
def vacuumLog (h : 0 < (wickSum α ends g C 0 - 1).orderTop) : R⟦Γ⟧ :=
  infLog _ h

/-- `wick:prop:connectedlog`, `wick:eq:log`: `log Z` is the strong sum of the family
`((-1)^{n+1} zⁿ / n)_{n ≥ 1}` (with a zero term at `n = 0`). -/
theorem exists_vacuumLog_family (h : 0 < (wickSum α ends g C 0 - 1).orderTop) :
    ∃ s : SummableFamily Γ R ℕ,
      (∀ n, s n = single 0 (if n = 0 then 0 else algebraMap ℚ R ((-1 : ℚ) ^ (n + 1) / n)) *
        (wickSum α ends g C 0 - 1) ^ n) ∧ vacuumLog α ends g C h = s.hsum :=
  ⟨infLogFamily _ h, infLogFamily_apply _ h, rfl⟩

/-- The vacuum logarithm is infinitesimal and exponentiates back to `Z`. -/
theorem infExp_vacuumLog (h : 0 < (wickSum α ends g C 0 - 1).orderTop) :
    ∃ hl : 0 < (vacuumLog α ends g C h).orderTop, infExp _ hl = wickSum α ends g C 0 := by
  exact ⟨infLog_orderTop_pos _ h, (infExp_infLog _ h).trans (add_sub_cancel _ _)⟩

end Wick

/-! ### The source's covariance-matrix setting -/

section Matrix

variable {Γ R V A : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field R] [Fintype V] [LinearOrder V] [Fintype A]

/-- **A valuation error estimate** (`wick:prop:tail`) in the source's setting: a covariance
matrix `C` with edge set `E = {(i, j) : i ≤ j, C_ij ≠ 0}` and nonzero couplings `gₐ`. If
`0 < η ≤ λₐ + αᵃ ⬝ p` for every `a` and `η ≤ c_ij - p_i - p_j` for every edge, then
`v(𝒵_β - 𝒵_{β,≤N}) ≥ p ⬝ β + (N + 1) η`. -/
theorem le_orderTop_wickSum_sub_truncSum_matrix (α : A → V → ℕ) {g : A → R⟦Γ⟧}
    (hg : ∀ a, g a ≠ 0) (C : Matrix V V R⟦Γ⟧) {p : V → Γ} {η : Γ} (hη : 0 < η)
    (hu : ∀ a, η ≤ (g a).order + ∑ i, α a i • p i)
    (hw : ∀ i j, i ≤ j → C i j ≠ 0 → η ≤ (C i j).order - p i - p j) (β : V → ℕ) (N : ℕ) :
    ((∑ i, β i • p i + (N + 1) • η : Γ) : WithTop Γ) ≤
      (wickSum α Subtype.val g (matrixCov C) β -
        truncSum α Subtype.val g (matrixCov C) β N).orderTop :=
  le_orderTop_wickSum_sub_truncSum hg (fun e => e.2.2) hη hu
    (fun e => hw e.1.1 e.1.2 e.2.1 e.2.2) β N

end Matrix

end

end Surreal.WickTail
