import Mathlib.Data.Nat.Nth
import Mathlib.Order.PartialSups
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.SetTheory.Cardinal.Cofinality.Basic
import Mathlib.Tactic.TFAE
import Surreal.HahnSeries.PartialThetaDomain
import Surreal.HahnSeries.TorsionCovariance

/-!
# The all-scale coefficient criterion and the countable-cofinality dichotomy

This file formalizes `hol:cf:prop:criterion`, `hol:cf:lem:min` and `hol:cf:cor:cofinality` of
`docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/article.tex`.

Strong summability, the strong domain and strong entireness (`hol:def:entire`) are those of
`Surreal.Holonomic` in `EscapeChain.lean`. The value group `Γ` is an arbitrary linearly ordered
abelian group; divisibility is not assumed, and neither is `Γ ≠ 0` except where stated. The
coefficient field `k` of characteristic zero of the source (`hol:cf:conv:field`) is generalized
to an arbitrary commutative semiring `R`: the arguments only multiply coefficients by monomials
`t^g` with coefficient `1`, which shift orders without any cancellation. Nontriviality of `R` is
used only to build the nonpolynomial witness of `hol:cf:cor:cofinality`. The valuation `v` is
`HahnSeries.order`; every order appearing in a statement below is that of a coefficient assumed
nonzero (proof terms may take the order of a zero coefficient, whose junk value is `0`).

* `criterion_tfae` is `hol:cf:prop:criterion`: for `f = ∑ a_n z^n` the three conditions
  (i) `f` is strongly entire, (ii) `(a_n t^{nγ})_n` is strongly summable for every `γ`, and
  (iii) for all `γ, β` only finitely many `n` with `a_n ≠ 0` satisfy `v(a_n) + nγ ≤ β`, are
  equivalent. The two-condition forms are `isStronglyEntire_iff_forall_stronglySummable` and
  `isStronglyEntire_iff_finite`; the implications (ii) ⇒ (iii) and (iii) ⇒ (ii) are
  `finite_of_forall_stronglySummable` and `stronglySummable_of_finite`. The necessity proof is
  the source's: at the more exterior argument `t^{γ - ε}` the leading exponents of the selected
  summands decrease. It takes `ε = max(β - α, 0)` instead of `max(β - α, 0) + η` with `η > 0`:
  the leading exponents are then only nonincreasing, which already contradicts strong
  summability (`hol:lem:nonincreasing`), so no positive element of `Γ` is needed and the
  criterion holds for `Γ = 0` as well.
* `exists_min_order_coeff` is `hol:cf:lem:min`: a nonzero strongly entire series has a nonzero
  coefficient of least valuation among its nonzero coefficients.
* `exists_nonpolynomial_isStronglyEntire_iff` is `hol:cf:cor:cofinality`: over a nontrivial
  `R`, a nonpolynomial strongly entire series exists if and only if `Order.cof Γ = ℵ₀`. This
  form needs no hypothesis `Γ ≠ 0`: for `Γ = 0` both sides are false. Under the source's
  convention `Γ ≠ 0` (`hol:conv:group`) the same dichotomy is stated with `Order.cof Γ ≤ ℵ₀`
  (`exists_nonpolynomial_isStronglyEntire_iff_cof_le`) and with a cofinal sequence
  (`exists_nonpolynomial_isStronglyEntire_iff_exists_cofinal`). The necessity half is
  `exists_lt_order_coeff`: the values of the nonzero coefficients are strictly cofinal. For
  sufficiency the witness `cofinalSeries s = ∑ t^{n δ_n} z^n` uses the running maxima
  `δ_n = max(s_0, …, s_n)` of a cofinal sequence; its coefficients are all nonzero, so it is not
  a polynomial (`not_exists_polynomial_cofinalSeries`), and it is strongly entire by the
  criterion (`isStronglyEntire_cofinalSeries`). Positivity of the `δ_n`, used in the source, is
  not needed. `exists_polynomial_eq_iff` identifies polynomials among power series as those with
  finitely many nonzero coefficients.

Nothing in the three statements is left pending. The remarks after `hol:cf:prop:criterion`
(bounded valuations at one argument, the example `(t^{n/(n+1)})` in `k((t^ℚ))`) are not
formalized here.
-/

namespace Surreal.CofinalityCriterion

open _root_.HahnSeries
open Surreal.Holonomic Surreal.HolonomicTorsion
open Cardinal

noncomputable section

section Polynomial

variable {S : Type*} [Semiring S]

/-- A formal power series is a polynomial exactly when only finitely many of its coefficients
are nonzero. -/
theorem exists_polynomial_eq_iff (f : PowerSeries S) :
    (∃ P : Polynomial S, (P : PowerSeries S) = f) ↔ {n | PowerSeries.coeff n f ≠ 0}.Finite := by
  constructor
  · rintro ⟨P, rfl⟩
    refine P.support.finite_toSet.subset fun n hn => ?_
    rw [Finset.mem_coe, Polynomial.mem_support_iff]
    rwa [Set.mem_setOf_eq, Polynomial.coeff_coe] at hn
  · intro hfin
    obtain ⟨N, hN⟩ := hfin.bddAbove
    refine ⟨PowerSeries.trunc (N + 1) f, PowerSeries.ext fun n => ?_⟩
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with hn
    · rfl
    · by_contra hne
      exact hn (Nat.lt_succ_of_le (hN (show n ∈ {n | PowerSeries.coeff n f ≠ 0} from
        fun h => hne h.symm)))

end Polynomial

section Cofinality

variable {α : Type*} [LinearOrder α]

/-- A linear order has cofinality `ℵ₀` exactly when some sequence is strictly cofinal in it. -/
theorem exists_strictly_cofinal_iff_cof_eq_aleph0 :
    (∃ s : ℕ → α, ∀ a, ∃ n, a < s n) ↔ Order.cof α = ℵ₀ := by
  constructor
  · rintro ⟨s, hs⟩
    have hne : Nonempty α := ⟨s 0⟩
    have hmax : NoMaxOrder α := ⟨fun a => let ⟨n, hn⟩ := hs a; ⟨s n, hn⟩⟩
    refine le_antisymm ?_ Order.aleph0_le_cof
    calc Order.cof α ≤ #(Set.range s) :=
          Order.cof_le fun a => let ⟨n, hn⟩ := hs a; ⟨s n, Set.mem_range_self n, hn.le⟩
      _ ≤ ℵ₀ := Cardinal.mk_le_aleph0_iff.mpr (Set.countable_range s).to_subtype
  · intro h
    have hne : Nonempty α := Order.cof_ne_zero_iff.mp (by rw [h]; exact Cardinal.aleph0_ne_zero)
    have htop : NoTopOrder α := (Order.one_lt_cof_iff).mp (by rw [h]; exact Cardinal.one_lt_aleph0)
    obtain ⟨C, hC, hCcard⟩ := Order.exists_cof_eq α
    have hCc : C.Countable := Cardinal.mk_le_aleph0_iff.mp (hCcard.trans h).le
    obtain ⟨c, hc, -⟩ := hC (Classical.arbitrary α)
    obtain ⟨s, rfl⟩ := hCc.exists_eq_range ⟨c, hc⟩
    refine ⟨s, fun a => ?_⟩
    obtain ⟨b, hb⟩ := exists_not_le a
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hC b
    exact ⟨n, (not_le.mp hb).trans_le hn⟩

end Cofinality

section Criterion

variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [CommSemiring R]

/-- Multiplication by a monomial `t^g` with coefficient `1` keeps a Hahn series nonzero. -/
theorem mul_single_one_ne_zero {x : R⟦Γ⟧} (hx : x ≠ 0) (g : Γ) : x * single g (1 : R) ≠ 0 := by
  intro h
  have hc := congrArg (fun y : R⟦Γ⟧ => y.coeff (x.order + g)) h
  simp only [coeff_mul_single_add, mul_one, coeff_zero] at hc
  exact coeff_order_eq_zero.not.mpr hx hc

/-- Multiplication by a monomial `t^g` with coefficient `1` shifts the order by `g`. -/
theorem order_mul_single_one {x : R⟦Γ⟧} (hx : x ≠ 0) (g : Γ) :
    (x * single g (1 : R)).order = x.order + g := by
  rw [mul_comm, order_single_mul_of_isRegular isRegular_one hx, add_comm]

/-- The evaluation family of `f` at the monomial `t^γ` is `(a_n t^{nγ})_n`. -/
theorem coeff_mul_single_pow (f : PowerSeries R⟦Γ⟧) (γ : Γ) (n : ℕ) :
    PowerSeries.coeff n f * single γ (1 : R) ^ n = PowerSeries.coeff n f * single (n • γ) 1 := by
  rw [single_pow, one_pow]

/-- The monomial `t^γ` lies in `Dom(f)` exactly when `(a_n t^{nγ})_n` is strongly summable. -/
theorem single_mem_strongDomain_iff (f : PowerSeries R⟦Γ⟧) (γ : Γ) :
    single γ (1 : R) ∈ strongDomain f ↔
      StronglySummable fun n => PowerSeries.coeff n f * single (n • γ) (1 : R) :=
  Iff.of_eq (congrArg StronglySummable (funext (coeff_mul_single_pow f γ)))

/-- `hol:cf:prop:criterion`, (iii) ⇒ (ii) at one scale `γ`: if for every `β` only finitely many
`n` with `a_n ≠ 0` satisfy `v(a_n) + nγ ≤ β`, then `(a_n t^{nγ})_n` is strongly summable. This is
`hol:lem:certificate` (a) for the summands `a_n t^{nγ}`. -/
theorem stronglySummable_of_finite {f : PowerSeries R⟦Γ⟧} {γ : Γ}
    (h : ∀ β : Γ,
      {n | PowerSeries.coeff n f ≠ 0 ∧ (PowerSeries.coeff n f).order + n • γ ≤ β}.Finite) :
    StronglySummable fun n => PowerSeries.coeff n f * single (n • γ) (1 : R) := by
  refine stronglySummable_of_finite_order_le _ fun β => (h β).subset fun n hn => ?_
  obtain ⟨hne, hle⟩ := hn
  have ha : PowerSeries.coeff n f ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
  exact ⟨ha, by rwa [order_mul_single_one ha] at hle⟩

/-- `hol:cf:prop:criterion`, (ii) ⇒ (iii): if `(a_n t^{nγ})_n` is strongly summable for every
`γ`, then for all `γ, β` only finitely many `n` with `a_n ≠ 0` satisfy `v(a_n) + nγ ≤ β`.
Otherwise let `α` be a lower bound of the weighted values `A_n = v(a_n) + nγ` (the least element
of the union of supports at `t^γ`) and `ε = max(β - α, 0)`. At `t^{γ - ε}` the leading exponents
`A_n - nε` of the infinitely many selected summands are nonincreasing, which contradicts strong
summability. -/
theorem finite_of_forall_stronglySummable {f : PowerSeries R⟦Γ⟧}
    (hf : ∀ γ : Γ, StronglySummable fun n => PowerSeries.coeff n f * single (n • γ) (1 : R))
    (γ β : Γ) :
    {n | PowerSeries.coeff n f ≠ 0 ∧ (PowerSeries.coeff n f).order + n • γ ≤ β}.Finite := by
  set p : ℕ → Prop :=
    fun n => PowerSeries.coeff n f ≠ 0 ∧ (PowerSeries.coeff n f).order + n • γ ≤ β with hp
  change (setOf p).Finite
  by_contra hS
  obtain ⟨hwf, -⟩ := (stronglySummable_iff_isWF _).mp (hf γ)
  have hmem : ∀ n, p n → (PowerSeries.coeff n f).order + n • γ ∈
      ⋃ i, (PowerSeries.coeff i f * single (i • γ) (1 : R)).support := by
    intro n hn
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    rw [← order_mul_single_one hn.1]
    exact (mem_support _ _).mpr (coeff_order_eq_zero.not.mpr (mul_single_one_ne_zero hn.1 _))
  obtain ⟨n₀, hn₀⟩ := Set.Infinite.nonempty hS
  have hU : (⋃ i, (PowerSeries.coeff i f * single (i • γ) (1 : R)).support).Nonempty :=
    ⟨_, hmem n₀ hn₀⟩
  have hα : ∀ n, p n → hwf.min hU ≤ (PowerSeries.coeff n f).order + n • γ :=
    fun n hn => hwf.min_le hU (hmem n hn)
  set α := hwf.min hU
  set ε := max (β - α) 0
  have hε1 : β - α ≤ ε := le_max_left _ _
  have hε0 : 0 ≤ ε := le_max_right _ _
  have step : ∀ m m', p m → p m' → m ≤ m' →
      (PowerSeries.coeff m' f).order + m' • (γ - ε) ≤
        (PowerSeries.coeff m f).order + m • (γ - ε) := by
    intro m m' hm hm' hle
    rcases hle.eq_or_lt with rfl | hlt
    · exact le_rfl
    obtain ⟨d, rfl⟩ : ∃ d, m' = m + (d + 1) := ⟨m' - m - 1, by omega⟩
    have hdε : ε ≤ (d + 1) • ε := le_self_nsmul hε0 (Nat.succ_ne_zero d)
    have key : (PowerSeries.coeff (m + (d + 1)) f).order + (m + (d + 1)) • γ ≤
        (PowerSeries.coeff m f).order + m • γ + (d + 1) • ε :=
      calc _ ≤ β := hm'.2
        _ = α + (β - α) := by abel
        _ ≤ _ := add_le_add (hα m hm) (hε1.trans hdε)
    calc (PowerSeries.coeff (m + (d + 1)) f).order + (m + (d + 1)) • (γ - ε)
        = ((PowerSeries.coeff (m + (d + 1)) f).order + (m + (d + 1)) • γ - (d + 1) • ε) -
            m • ε := by rw [smul_sub, add_nsmul ε m (d + 1)]; abel
      _ ≤ ((PowerSeries.coeff m f).order + m • γ) - m • ε :=
          sub_le_sub_right (sub_le_iff_le_add.mpr key) _
      _ = (PowerSeries.coeff m f).order + m • (γ - ε) := by rw [smul_sub]; abel
  refine not_stronglySummable_of_antitone_order
    (b := fun n => PowerSeries.coeff n f * single (n • (γ - ε)) (1 : R))
    (Nat.nth_strictMono hS).injective
    (fun r => mul_single_one_ne_zero (Nat.nth_mem_of_infinite hS r).1 _) (fun r r' hrr' => ?_)
    (hf (γ - ε))
  have hm := Nat.nth_mem_of_infinite hS r
  have hm' := Nat.nth_mem_of_infinite hS r'
  simp only
  rw [order_mul_single_one hm'.1, order_mul_single_one hm.1]
  exact step _ _ hm hm' ((Nat.nth_strictMono hS).monotone hrr')

/-- `hol:cf:prop:criterion`: for `f = ∑ a_n z^n` over `R((t^Γ))` the following are equivalent:
(i) `f` is strongly entire; (ii) the family `(a_n t^{nγ})_n` is strongly summable for every
`γ ∈ Γ`; (iii) for all `γ, β ∈ Γ`, only finitely many `n` with `a_n ≠ 0` satisfy
`v(a_n) + nγ ≤ β`. -/
theorem criterion_tfae (f : PowerSeries R⟦Γ⟧) :
    List.TFAE [IsStronglyEntire f,
      ∀ γ : Γ, StronglySummable fun n => PowerSeries.coeff n f * single (n • γ) (1 : R),
      ∀ γ β : Γ,
        {n | PowerSeries.coeff n f ≠ 0 ∧ (PowerSeries.coeff n f).order + n • γ ≤ β}.Finite] := by
  tfae_have 1 ↔ 2 := by
    rw [isStronglyEntire_iff_forall_single_mem]
    exact forall_congr' fun γ => single_mem_strongDomain_iff f γ
  tfae_have 2 → 3 := finite_of_forall_stronglySummable
  tfae_have 3 → 2 := fun h γ => stronglySummable_of_finite (h γ)
  tfae_finish

/-- `hol:cf:prop:criterion`, (i) ⇔ (ii). -/
theorem isStronglyEntire_iff_forall_stronglySummable (f : PowerSeries R⟦Γ⟧) :
    IsStronglyEntire f ↔
      ∀ γ : Γ, StronglySummable fun n => PowerSeries.coeff n f * single (n • γ) (1 : R) :=
  (criterion_tfae f).out 0 1

/-- `hol:cf:prop:criterion`, (i) ⇔ (iii): `f` is strongly entire exactly when for all
`γ, β ∈ Γ` only finitely many `n` with `a_n ≠ 0` satisfy `v(a_n) + nγ ≤ β`. -/
theorem isStronglyEntire_iff_finite (f : PowerSeries R⟦Γ⟧) :
    IsStronglyEntire f ↔ ∀ γ β : Γ,
      {n | PowerSeries.coeff n f ≠ 0 ∧ (PowerSeries.coeff n f).order + n • γ ≤ β}.Finite :=
  (criterion_tfae f).out 0 2

/-- `hol:cf:lem:min`: if `h = ∑ h_n z^n` is nonzero and strongly entire, some nonzero `h_j`
satisfies `v(h_j) ≤ v(h_n)` for every nonzero `h_n`. -/
theorem exists_min_order_coeff {h : PowerSeries R⟦Γ⟧} (hh : IsStronglyEntire h) (h0 : h ≠ 0) :
    ∃ j, PowerSeries.coeff j h ≠ 0 ∧ ∀ n, PowerSeries.coeff n h ≠ 0 →
      (PowerSeries.coeff j h).order ≤ (PowerSeries.coeff n h).order := by
  obtain ⟨n₀, hn₀⟩ := PowerSeries.exists_coeff_ne_zero_iff_ne_zero.mpr h0
  have hfin := (isStronglyEntire_iff_finite h).mp hh 0 (PowerSeries.coeff n₀ h).order
  simp only [smul_zero, add_zero] at hfin
  obtain ⟨j, hj, hmin⟩ := Set.exists_min_image _ (fun n => (PowerSeries.coeff n h).order) hfin
    ⟨n₀, hn₀, le_rfl⟩
  refine ⟨j, hj.1, fun n hn => ?_⟩
  by_cases hle : (PowerSeries.coeff n h).order ≤ (PowerSeries.coeff n₀ h).order
  · exact hmin n ⟨hn, hle⟩
  · exact hj.2.trans (not_le.mp hle).le

/-- `hol:cf:cor:cofinality`, necessity: the values of the nonzero coefficients of a
nonpolynomial strongly entire series are strictly cofinal in `Γ`. -/
theorem exists_lt_order_coeff {f : PowerSeries R⟦Γ⟧} (hf : IsStronglyEntire f)
    (hfp : ¬ ∃ P : Polynomial R⟦Γ⟧, (P : PowerSeries R⟦Γ⟧) = f) (γ : Γ) :
    ∃ n, PowerSeries.coeff n f ≠ 0 ∧ γ < (PowerSeries.coeff n f).order := by
  have hinf : {n | PowerSeries.coeff n f ≠ 0}.Infinite :=
    fun h => hfp ((exists_polynomial_eq_iff f).mpr h)
  have hfin := (isStronglyEntire_iff_finite f).mp hf 0 γ
  obtain ⟨n, hn, hn'⟩ := (hinf.sdiff hfin).nonempty
  refine ⟨n, hn, not_le.mp fun hle => hn' ⟨hn, ?_⟩⟩
  rwa [smul_zero, add_zero]

/-- The witness of `hol:cf:cor:cofinality`: `∑ t^{n δ_n} z^n` with the running maxima
`δ_n = max(s_0, …, s_n)` of a sequence `s`. -/
def cofinalSeries (s : ℕ → Γ) : PowerSeries R⟦Γ⟧ :=
  PowerSeries.mk fun n => single (n • partialSups s n) 1

/-- The `n`-th coefficient of `cofinalSeries s` is `t^{n δ_n}`, with `δ_n = max(s_0, …, s_n)`. -/
theorem coeff_cofinalSeries (s : ℕ → Γ) (n : ℕ) :
    PowerSeries.coeff n (cofinalSeries (R := R) s) = single (n • partialSups s n) 1 :=
  PowerSeries.coeff_mk _ _

/-- `hol:cf:cor:cofinality`, sufficiency: for a strictly cofinal sequence `s`, the series
`∑ t^{n δ_n} z^n` is strongly entire. Given `γ, β`, eventually `δ_n + γ > max(β, 0)`, so
`n(δ_n + γ) > β`, and the criterion applies. -/
theorem isStronglyEntire_cofinalSeries {s : ℕ → Γ} (hs : ∀ γ, ∃ n, γ < s n) :
    IsStronglyEntire (cofinalSeries (R := R) s) := by
  rw [isStronglyEntire_iff_finite]
  intro γ β
  obtain ⟨m, hm⟩ := hs (max β 0 - γ)
  refine (Set.finite_Iic m).subset fun n hn => ?_
  obtain ⟨hne, hle⟩ := hn
  rw [coeff_cofinalSeries] at hne hle
  have h1 : (1 : R) ≠ 0 := fun h => hne (by rw [h, single_eq_zero])
  rw [order_single h1, ← smul_add] at hle
  by_contra hmn
  rw [Set.mem_Iic, not_le] at hmn
  have hδ : max β 0 < partialSups s n + γ :=
    sub_lt_iff_lt_add.mp (hm.trans_le (le_partialSups_of_le s hmn.le))
  have hn1 : partialSups s n + γ ≤ n • (partialSups s n + γ) :=
    le_self_nsmul ((le_max_right β 0).trans hδ.le) (by omega)
  exact absurd hle (not_le.mpr ((le_max_left β 0).trans_lt (hδ.trans_le hn1)))

/-- The witness `∑ t^{n δ_n} z^n` has all coefficients nonzero, so it is not a polynomial. -/
theorem not_exists_polynomial_cofinalSeries [Nontrivial R] (s : ℕ → Γ) :
    ¬ ∃ P : Polynomial R⟦Γ⟧, (P : PowerSeries R⟦Γ⟧) = cofinalSeries s := by
  rw [exists_polynomial_eq_iff]
  refine Set.Infinite.mono (fun n _ => ?_) Set.infinite_univ
  rw [Set.mem_setOf_eq, coeff_cofinalSeries]
  exact single_ne_zero one_ne_zero

/-- `hol:cf:cor:cofinality`, sequence form: over a nontrivial `R`, a nonpolynomial strongly
entire series exists if and only if some sequence is strictly cofinal in `Γ`. -/
theorem exists_nonpolynomial_iff_exists_strictly_cofinal [Nontrivial R] :
    (∃ f : PowerSeries R⟦Γ⟧, IsStronglyEntire f ∧
        ¬ ∃ P : Polynomial R⟦Γ⟧, (P : PowerSeries R⟦Γ⟧) = f) ↔
      ∃ s : ℕ → Γ, ∀ γ, ∃ n, γ < s n := by
  constructor
  · rintro ⟨f, hf, hfp⟩
    refine ⟨fun n => (PowerSeries.coeff n f).order, fun γ => ?_⟩
    obtain ⟨n, -, hn⟩ := exists_lt_order_coeff hf hfp γ
    exact ⟨n, hn⟩
  · rintro ⟨s, hs⟩
    exact ⟨cofinalSeries s, isStronglyEntire_cofinalSeries hs,
      not_exists_polynomial_cofinalSeries s⟩

/-- `hol:cf:cor:cofinality`: over a nontrivial coefficient semiring (in the source, a field `k`),
a nonpolynomial strongly entire series exists if and only if `Γ` has countable cofinality,
`cf(Γ) = ℵ₀`. No hypothesis `Γ ≠ 0` is needed: for `Γ = 0` both sides are false. -/
theorem exists_nonpolynomial_isStronglyEntire_iff [Nontrivial R] :
    (∃ f : PowerSeries R⟦Γ⟧, IsStronglyEntire f ∧
        ¬ ∃ P : Polynomial R⟦Γ⟧, (P : PowerSeries R⟦Γ⟧) = f) ↔ Order.cof Γ = ℵ₀ := by
  rw [exists_nonpolynomial_iff_exists_strictly_cofinal, exists_strictly_cofinal_iff_cof_eq_aleph0]

/-- `hol:cf:cor:cofinality` under the source's convention `Γ ≠ 0`: a nonzero ordered abelian
group has no largest element, so its cofinality is infinite, and a nonpolynomial strongly entire
series exists if and only if `cf(Γ) ≤ ℵ₀`. -/
theorem exists_nonpolynomial_isStronglyEntire_iff_cof_le [Nontrivial R] [Nontrivial Γ] :
    (∃ f : PowerSeries R⟦Γ⟧, IsStronglyEntire f ∧
        ¬ ∃ P : Polynomial R⟦Γ⟧, (P : PowerSeries R⟦Γ⟧) = f) ↔ Order.cof Γ ≤ ℵ₀ := by
  rw [exists_nonpolynomial_isStronglyEntire_iff]
  exact ⟨le_of_eq, fun h => le_antisymm h Order.aleph0_le_cof⟩

/-- `hol:cf:cor:cofinality` under the source's convention `Γ ≠ 0`, with countable cofinality
expressed by a cofinal sequence: a nonpolynomial strongly entire series exists if and only if
some sequence `s : ℕ → Γ` is cofinal. -/
theorem exists_nonpolynomial_isStronglyEntire_iff_exists_cofinal [Nontrivial R] [Nontrivial Γ] :
    (∃ f : PowerSeries R⟦Γ⟧, IsStronglyEntire f ∧
        ¬ ∃ P : Polynomial R⟦Γ⟧, (P : PowerSeries R⟦Γ⟧) = f) ↔
      ∃ s : ℕ → Γ, ∀ γ, ∃ n, γ ≤ s n := by
  rw [exists_nonpolynomial_iff_exists_strictly_cofinal]
  refine ⟨fun ⟨s, hs⟩ => ⟨s, fun γ => let ⟨n, hn⟩ := hs γ; ⟨n, hn.le⟩⟩, fun ⟨s, hs⟩ => ⟨s, ?_⟩⟩
  intro γ
  obtain ⟨b, hb⟩ := exists_gt γ
  obtain ⟨n, hn⟩ := hs b
  exact ⟨n, hb.trans_le hn⟩

end Criterion

end

end Surreal.CofinalityCriterion
