import Mathlib.Algebra.Group.Submonoid.Pointwise
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Surreal.HahnSeries.EscapeChain

/-!
# Torsion covariance: eigen-series of finite-order dilations

This file formalizes `hol:prop:torsion` of
`docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/article.tex`, together with the
two lemmas its proof uses: multiplication of a strongly summable family by a fixed Hahn element
(`hol:lem:support` (3), in the form needed) and inward stability of strong evaluation
(`hol:lem:inward`).

The value group `Γ` is an arbitrary linearly ordered abelian group; neither divisibility nor
`Γ ≠ 0` is assumed (`hol:conv:group`). Strong summability, the strong domain and strong
entireness are those of `Surreal.Holonomic` (`hol:def:entire`, in `EscapeChain.lean`). As
there, the valuation `v` is `HahnSeries.order`, with the junk value `order 0 = 0`. The dilation
`f(z) ↦ f(qz)` is `PowerSeries.rescale q`, and `G(z) ↦ G(z^m)` is `PowerSeries.expand m`.

* `rescale_eq_C_pow_mul_iff` is `hol:prop:torsion` (a) for an arbitrary commutative ring `S`
  without zero divisors and an arbitrary `q ∈ S` of exact finite order `m ≥ 1`:
  `f(qz) = q^r f(z)` iff `f = z^r G(z^m)` for a unique `G`. Its instance at the Hahn ring,
  with `q` a constant of exact order `m`, is `rescale_C_eq_C_pow_mul_iff`; the source's `q ∈ ℂ^×`
  is the case `R = ℂ`, and by the root-of-unity clause below every Hahn series of finite order
  is such a constant.
* `mem_strongDomain_X_pow_mul_expand` is `hol:prop:torsion` (b) pointwise: `x^m ∈ Dom(G)`
  implies `x ∈ Dom(z^r G(z^m))`, over any commutative coefficient ring;
  `isStronglyEntire_X_pow_mul_expand` is (b) itself.
* `isStronglyEntire_of_X_pow_mul_expand` and `isStronglyEntire_X_pow_mul_expand_iff` are
  `hol:prop:torsion` (c), over any commutative coefficient ring and without divisibility of `Γ`.
  As in the source, no root of the argument is extracted: the proof evaluates at the monomial
  `t^γ` with `γ = min(v(y), 0)` and then uses inward stability. Over a field,
  `mem_strongDomain_X_pow_mul_expand_iff` records the exact pointwise statement
  `Dom(z^r G(z^m)) = {x : x^m ∈ Dom(G)}`.
* `eq_C_coeff_zero_of_pow_eq_one`, `eq_C_coeff_zero_of_isOfFinOrder` and
  `isOfFinOrder_iff_exists_C` are the final clause: every root of unity of the Hahn ring over a
  characteristic-zero coefficient domain is a constant. `orderOf_C` says that constants keep
  their multiplicative order.
* `torsion_covariance` collects all four clauses over an arbitrary field of characteristic
  zero, and `torsion_covariance_complex` is the source's statement over `K = ℂ((t^Γ))`.

Supporting results: `stronglySummable_mul_of_support_subset` (termwise multiplication by a
family with supports in one partially well-ordered set, which contains `hol:lem:support` (3)
for a fixed multiplier), reindexing along injections (`stronglySummable_comp_injective`,
`stronglySummable_of_comp`), `zero_mem_strongDomain` (evaluation at zero is finite, as used in
the proofs of `hol:lem:inward` and `hol:prop:torsion`), and `hol:lem:inward` in five forms:
`mul_mem_strongDomain` (multiplication of the argument by an element of nonnegative support,
over any commutative semiring), `mem_strongDomain_of_single_mem` (the monomial form:
`t^γ ∈ Dom(f)` and `γ ≤ v(y)` give `y ∈ Dom(f)`, over any commutative semiring),
`mem_strongDomain_of_order_le` (the source statement over a field, with `y = 0` allowed),
`mem_strongDomain_iff_of_order_eq` (membership of a nonzero argument depends only on its
valuation) and `isStronglyEntire_iff_forall_single_mem` (entireness can be tested on
monomials).

Nothing in `hol:prop:torsion` is left pending. The remaining parts of `hol:lem:support`
(parts (1) and (2), and reflection of summability by a nonzero multiplier) are not stated here;
part (2) is in `NeumannWords.lean`.
-/

namespace Surreal.HolonomicTorsion

open _root_.HahnSeries
open Surreal.Holonomic
open scoped Pointwise

section Eigenseries

variable {S : Type*} [CommRing S]

/-- The coefficient of `z^r G(z^m)` of degree `mk + r` is the `k`-th coefficient of `G`. -/
theorem coeff_X_pow_mul_expand_add {m : ℕ} (hm : m ≠ 0) (r : ℕ) (G : PowerSeries S) (k : ℕ) :
    PowerSeries.coeff (m * k + r) (PowerSeries.X ^ r * PowerSeries.expand m hm G) =
      PowerSeries.coeff k G := by
  rw [PowerSeries.coeff_X_pow_mul, PowerSeries.coeff_expand_mul]

/-- The coefficients of `z^r G(z^m)` vanish outside the progression `r + mℕ`. -/
theorem coeff_X_pow_mul_expand_of_forall_ne {m : ℕ} (hm : m ≠ 0) (r : ℕ) (G : PowerSeries S)
    {n : ℕ} (hn : ∀ k, m * k + r ≠ n) :
    PowerSeries.coeff n (PowerSeries.X ^ r * PowerSeries.expand m hm G) = 0 := by
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · refine PowerSeries.coeff_expand_of_not_dvd m hm G fun ⟨k, hk⟩ => hn k ?_
    rw [← hk, Nat.sub_add_cancel h]
  · rfl

/-- `hol:prop:torsion` (a): let `q` have exact finite order `m ≥ 1` and let `0 ≤ r < m`. A
formal power series satisfies `f(qz) = q^r f(z)` if and only if `f(z) = z^r G(z^m)` for a
unique formal power series `G`. The coefficient ring is any commutative ring without zero
divisors (the source takes the Hahn field `ℂ((t^Γ))` and `q ∈ ℂ^×`). -/
theorem rescale_eq_C_pow_mul_iff [NoZeroDivisors S] {q : S} {m : ℕ} (hm : m ≠ 0)
    (hq : orderOf q = m) {r : ℕ} (hr : r < m) (f : PowerSeries S) :
    PowerSeries.rescale q f = PowerSeries.C (q ^ r) * f ↔
      ∃! G : PowerSeries S, f = PowerSeries.X ^ r * PowerSeries.expand m hm G := by
  have hfin : IsOfFinOrder q := orderOf_pos_iff.mp (hq ▸ Nat.pos_of_ne_zero hm)
  have hqm : q ^ m = 1 := hq ▸ pow_orderOf_eq_one q
  constructor
  · intro h
    refine ⟨PowerSeries.mk fun k => PowerSeries.coeff (m * k + r) f, ?_, fun G hG => ?_⟩
    · ext n
      by_cases hn : ∃ k, m * k + r = n
      · obtain ⟨k, rfl⟩ := hn
        rw [coeff_X_pow_mul_expand_add, PowerSeries.coeff_mk]
      · push Not at hn
        rw [coeff_X_pow_mul_expand_of_forall_ne hm r _ hn]
        by_contra ha
        have hc := congrArg (PowerSeries.coeff n) h
        rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C_mul] at hc
        have hpow : q ^ n = q ^ r := mul_right_cancel₀ ha hc
        have hmod : n % m = r := by
          have h2 : n % orderOf q = r % orderOf q := hfin.pow_eq_pow_iff_modEq.mp hpow
          rw [hq, Nat.mod_eq_of_lt hr] at h2
          exact h2
        exact hn (n / m) (by rw [← hmod]; exact Nat.div_add_mod n m)
    · ext k
      rw [PowerSeries.coeff_mk, hG, coeff_X_pow_mul_expand_add]
  · rintro ⟨G, rfl, -⟩
    ext n
    rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C_mul]
    by_cases hn : ∃ k, m * k + r = n
    · obtain ⟨k, rfl⟩ := hn
      rw [pow_add, pow_mul, hqm, one_pow, one_mul]
    · push Not at hn
      rw [coeff_X_pow_mul_expand_of_forall_ne hm r G hn, mul_zero, mul_zero]

end Eigenseries

section Reindex

variable {Γ R : Type*} [PartialOrder Γ] [AddCommMonoid R]

/-- Restricting a strongly summable family along an injection keeps it strongly summable. -/
theorem stronglySummable_comp_injective {ι κ : Type*} {b : ι → R⟦Γ⟧}
    (hb : StronglySummable b) {e : κ → ι} (he : Function.Injective e) :
    StronglySummable fun k => b (e k) := by
  rw [stronglySummable_iff] at hb ⊢
  exact ⟨hb.1.mono (Set.iUnion_subset fun k => Set.subset_iUnion (fun i => (b i).support) (e k)),
    fun g => (hb.2 g).preimage he.injOn⟩

/-- A family vanishing outside the range of `e` is strongly summable as soon as its
restriction along `e` is. -/
theorem stronglySummable_of_comp {ι κ : Type*} {b : ι → R⟦Γ⟧} {e : κ → ι}
    (hzero : ∀ i, (∀ k, e k ≠ i) → b i = 0) (hb : StronglySummable fun k => b (e k)) :
    StronglySummable b := by
  rw [stronglySummable_iff] at hb ⊢
  have hmem : ∀ i g, g ∈ (b i).support → ∃ k, e k = i := fun i g hg => by
    by_contra h
    push Not at h
    simp [hzero i h] at hg
  refine ⟨hb.1.mono (Set.iUnion_subset fun i g hg => ?_),
    fun g => ((hb.2 g).image e).subset fun i hi => ?_⟩
  · obtain ⟨k, rfl⟩ := hmem i g hg
    exact Set.mem_iUnion.mpr ⟨k, hg⟩
  · obtain ⟨k, rfl⟩ := hmem i g ((mem_support _ _).mpr hi)
    exact ⟨k, hi, rfl⟩

end Reindex

section Multiplier

variable {Γ R : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]

/-- `hol:lem:support` (3), in the termwise form used for evaluation: if `(b_i)` is strongly
summable and all supports of the `c_i` lie in one partially well-ordered set `M`, then
`(b_i c_i)` is strongly summable. With `c_i` constant this is multiplication of a strongly
summable family by a fixed Hahn element. -/
theorem stronglySummable_mul_of_support_subset [NonUnitalNonAssocSemiring R] {ι : Type*}
    {b c : ι → R⟦Γ⟧} (hb : StronglySummable b) {M : Set Γ} (hM : M.IsPWO)
    (hc : ∀ i, (c i).support ⊆ M) : StronglySummable fun i => b i * c i := by
  rw [stronglySummable_iff] at hb ⊢
  obtain ⟨hpwo, hfin⟩ := hb
  refine ⟨(hpwo.add hM).mono (Set.iUnion_subset fun i => support_mul_subset.trans
      (Set.add_subset_add (Set.subset_iUnion (fun j => (b j).support) i) (hc i))), fun g => ?_⟩
  refine ((Set.AddAntidiagonal.finite_of_isPWO hpwo hM g).biUnion
    fun a _ => hfin a.1).subset fun i hi => ?_
  obtain ⟨α, hα, μ, hμ, hαμ⟩ := support_mul_subset (x := b i) (y := c i) ((mem_support _ _).mpr hi)
  exact Set.mem_biUnion (x := (α, μ)) ⟨Set.mem_iUnion.mpr ⟨i, hα⟩, hc i hμ, hαμ⟩
    ((mem_support _ _).mp hα)

/-- Evaluation at zero is always strongly summable: `0 ∈ Dom(f)` for every `f`. This is a
consequence of `hol:def:entire`, used in the proofs of `hol:lem:inward` and
`hol:prop:torsion` (b) and (c). -/
theorem zero_mem_strongDomain [Semiring R] (f : PowerSeries R⟦Γ⟧) :
    (0 : R⟦Γ⟧) ∈ strongDomain f := by
  have h : ∀ n, n ≠ 0 → PowerSeries.coeff n f * (0 : R⟦Γ⟧) ^ n = 0 := fun n hn => by
    rw [zero_pow hn, mul_zero]
  show StronglySummable fun n => PowerSeries.coeff n f * (0 : R⟦Γ⟧) ^ n
  rw [stronglySummable_iff]
  refine ⟨(PowerSeries.coeff 0 f * (0 : R⟦Γ⟧) ^ 0).isPWO_support.mono
      (Set.iUnion_subset fun n => ?_), fun g => (Set.finite_singleton 0).subset fun n hn => ?_⟩
  · rcases eq_or_ne n 0 with rfl | hn
    · exact subset_rfl
    · rw [h n hn, support_zero]
      exact Set.empty_subset _
  · by_contra hn'
    exact hn (by rw [h n hn', coeff_zero])

/-- `hol:lem:inward`, multiplicative form: if `x ∈ Dom(f)` and `u` has support in `Γ_{≥0}`,
then `xu ∈ Dom(f)`. The supports of the powers `u^n` lie in the partially well-ordered monoid
generated by `supp(u)`. -/
theorem mul_mem_strongDomain [CommSemiring R] {f : PowerSeries R⟦Γ⟧} {x u : R⟦Γ⟧}
    (hx : x ∈ strongDomain f) (hu : ∀ g ∈ u.support, 0 ≤ g) : x * u ∈ strongDomain f := by
  have hx' : StronglySummable fun n => PowerSeries.coeff n f * x ^ n := hx
  have h := stronglySummable_mul_of_support_subset hx'
    (u.isPWO_support.addSubmonoid_closure hu)
    (fun n => SummableFamily.support_pow_subset_closure u n)
  have heq : (fun n => PowerSeries.coeff n f * (x * u) ^ n) =
      fun n => PowerSeries.coeff n f * x ^ n * u ^ n :=
    funext fun n => by rw [mul_pow, mul_assoc]
  show StronglySummable fun n => PowerSeries.coeff n f * (x * u) ^ n
  rw [heq]
  exact h

section CommRing

variable [CommRing R]

/-- `hol:prop:torsion` (b), pointwise: if `x^m ∈ Dom(G)`, then `x ∈ Dom(z^r G(z^m))`. The
evaluation family of `z^r G(z^m)` at `x` is that of `G` at `x^m`, multiplied by `x^r` and
spread along the progression `r + mℕ`. -/
theorem mem_strongDomain_X_pow_mul_expand {m : ℕ} (hm : m ≠ 0) (r : ℕ) (G : PowerSeries R⟦Γ⟧)
    {x : R⟦Γ⟧} (hx : x ^ m ∈ strongDomain G) :
    x ∈ strongDomain (PowerSeries.X ^ r * PowerSeries.expand m hm G) := by
  have hx' : StronglySummable fun k => PowerSeries.coeff k G * (x ^ m) ^ k := hx
  have h1 := stronglySummable_mul_of_support_subset (c := fun _ => x ^ r) hx'
    (x ^ r).isPWO_support (fun _ => subset_rfl)
  refine stronglySummable_of_comp (e := fun k => m * k + r) (fun n hn => ?_) ?_
  · rw [coeff_X_pow_mul_expand_of_forall_ne hm r G hn, zero_mul]
  · have heq : (fun k => PowerSeries.coeff (m * k + r)
        (PowerSeries.X ^ r * PowerSeries.expand m hm G) * x ^ (m * k + r)) =
        fun k => PowerSeries.coeff k G * (x ^ m) ^ k * x ^ r :=
      funext fun k => by rw [coeff_X_pow_mul_expand_add, pow_add, pow_mul, mul_assoc]
    show StronglySummable fun k => PowerSeries.coeff (m * k + r)
      (PowerSeries.X ^ r * PowerSeries.expand m hm G) * x ^ (m * k + r)
    rw [heq]
    exact h1

/-- The converse step in `hol:prop:torsion` (c): if `x^r` has an inverse `w` and
`x ∈ Dom(z^r G(z^m))`, then `x^m ∈ Dom(G)`. The evaluation family of `G` at `x^m` is the
restriction of that of `z^r G(z^m)` at `x` to the degrees `r + mℕ`, multiplied by `x^{-r}`. -/
theorem pow_mem_strongDomain_of_mem {m : ℕ} (hm : m ≠ 0) (r : ℕ) (G : PowerSeries R⟦Γ⟧)
    {x w : R⟦Γ⟧} (hw : x ^ r * w = 1)
    (hx : x ∈ strongDomain (PowerSeries.X ^ r * PowerSeries.expand m hm G)) :
    x ^ m ∈ strongDomain G := by
  have hx' : StronglySummable fun n => PowerSeries.coeff n
      (PowerSeries.X ^ r * PowerSeries.expand m hm G) * x ^ n := hx
  have hinj : Function.Injective fun k => m * k + r := fun a b hab =>
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm) (Nat.add_right_cancel hab)
  have h1 := stronglySummable_comp_injective hx' hinj
  have h2 := stronglySummable_mul_of_support_subset (c := fun _ => w) h1 w.isPWO_support
    (fun _ => subset_rfl)
  have heq : (fun k => PowerSeries.coeff (m * k + r)
      (PowerSeries.X ^ r * PowerSeries.expand m hm G) * x ^ (m * k + r) * w) =
      fun k => PowerSeries.coeff k G * (x ^ m) ^ k :=
    funext fun k => by
      rw [coeff_X_pow_mul_expand_add, pow_add, pow_mul, mul_assoc, mul_assoc, hw, mul_one]
  show StronglySummable fun k => PowerSeries.coeff k G * (x ^ m) ^ k
  rw [← heq]
  exact h2

/-- `hol:prop:torsion` (b): if `G` is strongly entire, so is `z^r G(z^m)`. -/
theorem isStronglyEntire_X_pow_mul_expand {m : ℕ} (hm : m ≠ 0) (r : ℕ)
    {G : PowerSeries R⟦Γ⟧} (hG : IsStronglyEntire G) :
    IsStronglyEntire (PowerSeries.X ^ r * PowerSeries.expand m hm G) :=
  Set.eq_univ_of_forall fun x => mem_strongDomain_X_pow_mul_expand hm r G (by
    rw [hG]
    exact Set.mem_univ _)

end CommRing

end Multiplier

section Group

variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

section CommSemiring

variable [CommSemiring R]

/-- `hol:lem:inward`, monomial form: if the monomial `t^γ` lies in `Dom(f)` and
`γ ≤ v(y)`, then `y ∈ Dom(f)`. For `y = 0` the hypothesis reads `γ ≤ 0`. -/
theorem mem_strongDomain_of_single_mem {f : PowerSeries R⟦Γ⟧} {γ : Γ}
    (hγ : single γ (1 : R) ∈ strongDomain f) {y : R⟦Γ⟧} (hy : γ ≤ y.order) :
    y ∈ strongDomain f := by
  have hu : ∀ g ∈ (single (-γ) (1 : R) * y).support, 0 ≤ g := by
    intro g hg
    obtain ⟨a, ha, s, hs, rfl⟩ := support_mul_subset hg
    show 0 ≤ a + s
    rw [Set.mem_singleton_iff.mp (support_single_subset ha), neg_add_eq_sub, sub_nonneg]
    exact hy.trans (order_le_of_coeff_ne_zero ((mem_support _ _).mp hs))
  have h := mul_mem_strongDomain hγ hu
  rwa [← mul_assoc, single_mul_single, add_neg_cancel, mul_one, single_zero_one, one_mul] at h

/-- `hol:lem:inward`, last sentence: strong entireness can be tested on monomial
arguments `t^γ`. -/
theorem isStronglyEntire_iff_forall_single_mem {f : PowerSeries R⟦Γ⟧} :
    IsStronglyEntire f ↔ ∀ γ : Γ, single γ (1 : R) ∈ strongDomain f := by
  refine ⟨fun hf γ => ?_, fun h => Set.eq_univ_of_forall fun y =>
    mem_strongDomain_of_single_mem (h y.order) le_rfl⟩
  rw [hf]
  exact Set.mem_univ _

end CommSemiring

section CommRing

variable [CommRing R]

/-- `hol:prop:torsion` (c): if `z^r G(z^m)` is strongly entire (`m ≥ 1`), so is `G`. No
divisibility of `Γ` is used and no root of the argument is extracted: for `y` put
`γ = min(v(y), 0)`; evaluation at `t^γ`, restricted to the degrees `r + mℕ` and multiplied by
`t^{-rγ}`, is evaluation of `G` at `t^{mγ}`, and `mγ ≤ v(y)`, so inward stability applies. -/
theorem isStronglyEntire_of_X_pow_mul_expand {m : ℕ} (hm : m ≠ 0) (r : ℕ)
    {G : PowerSeries R⟦Γ⟧}
    (hF : IsStronglyEntire (PowerSeries.X ^ r * PowerSeries.expand m hm G)) :
    IsStronglyEntire G := by
  refine Set.eq_univ_of_forall fun y => ?_
  have hx : single (min y.order 0) (1 : R) ∈
      strongDomain (PowerSeries.X ^ r * PowerSeries.expand m hm G) := by
    rw [hF]
    exact Set.mem_univ _
  have hw : single (min y.order 0) (1 : R) ^ r * single (-(r • min y.order 0)) 1 = 1 := by
    rw [single_pow, single_mul_single, add_neg_cancel, one_pow, mul_one, single_zero_one]
  have h := pow_mem_strongDomain_of_mem hm r G hw hx
  rw [single_pow, one_pow] at h
  refine mem_strongDomain_of_single_mem h ?_
  calc m • min y.order 0 ≤ 1 • min y.order 0 :=
        nsmul_le_nsmul_left_of_nonpos (min_le_right _ _) (Nat.one_le_iff_ne_zero.mpr hm)
    _ = min y.order 0 := one_nsmul _
    _ ≤ y.order := min_le_left _ _

/-- `hol:prop:torsion` (b) and (c): for `m ≥ 1`, `z^r G(z^m)` is strongly entire if and only
if `G` is, without divisibility of `Γ`. -/
theorem isStronglyEntire_X_pow_mul_expand_iff {m : ℕ} (hm : m ≠ 0) (r : ℕ)
    (G : PowerSeries R⟦Γ⟧) :
    IsStronglyEntire (PowerSeries.X ^ r * PowerSeries.expand m hm G) ↔ IsStronglyEntire G :=
  ⟨isStronglyEntire_of_X_pow_mul_expand hm r, isStronglyEntire_X_pow_mul_expand hm r⟩

end CommRing

section Field

variable {k : Type*} [Field k]

/-- `hol:lem:inward`: if `x ≠ 0`, `v(x) ≤ v(y)` and `x ∈ Dom(f)`, then `y ∈ Dom(f)`. The
source assumes `y ≠ 0` as well; for `y = 0` the conclusion holds trivially. -/
theorem mem_strongDomain_of_order_le {f : PowerSeries k⟦Γ⟧} {x y : k⟦Γ⟧} (hx0 : x ≠ 0)
    (hxy : x.order ≤ y.order) (hx : x ∈ strongDomain f) : y ∈ strongDomain f := by
  rcases eq_or_ne y 0 with rfl | hy0
  · exact zero_mem_strongDomain f
  have hu0 : x⁻¹ * y ≠ 0 := mul_ne_zero (inv_ne_zero hx0) hy0
  have hxu : x * (x⁻¹ * y) = y := by rw [← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
  have hord : x.order + (x⁻¹ * y).order = y.order := by rw [← order_mul hx0 hu0, hxu]
  have hu : ∀ g ∈ (x⁻¹ * y).support, 0 ≤ g := fun g hg => by
    have h1 : 0 ≤ (x⁻¹ * y).order := by
      rw [← hord] at hxy
      exact le_add_iff_nonneg_right _ |>.mp hxy
    exact h1.trans (order_le_of_coeff_ne_zero ((mem_support _ _).mp hg))
  have h := mul_mem_strongDomain hx hu
  rwa [hxu] at h

/-- `hol:lem:inward`: membership of a nonzero argument in `Dom(f)` depends only on its
valuation. -/
theorem mem_strongDomain_iff_of_order_eq {f : PowerSeries k⟦Γ⟧} {x y : k⟦Γ⟧} (hx0 : x ≠ 0)
    (hy0 : y ≠ 0) (hxy : x.order = y.order) : x ∈ strongDomain f ↔ y ∈ strongDomain f :=
  ⟨mem_strongDomain_of_order_le hx0 hxy.le, mem_strongDomain_of_order_le hy0 hxy.ge⟩

/-- `hol:prop:torsion` (b) and (c), exact pointwise form over a field: for `m ≥ 1`,
`Dom(z^r G(z^m)) = {x : x^m ∈ Dom(G)}`. -/
theorem mem_strongDomain_X_pow_mul_expand_iff {m : ℕ} (hm : m ≠ 0) (r : ℕ)
    (G : PowerSeries k⟦Γ⟧) (x : k⟦Γ⟧) :
    x ∈ strongDomain (PowerSeries.X ^ r * PowerSeries.expand m hm G) ↔
      x ^ m ∈ strongDomain G := by
  refine ⟨fun hx => ?_, mem_strongDomain_X_pow_mul_expand hm r G⟩
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [zero_pow hm]
    exact zero_mem_strongDomain G
  · exact pow_mem_strongDomain_of_mem hm r G (mul_inv_cancel₀ (pow_ne_zero r hx0)) hx

end Field

section Torsion

variable [CommRing R]

/-- Constants of the Hahn ring keep their multiplicative order. -/
theorem orderOf_C (q : R) : orderOf (C q : R⟦Γ⟧) = orderOf q :=
  orderOf_injective (C : R →+* R⟦Γ⟧).toMonoidHom C_injective q

variable [NoZeroDivisors R]

/-- `hol:prop:torsion` (a) at the Hahn ring: for a constant `q` of exact finite order `m ≥ 1`
and `0 ≤ r < m`, `f(qz) = q^r f(z)` if and only if `f = z^r G(z^m)` for a unique `G`. -/
theorem rescale_C_eq_C_pow_mul_iff {q : R} {m : ℕ} (hm : m ≠ 0) (hq : orderOf q = m) {r : ℕ}
    (hr : r < m) (f : PowerSeries R⟦Γ⟧) :
    PowerSeries.rescale (C q) f = PowerSeries.C (C q ^ r) * f ↔
      ∃! G : PowerSeries R⟦Γ⟧, f = PowerSeries.X ^ r * PowerSeries.expand m hm G :=
  rescale_eq_C_pow_mul_iff hm ((orderOf_C (Γ := Γ) q).trans hq) hr f

variable [CharZero R]

/-- `hol:prop:torsion`, last clause: over a characteristic-zero coefficient domain, every root
of unity of the Hahn ring is a constant. A root of unity has valuation zero; if it differed
from its constant term `c`, the difference `w` would have positive valuation `β`, and the
coefficient of `(C c + w)^n` at `β` would be `n c^{n-1} lc(w) ≠ 0`. -/
theorem eq_C_coeff_zero_of_pow_eq_one {ζ : R⟦Γ⟧} {n : ℕ} (hn : n ≠ 0) (hζ : ζ ^ n = 1) :
    ζ = C (ζ.coeff 0) := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hζ
    exact zero_ne_one hζ
  have hord : ζ.order = 0 := by
    have h := order_pow ζ n
    rw [hζ, order_one] at h
    rcases lt_trichotomy ζ.order 0 with hlt | heq | hgt
    · have h2 := nsmul_pos (neg_pos.mpr hlt) hn
      rw [smul_neg, ← h, neg_zero] at h2
      exact absurd h2 (lt_irrefl 0)
    · exact heq
    · have h2 := nsmul_pos hgt hn
      rw [← h] at h2
      exact absurd h2 (lt_irrefl 0)
  have hc : ζ.coeff 0 ≠ 0 := hord ▸ coeff_order_eq_zero.not.mpr hζ0
  by_contra hne
  obtain ⟨w, hw⟩ : ∃ w, w = ζ - C (ζ.coeff 0) := ⟨_, rfl⟩
  have hw0 : w ≠ 0 := by
    rw [hw]
    exact sub_ne_zero.mpr hne
  have hcoeff : ∀ g, g ≤ 0 → w.coeff g = 0 := by
    intro g hg
    rcases hg.lt_or_eq with hlt | rfl
    · rw [hw, coeff_sub, C_apply, coeff_single_of_ne hlt.ne,
        coeff_eq_zero_of_lt_order (hord ▸ hlt), sub_zero]
    · rw [hw, coeff_sub, C_apply, coeff_single_same, sub_self]
  have hβ : 0 < w.order := by
    by_contra hle
    exact hw0 (coeff_order_eq_zero.mp (hcoeff _ (not_lt.mp hle)))
  have hexp : ζ ^ n = ∑ j ∈ Finset.range (n + 1),
      ((ζ.coeff 0) ^ (n - j) * (n.choose j : R)) • w ^ j := by
    have hsplit : ζ = w + C (ζ.coeff 0) := by rw [hw, sub_add_cancel]
    conv_lhs => rw [hsplit, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← C_mul_eq_smul, map_mul, map_pow, map_natCast]
    ring
  have hsum : (ζ ^ n).coeff w.order = ((ζ.coeff 0) ^ (n - 1) * (n : R)) * w.coeff w.order := by
    rw [hexp, coeff_sum, Finset.sum_eq_single 1]
    · rw [coeff_smul, smul_eq_mul, pow_one, Nat.choose_one_right]
    · intro j _ hj
      rw [coeff_smul, smul_eq_mul]
      rcases Nat.lt_or_gt_of_ne hj with h0 | h2
      · rw [Nat.lt_one_iff.mp h0, pow_zero, coeff_one, if_neg hβ.ne', mul_zero]
      · have hlt : w.order < (w ^ j).order := by
          rw [order_pow]
          calc w.order = 1 • w.order := (one_nsmul _).symm
            _ < j • w.order := nsmul_lt_nsmul_left hβ h2
        rw [coeff_eq_zero_of_lt_order hlt, mul_zero]
    · intro h1
      exact absurd (Finset.mem_range.mpr (by omega)) h1
  rw [hζ, coeff_one, if_neg hβ.ne'] at hsum
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hc) (Nat.cast_ne_zero.mpr hn))
    (coeff_order_eq_zero.not.mpr hw0) hsum.symm

/-- `hol:prop:torsion`, last clause: every element of finite multiplicative order of the Hahn
ring over a characteristic-zero coefficient domain is a constant. -/
theorem eq_C_coeff_zero_of_isOfFinOrder {ζ : R⟦Γ⟧} (hζ : IsOfFinOrder ζ) :
    ζ = C (ζ.coeff 0) := by
  obtain ⟨n, hn, hζn⟩ := isOfFinOrder_iff_pow_eq_one.mp hζ
  exact eq_C_coeff_zero_of_pow_eq_one hn.ne' hζn

/-- `hol:prop:torsion`, last clause: the torsion elements of the Hahn ring are exactly the
constants `C q` with `q` of finite order, so restricting to `q` in the coefficient ring loses no
torsion element. -/
theorem isOfFinOrder_iff_exists_C {ζ : R⟦Γ⟧} :
    IsOfFinOrder ζ ↔ ∃ q : R, IsOfFinOrder q ∧ C q = ζ := by
  constructor
  · intro hζ
    refine ⟨ζ.coeff 0, ?_, (eq_C_coeff_zero_of_isOfFinOrder hζ).symm⟩
    rw [← orderOf_pos_iff, ← orderOf_C (Γ := Γ), ← eq_C_coeff_zero_of_isOfFinOrder hζ]
    exact orderOf_pos_iff.mpr hζ
  · rintro ⟨q, hq, rfl⟩
    rw [← orderOf_pos_iff, orderOf_C]
    exact orderOf_pos_iff.mpr hq

end Torsion

/-- `hol:prop:torsion`, all clauses, over the Hahn field `k((t^Γ))` for an arbitrary field `k`
of characteristic zero: for `q ∈ k` of exact finite order `m ≥ 1` and `0 ≤ r < m`,
(a) `f(qz) = q^r f(z)` iff `f = z^r G(z^m)` for a unique `G`; (b) if `G` is strongly entire,
so is `z^r G(z^m)`; (c) conversely, without divisibility of `Γ`; and every root of unity of
`k((t^Γ))` lies in `k`. -/
theorem torsion_covariance {k : Type*} [Field k] [CharZero k] {q : k} {m : ℕ} (hm : m ≠ 0)
    (hq : orderOf q = m) {r : ℕ} (hr : r < m) :
    (∀ f : PowerSeries k⟦Γ⟧, PowerSeries.rescale (C q) f = PowerSeries.C (C q ^ r) * f ↔
      ∃! G : PowerSeries k⟦Γ⟧, f = PowerSeries.X ^ r * PowerSeries.expand m hm G) ∧
    (∀ G : PowerSeries k⟦Γ⟧, IsStronglyEntire G →
      IsStronglyEntire (PowerSeries.X ^ r * PowerSeries.expand m hm G)) ∧
    (∀ G : PowerSeries k⟦Γ⟧,
      IsStronglyEntire (PowerSeries.X ^ r * PowerSeries.expand m hm G) ↔ IsStronglyEntire G) ∧
    (∀ ζ : k⟦Γ⟧, IsOfFinOrder ζ → ζ ∈ Set.range (C : k → k⟦Γ⟧)) :=
  ⟨rescale_C_eq_C_pow_mul_iff hm hq hr, fun _ => isStronglyEntire_X_pow_mul_expand hm r,
    isStronglyEntire_X_pow_mul_expand_iff hm r,
    fun _ hζ => ⟨_, (eq_C_coeff_zero_of_isOfFinOrder hζ).symm⟩⟩

/-- `hol:prop:torsion` verbatim over `K = ℂ((t^Γ))`, for `q ∈ ℂ^×` of exact finite order
`m ≥ 1` and `0 ≤ r < m`. -/
theorem torsion_covariance_complex {q : ℂ} {m : ℕ} (hm : m ≠ 0) (hq : orderOf q = m) {r : ℕ}
    (hr : r < m) :
    (∀ f : PowerSeries ℂ⟦Γ⟧, PowerSeries.rescale (C q) f = PowerSeries.C (C q ^ r) * f ↔
      ∃! G : PowerSeries ℂ⟦Γ⟧, f = PowerSeries.X ^ r * PowerSeries.expand m hm G) ∧
    (∀ G : PowerSeries ℂ⟦Γ⟧, IsStronglyEntire G →
      IsStronglyEntire (PowerSeries.X ^ r * PowerSeries.expand m hm G)) ∧
    (∀ G : PowerSeries ℂ⟦Γ⟧,
      IsStronglyEntire (PowerSeries.X ^ r * PowerSeries.expand m hm G) ↔ IsStronglyEntire G) ∧
    (∀ ζ : ℂ⟦Γ⟧, IsOfFinOrder ζ → ζ ∈ Set.range (C : ℂ → ℂ⟦Γ⟧)) :=
  torsion_covariance hm hq hr

end Group

end Surreal.HolonomicTorsion
