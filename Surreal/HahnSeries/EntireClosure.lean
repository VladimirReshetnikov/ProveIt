import Mathlib.Data.Finset.MulAntidiagonal
import Mathlib.RingTheory.PowerSeries.Derivative
import Surreal.HahnSeries.TorsionCovariance

/-!
# Closure of the entire class under algebra operations, dilation and differentiation

This file formalizes `hol:prop:closure` of
`docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/article.tex`, together with the
support facts its proof uses: part (1) of `hol:lem:support`, the reflection half of part (3) of
`hol:lem:support`, and the block-grouping clause of `hol:lem:certificate`. The same statements
give the first sentence of `hol:cf:prop:ring` (a differential subalgebra stable under every
dilation), whose proof in the source refers back to `hol:prop:closure`.

Strong summability, the strong domain `Dom(f)` and strong entireness (`hol:def:entire`) are
those of `Surreal.Holonomic` in `EscapeChain.lean`: a family is strongly summable when it is the
family of terms of a Mathlib `SummableFamily`. The dilation `σ_q f(z) = f(qz)` is
`PowerSeries.rescale q`, and `D_z` is `PowerSeries.derivative`. The coefficient field `ℂ` of
the source is replaced by an arbitrary commutative semiring `R`, and the value group by an
ordered cancellative commutative monoid, except where inverses are needed. Inverses of Hahn
series are used by the source form of the reflection half of `hol:lem:support` (3) and by the
pointwise derivative statement, so these two are stated over an arbitrary field `k` with `Γ`
an ordered abelian group; inverse exponents are used by the derivative clause `D_z(E) ⊆ E`,
which is stated for an ordered abelian group `Γ` over any commutative semiring.

* `isPWO_add_and_finite` and `isWF_add_and_finite` are `hol:lem:support` (1): for partially
  well-ordered (respectively well-ordered) `A, B`, the set `A + B` is again partially
  well-ordered (well-ordered) and each `γ` has only finitely many representations `a + b`.
* `stronglySummable_const_mul` is the preservation half of `hol:lem:support` (3) for a fixed
  multiplier on the left, over any non-unital non-associative semiring;
  `stronglySummable_of_const_mul` is the reflection half for a multiplier with a left inverse,
  and `stronglySummable_const_mul_iff_of_ne_zero` is the source statement: over a field, a
  nonzero multiplier preserves and reflects strong summability.
* `blockFamily`, `stronglySummable_sum_blocks` and `hsum_blockFamily` are the last clause of
  `hol:lem:certificate`: grouping a strongly summable family into finite blocks (the fibres of
  a map `g`, listed by finsets `F k`) preserves strong summability and the sum.
* The pointwise forms of `hol:prop:closure`: `mem_strongDomain_add` and
  `mem_strongDomain_mul` (`Dom(f) ∩ Dom(g) ⊆ Dom(f + g)` and `⊆ Dom(fg)`, the latter by the
  source's route: the doubly indexed product family, grouped by total degree),
  `mem_strongDomain_smul` and `mem_strongDomain_C` (scalars), `mem_strongDomain_rescale_iff`
  (`x ∈ Dom(σ_q f)` iff `qx ∈ Dom(f)`, for every `q`, including `q = 0`),
  `mem_strongDomain_derivative_of_mul_eq_one` (a unit argument in `Dom(f)` lies in
  `Dom(D_z f)`, over any commutative semiring) and `mem_strongDomain_derivative`
  (`Dom(f) ⊆ Dom(D_z f)` over any field). `exists_summableFamily_mul` adds that the product
  family sums to the product of the two sums.
* `entireSubalgebra` is the class `E` as an `R((t^Γ))`-subalgebra of `R((t^Γ))[[z]]`;
  `rescale_mem_entireSubalgebra` is `σ_q(E) ⊆ E` for every `q` (the source asks only
  `q ≠ 0`), and `derivative_mem_entireSubalgebra` and `iterate_derivative_mem_entireSubalgebra`
  are `D_z(E) ⊆ E` and its iteration. The derivative clause uses inverse exponents
  (evaluation at the monomials `t^γ`), so it is stated for an ordered abelian group `Γ`.
  `entireSubalgebra_closure` collects the clauses of `hol:prop:closure`; over a field
  of characteristic zero it is also the first sentence of `hol:cf:prop:ring`.

Elsewhere: part (2) of `hol:lem:support` is in `NeumannWords.lean`, the preservation half of
part (3) for termwise right multiplication in `TorsionCovariance.lean`, and certificates (a)
and (b) of `hol:lem:certificate` in `PartialThetaDomain.lean`. Nothing of `hol:prop:closure`
is pending. Pending: the second sentence of `hol:cf:prop:ring` (the fraction field of `E` is a
differential subfield of `K((z))`) and the `d`-variable clause of `hol:def:entire`.
-/

namespace Surreal.EntireClosure

open _root_.HahnSeries
open Surreal.Holonomic Surreal.HolonomicTorsion
open scoped Pointwise

noncomputable section

section Support

variable {Γ : Type*}

/-- `hol:lem:support` (1), partially ordered form: in an ordered cancellative commutative
monoid, if `A` and `B` are partially well-ordered then so is `A + B`, and each `γ` has only
finitely many representations `γ = a + b` with `(a, b) ∈ A × B`. -/
theorem isPWO_add_and_finite [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
    {A B : Set Γ} (hA : A.IsPWO) (hB : B.IsPWO) (g : Γ) :
    (A + B).IsPWO ∧ {p : Γ × Γ | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = g}.Finite :=
  ⟨hA.add hB, Set.AddAntidiagonal.finite_of_isPWO hA hB g⟩

/-- `hol:lem:support` (1): if `A` and `B` are well-ordered subsets of a linearly ordered
cancellative commutative monoid (for instance an ordered abelian group), then `A + B` is well
ordered, and each `γ` has only finitely many representations `γ = a + b` with
`(a, b) ∈ A × B`. -/
theorem isWF_add_and_finite [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
    {A B : Set Γ} (hA : A.IsWF) (hB : B.IsWF) (g : Γ) :
    (A + B).IsWF ∧ {p : Γ × Γ | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = g}.Finite :=
  ⟨hA.add hB, Set.AddAntidiagonal.finite_of_isPWO hA.isPWO hB.isPWO g⟩

end Support

section Multiplier

variable {Γ R ι : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]

/-- `hol:lem:support` (3), preservation half: multiplying every member of a strongly summable
family on the left by a fixed Hahn element keeps it strongly summable. The new supports lie in
`supp(c) + A`, where `A` is the union of the old supports. -/
theorem stronglySummable_const_mul [NonUnitalNonAssocSemiring R] {b : ι → R⟦Γ⟧}
    (hb : StronglySummable b) (c : R⟦Γ⟧) : StronglySummable fun i => c * b i := by
  rw [stronglySummable_iff] at hb ⊢
  obtain ⟨hpwo, hfin⟩ := hb
  refine ⟨(c.isPWO_support.add hpwo).mono (Set.iUnion_subset fun i => support_mul_subset.trans
      (Set.add_subset_add subset_rfl (Set.subset_iUnion (fun j => (b j).support) i))),
    fun g => ?_⟩
  refine ((Set.AddAntidiagonal.finite_of_isPWO c.isPWO_support hpwo g).biUnion
    fun a _ => hfin a.2).subset fun i hi => ?_
  obtain ⟨μ, hμ, α, hα, hμα⟩ := support_mul_subset (x := c) (y := b i) ((mem_support _ _).mpr hi)
  exact Set.mem_biUnion (x := (μ, α)) ⟨hμ, Set.mem_iUnion.mpr ⟨i, hα⟩, hμα⟩
    ((mem_support _ _).mp hα)

/-- `hol:lem:support` (3), reflection half: if `d * c = 1` and `(c b_i)` is strongly summable,
then so is `(b_i)`, since `b_i = d (c b_i)`. -/
theorem stronglySummable_of_const_mul [Semiring R] {b : ι → R⟦Γ⟧} {c d : R⟦Γ⟧}
    (hdc : d * c = 1) (hb : StronglySummable fun i => c * b i) : StronglySummable b := by
  have h := stronglySummable_const_mul hb d
  simp only [← mul_assoc, hdc, one_mul] at h
  exact h

/-- `hol:lem:support` (3) for an invertible multiplier: multiplication by `c` with a left
inverse preserves and reflects strong summability. -/
theorem stronglySummable_const_mul_iff [Semiring R] {b : ι → R⟦Γ⟧} {c d : R⟦Γ⟧}
    (hdc : d * c = 1) : (StronglySummable fun i => c * b i) ↔ StronglySummable b :=
  ⟨stronglySummable_of_const_mul hdc, fun hb => stronglySummable_const_mul hb c⟩

end Multiplier

section FieldMultiplier

variable {Γ k ι : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field k]

/-- `hol:lem:support` (3): over a field `k`, multiplication by a nonzero Hahn element
`c ∈ k((t^Γ))` preserves and reflects strong summability. -/
theorem stronglySummable_const_mul_iff_of_ne_zero {b : ι → k⟦Γ⟧} {c : k⟦Γ⟧} (hc : c ≠ 0) :
    (StronglySummable fun i => c * b i) ↔ StronglySummable b :=
  stronglySummable_const_mul_iff (inv_mul_cancel₀ hc)

end FieldMultiplier

section Blocks

variable {Γ R ι κ : Type*} [PartialOrder Γ] [AddCommMonoid R]

/-- A coefficient of a finite sum of Hahn series is nonzero only if the same coefficient of
some summand is nonzero. -/
theorem exists_coeff_ne_zero_of_sum {F : Finset ι} {b : ι → R⟦Γ⟧} {γ : Γ}
    (h : (∑ i ∈ F, b i).coeff γ ≠ 0) : ∃ i ∈ F, (b i).coeff γ ≠ 0 := by
  rw [coeff_sum] at h
  exact Finset.exists_ne_zero_of_sum_ne_zero h

/-- The finite blocks of a summable family: the blocks are the fibres of `g : ι → κ`, listed by
finsets `F k`, and the `k`-th member is the finite sum of the members in the `k`-th block. -/
def blockFamily (s : SummableFamily Γ R ι) (g : ι → κ) (F : κ → Finset ι)
    (hF : ∀ k i, i ∈ F k ↔ g i = k) : SummableFamily Γ R κ where
  toFun k := ∑ i ∈ F k, s i
  isPWO_iUnion_support' := s.isPWO_iUnion_support.mono (Set.iUnion_subset fun k γ hγ => by
    obtain ⟨i, -, hi⟩ := exists_coeff_ne_zero_of_sum ((mem_support _ _).mp hγ)
    exact Set.mem_iUnion.mpr ⟨i, (mem_support _ _).mpr hi⟩)
  finite_co_support' γ := ((s.finite_co_support γ).image g).subset fun k hk => by
    obtain ⟨i, hiF, hi⟩ := exists_coeff_ne_zero_of_sum hk
    exact ⟨i, hi, (hF k i).mp hiF⟩

/-- The `k`-th member of `blockFamily s g F hF` is the finite block sum `∑ i ∈ F k, s i`. -/
theorem blockFamily_apply (s : SummableFamily Γ R ι) (g : ι → κ) (F : κ → Finset ι)
    (hF : ∀ k i, i ∈ F k ↔ g i = k) (k : κ) : blockFamily s g F hF k = ∑ i ∈ F k, s i :=
  rfl

/-- `hol:lem:certificate`, last clause (summability): grouping a strongly summable family into
finite blocks, the fibres of `g` listed by the finsets `F k`, gives a strongly summable family
of block sums. -/
theorem stronglySummable_sum_blocks {b : ι → R⟦Γ⟧} (hb : StronglySummable b) (g : ι → κ)
    (F : κ → Finset ι) (hF : ∀ k i, i ∈ F k ↔ g i = k) :
    StronglySummable fun k => ∑ i ∈ F k, b i := by
  obtain ⟨s, hs⟩ := hb
  exact ⟨blockFamily s g F hF, fun k => by
    rw [blockFamily_apply]
    exact Finset.sum_congr rfl fun i _ => hs i⟩

/-- `hol:lem:certificate`, last clause (the sum): grouping a summable family into finite blocks
does not change its Hahn sum. At each exponent this is a finite regrouping of a finite sum. -/
theorem hsum_blockFamily (s : SummableFamily Γ R ι) (g : ι → κ) (F : κ → Finset ι)
    (hF : ∀ k i, i ∈ F k ↔ g i = k) : (blockFamily s g F hF).hsum = s.hsum := by
  classical
  ext γ
  set T := (s.finite_co_support γ).toFinset with hTdef
  have hT : ∀ i, (s i).coeff γ ≠ 0 → i ∈ T := fun i hi => (Set.Finite.mem_toFinset _).mpr hi
  have hsub : {k | (blockFamily s g F hF k).coeff γ ≠ 0} ⊆ (T.image g : Set κ) := by
    intro k hk
    obtain ⟨i, hiF, hi⟩ := exists_coeff_ne_zero_of_sum hk
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, hT i hi, (hF k i).mp hiF⟩)
  rw [SummableFamily.coeff_hsum_eq_sum_of_subset hsub,
    SummableFamily.coeff_hsum_eq_sum_of_subset (t := T) fun i hi => hT i hi,
    ← Finset.sum_fiberwise_of_maps_to (s := T) (t := T.image g)
      (fun i hi => Finset.mem_image_of_mem g hi)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [blockFamily_apply, coeff_sum]
  symm
  refine Finset.sum_subset (fun i hi => (hF k i).mpr (Finset.mem_filter.mp hi).2)
    fun i hiF hiT => ?_
  by_contra hne
  exact hiT (Finset.mem_filter.mpr ⟨hT i hne, (hF k i).mp hiF⟩)

/-- A family with at most one nonzero member is strongly summable. -/
theorem stronglySummable_of_eq_zero_of_ne {b : ι → R⟦Γ⟧} (i₀ : ι)
    (h : ∀ i, i ≠ i₀ → b i = 0) : StronglySummable b := by
  rw [stronglySummable_iff]
  refine ⟨(b i₀).isPWO_support.mono (Set.iUnion_subset fun i => ?_),
    fun g => (Set.finite_singleton i₀).subset fun i hi => ?_⟩
  · by_cases hi : i = i₀
    · rw [hi]
    · rw [h i hi, support_zero]
      exact Set.empty_subset _
  · by_contra hne
    exact hi (by rw [h i hne, coeff_zero])

/-- The sum of two strongly summable families is strongly summable: its supports lie in the
union of the two support unions, and each exponent has finitely many contributors. -/
theorem stronglySummable_add {b c : ι → R⟦Γ⟧}
    (hb : StronglySummable b) (hc : StronglySummable c) : StronglySummable fun i => b i + c i := by
  obtain ⟨s, hs⟩ := hb
  obtain ⟨t, ht⟩ := hc
  exact ⟨s + t, fun i => by rw [SummableFamily.add_apply, hs, ht]⟩

end Blocks

section Domain

variable {Γ R : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]

section Semiring

variable [Semiring R]

/-- `hol:prop:closure`, addition, pointwise: `Dom(f) ∩ Dom(g) ⊆ Dom(f + g)`. -/
theorem mem_strongDomain_add {f g : PowerSeries R⟦Γ⟧} {x : R⟦Γ⟧} (hf : x ∈ strongDomain f)
    (hg : x ∈ strongDomain g) : x ∈ strongDomain (f + g) := by
  have h := stronglySummable_add (show StronglySummable fun n => PowerSeries.coeff n f * x ^ n
    from hf) (show StronglySummable fun n => PowerSeries.coeff n g * x ^ n from hg)
  show StronglySummable fun n => PowerSeries.coeff n (f + g) * x ^ n
  simp only [map_add, add_mul]
  exact h

/-- `hol:prop:closure`, constants, pointwise: a constant series `c` is strongly evaluable at
every `x`, that is `Dom(c) = K`. -/
theorem mem_strongDomain_C (c x : R⟦Γ⟧) : x ∈ strongDomain (PowerSeries.C c) := by
  show StronglySummable fun n => PowerSeries.coeff n (PowerSeries.C c) * x ^ n
  refine stronglySummable_of_eq_zero_of_ne 0 fun n hn => ?_
  rw [PowerSeries.coeff_C, if_neg hn, zero_mul]

end Semiring

section CommSemiring

variable [CommSemiring R]

/-- `hol:prop:closure`, scalar multiplication, pointwise: `Dom(f) ⊆ Dom(c f)` for every
`c ∈ K`. -/
theorem mem_strongDomain_smul (c : R⟦Γ⟧) {f : PowerSeries R⟦Γ⟧} {x : R⟦Γ⟧}
    (hf : x ∈ strongDomain f) : x ∈ strongDomain (c • f) := by
  have h := stronglySummable_const_mul
    (show StronglySummable fun n => PowerSeries.coeff n f * x ^ n from hf) c
  show StronglySummable fun n => PowerSeries.coeff n (c • f) * x ^ n
  simp only [PowerSeries.coeff_smul, smul_eq_mul, mul_assoc]
  exact h

/-- `hol:prop:closure`, multiplication, with the sum: if `(a_n x^n)` and `(b_n x^n)` are the
terms of summable families `s` and `t`, then the evaluation family of `fg` at `x` is the terms
of a summable family whose sum is `(∑ s) (∑ t)`. As in the source, it is the doubly indexed
product family, grouped by total degree (the last clause of `hol:lem:certificate`). -/
theorem exists_summableFamily_mul {f g : PowerSeries R⟦Γ⟧} {x : R⟦Γ⟧}
    (s t : SummableFamily Γ R ℕ) (hs : ∀ n, s n = PowerSeries.coeff n f * x ^ n)
    (ht : ∀ n, t n = PowerSeries.coeff n g * x ^ n) :
    ∃ u : SummableFamily Γ R ℕ,
      (∀ n, u n = PowerSeries.coeff n (f * g) * x ^ n) ∧ u.hsum = s.hsum * t.hsum := by
  refine ⟨blockFamily (s.mul t) (fun p : ℕ × ℕ => p.1 + p.2)
    Finset.HasAntidiagonal.antidiagonal (fun _ _ => Finset.HasAntidiagonal.mem_antidiagonal),
    fun n => ?_, ?_⟩
  · rw [blockFamily_apply, PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
    change s p.1 * t p.2 = _
    rw [hs, ht, pow_add]
    ring
  · rw [hsum_blockFamily, SummableFamily.hsum_mul]

/-- `hol:prop:closure`, multiplication, pointwise: `Dom(f) ∩ Dom(g) ⊆ Dom(fg)`. -/
theorem mem_strongDomain_mul {f g : PowerSeries R⟦Γ⟧} {x : R⟦Γ⟧} (hf : x ∈ strongDomain f)
    (hg : x ∈ strongDomain g) : x ∈ strongDomain (f * g) := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg
  obtain ⟨u, hu, -⟩ := exists_summableFamily_mul s t hs ht
  exact ⟨u, hu⟩

/-- `hol:prop:closure`, dilation, pointwise: `x ∈ Dom(σ_q f)` if and only if `qx ∈ Dom(f)`,
where `σ_q f(z) = f(qz)`; this holds for every `q`, including `q = 0`. -/
theorem mem_strongDomain_rescale_iff (q : R⟦Γ⟧) (f : PowerSeries R⟦Γ⟧) (x : R⟦Γ⟧) :
    x ∈ strongDomain (PowerSeries.rescale q f) ↔ q * x ∈ strongDomain f := by
  have h : (fun n => PowerSeries.coeff n (PowerSeries.rescale q f) * x ^ n) =
      fun n => PowerSeries.coeff n f * (q * x) ^ n :=
    funext fun n => by rw [PowerSeries.coeff_rescale, mul_pow]; ring
  exact Iff.of_eq (congrArg StronglySummable h)

/-- `hol:prop:closure`, differentiation, pointwise at a unit argument: if `x w = 1` and
`x ∈ Dom(f)`, then `x ∈ Dom(D_z f)`. The derivative family is
`(n + 1) a_{n+1} x^n = a_{n+1} x^{n+1} · ((n + 1) x⁻¹)`: one term is discarded, and the
multipliers `(n + 1) x⁻¹` all have support in `supp(x⁻¹)`. -/
theorem mem_strongDomain_derivative_of_mul_eq_one {f : PowerSeries R⟦Γ⟧} {x w : R⟦Γ⟧}
    (hw : x * w = 1) (hx : x ∈ strongDomain f) :
    x ∈ strongDomain (PowerSeries.derivative R⟦Γ⟧ f) := by
  have h1 := stronglySummable_comp_injective
    (show StronglySummable fun n => PowerSeries.coeff n f * x ^ n from hx)
    (e := fun n => n + 1) fun a b hab => Nat.succ_injective hab
  have hsupp : ∀ n : ℕ, (((n + 1 : ℕ) : R⟦Γ⟧) * w).support ⊆ w.support := by
    intro n γ hγ
    rw [mem_support] at hγ ⊢
    intro h0
    apply hγ
    rw [← nsmul_eq_mul, coeff_nsmul, Pi.smul_apply, h0, smul_zero]
  have h2 := stronglySummable_mul_of_support_subset h1 w.isPWO_support hsupp
  have heq : (fun n => PowerSeries.coeff n (PowerSeries.derivative R⟦Γ⟧ f) * x ^ n) =
      fun n => PowerSeries.coeff (n + 1) f * x ^ (n + 1) * (((n + 1 : ℕ) : R⟦Γ⟧) * w) := by
    funext n
    rw [PowerSeries.coeff_derivative, Nat.cast_succ]
    calc PowerSeries.coeff (n + 1) f * ((n : R⟦Γ⟧) + 1) * x ^ n
        = PowerSeries.coeff (n + 1) f * ((n : R⟦Γ⟧) + 1) * x ^ n * (x * w) := by
          rw [hw, mul_one]
      _ = _ := by ring
  show StronglySummable fun n => PowerSeries.coeff n (PowerSeries.derivative R⟦Γ⟧ f) * x ^ n
  rw [heq]
  exact h2

variable (Γ R) in
/-- `hol:prop:closure`: the class `E` of strongly entire series is an `R((t^Γ))`-subalgebra of
`R((t^Γ))[[z]]`, over any commutative semiring `R`. -/
def entireSubalgebra : Subalgebra R⟦Γ⟧ (PowerSeries R⟦Γ⟧) where
  carrier := {f | IsStronglyEntire f}
  mul_mem' hf hg := Set.eq_univ_of_forall fun x =>
    mem_strongDomain_mul (Set.eq_univ_iff_forall.mp hf x) (Set.eq_univ_iff_forall.mp hg x)
  add_mem' hf hg := Set.eq_univ_of_forall fun x =>
    mem_strongDomain_add (Set.eq_univ_iff_forall.mp hf x) (Set.eq_univ_iff_forall.mp hg x)
  algebraMap_mem' c := Set.eq_univ_of_forall fun x => mem_strongDomain_C c x

/-- Membership in `entireSubalgebra Γ R` is strong entireness (`hol:def:entire`). -/
theorem mem_entireSubalgebra {f : PowerSeries R⟦Γ⟧} :
    f ∈ entireSubalgebra Γ R ↔ IsStronglyEntire f :=
  Iff.rfl

/-- `hol:prop:closure`, dilation: `σ_q(E) ⊆ E`, for every `q ∈ K` (the source asks `q ≠ 0`). -/
theorem rescale_mem_entireSubalgebra (q : R⟦Γ⟧) {f : PowerSeries R⟦Γ⟧}
    (hf : f ∈ entireSubalgebra Γ R) : PowerSeries.rescale q f ∈ entireSubalgebra Γ R :=
  Set.eq_univ_of_forall fun x =>
    (mem_strongDomain_rescale_iff q f x).mpr (Set.eq_univ_iff_forall.mp hf _)

end CommSemiring

end Domain

section Derivative

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- `hol:prop:closure`, differentiation, pointwise over a field: `Dom(f) ⊆ Dom(D_z f)`. At
`x = 0` only the constant term contributes; for `x ≠ 0` the argument is a unit. -/
theorem mem_strongDomain_derivative {k : Type*} [Field k] {f : PowerSeries k⟦Γ⟧} {x : k⟦Γ⟧}
    (hx : x ∈ strongDomain f) : x ∈ strongDomain (PowerSeries.derivative k⟦Γ⟧ f) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact zero_mem_strongDomain _
  · exact mem_strongDomain_derivative_of_mul_eq_one (mul_inv_cancel₀ hx0) hx

variable {R : Type*} [CommSemiring R]

/-- `hol:prop:closure`, differentiation: `D_z(E) ⊆ E`, over any commutative semiring. By the
monomial test (`hol:lem:inward`) it suffices to evaluate at the monomials `t^γ`, which are
units. -/
theorem derivative_mem_entireSubalgebra {f : PowerSeries R⟦Γ⟧}
    (hf : f ∈ entireSubalgebra Γ R) :
    PowerSeries.derivative R⟦Γ⟧ f ∈ entireSubalgebra Γ R := by
  rw [mem_entireSubalgebra, isStronglyEntire_iff_forall_single_mem] at hf ⊢
  intro γ
  refine mem_strongDomain_derivative_of_mul_eq_one (w := single (-γ) 1) ?_ (hf γ)
  rw [single_mul_single, add_neg_cancel, mul_one, single_zero_one]

/-- `hol:prop:closure`, iterated differentiation: `D_z^r(E) ⊆ E` for every `r`. -/
theorem iterate_derivative_mem_entireSubalgebra {f : PowerSeries R⟦Γ⟧}
    (hf : f ∈ entireSubalgebra Γ R) (r : ℕ) :
    (⇑(PowerSeries.derivative R⟦Γ⟧))^[r] f ∈ entireSubalgebra Γ R := by
  induction r with
  | zero => exact hf
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact derivative_mem_entireSubalgebra ih

/-- `hol:prop:closure`: the class `E = entireSubalgebra Γ R` of strongly entire series
contains the constants and is closed under sums and products (it is an
`R((t^Γ))`-subalgebra of `R((t^Γ))[[z]]`), and it is stable under every dilation `σ_q` and
under `D_z`. Over a field of characteristic zero this is also the first sentence of
`hol:cf:prop:ring`. -/
theorem entireSubalgebra_closure :
    (∀ c : R⟦Γ⟧, PowerSeries.C c ∈ entireSubalgebra Γ R) ∧
      (∀ f ∈ entireSubalgebra Γ R, ∀ g ∈ entireSubalgebra Γ R,
        f + g ∈ entireSubalgebra Γ R ∧ f * g ∈ entireSubalgebra Γ R) ∧
      (∀ q : R⟦Γ⟧, ∀ f ∈ entireSubalgebra Γ R,
        PowerSeries.rescale q f ∈ entireSubalgebra Γ R) ∧
      ∀ f ∈ entireSubalgebra Γ R, PowerSeries.derivative R⟦Γ⟧ f ∈ entireSubalgebra Γ R :=
  ⟨fun c => Set.eq_univ_of_forall fun x => mem_strongDomain_C c x,
    fun _ hf _ hg => ⟨add_mem hf hg, mul_mem hf hg⟩,
    fun q _ hf => rescale_mem_entireSubalgebra q hf,
    fun _ hf => derivative_mem_entireSubalgebra hf⟩

end Derivative

end

end Surreal.EntireClosure
