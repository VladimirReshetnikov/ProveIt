import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.ContinuousMap.Compact
import Surreal.Algebra.GenericConstantPoint
import Surreal.HahnSeries.FiniteVisibility

/-!
# Valuation barriers for polynomial and continuous tests

This file formalizes `meas:thm:barrier`, the real form of `meas:cor:hermitianbarrier`,
`meas:cor:multivariate`, `meas:thm:continuousbarrier` (with `meas:eq:orderbound`) and the
valuation clause of `meas:lem:sumalgebra` of
`docs/surreal/hahn-valued-measures-and-probability/article.tex`.

As in `Surreal.FiniteVisibility`, the ordinary sample set `Ω ⊆ ℝ` is an index type `X`
with injective positions `e : X → K` in a linearly ordered commutative ring `K` (for
instance `K = ℝ`), a strong Hahn measure is represented by its strongly summable family of
point weights (`meas:thm:atomic`), and the exponents `Γ` form any linearly ordered
cancellative commutative monoid. The integral of a polynomial with Hahn coefficients is
`polyIntegral` of `meas:prop:integration`(iv).

* `meas:lem:sumalgebra`, valuation clause: a strong sum of nonnegative Hahn series with a
  nonzero summand has valuation `min_{f_i ≠ 0} v(f_i)` (`isLeast_orderTop_hsum`,
  `orderTop_hsum_le_of_nonneg`), for coefficients in any linearly ordered cancellative
  monoid.
* The earlier atom set `E_γ(ν) = {x | u_x > 0, v(u_x) < γ}` (`earlyAtoms`) and the
  condition that `τ` starts at scale `γ` (`StartsAt`).
* `meas:thm:barrier`: if `ν` is positive with `E_γ(ν)` infinite and `τ` is any signed
  measure starting at scale `γ`, then `L(P) = ∫ P dν + ∫ P dτ > 0` for every nonzero `P`
  with Hahn coefficients that is nonnegative at every sample point (`barrier`), and
  `L(P²) > 0` for every nonzero `P` (`barrier_sq`). The least valuation `δ` of the
  coefficients of `P` and the nonzero ordinary polynomial `p_δ` of its `t^δ` coefficients
  are `exists_least_coeffPoly` and `coeff_eval_C`. The common valuation argument, for
  arbitrary nonnegative Hahn values, is `barrier_of_values`. The statement for strong Hahn
  measures on a countably separated space is `measure_barrier`.
* `meas:cor:hermitianbarrier`, real form: for sample points in `[0, 1]` and
  `A, B ∈ K((t^Γ))[X]` not both zero, `L(R · (A² + B²)) > 0` for
  `R ∈ {1, X, 1 - X, X (1 - X)}` (`hermitianBarrier`); `L(A² + B²) > 0` holds without the
  `[0, 1]` hypothesis (`barrier_sq_add_sq`), and `A² + B² ≠ 0` is `sq_add_sq_ne_zero`.
* `meas:cor:multivariate`: for sample positions in `K^σ`, if no nonzero ordinary
  polynomial vanishes on all of `E_γ(ν)`, every nonzero `P ∈ K((t^Γ))[X_i : i ∈ σ]`
  nonnegative at the sample points has `L(P) > 0` (`mvBarrier`), and `L(P²) > 0` for every
  nonzero `P` (`mvBarrier_sq`), with the multivariate integral `mvPolyIntegral` built like
  `polyIntegral` (`mvPolyFamily_apply`) and the coefficient polynomials of
  `Surreal.GenericPoint`.
* `meas:thm:continuousbarrier`: if every atom of `τ` lies in the closure of `E_γ(ν)`, then
  `T(f) = ∫ f dν + ∫ f dτ ≥ 0` for every continuous `f ≥ 0` (`continuousBarrier`), on an
  arbitrary topological space with coefficients in any ordered ring whose points are
  closed. If `T(1) = 1` and `|f| ≤ M` then `-M ≤ T(f) ≤ M` (`continuousBarrier_bound`); on
  a compact space this is `meas:eq:orderbound`, `-‖f‖_∞ ≤ T(f) ≤ ‖f‖_∞` for
  `f ∈ C(Ω, ℝ)` (`continuousBarrier_norm_bound`). The statements for strong Hahn measures
  on a countably separated space are `measure_continuousBarrier` and
  `measure_continuousBarrier_norm_bound`, with `T(1) = ν(Ω) + τ(Ω)`.

The metrizability and Borel hypotheses of `meas:thm:continuousbarrier` are not used; only
countable separation is needed, and only for the passage from a strong Hahn measure to its
point weights. Pending: the complex form of `meas:cor:hermitianbarrier`, with `L` extended
complex-linearly to `K((t^Γ))[i][X]` and `P^*` conjugating coefficients, is not stated. The
source reduces it to the real form above through `P^* P = A² + B²` for `P = A + iB`; that
reduction is not formalized here. The Hermitian and multivariate corollaries are stated for
point weights only, not separately for strong Hahn measures as `measure_barrier` is.
-/

namespace Surreal.MeasureBarrier

open _root_.HahnSeries Surreal.HahnSeries Surreal.FiniteVisibility
open scoped Polynomial

noncomputable section

section SumValuation

variable {Γ R α : Type*} [LinearOrder Γ] [AddCommMonoid R] [LinearOrder R]
  [IsOrderedCancelAddMonoid R]

/-- The least-exponent argument of `meas:lem:sumalgebra`: for a strong sum of nonnegative
Hahn series with a nonzero member, the least exponent `α` of the union of the supports is
the valuation of some member, bounds every member's valuation from below, and is the
valuation of the sum. -/
theorem exists_least_exponent (s : SummableFamily Γ R α) (hs : ∀ a, 0 ≤ toLex (s a))
    (hne : ∃ a, s a ≠ 0) :
    ∃ g : Γ, (∀ a, (g : WithTop Γ) ≤ (s a).orderTop) ∧ (∃ a, (s a).orderTop = g) ∧
      s.hsum.orderTop = g := by
  classical
  have hwf : (⋃ a, (s a).support).IsWF := s.isPWO_iUnion_support.isWF
  obtain ⟨a₀, ha₀⟩ := hne
  have hne' : (⋃ a, (s a).support).Nonempty := by
    obtain ⟨i, hi⟩ := support_nonempty_iff.mpr ha₀
    exact ⟨i, Set.mem_iUnion.mpr ⟨a₀, hi⟩⟩
  set g := hwf.min hne'
  have hmin : ∀ a, ∀ j ∈ (s a).support, g ≤ j := fun a j hj =>
    hwf.min_le hne' (Set.mem_iUnion.mpr ⟨a, hj⟩)
  have hle : ∀ a, (g : WithTop Γ) ≤ (s a).orderTop := fun a =>
    le_orderTop_iff_forall.mpr fun j hj => by
      by_contra h
      exact (not_le.mpr (WithTop.coe_lt_coe.mp hj)) (hmin a j ((mem_support _ _).mpr h))
  -- Every nonzero coefficient at the least exponent is a positive leading coefficient.
  have hcoeff : ∀ a, (s a).coeff g ≠ 0 → 0 < (s a).coeff g := by
    intro a ha
    have hpos : 0 < toLex (s a) := by
      refine lt_of_le_of_ne (hs a) fun h => ha ?_
      rw [show s a = ofLex (toLex (s a)) from rfl, ← h]
      simp
    obtain ⟨i, hi, hlt⟩ := exists_coeff_pos_of_pos hpos
    rcases (hmin a i ((mem_support _ _).mpr hlt.ne')).lt_or_eq with h | h
    · exact absurd (hi g h) ha
    · exact h ▸ hlt
  obtain ⟨a₁, ha₁⟩ := Set.mem_iUnion.mp (hwf.min_mem hne')
  have ha₁' : (s a₁).coeff g ≠ 0 := (mem_support _ _).mp ha₁
  refine ⟨g, hle, ⟨a₁, orderTop_eq_of_le ha₁ (hmin a₁)⟩, ?_⟩
  have hsum : 0 < s.hsum.coeff g := by
    rw [SummableFamily.coeff_hsum_eq_sum]
    refine Finset.sum_pos' (fun a _ => ?_) ⟨a₁, ?_, hcoeff a₁ ha₁'⟩
    · by_cases ha : (s a).coeff g = 0
      · exact ha.ge
      · exact (hcoeff a ha).le
    · simpa [SummableFamily.coeff_def] using ha₁'
  refine orderTop_eq_of_le ((mem_support _ _).mpr hsum.ne') fun j hj => ?_
  by_contra hlt
  push Not at hlt
  apply (mem_support _ _).mp hj
  rw [SummableFamily.coeff_hsum]
  exact finsum_eq_zero_of_forall_eq_zero fun a =>
    coeff_eq_zero_of_lt_orderTop ((WithTop.coe_lt_coe.mpr hlt).trans_le (hle a))

/-- `meas:lem:sumalgebra`, valuation clause, upper bound: a strong sum of nonnegative Hahn
series has valuation at most the valuation of each summand. -/
theorem orderTop_hsum_le_of_nonneg (s : SummableFamily Γ R α) (hs : ∀ a, 0 ≤ toLex (s a))
    (a : α) : s.hsum.orderTop ≤ (s a).orderTop := by
  by_cases ha : s a = 0
  · simp [ha]
  obtain ⟨g, hle, -, hg⟩ := exists_least_exponent s hs ⟨a, ha⟩
  rw [hg]
  exact hle a

/-- `meas:lem:sumalgebra`, valuation clause: if a strong sum of nonnegative Hahn series has
a nonzero (equivalently, a positive) summand, then `v(∑ˢ_i f_i) = min_{f_i ≠ 0} v(f_i)`. -/
theorem isLeast_orderTop_hsum (s : SummableFamily Γ R α) (hs : ∀ a, 0 ≤ toLex (s a))
    (hne : ∃ a, s a ≠ 0) :
    IsLeast ((fun a => (s a).orderTop) '' {a | s a ≠ 0}) s.hsum.orderTop := by
  obtain ⟨g, hle, ⟨a₁, ha₁⟩, hg⟩ := exists_least_exponent s hs hne
  refine ⟨⟨a₁, ne_zero_of_coeff_ne_zero (coeff_orderTop_ne ha₁), ?_⟩, ?_⟩
  · change (s a₁).orderTop = _
    rw [ha₁, hg]
  rintro _ ⟨a, -, rfl⟩
  rw [hg]
  exact hle a

end SumValuation

section Lex

variable {Γ R : Type*} [LinearOrder Γ] [LinearOrder R]

/-- A lexicographically positive Hahn series is nonzero. -/
theorem ne_zero_of_toLex_pos [Zero R] {x : R⟦Γ⟧} (h : 0 < toLex x) : x ≠ 0 := by
  rintro rfl
  simp at h

/-- A nonnegative nonzero Hahn series is positive. -/
theorem toLex_pos_of_nonneg_of_ne_zero [Zero R] {x : R⟦Γ⟧} (h : 0 ≤ toLex x) (hx : x ≠ 0) :
    0 < toLex x := by
  refine lt_of_le_of_ne h fun h' => hx ?_
  rw [show x = ofLex (toLex x) from rfl, ← h']
  simp

/-- A tail of strictly larger valuation cannot change the sign of a positive Hahn series. -/
theorem pos_add_of_orderTop_lt [AddMonoid R] {a b : R⟦Γ⟧} (ha : 0 < toLex a)
    (h : a.orderTop < b.orderTop) : 0 < toLex (a + b) := by
  have ha' : 0 < a.leadingCoeff := leadingCoeff_pos_iff.mpr ha
  refine leadingCoeff_pos_iff.mp ?_
  change 0 < (a + b).leadingCoeff
  rwa [leadingCoeff_add_eq_left h]

end Lex

section CoeffPoly

variable {Γ K : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing K]

/-- The ordinary polynomial `p_g = ∑_j coeff_g(b_j) X^j` collecting the coefficients of
`t^g` in the Hahn coefficients `b_j` of `P = ∑_j b_j X^j`. -/
def coeffPoly (P : K⟦Γ⟧[X]) (g : Γ) : K[X] :=
  ∑ j ∈ P.support, Polynomial.monomial j ((P.coeff j).coeff g)

theorem coeff_coeffPoly (P : K⟦Γ⟧[X]) (g : Γ) (j : ℕ) :
    (coeffPoly P g).coeff j = (P.coeff j).coeff g := by
  classical
  simp only [coeffPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Finset.sum_ite_eq', Polynomial.mem_support_iff]
  split_ifs with h
  · rfl
  · rw [not_not.mp h, coeff_zero]

/-- At an ordinary sample point, the coefficient of `t^g` in `P(x)` is `p_g(x)`. -/
theorem coeff_eval_C (P : K⟦Γ⟧[X]) (x : K) (g : Γ) :
    (P.eval (HahnSeries.C x)).coeff g = (coeffPoly P g).eval x := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, _root_.HahnSeries.coeff_sum, coeffPoly,
    Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_monomial, ← map_pow, mul_comm (P.coeff j), C_mul_eq_smul, coeff_smul,
    smul_eq_mul, mul_comm]

end CoeffPoly

section LeastCoeffPoly

variable {Γ K : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing K]

/-- The least valuation `δ` of the nonzero coefficients of a nonzero Hahn-coefficient
polynomial: its coefficient polynomial `p_δ` is a nonzero ordinary polynomial, and all
coefficient polynomials below `δ` vanish. -/
theorem exists_least_coeffPoly {P : K⟦Γ⟧[X]} (hP : P ≠ 0) :
    ∃ δ : Γ, coeffPoly P δ ≠ 0 ∧ ∀ g < δ, coeffPoly P g = 0 := by
  obtain ⟨j₀, hj₀, hmin⟩ := P.support.exists_min_image (fun j => (P.coeff j).orderTop)
    (Polynomial.nonempty_support_iff.mpr hP)
  obtain ⟨δ, hδ⟩ := exists_orderTop_eq_of_ne_zero (Polynomial.mem_support_iff.mp hj₀)
  refine ⟨δ, fun h => coeff_orderTop_ne hδ ?_, fun g hg => Polynomial.ext fun j => ?_⟩
  · rw [← coeff_coeffPoly, h, Polynomial.coeff_zero]
  · rw [coeff_coeffPoly, Polynomial.coeff_zero]
    by_cases hj : j ∈ P.support
    · have h := hmin j hj
      rw [hδ] at h
      exact coeff_eq_zero_of_lt_orderTop ((WithTop.coe_lt_coe.mpr hg).trans_le h)
    · rw [Polynomial.notMem_support_iff.mp hj, coeff_zero]

end LeastCoeffPoly

section Defs

variable {Γ K X : Type*} [LinearOrder Γ] [AddCommMonoid K]

/-- The earlier atom set `E_γ(ν) = {x | u_x > 0, v(u_x) < γ}` of a measure with point
weights `u`. -/
def earlyAtoms [LinearOrder K] (u : SummableFamily Γ K X) (γ : Γ) : Set X :=
  {x | 0 < toLex (u x) ∧ (u x).orderTop < γ}

theorem mem_earlyAtoms [LinearOrder K] {u : SummableFamily Γ K X} {γ : Γ} {x : X} :
    x ∈ earlyAtoms u γ ↔ 0 < toLex (u x) ∧ (u x).orderTop < γ :=
  Iff.rfl

/-- A signed measure with point weights `τ` starts at scale `γ` if every nonzero point
weight has valuation at least `γ`. -/
def StartsAt (τ : SummableFamily Γ K X) (γ : Γ) : Prop :=
  ∀ x, τ x ≠ 0 → (γ : WithTop Γ) ≤ (τ x).orderTop

/-- Zero weights have valuation `⊤`, so a measure starting at scale `γ` has every point
weight of valuation at least `γ`. -/
theorem StartsAt.le {τ : SummableFamily Γ K X} {γ : Γ} (h : StartsAt τ γ) (x : X) :
    (γ : WithTop Γ) ≤ (τ x).orderTop := by
  by_cases hx : τ x = 0
  · simp [hx]
  · exact h x hx

end Defs

section Barrier

variable {Γ K X : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The valuation argument shared by `meas:thm:barrier` and `meas:thm:continuousbarrier`.
Let `F x` be nonnegative Hahn values of valuation at least `δ`, with valuation exactly `δ`
at an early atom `x₀ ∈ E_γ(ν)`. Then `∑ˢ_x F x u_x` is positive with valuation below
`δ + γ`, while `∑ˢ_x F x τ_x` has valuation at least `δ + γ`, so their sum is positive. -/
theorem barrier_of_values (u τ : SummableFamily Γ K X) {γ : Γ} (hu : ∀ x, 0 ≤ toLex (u x))
    (hτ : StartsAt τ γ) (F : X → K⟦Γ⟧) (s t : SummableFamily Γ K X)
    (hs : ∀ x, s x = F x * u x) (ht : ∀ x, t x = F x * τ x) (hF : ∀ x, 0 ≤ toLex (F x))
    {δ : Γ} (hδ : ∀ x, (δ : WithTop Γ) ≤ (F x).orderTop) {x₀ : X}
    (hx₀ : x₀ ∈ earlyAtoms u γ) (hFx₀ : (F x₀).orderTop = δ) :
    0 < toLex (s.hsum + t.hsum) := by
  obtain ⟨hux₀, hvx₀⟩ := hx₀
  have hsnn : ∀ x, 0 ≤ toLex (s x) := fun x => by
    rw [hs, toLex_mul]
    exact mul_nonneg (hF x) (hu x)
  have hFpos : 0 < toLex (F x₀) :=
    toLex_pos_of_nonneg_of_ne_zero (hF x₀) (ne_zero_of_coeff_ne_zero (coeff_orderTop_ne hFx₀))
  have hsx₀ : 0 < toLex (s x₀) := by
    rw [hs, toLex_mul]
    exact mul_pos hFpos hux₀
  obtain ⟨β, hβ⟩ := exists_orderTop_eq_of_ne_zero (ne_zero_of_toLex_pos hux₀)
  have hS : s.hsum.orderTop < ((δ + γ : Γ) : WithTop Γ) := by
    refine (orderTop_hsum_le_of_nonneg s hsnn x₀).trans_lt ?_
    rw [hs, orderTop_mul, hFx₀, hβ, ← WithTop.coe_add, WithTop.coe_lt_coe,
      add_lt_add_iff_left]
    rw [hβ] at hvx₀
    exact WithTop.coe_lt_coe.mp hvx₀
  have hT : ((δ + γ : Γ) : WithTop Γ) ≤ t.hsum.orderTop := by
    refine le_orderTop_iff_forall.mpr fun j hj => ?_
    rw [SummableFamily.coeff_hsum]
    refine finsum_eq_zero_of_forall_eq_zero fun x =>
      coeff_eq_zero_of_lt_orderTop (hj.trans_le ?_)
    rw [ht, WithTop.coe_add]
    exact (add_le_add (hδ x) (hτ.le x)).trans orderTop_add_le_mul
  exact pos_add_of_orderTop_lt (hsum_pos s hsnn hsx₀) (hS.trans_le hT)

/-- `meas:thm:barrier`: let `ν` be a positive strong measure with point weights `u` whose
earlier atom set `E_γ(ν)` is infinite, let `τ` be any signed strong measure starting at
scale `γ`, and let `L(P) = ∫ P dν + ∫ P dτ`. Every nonzero polynomial `P` with Hahn
coefficients that is nonnegative at every ordinary sample point has `L(P) > 0`. The sample
points are the injective positions `e : X → K`; no sign assumption is made on `τ`. -/
theorem barrier (u τ : SummableFamily Γ K X) {e : X → K} (he : Function.Injective e)
    {γ : Γ} (hu : ∀ x, 0 ≤ toLex (u x)) (hinf : (earlyAtoms u γ).Infinite)
    (hτ : StartsAt τ γ) {P : K⟦Γ⟧[X]} (hP : P ≠ 0)
    (hPpos : ∀ x, 0 ≤ toLex (P.eval (HahnSeries.C (e x)))) :
    0 < toLex (polyIntegral u e P + polyIntegral τ e P) := by
  obtain ⟨δ, hδ, hlow⟩ := exists_least_coeffPoly hP
  have hroots : {x | (coeffPoly P δ).eval (e x) = 0}.Finite :=
    (Polynomial.finite_setOf_isRoot hδ).preimage he.injOn
  obtain ⟨x₀, hx₀E, hx₀⟩ := (hinf.sdiff hroots).nonempty
  refine barrier_of_values u τ hu hτ (fun x => P.eval (HahnSeries.C (e x))) _ _
    (polyFamily_apply u e P) (polyFamily_apply τ e P) hPpos (δ := δ) (fun x => ?_) hx₀E ?_
  · refine le_orderTop_iff_forall.mpr fun j hj => ?_
    rw [coeff_eval_C, hlow j (WithTop.coe_lt_coe.mp hj), Polynomial.eval_zero]
  · refine orderTop_eq_of_le ?_ fun j hj => ?_
    · rw [mem_support, coeff_eval_C]
      exact hx₀
    · by_contra hlt
      push Not at hlt
      rw [mem_support, coeff_eval_C, hlow j hlt, Polynomial.eval_zero] at hj
      exact hj rfl

/-- `meas:thm:barrier`, squares: `L(P²) > 0` for every nonzero `P` with Hahn
coefficients. -/
theorem barrier_sq (u τ : SummableFamily Γ K X) {e : X → K} (he : Function.Injective e)
    {γ : Γ} (hu : ∀ x, 0 ≤ toLex (u x)) (hinf : (earlyAtoms u γ).Infinite)
    (hτ : StartsAt τ γ) {P : K⟦Γ⟧[X]} (hP : P ≠ 0) :
    0 < toLex (polyIntegral u e (P ^ 2) + polyIntegral τ e (P ^ 2)) :=
  barrier u τ he hu hinf hτ (pow_ne_zero 2 hP) fun x => by
    rw [Polynomial.eval_pow, toLex_pow]
    exact sq_nonneg _

/-- Nonnegative ordinary constants are nonnegative Hahn series. -/
theorem toLex_C_nonneg {c : K} (hc : 0 ≤ c) : 0 ≤ toLex (HahnSeries.C c : K⟦Γ⟧) := by
  rw [← mul_one (HahnSeries.C c), C_mul_eq_smul]
  refine smul_nonneg_toLex hc ?_
  rw [toLex_one]
  exact zero_le_one

/-- Over an ordered coefficient ring, `A² + B²` vanishes only when `A = B = 0`: at a point
where `A` does not vanish, `A(c)² + B(c)²` is positive. -/
theorem sq_add_sq_ne_zero {A B : K⟦Γ⟧[X]} (hAB : A ≠ 0 ∨ B ≠ 0) : A ^ 2 + B ^ 2 ≠ 0 := by
  haveI : Infinite K⟦Γ⟧ := Infinite.of_injective (fun n : ℕ => HahnSeries.C (n : K))
    (C_injective.comp Nat.cast_injective)
  have key : ∀ A B : K⟦Γ⟧[X], A ≠ 0 → A ^ 2 + B ^ 2 ≠ 0 := by
    intro A B hA hQ
    obtain ⟨c, hc⟩ : ∃ c, A.eval c ≠ 0 := by
      by_contra h
      push Not at h
      exact hA (Polynomial.funext fun r => by rw [h r, Polynomial.eval_zero])
    have hpos : 0 < toLex ((A ^ 2 + B ^ 2).eval c) := by
      rw [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_pow, toLex_add, toLex_pow,
        toLex_pow]
      exact add_pos_of_pos_of_nonneg
        (sq_pos_of_ne_zero (show toLex (A.eval c) ≠ 0 from toLex.injective.ne hc))
        (sq_nonneg _)
    rw [hQ, Polynomial.eval_zero] at hpos
    exact lt_irrefl _ hpos
  rcases hAB with hA | hB
  · exact key A B hA
  · rw [add_comm]
    exact key B A hB

end Barrier

section Hermitian

variable {Γ K X : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- `meas:thm:barrier` applied to `R · (A² + B²)` for a nonzero localizing multiplier `R`
that is nonnegative at the sample points. -/
theorem barrier_mul_sq_add_sq (u τ : SummableFamily Γ K X) {e : X → K}
    (he : Function.Injective e) {γ : Γ} (hu : ∀ x, 0 ≤ toLex (u x))
    (hinf : (earlyAtoms u γ).Infinite) (hτ : StartsAt τ γ) {A B R : K⟦Γ⟧[X]}
    (hAB : A ≠ 0 ∨ B ≠ 0) (hR : R ≠ 0)
    (hRpos : ∀ x, 0 ≤ toLex (R.eval (HahnSeries.C (e x)))) :
    0 < toLex (polyIntegral u e (R * (A ^ 2 + B ^ 2)) +
      polyIntegral τ e (R * (A ^ 2 + B ^ 2))) :=
  barrier u τ he hu hinf hτ (mul_ne_zero hR (sq_add_sq_ne_zero hAB)) fun x => by
    rw [Polynomial.eval_mul, toLex_mul, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_pow, toLex_add, toLex_pow, toLex_pow]
    exact mul_nonneg (hRpos x) (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- `meas:cor:hermitianbarrier`, real form, `R = 1` case written without the factor `1`:
under the hypotheses of `meas:thm:barrier`, `L(A² + B²) > 0` for `A, B ∈ K((t^Γ))[X]` not
both zero. No hypothesis on the position of the sample points is needed. -/
theorem barrier_sq_add_sq (u τ : SummableFamily Γ K X) {e : X → K}
    (he : Function.Injective e) {γ : Γ} (hu : ∀ x, 0 ≤ toLex (u x))
    (hinf : (earlyAtoms u γ).Infinite) (hτ : StartsAt τ γ) {A B : K⟦Γ⟧[X]}
    (hAB : A ≠ 0 ∨ B ≠ 0) :
    0 < toLex (polyIntegral u e (A ^ 2 + B ^ 2) + polyIntegral τ e (A ^ 2 + B ^ 2)) :=
  barrier u τ he hu hinf hτ (sq_add_sq_ne_zero hAB) fun x => by
    rw [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_pow, toLex_add, toLex_pow,
      toLex_pow]
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- `meas:cor:hermitianbarrier`, real form: suppose the sample points lie in `[0, 1]` and the
hypotheses of `meas:thm:barrier` hold. For `A, B ∈ K((t^Γ))[X]` not both zero,
`L(R · (A² + B²)) > 0` for each localizing multiplier `R ∈ {1, X, 1 - X, X (1 - X)}` (for
`R = 1` the statement reads `L(1 · (A² + B²))`; see `barrier_sq_add_sq`). The source's
complex statement, positivity of `L(P^* P)`, `L(X P^* P)`, `L((1 - X) P^* P)` and
`L(X (1 - X) P^* P)` for nonzero `P ∈ K_C[X]`, reduces to this through `P^* P = A² + B²`
for `P = A + iB`; that reduction is not formalized here. -/
theorem hermitianBarrier (u τ : SummableFamily Γ K X) {e : X → K}
    (he : Function.Injective e) {γ : Γ} (hu : ∀ x, 0 ≤ toLex (u x))
    (hinf : (earlyAtoms u γ).Infinite) (hτ : StartsAt τ γ) (hΩ : ∀ x, 0 ≤ e x ∧ e x ≤ 1)
    {A B : K⟦Γ⟧[X]} (hAB : A ≠ 0 ∨ B ≠ 0) :
    ∀ R ∈ ({1, Polynomial.X, 1 - Polynomial.X, Polynomial.X * (1 - Polynomial.X)} :
      Set K⟦Γ⟧[X]), 0 < toLex (polyIntegral u e (R * (A ^ 2 + B ^ 2)) +
        polyIntegral τ e (R * (A ^ 2 + B ^ 2))) := by
  have hX : ∀ x, 0 ≤ toLex ((Polynomial.X : K⟦Γ⟧[X]).eval (HahnSeries.C (e x))) :=
    fun x => by
      rw [Polynomial.eval_X]
      exact toLex_C_nonneg (hΩ x).1
  have h1X : ∀ x, 0 ≤ toLex ((1 - Polynomial.X : K⟦Γ⟧[X]).eval (HahnSeries.C (e x))) :=
    fun x => by
      rw [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X, ← map_one HahnSeries.C,
        ← map_sub]
      exact toLex_C_nonneg (sub_nonneg.mpr (hΩ x).2)
  have h1Xne : (1 - Polynomial.X : K⟦Γ⟧[X]) ≠ 0 := fun h => by
    have := congrArg (Polynomial.eval 0) h
    simp at this
  intro R hR
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hR
  rcases hR with rfl | rfl | rfl | rfl
  · refine barrier_mul_sq_add_sq u τ he hu hinf hτ hAB one_ne_zero fun x => ?_
    rw [Polynomial.eval_one, toLex_one]
    exact zero_le_one
  · exact barrier_mul_sq_add_sq u τ he hu hinf hτ hAB Polynomial.X_ne_zero hX
  · exact barrier_mul_sq_add_sq u τ he hu hinf hτ hAB h1Xne h1X
  · refine barrier_mul_sq_add_sq u τ he hu hinf hτ hAB (mul_ne_zero Polynomial.X_ne_zero h1Xne)
      fun x => ?_
    rw [Polynomial.eval_mul, toLex_mul]
    exact mul_nonneg (hX x) (h1X x)

end Hermitian

section MvIntegral

variable {Γ K X σ : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing K]

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
/-- Members of a finite sum of strongly summable families are the finite sums of members. -/
theorem summableFamily_finsetSum_apply {ι : Type*} (s : Finset ι)
    (F : ι → SummableFamily Γ K X) (x : X) : (∑ j ∈ s, F j) x = ∑ j ∈ s, F j x := by
  classical
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, SummableFamily.zero_apply]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, SummableFamily.add_apply, ih]

/-- The family `(P(e x) w_x)_x` for a polynomial `P = ∑_m b_m X^m` in several variables with
Hahn coefficients and sample positions `e x ∈ K^σ`: the finite sum over `m` of the products
of `b_m` with the strongly summable families `((e x)^m w_x)_x`. -/
def mvPolyFamily (w : SummableFamily Γ K X) (e : X → σ → K) (P : MvPolynomial σ K⟦Γ⟧) :
    SummableFamily Γ K X :=
  ∑ m ∈ P.support,
    P.coeff m • SummableFamily.smulFamily (fun x => ∏ i ∈ m.support, e x i ^ m i) w

/-- The members of `mvPolyFamily` are the products `P(e x) w_x`. -/
theorem mvPolyFamily_apply (w : SummableFamily Γ K X) (e : X → σ → K)
    (P : MvPolynomial σ K⟦Γ⟧) (x : X) :
    mvPolyFamily w e P x = MvPolynomial.eval (fun i => HahnSeries.C (e x i)) P * w x := by
  rw [mvPolyFamily, summableFamily_finsetSum_apply, MvPolynomial.eval_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hsf : SummableFamily.smulFamily (fun x => ∏ i ∈ m.support, e x i ^ m i) w x =
      (∏ i ∈ m.support, e x i ^ m i) • w x := rfl
  rw [SummableFamily.smul_apply, of_symm_smul_of_eq_mul, hsf, ← C_mul_eq_smul, map_prod]
  simp only [map_pow, mul_assoc]

/-- The multivariate integral `L(P) = ∫ P dμ = ∑ˢ_x P(e x) w_x`. -/
def mvPolyIntegral (w : SummableFamily Γ K X) (e : X → σ → K) (P : MvPolynomial σ K⟦Γ⟧) :
    K⟦Γ⟧ :=
  (mvPolyFamily w e P).hsum

end MvIntegral

section MvBarrier

variable {Γ K X σ : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- `meas:cor:multivariate`: for sample positions `e x ∈ K^σ` (for instance `Ω ⊆ ℝ^d`),
replace the infinitude of `E_γ(ν)` by the condition that no nonzero ordinary polynomial
vanishes on all of `E_γ(ν)`. Then every nonzero `P` in `K((t^Γ))[X_i : i ∈ σ]` that is
nonnegative at every sample point has `L(P) = ∫ P dν + ∫ P dτ > 0`, with the same proof as
`meas:thm:barrier`. -/
theorem mvBarrier (u τ : SummableFamily Γ K X) {e : X → σ → K} {γ : Γ}
    (hu : ∀ x, 0 ≤ toLex (u x)) (hτ : StartsAt τ γ)
    (hZ : ∀ p : MvPolynomial σ K, p ≠ 0 → ∃ x ∈ earlyAtoms u γ, MvPolynomial.eval (e x) p ≠ 0)
    {P : MvPolynomial σ K⟦Γ⟧} (hP : P ≠ 0)
    (hPpos : ∀ x, 0 ≤ toLex (MvPolynomial.eval (fun i => HahnSeries.C (e x i)) P)) :
    0 < toLex (mvPolyIntegral u e P + mvPolyIntegral τ e P) := by
  obtain ⟨δ, -, hδ, hlow⟩ := GenericPoint.exists_isLeast_coeffPoly hP
  obtain ⟨x₀, hx₀E, hx₀⟩ := hZ _ hδ
  refine barrier_of_values u τ hu hτ (fun x => MvPolynomial.eval (fun i => HahnSeries.C (e x i)) P)
    _ _ (mvPolyFamily_apply u e P) (mvPolyFamily_apply τ e P) hPpos (δ := δ) (fun x => ?_)
    hx₀E ?_
  · refine le_orderTop_iff_forall.mpr fun j hj => ?_
    rw [GenericPoint.coeff_eval_C, hlow j (WithTop.coe_lt_coe.mp hj), map_zero]
  · refine orderTop_eq_of_le ?_ fun j hj => ?_
    · rw [mem_support, GenericPoint.coeff_eval_C]
      exact hx₀
    · by_contra hlt
      push Not at hlt
      rw [mem_support, GenericPoint.coeff_eval_C, hlow j hlt, map_zero] at hj
      exact hj rfl

/-- `meas:cor:multivariate`, squares: under the hypotheses of `mvBarrier`,
`L(P²) = ∫ P² dν + ∫ P² dτ > 0` for every nonzero `P` in `K((t^Γ))[X_i : i ∈ σ]`, the
multivariate form of the square clause of `meas:thm:barrier`. -/
theorem mvBarrier_sq (u τ : SummableFamily Γ K X) {e : X → σ → K} {γ : Γ}
    (hu : ∀ x, 0 ≤ toLex (u x)) (hτ : StartsAt τ γ)
    (hZ : ∀ p : MvPolynomial σ K, p ≠ 0 → ∃ x ∈ earlyAtoms u γ, MvPolynomial.eval (e x) p ≠ 0)
    {P : MvPolynomial σ K⟦Γ⟧} (hP : P ≠ 0) :
    0 < toLex (mvPolyIntegral u e (P ^ 2) + mvPolyIntegral τ e (P ^ 2)) :=
  mvBarrier u τ hu hτ hZ (pow_ne_zero 2 hP) fun x => by
    rw [map_pow, toLex_pow]
    exact sq_nonneg _

end MvBarrier

section Continuous

variable {Γ K X : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing K] [LinearOrder K] [IsStrictOrderedRing K] [TopologicalSpace X]
  [TopologicalSpace K] [T1Space K]

/-- `meas:thm:continuousbarrier`, positivity: let `ν` be a positive strong measure with point
weights `u`, let `τ` start at scale `γ`, and assume every atom of `τ` lies in the closure of
`E_γ(ν)`. Then `T(f) = ∫ f dν + ∫ f dτ ≥ 0` for every continuous `f ≥ 0`. The space `X` is
an arbitrary topological space and the coefficients any ordered ring with closed points. -/
theorem continuousBarrier (u τ : SummableFamily Γ K X) {γ : Γ} (hu : ∀ x, 0 ≤ toLex (u x))
    (hτ : StartsAt τ γ) (hcl : {x | τ x ≠ 0} ⊆ closure (earlyAtoms u γ)) {f : X → K}
    (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) :
    0 ≤ toLex (atomicIntegral u f + atomicIntegral τ f) := by
  by_cases h : ∃ x ∈ earlyAtoms u γ, f x ≠ 0
  · obtain ⟨x₀, hx₀, hfx₀⟩ := h
    refine (barrier_of_values u τ hu hτ (fun x => HahnSeries.C (f x))
      (SummableFamily.smulFamily f u) (SummableFamily.smulFamily f τ)
      (fun x => (C_mul_eq_smul (r := f x) (x := u x)).symm)
      (fun x => (C_mul_eq_smul (r := f x) (x := τ x)).symm)
      (fun x => toLex_C_nonneg (hf0 x)) (δ := 0) (fun x => ?_) hx₀ ?_).le
    · by_cases hx : f x = 0
      · simp [hx]
      · rw [C_apply, orderTop_single hx]
    · rw [C_apply, orderTop_single hfx₀]
  · push Not at h
    have hzero : closure (earlyAtoms u γ) ⊆ f ⁻¹' {0} :=
      closure_minimal (fun x hx => h x hx) (isClosed_singleton.preimage hf)
    have hτ0 : atomicIntegral τ f = 0 := by
      ext g
      rw [coeff_atomicIntegral, coeff_zero]
      refine finsum_eq_zero_of_forall_eq_zero fun x => ?_
      by_cases hx : τ x = 0
      · rw [hx, coeff_zero, mul_zero]
      · rw [show f x = 0 from hzero (hcl hx), zero_mul]
    rw [hτ0, add_zero]
    exact atomicIntegral_nonneg u hu hf0

/-- `meas:eq:orderbound` of `meas:thm:continuousbarrier` for a bounded continuous function:
if `T(1) = 1` and `|f| ≤ M` with `M` an ordinary scalar, then `-M ≤ T(f) ≤ M`. Positivity
is applied to `M ± f`. -/
theorem continuousBarrier_bound [IsTopologicalRing K] (u τ : SummableFamily Γ K X) {γ : Γ}
    (hu : ∀ x, 0 ≤ toLex (u x)) (hτ : StartsAt τ γ)
    (hcl : {x | τ x ≠ 0} ⊆ closure (earlyAtoms u γ))
    (h1 : atomicIntegral u 1 + atomicIntegral τ 1 = 1) {f : X → K} (hf : Continuous f)
    {M : K} (hM : ∀ x, |f x| ≤ M) :
    toLex (HahnSeries.C (-M)) ≤ toLex (atomicIntegral u f + atomicIntegral τ f) ∧
      toLex (atomicIntegral u f + atomicIntegral τ f) ≤ toLex (HahnSeries.C M) := by
  have hlin : ∀ d : K, atomicIntegral u (fun x => M + d * f x) +
      atomicIntegral τ (fun x => M + d * f x) =
        HahnSeries.C M + d • (atomicIntegral u f + atomicIntegral τ f) := by
    intro d
    have hfun : (fun x => M + d * f x) = (fun x => M * (1 : X → K) x) + fun x => d * f x := by
      funext x
      simp
    have hC : HahnSeries.C M = M • (atomicIntegral u 1 + atomicIntegral τ 1) := by
      rw [h1, ← C_mul_eq_smul, mul_one]
    rw [hfun, atomicIntegral_add, atomicIntegral_add, atomicIntegral_const_mul,
      atomicIntegral_const_mul, atomicIntegral_const_mul, atomicIntegral_const_mul, hC,
      smul_add, smul_add]
    abel
  have hpos : ∀ d : K, (∀ x, 0 ≤ M + d * f x) →
      0 ≤ toLex (HahnSeries.C M + d • (atomicIntegral u f + atomicIntegral τ f)) := by
    intro d hd
    rw [← hlin d]
    exact continuousBarrier u τ hu hτ hcl (continuous_const.add (continuous_const.mul hf)) hd
  constructor
  · have h := hpos 1 fun x => by
      rw [one_mul]
      exact neg_le_iff_add_nonneg'.mp ((neg_le_neg (hM x)).trans (neg_abs_le (f x)))
    rw [one_smul, toLex_add] at h
    rw [map_neg, toLex_neg]
    exact neg_le_iff_add_nonneg'.mpr h
  · have h := hpos (-1) fun x => by
      rw [neg_one_mul, ← sub_eq_add_neg, sub_nonneg]
      exact (le_abs_self (f x)).trans (hM x)
    rw [neg_one_smul, toLex_add, toLex_neg, ← sub_eq_add_neg, sub_nonneg] at h
    exact h

end Continuous

section Real

variable {Γ X : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [TopologicalSpace X] [CompactSpace X]

/-- `meas:eq:orderbound` of `meas:thm:continuousbarrier`: on a compact space with
`T(1) = 1`, every real continuous function satisfies `-‖f‖_∞ ≤ T(f) ≤ ‖f‖_∞`, an
ordered-field inequality with the ordinary real sup norm. -/
theorem continuousBarrier_norm_bound (u τ : SummableFamily Γ ℝ X) {γ : Γ}
    (hu : ∀ x, 0 ≤ toLex (u x)) (hτ : StartsAt τ γ)
    (hcl : {x | τ x ≠ 0} ⊆ closure (earlyAtoms u γ))
    (h1 : atomicIntegral u 1 + atomicIntegral τ 1 = 1) (f : C(X, ℝ)) :
    toLex (HahnSeries.C (-‖f‖)) ≤ toLex (atomicIntegral u f + atomicIntegral τ f) ∧
      toLex (atomicIntegral u f + atomicIntegral τ f) ≤ toLex (HahnSeries.C ‖f‖) :=
  continuousBarrier_bound u τ hu hτ hcl h1 f.continuous fun x => by
    rw [← Real.norm_eq_abs]
    exact f.norm_coe_le_norm x

end Real

section Measure

variable {Γ K X : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing K] [LinearOrder K] [IsStrictOrderedRing K] [MeasurableSpace X]
  {ν τ : Set X → K⟦Γ⟧}

/-- `meas:thm:barrier` for strong Hahn measures on a countably separated space: `ν` is
positive with infinitely many atoms `x` of `ν({x}) > 0` and `v(ν({x})) < γ`, every nonzero
atom of `τ` has valuation at least `γ`, and `L(P) = ∫ P dν + ∫ P dτ` integrates against the
point weights of `meas:thm:atomic`. Then `L(P) > 0` for every nonzero `P` nonnegative at the
sample points. -/
theorem measure_barrier (hν : IsStrongHahnMeasure ν) (hτ : IsStrongHahnMeasure τ)
    (hX : IsCountablySeparated X) (hνpos : ∀ A, MeasurableSet A → 0 ≤ toLex (ν A))
    {e : X → K} (he : Function.Injective e) {γ : Γ}
    (hinf : {x | 0 < toLex (ν {x}) ∧ (ν {x}).orderTop < γ}.Infinite)
    (hstart : ∀ x, τ {x} ≠ 0 → (γ : WithTop Γ) ≤ (τ {x}).orderTop) {P : K⟦Γ⟧[X]}
    (hP : P ≠ 0) (hPpos : ∀ x, 0 ≤ toLex (P.eval (HahnSeries.C (e x)))) :
    0 < toLex (polyIntegral (strongWeights hν hX) e P +
      polyIntegral (strongWeights hτ hX) e P) :=
  barrier (strongWeights hν hX) (strongWeights hτ hX) he
    ((nonneg_iff_strongWeights hν hX).mp hνpos) hinf hstart hP hPpos

/-- `meas:thm:continuousbarrier`, positivity, for strong Hahn measures on a countably
separated topological space: if every atom of `τ` lies in the closure of
`E_γ(ν) = {x | ν({x}) > 0, v(ν({x})) < γ}`, then `∫ f dν + ∫ f dτ ≥ 0` for every
continuous `f ≥ 0`. -/
theorem measure_continuousBarrier [TopologicalSpace X] [TopologicalSpace K] [T1Space K]
    (hν : IsStrongHahnMeasure ν) (hτ : IsStrongHahnMeasure τ) (hX : IsCountablySeparated X)
    (hνpos : ∀ A, MeasurableSet A → 0 ≤ toLex (ν A)) {γ : Γ}
    (hstart : ∀ x, τ {x} ≠ 0 → (γ : WithTop Γ) ≤ (τ {x}).orderTop)
    (hcl : {x | τ {x} ≠ 0} ⊆ closure {x | 0 < toLex (ν {x}) ∧ (ν {x}).orderTop < γ})
    {f : X → K} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) :
    0 ≤ toLex (atomicIntegral (strongWeights hν hX) f +
      atomicIntegral (strongWeights hτ hX) f) :=
  continuousBarrier (strongWeights hν hX) (strongWeights hτ hX)
    ((nonneg_iff_strongWeights hν hX).mp hνpos) hstart hcl hf hf0

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [LinearOrder K] [IsStrictOrderedRing K] in
/-- The integral of the constant function `1` against the point weights of a strong Hahn
measure is its total mass. -/
theorem atomicIntegral_one_strongWeights (hν : IsStrongHahnMeasure ν)
    (hX : IsCountablySeparated X) : atomicIntegral (strongWeights hν hX) 1 = ν Set.univ := by
  rw [eq_atomicMeasure_strongWeights hν hX MeasurableSet.univ, ← atomicIntegral_indicator,
    Set.indicator_univ]

end Measure

section MeasureReal

variable {Γ X : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X] {ν τ : Set X → ℝ⟦Γ⟧}

/-- `meas:thm:continuousbarrier`, order bound, for strong Hahn measures on a compact
countably separated space: if `T(1) = ν(Ω) + τ(Ω) = 1`, then `-‖f‖_∞ ≤ T(f) ≤ ‖f‖_∞` for
every `f ∈ C(Ω, ℝ)`. -/
theorem measure_continuousBarrier_norm_bound (hν : IsStrongHahnMeasure ν)
    (hτ : IsStrongHahnMeasure τ) (hX : IsCountablySeparated X)
    (hνpos : ∀ A, MeasurableSet A → 0 ≤ toLex (ν A)) {γ : Γ}
    (hstart : ∀ x, τ {x} ≠ 0 → (γ : WithTop Γ) ≤ (τ {x}).orderTop)
    (hcl : {x | τ {x} ≠ 0} ⊆ closure {x | 0 < toLex (ν {x}) ∧ (ν {x}).orderTop < γ})
    (h1 : ν Set.univ + τ Set.univ = 1) (f : C(X, ℝ)) :
    toLex (HahnSeries.C (-‖f‖)) ≤ toLex (atomicIntegral (strongWeights hν hX) f +
        atomicIntegral (strongWeights hτ hX) f) ∧
      toLex (atomicIntegral (strongWeights hν hX) f +
        atomicIntegral (strongWeights hτ hX) f) ≤ toLex (HahnSeries.C ‖f‖) := by
  refine continuousBarrier_norm_bound (strongWeights hν hX) (strongWeights hτ hX)
    ((nonneg_iff_strongWeights hν hX).mp hνpos) hstart
    hcl ?_ f
  rw [atomicIntegral_one_strongWeights, atomicIntegral_one_strongWeights, h1]

end MeasureReal

end

end Surreal.MeasureBarrier
