import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Avoiding countably many polynomial conditions at a constant point

This file proves `hol:lem:generic` of
`docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/article.tex`: for any
countable family of nonzero polynomials in `K[z_1, …, z_d]`, `K = ℂ((t^Γ))`, there is a
point `c ∈ ℂ^d` with ordinary complex (constant) coordinates at which none of them
vanishes.

The proof is split into three layers, each proved at its natural generality.

* **Core.** Over an uncountable integral domain `R`, a countable family of nonzero
  polynomials in finitely many variables has a common non-vanishing point in `R^σ`
  (`exists_eval_ne_zero`). The proof is by induction on the number of variables through
  `MvPolynomial.finSuccEquiv`: a point avoiding the leading coefficients specializes every
  polynomial to a nonzero one-variable polynomial, the countably many finite root sets do
  not cover `R`, and a last coordinate outside them works. This replaces the manuscript's
  choice of coordinates algebraically independent over a countable field; both arguments
  use only that the constant field is uncountable.
* **Coefficient reduction.** For a commutative `R`-algebra `A` whose `R`-linear
  functionals separate points (for instance a projective module, hence any algebra over a
  field), a linear functional `φ` applied coefficientwise turns `H ∈ A[z]` into
  `coeffwise φ H ∈ R[z]`, with `(coeffwise φ H)(c) = φ (H(c))` at constant points
  (`eval_coeffwise`). This gives the algebra form
  `exists_algebraMap_eval_ne_zero_of_separating`, its projective and field corollaries.
* **Hahn series.** For `A = R((t^Γ))` over any ordered cancellative commutative monoid
  `Γ`, the functional is a Hahn coefficient, `coeffPoly H β` is the polynomial of
  `β`-coefficients, and `(H(c)).coeff β = (coeffPoly H β)(c)` (`coeff_eval_C`). This is
  the reduction of the manuscript's proof and gives `exists_const_point_eval_ne_zero`.
  When `Γ` is linearly ordered, taking `β` to be the least Hahn exponent among the nonzero
  coefficients, as the manuscript does, shows moreover that the value at the chosen point
  has valuation exactly that least exponent (`exists_const_point_order_eq`).

The instances at the manuscript's fields are `exists_complex_point_eval_ne_zero`
(`K = ℂ((t^Γ))`, the statement of `hol:lem:generic`) and
`exists_real_point_eval_ne_zero` (`ℝ((t^Γ))`, as used in `hol:sec:fields`).

Uncountability of the constant field is a genuine hypothesis:
`exists_family_without_const_point` shows that over any countable nontrivial coefficient
ring the countable family `z - q` has no common non-vanishing constant point. In particular
the constant-coordinate conclusion fails over `k((t^Γ))` for a countable field `k` such as
`ℚ`. This does not bear on `hol:main:multi` over such `k`: its generic point may be taken in
`K^d` for the field `K = k((t^Γ))` itself, which is uncountable when `Γ ≠ 0`, and the core
`exists_eval_ne_zero` applies with `R = K`.

Nothing of `hol:lem:generic` is pending. Its use in the proof of `hol:main:multi`
(restriction to a generic line, multivariate D-finiteness) is not formalized here.
-/

namespace Surreal.GenericPoint

open MvPolynomial

section Core

variable {R : Type*} [CommRing R] [IsDomain R] [Uncountable R] {ι : Type*} [Countable ι]

/-- Core of `hol:lem:generic` in the variables `Fin n`: over an uncountable integral
domain, a countable family of nonzero polynomials has a common non-vanishing point. -/
theorem exists_eval_ne_zero_fin :
    ∀ (n : ℕ) (H : ι → MvPolynomial (Fin n) R), (∀ i, H i ≠ 0) →
      ∃ c : Fin n → R, ∀ i, eval c (H i) ≠ 0
  | 0, H, hH => by
    refine ⟨Fin.elim0, fun i h0 => hH i ?_⟩
    have h := MvPolynomial.eq_C_of_isEmpty (H i)
    rw [h, eval_C] at h0
    rw [h, h0, C_0]
  | n + 1, H, hH => by
    have hQ : ∀ i, finSuccEquiv R n (H i) ≠ 0 := fun i =>
      (map_ne_zero_iff _ (finSuccEquiv R n).injective).mpr (hH i)
    obtain ⟨c', hc'⟩ := exists_eval_ne_zero_fin n
      (fun i => (finSuccEquiv R n (H i)).leadingCoeff)
      (fun i => Polynomial.leadingCoeff_ne_zero.mpr (hQ i))
    have hP : ∀ i, (finSuccEquiv R n (H i)).map (eval c') ≠ 0 := fun i h => by
      have := congrArg (fun p => Polynomial.coeff p (finSuccEquiv R n (H i)).natDegree) h
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at this
      exact hc' i this
    have hcount :
        (⋃ i, {y : R | ((finSuccEquiv R n (H i)).map (eval c')).IsRoot y}).Countable :=
      Set.countable_iUnion fun i => (Polynomial.finite_setOf_isRoot (hP i)).countable
    have hne : (⋃ i, {y : R | ((finSuccEquiv R n (H i)).map (eval c')).IsRoot y}) ≠
        Set.univ := fun h => Set.not_countable_univ (h ▸ hcount)
    obtain ⟨y, hy⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
    refine ⟨Fin.cons y c', fun i h0 => hy (Set.mem_iUnion.mpr ⟨i, ?_⟩)⟩
    rw [eval_eq_eval_mv_eval'] at h0
    exact h0

/-- Core of `hol:lem:generic`: over an uncountable integral domain `R`, a countable family
of nonzero polynomials in finitely many variables has a common non-vanishing point in
`R^σ`. -/
theorem exists_eval_ne_zero {σ : Type*} [Finite σ] (H : ι → MvPolynomial σ R)
    (hH : ∀ i, H i ≠ 0) : ∃ c : σ → R, ∀ i, eval c (H i) ≠ 0 := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  obtain ⟨c, hc⟩ := exists_eval_ne_zero_fin n (fun i => rename e (H i))
    (fun i => (map_ne_zero_iff _ (rename_injective _ e.injective)).mpr (hH i))
  refine ⟨c ∘ e, fun i => ?_⟩
  rw [← eval_rename]
  exact hc i

end Core

section Coefficientwise

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {σ : Type*}

/-- The polynomial over `R` obtained by applying an `R`-linear functional `φ : A → R` to
every coefficient of a polynomial over `A`. -/
noncomputable def coeffwise (φ : A →ₗ[R] R) (H : MvPolynomial σ A) : MvPolynomial σ R :=
  ∑ m ∈ H.support, monomial m (φ (H.coeff m))

/-- The coefficients of `coeffwise φ H` are the images under `φ` of those of `H`. -/
theorem coeff_coeffwise (φ : A →ₗ[R] R) (H : MvPolynomial σ A) (m : σ →₀ ℕ) :
    (coeffwise φ H).coeff m = φ (H.coeff m) := by
  classical
  rw [coeffwise, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, map_zero]

/-- At a constant point, evaluation commutes with a coefficientwise linear functional:
`(coeffwise φ H)(c) = φ (H(c))`. -/
theorem eval_coeffwise (φ : A →ₗ[R] R) (H : MvPolynomial σ A) (c : σ → R) :
    eval c (coeffwise φ H) = φ (eval (fun j => algebraMap R A (c j)) H) := by
  conv_rhs => rw [H.as_sum]
  rw [coeffwise, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [eval_monomial, eval_monomial]
  have : (m.prod fun n e => algebraMap R A (c n) ^ e) =
      algebraMap R A (m.prod fun n e => c n ^ e) := by
    rw [map_finsuppProd]
    simp only [map_pow]
  rw [this, ← Algebra.commutes, ← Algebra.smul_def, φ.map_smul, smul_eq_mul, mul_comm]

/-- If linear functionals separate the points of `A`, every nonzero polynomial over `A` has
a nonzero coefficientwise image over `R`. -/
theorem exists_coeffwise_ne_zero_of_separating
    (hsep : ∀ a : A, a ≠ 0 → ∃ φ : A →ₗ[R] R, φ a ≠ 0) {H : MvPolynomial σ A}
    (hH : H ≠ 0) : ∃ φ : A →ₗ[R] R, coeffwise φ H ≠ 0 := by
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hH
  obtain ⟨φ, hφ⟩ := hsep _ hm
  exact ⟨φ, ne_zero_iff.mpr ⟨m, by rwa [coeff_coeffwise]⟩⟩

/-- `hol:lem:generic` for an algebra `A` over an uncountable integral domain `R` whose
linear functionals separate points: a countable family of nonzero polynomials over `A` in
finitely many variables has a common non-vanishing point with coordinates in `R`. -/
theorem exists_algebraMap_eval_ne_zero_of_separating [IsDomain R] [Uncountable R]
    {ι : Type*} [Countable ι] [Finite σ]
    (hsep : ∀ a : A, a ≠ 0 → ∃ φ : A →ₗ[R] R, φ a ≠ 0)
    (H : ι → MvPolynomial σ A) (hH : ∀ i, H i ≠ 0) :
    ∃ c : σ → R, ∀ i, eval (fun j => algebraMap R A (c j)) (H i) ≠ 0 := by
  choose φ hφ using fun i => exists_coeffwise_ne_zero_of_separating hsep (hH i)
  obtain ⟨c, hc⟩ := exists_eval_ne_zero (fun i => coeffwise (φ i) (H i)) hφ
  refine ⟨c, fun i h0 => hc i ?_⟩
  show eval c (coeffwise (φ i) (H i)) = 0
  rw [eval_coeffwise, h0, map_zero]

/-- `hol:lem:generic` for an algebra that is a projective (for instance free) module over an
uncountable integral domain `R`. -/
theorem exists_algebraMap_eval_ne_zero [IsDomain R] [Uncountable R] [Module.Projective R A]
    {ι : Type*} [Countable ι] [Finite σ] (H : ι → MvPolynomial σ A) (hH : ∀ i, H i ≠ 0) :
    ∃ c : σ → R, ∀ i, eval (fun j => algebraMap R A (c j)) (H i) ≠ 0 :=
  exists_algebraMap_eval_ne_zero_of_separating
    (fun _ ha => Module.Projective.exists_dual_ne_zero R ha) H hH

end Coefficientwise

/-- `hol:lem:generic` for an arbitrary commutative algebra over an uncountable field `k`. -/
theorem exists_algebraMap_eval_ne_zero_of_field {k A : Type*} [Field k] [Uncountable k]
    [CommRing A] [Algebra k A] {σ ι : Type*} [Finite σ] [Countable ι]
    (H : ι → MvPolynomial σ A) (hH : ∀ i, H i ≠ 0) :
    ∃ c : σ → k, ∀ i, eval (fun j => algebraMap k A (c j)) (H i) ≠ 0 :=
  exists_algebraMap_eval_ne_zero H hH

section Hahn

variable {Γ R : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing R] {σ : Type*}

/-- The polynomial `H̄ ∈ R[z]` of `β`-coefficients of a polynomial `H` over `R((t^Γ))`,
the reduction used in the proof of `hol:lem:generic`. -/
noncomputable def coeffPoly (H : MvPolynomial σ (HahnSeries Γ R)) (β : Γ) :
    MvPolynomial σ R :=
  coeffwise (HahnSeries.coeff.linearMap β) H

/-- The `m`-th coefficient of `coeffPoly H β` is the `β`-coefficient of the `m`-th
coefficient of `H`. -/
theorem coeff_coeffPoly (H : MvPolynomial σ (HahnSeries Γ R)) (β : Γ) (m : σ →₀ ℕ) :
    (coeffPoly H β).coeff m = (H.coeff m).coeff β :=
  coeff_coeffwise _ H m

/-- At a constant point `c`, the `β`-coefficient of `H(c)` is `H̄(c)` with `H̄` the
polynomial of `β`-coefficients; hence `H̄(c) ≠ 0` implies `H(c) ≠ 0`. -/
theorem coeff_eval_C (H : MvPolynomial σ (HahnSeries Γ R)) (c : σ → R) (β : Γ) :
    (eval (fun j => HahnSeries.C (c j)) H).coeff β = eval c (coeffPoly H β) := by
  rw [coeffPoly, eval_coeffwise]
  rfl

/-- A nonzero polynomial over `R((t^Γ))` has a nonzero `β`-coefficient polynomial for some
exponent `β`. -/
theorem exists_coeffPoly_ne_zero {H : MvPolynomial σ (HahnSeries Γ R)} (hH : H ≠ 0) :
    ∃ β, coeffPoly H β ≠ 0 := by
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hH
  obtain ⟨β, hβ⟩ : ∃ β, (H.coeff m).coeff β ≠ 0 := by
    by_contra h
    exact hm (HahnSeries.ext (funext fun β => not_not.mp fun hβ => h ⟨β, hβ⟩))
  exact ⟨β, ne_zero_iff.mpr ⟨m, by rwa [coeff_coeffPoly]⟩⟩

/-- `hol:lem:generic` over `R((t^Γ))` for an uncountable integral domain `R` and any ordered
cancellative commutative monoid `Γ`: a countable family of nonzero polynomials in finitely
many variables has a common non-vanishing point with constant coordinates in `R`. -/
theorem exists_const_point_eval_ne_zero [IsDomain R] [Uncountable R] {ι : Type*}
    [Countable ι] [Finite σ] (H : ι → MvPolynomial σ (HahnSeries Γ R)) (hH : ∀ i, H i ≠ 0) :
    ∃ c : σ → R, ∀ i, eval (fun j => HahnSeries.C (c j)) (H i) ≠ 0 := by
  choose β hβ using fun i => exists_coeffPoly_ne_zero (hH i)
  obtain ⟨c, hc⟩ := exists_eval_ne_zero (fun i => coeffPoly (H i) (β i)) hβ
  refine ⟨c, fun i h0 => hc i ?_⟩
  show eval c (coeffPoly (H i) (β i)) = 0
  rw [← coeff_eval_C, h0, HahnSeries.coeff_zero]

/-- Uncountability of the constant ring is necessary in `hol:lem:generic`: over a countable
nontrivial ring `R`, the countable family `z - q` (`q ∈ R`) of nonzero polynomials over
`R((t^Γ))` vanishes somewhere at every constant point. -/
theorem exists_family_without_const_point [Nontrivial R] [Countable R] :
    ∃ H : R → MvPolynomial (Fin 1) (HahnSeries Γ R), (∀ q, H q ≠ 0) ∧
      ∀ c : Fin 1 → R, ∃ q, eval (fun j => HahnSeries.C (c j)) (H q) = 0 := by
  refine ⟨fun q => X 0 - C (HahnSeries.C q), fun q h => ?_, fun c => ⟨c 0, ?_⟩⟩
  · have := congrArg (eval fun _ => HahnSeries.C (q + 1)) h
    rw [eval_sub, eval_X, eval_C, map_zero, ← map_sub, add_sub_cancel_left, map_one] at this
    exact one_ne_zero this
  · rw [eval_sub, eval_X, eval_C, sub_self]

end Hahn

section Initial

variable {Γ R : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing R] {σ : Type*}

/-- The least Hahn exponent `β` among the nonzero coefficients of `H ≠ 0`, as chosen in the
proof of `hol:lem:generic`: its coefficient polynomial is nonzero and every lower one
vanishes. -/
theorem exists_isLeast_coeffPoly {H : MvPolynomial σ (HahnSeries Γ R)} (hH : H ≠ 0) :
    ∃ β, IsLeast ((fun m => (H.coeff m).order) '' (H.support : Set (σ →₀ ℕ))) β ∧
      coeffPoly H β ≠ 0 ∧ ∀ γ < β, coeffPoly H γ = 0 := by
  obtain ⟨m₀, hm₀, hmin⟩ :=
    H.support.exists_min_image (fun m => (H.coeff m).order) (support_nonempty.mpr hH)
  refine ⟨(H.coeff m₀).order, ⟨⟨m₀, Finset.mem_coe.mpr hm₀, rfl⟩, ?_⟩,
    ne_zero_iff.mpr ⟨m₀, ?_⟩, fun γ hγ => ?_⟩
  · rintro _ ⟨m, hm, rfl⟩
    exact hmin m (Finset.mem_coe.mp hm)
  · rw [coeff_coeffPoly]
    exact HahnSeries.coeff_order_eq_zero.not.mpr (mem_support_iff.mp hm₀)
  · ext m
    rw [coeff_coeffPoly, coeff_zero]
    by_cases hm : m ∈ H.support
    · exact HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hγ (hmin m hm))
    · rw [notMem_support_iff.mp hm, HahnSeries.coeff_zero]

/-- If all coefficient polynomials below `β` vanish and the one at `β` does not vanish at
the constant point `c`, then `H(c) ≠ 0` and `H(c)` has valuation exactly `β`. -/
theorem order_eval_C_eq {H : MvPolynomial σ (HahnSeries Γ R)} {β : Γ}
    (hlow : ∀ γ < β, coeffPoly H γ = 0) {c : σ → R} (hc : eval c (coeffPoly H β) ≠ 0) :
    eval (fun j => HahnSeries.C (c j)) H ≠ 0 ∧
      (eval (fun j => HahnSeries.C (c j)) H).order = β := by
  have hβ : (eval (fun j => HahnSeries.C (c j)) H).coeff β ≠ 0 := by rwa [coeff_eval_C]
  have hne : eval (fun j => HahnSeries.C (c j)) H ≠ 0 := fun h =>
    hβ (by rw [h, HahnSeries.coeff_zero])
  refine ⟨hne, le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hβ)
    (not_lt.mp fun hlt => ?_)⟩
  apply HahnSeries.coeff_order_eq_zero.not.mpr hne
  rw [coeff_eval_C, hlow _ hlt, map_zero]

/-- `hol:lem:generic` with the least-exponent choice of its proof: for a linearly ordered
`Γ` there is a constant point at which every member of the countable family is nonzero and
takes as valuation the least Hahn exponent among its nonzero coefficients. -/
theorem exists_const_point_order_eq [IsDomain R] [Uncountable R] {ι : Type*} [Countable ι]
    [Finite σ] (H : ι → MvPolynomial σ (HahnSeries Γ R)) (hH : ∀ i, H i ≠ 0) :
    ∃ c : σ → R, ∀ i, eval (fun j => HahnSeries.C (c j)) (H i) ≠ 0 ∧
      IsLeast ((fun m => ((H i).coeff m).order) '' ((H i).support : Set (σ →₀ ℕ)))
        (eval (fun j => HahnSeries.C (c j)) (H i)).order := by
  choose β hleast hβ hlow using fun i => exists_isLeast_coeffPoly (hH i)
  obtain ⟨c, hc⟩ := exists_eval_ne_zero (fun i => coeffPoly (H i) (β i)) hβ
  refine ⟨c, fun i => ?_⟩
  obtain ⟨hne, hord⟩ := order_eval_C_eq (hlow i) (hc i)
  exact ⟨hne, hord ▸ hleast i⟩

end Initial

/-- The complex numbers are uncountable. -/
theorem uncountable_complex : Uncountable ℂ :=
  Set.not_countable_univ_iff.mp not_countable_complex

/-- `hol:lem:generic`: for any countable family of nonzero polynomials in
`K[z_1, …, z_d]`, `K = ℂ((t^Γ))`, there is `c ∈ ℂ^d` at which none of them vanishes. -/
theorem exists_complex_point_eval_ne_zero {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] {ι : Type*} [Countable ι] {d : ℕ}
    (H : ι → MvPolynomial (Fin d) (HahnSeries Γ ℂ)) (hH : ∀ i, H i ≠ 0) :
    ∃ c : Fin d → ℂ, ∀ i, eval (fun j => HahnSeries.C (c j)) (H i) ≠ 0 :=
  haveI := uncountable_complex
  exists_const_point_eval_ne_zero H hH

/-- `hol:lem:generic` over `ℝ((t^Γ))`, with real constant coordinates, as used for the
surreal workspaces in `hol:sec:fields`. -/
theorem exists_real_point_eval_ne_zero {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] {ι : Type*} [Countable ι] {d : ℕ}
    (H : ι → MvPolynomial (Fin d) (HahnSeries Γ ℝ)) (hH : ∀ i, H i ≠ 0) :
    ∃ c : Fin d → ℝ, ∀ i, eval (fun j => HahnSeries.C (c j)) (H i) ≠ 0 :=
  exists_const_point_eval_ne_zero H hH

end Surreal.GenericPoint
