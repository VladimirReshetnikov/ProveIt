import Surreal.Algebra.PolynomialDiscriminant
import Surreal.Algebra.PolynomialNormResultant
import Surreal.Surcomplex.AlgebraicallyClosed
import Surreal.HahnSeries.AlgebraicallyClosed
import Surreal.HahnSeries.Characteristic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Branch values, ramification and polynomial maps

This file proves `polynomial:thm:branchvalues` (with its display
`polynomial:eq:branchvalues`), `polynomial:prop:ramification` (with
`polynomial:eq:finiteRH`) and `polynomial:cor:polynomialmaps` of
`docs/surcomplex/polynomial-algebra/article.tex`.

The fiber family `P(z) - Y` is the polynomial `fiberFamily P` in `z` over `K[Y]`. Its
discriminant is computed exactly as in the source proof: the monic discriminant is the
signed derivative resultant (`FinitePolynomial.monic_resultant_derivative_eq_sign_mul_discr`),
the interchange sign `(-1)^(n(n-1))` is one, and the resultant of the split derivative
`P'` against `A` is `n^n ∏ A(c_j)`. This is done once over an arbitrary integral domain
(`discr_eq_sign_mul_prod_eval_roots_derivative`) and applied both over `K[Y]` and over `K`,
so the identity specializes: `Disc_z(P - Y)` evaluated at `y` is `Disc(P - y)`.

Generic results are stated over a field of characteristic zero in which `P'` splits. The
identity, degree, leading-coefficient, root-multiset and multiplicity lemmas hold for every
monic `P`, including `n ≤ 1` where both sides of the identity are one (the source assumes
`n ≥ 2`). The zero-set, multiple-root, specialization and nonreduced-fiber lemmas assume
`n ≥ 1`. For the zero-set lemma this is necessary: for `P = 1` we have `P' = 0`, so
`y = 1` is the value of `P` at a root of `P'`, while the discriminant `1` has no roots.
The other three also hold at `P = 1` and use `n ≥ 1` only in their proofs. The
ramification lemmas do not assume `P`
monic; apart from `localIndex_pos`, which needs `n ≥ 1`, they need at most `P ≠ 0` (for the
chart at infinity) and a split derivative, and the source's nonconstant hypothesis enters
through the bundled statements. Over an algebraically closed field of characteristic zero,
`branchValues`, `ramification` and `polynomialMaps` bundle the source statements. They are
then instantiated at the complex Hahn workspaces `ℂ((t^Γ))` with divisible `Γ` (the field
`K` of the source) and at the actual surcomplex field `SC = No[i]`.

Conventions. A *nonreduced fiber* is taken literally: the fiber algebra
`K[z]/(P(z) - y) = AdjoinRoot (P - C y)` is not reduced; we also prove the equivalent
multiple-root form. The critical values are the multiset `P'.roots.map P.eval`, so
multiplicities are those "indicated by the product". The local index at a finite point is
`e_α = ord_α (P - P(α))` (`localIndex`), with truncated natural subtraction in
`e_α - 1`. The local index at infinity is the order at `u = 0` of the formal power series
`w(u) = u^n / P^rev(u)` (`infinityChart`), which is `1 / P(1/u)` because
`P^rev(u) = u^n P(1/u)` for `u ≠ 0` (`eval_reverse`).

Not formalized here: the remark after the theorem that the formula persists as a
universal identity over coherent coefficient rings when the critical values cannot be
labelled (only the integral-domain form with a split derivative is proved), and the
fiber decomposition of `polynomial:thm:finitemap`.
-/

universe u

namespace Surreal.BranchValues

open Polynomial

noncomputable section

section Domain

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The proof of `polynomial:thm:branchvalues` over an arbitrary integral domain: for a
monic `A` of degree `n` whose derivative has degree `n - 1` and splits,
`Disc A = (-1)^(n(n-1)/2) lc(A')^n ∏_{A'(c) = 0} A(c)`. -/
theorem discr_eq_sign_mul_prod_eval_roots_derivative {A : R[X]} (hA : A.Monic)
    (hd : A.derivative.natDegree = A.natDegree - 1) (hs : A.derivative.Splits) :
    A.discr = (-1) ^ (A.natDegree * (A.natDegree - 1) / 2) *
      A.derivative.leadingCoeff ^ A.natDegree * (A.derivative.roots.map A.eval).prod := by
  have key := FinitePolynomial.monic_resultant_derivative_eq_sign_mul_discr A hA
  have hsq : ((-1 : R) ^ (A.natDegree * (A.natDegree - 1) / 2)) *
      (-1) ^ (A.natDegree * (A.natDegree - 1) / 2) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hswap : A.resultant A.derivative = A.derivative.resultant A := by
    rw [FinitePolynomial.resultant_swap, hd, (Nat.even_mul_pred_self _).neg_one_pow, one_mul]
  have hprod : A.derivative.resultant A = A.derivative.leadingCoeff ^ A.natDegree *
      (A.derivative.roots.map A.eval).prod :=
    resultant_eq_prod_eval A.derivative A A.natDegree le_rfl hs
  calc A.discr = ((-1) ^ (A.natDegree * (A.natDegree - 1) / 2) *
        (-1) ^ (A.natDegree * (A.natDegree - 1) / 2)) * A.discr := by rw [hsq, one_mul]
    _ = (-1) ^ (A.natDegree * (A.natDegree - 1) / 2) * A.resultant A.derivative := by
        rw [key, mul_assoc]
    _ = _ := by rw [hswap, hprod, mul_assoc]

end Domain

section Field

variable {K : Type*} [Field K]

/-- The fiber family `A(z) = P(z) - Y` of `polynomial:thm:branchvalues`, a polynomial in
`z` whose coefficients lie in `K[Y]`. -/
def fiberFamily (P : K[X]) : K[X][X] := P.map C - C X

/-- Specializing `Y` to `y` in the fiber family gives the fiber polynomial `P - y`. -/
theorem map_evalRingHom_fiberFamily (P : K[X]) (y : K) :
    (fiberFamily P).map (evalRingHom y) = P - C y := by
  have h : (evalRingHom y).comp C = RingHom.id K := by
    ext
    simp
  simp [fiberFamily, Polynomial.map_map, h]

/-- The value of the fiber family at a point `c` of `K` is `P(c) - Y`. -/
theorem eval_C_fiberFamily (P : K[X]) (c : K) :
    (fiberFamily P).eval (C c) = C (P.eval c) - X := by
  simp [fiberFamily, eval_map, eval₂_at_apply]

/-- The `z`-derivative of `P(z) - Y` is `P'`. -/
theorem derivative_fiberFamily (P : K[X]) :
    (fiberFamily P).derivative = P.derivative.map C := by
  simp [fiberFamily, derivative_map]

/-- The fiber family has the `z`-degree of `P`. -/
theorem natDegree_fiberFamily (P : K[X]) : (fiberFamily P).natDegree = P.natDegree := by
  rw [fiberFamily, natDegree_sub_C, natDegree_map_eq_of_injective C_injective]

/-- For a nonconstant monic `P`, the fiber family is monic in `z`. -/
theorem monic_fiberFamily {P : K[X]} (hP : P.Monic) (hn : 0 < P.natDegree) :
    (fiberFamily P).Monic := by
  refine (hP.map C).sub_of_left ?_
  refine lt_of_le_of_lt degree_C_le ?_
  rw [degree_map_eq_of_injective C_injective]
  exact natDegree_pos_iff_degree_pos.mp hn

/-- The fibers of a nonconstant polynomial are nonzero polynomials. -/
theorem sub_C_ne_zero {P : K[X]} (hn : 0 < P.natDegree) (y : K) : P - C y ≠ 0 := by
  intro h
  have h' := congrArg natDegree h
  rw [natDegree_sub_C, natDegree_zero] at h'
  omega

/-- The fibers of a nonconstant monic polynomial are monic. -/
theorem monic_sub_C {P : K[X]} (hP : P.Monic) (hn : 0 < P.natDegree) (y : K) :
    (P - C y).Monic :=
  hP.sub_of_left (degree_C_le.trans_lt (natDegree_pos_iff_degree_pos.mp hn))

/-- The fiber algebra `K[z]/(f)` is reduced exactly when `f` is squarefree. -/
theorem isReduced_adjoinRoot_iff_squarefree {f : K[X]} (hf : f ≠ 0) :
    IsReduced (AdjoinRoot f) ↔ Squarefree f := by
  rw [← RingHom.ker_isRadical_iff_reduced_of_surjective (AdjoinRoot.mk_surjective (g := f))]
  have hker : RingHom.ker (AdjoinRoot.mk f) = Ideal.span {f} := by
    ext g
    rw [RingHom.mem_ker, AdjoinRoot.mk_eq_zero, Ideal.mem_span_singleton]
  rw [hker, ← isRadical_iff_span_singleton, isRadical_iff_squarefree_of_ne_zero hf]

/-- The critical values `P(c_1), …, P(c_{n-1})`, listed with the multiplicities of the
critical points `c_j` as roots of `P'`. -/
def criticalValues (P : K[X]) : Multiset K := P.derivative.roots.map P.eval

/-- Rewriting the factors `P(c_j) - Y` as `-(Y - P(c_j))`. -/
theorem prod_branch_factors (P : K[X]) :
    (P.derivative.roots.map fun c => C (P.eval c) - X).prod =
      (-1) ^ P.derivative.roots.card * ((criticalValues P).map fun y => X - C y).prod := by
  have h : (P.derivative.roots.map fun c => C (P.eval c) - X) =
      (P.derivative.roots.map fun c => X - C (P.eval c)).map Neg.neg := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun c _ => by simp
  rw [h, Multiset.prod_map_neg, Multiset.card_map, criticalValues, Multiset.map_map]
  rfl

/-- The local index `e_α = ord_α (P - P(α))` of `polynomial:prop:ramification`. For a
constant `P` the polynomial `P - P(α)` is zero and this junk value is `0`; for nonconstant
`P` it is at least one (`localIndex_pos`). -/
def localIndex (P : K[X]) (α : K) : ℕ := (P - C (P.eval α)).rootMultiplicity α

/-- For a nonconstant polynomial every finite local index is at least one. -/
theorem localIndex_pos {P : K[X]} (hn : 0 < P.natDegree) (α : K) : 0 < localIndex P α :=
  (rootMultiplicity_pos (sub_C_ne_zero hn _)).mpr (by simp)

/-- The chart at infinity of `polynomial:prop:ramification`: with `u = 1/z` and `w = 1/Y`,
`w(u) = 1/P(1/u) = u^n / P^rev(u)` as a formal power series in `u`. -/
def infinityChart (P : K[X]) : PowerSeries K :=
  PowerSeries.X ^ P.natDegree * (P.reverse : PowerSeries K)⁻¹

/-- The constant term of the reversed polynomial is the leading coefficient. -/
theorem constantCoeff_reverse (P : K[X]) :
    PowerSeries.constantCoeff (P.reverse : PowerSeries K) = P.leadingCoeff := by
  rw [Polynomial.constantCoeff_coe, coeff_zero_reverse]

/-- The chart at infinity solves `w · P^rev(u) = u^n`. -/
theorem infinityChart_mul_reverse {P : K[X]} (hP : P ≠ 0) :
    infinityChart P * (P.reverse : PowerSeries K) = PowerSeries.X ^ P.natDegree := by
  rw [infinityChart, mul_assoc, PowerSeries.inv_mul_cancel _
    (by rw [constantCoeff_reverse]; exact leadingCoeff_ne_zero.mpr hP), mul_one]

/-- The reversed polynomial is `u^n P(1/u)` at every nonzero `u`, so the chart at infinity
is the expansion of `1 / P(1/u)`. -/
theorem eval_reverse {P : K[X]} {u : K} (hu : u ≠ 0) :
    P.reverse.eval u = u ^ P.natDegree * P.eval u⁻¹ := by
  letI : Invertible u⁻¹ := invertibleOfNonzero (inv_ne_zero hu)
  have h := eval₂_reverse_mul_pow (RingHom.id K) u⁻¹ P
  rw [invOf_eq_inv, inv_inv, inv_pow] at h
  change P.reverse.eval u * (u ^ P.natDegree)⁻¹ = P.eval u⁻¹ at h
  rw [← h, mul_left_comm, mul_inv_cancel₀ (pow_ne_zero _ hu), mul_one]

/-- The infinity clause of `polynomial:prop:ramification`: for every `P ≠ 0` the order of
the chart `1/P(1/u)` at `u = 0` is the degree `n`. For nonconstant `P` this order is the
local index at infinity; for a nonzero constant `P` the chart is a unit of order `0`. -/
theorem order_infinityChart {P : K[X]} (hP : P ≠ 0) :
    (infinityChart P).order = P.natDegree := by
  have hu : IsUnit ((P.reverse : PowerSeries K)⁻¹) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_inv,
      constantCoeff_reverse]
    exact (inv_ne_zero (leadingCoeff_ne_zero.mpr hP)).isUnit
  rw [infinityChart, PowerSeries.order_mul, PowerSeries.order_X_pow,
    PowerSeries.order_zero_of_unit hu, add_zero]

variable [CharZero K]

/-- In characteristic zero the derivative of a monic `P` has leading coefficient `n`. -/
theorem leadingCoeff_derivative_of_monic {P : K[X]} (hP : P.Monic) :
    P.derivative.leadingCoeff = P.natDegree := by
  rw [leadingCoeff_derivative, hP.leadingCoeff, one_mul]

/-- The branch-value identity `polynomial:eq:branchvalues`:
`Disc_z (P(z) - Y) = (-1)^(n(n-1)/2) n^n ∏_j (P(c_j) - Y)`, the product running over the
roots `c_j` of `P'` with multiplicity. Valid for every monic `P` whose derivative
splits, in characteristic zero. -/
theorem discr_fiberFamily {P : K[X]} (hP : P.Monic) (hs : P.derivative.Splits) :
    (fiberFamily P).discr = C ((-1) ^ (P.natDegree * (P.natDegree - 1) / 2) *
      (P.natDegree : K) ^ P.natDegree) *
      (P.derivative.roots.map fun c => C (P.eval c) - X).prod := by
  rcases Nat.eq_zero_or_pos P.natDegree with h0 | hn
  · have h1 := eq_one_of_monic_natDegree_zero hP h0
    subst h1
    have hc : fiberFamily (1 : K[X]) = C (1 - X) := by
      simp [fiberFamily]
    rw [hc, Polynomial.discr_C]
    simp
  have hA := monic_fiberFamily hP hn
  rw [discr_eq_sign_mul_prod_eval_roots_derivative hA ?_ ?_, derivative_fiberFamily,
    natDegree_fiberFamily, leadingCoeff_map_of_injective C_injective,
    hs.roots_map_of_injective C_injective, Multiset.map_map,
    leadingCoeff_derivative_of_monic hP]
  · simp only [Function.comp_def, eval_C_fiberFamily, map_mul, map_pow, map_neg, map_one,
      map_natCast]
  · rw [derivative_fiberFamily, natDegree_fiberFamily,
      natDegree_map_eq_of_injective C_injective, natDegree_derivative]
  · rw [derivative_fiberFamily]
    exact hs.map C

/-- The leading coefficient of the branch-value polynomial is nonzero in characteristic
zero. -/
theorem branch_leadingCoeff_ne_zero (n : ℕ) :
    ((-1 : K) ^ (n * (n - 1) / 2) * (n : K) ^ n * (-1) ^ (n - 1)) ≠ 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (pow_ne_zero _ (Nat.cast_ne_zero.mpr hn.ne'))) (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

/-- The branch-value polynomial as a nonzero constant times the monic polynomial whose
roots are the critical values. -/
theorem discr_fiberFamily_eq_prod_X_sub_C {P : K[X]} (hP : P.Monic)
    (hs : P.derivative.Splits) :
    (fiberFamily P).discr = C ((-1) ^ (P.natDegree * (P.natDegree - 1) / 2) *
      (P.natDegree : K) ^ P.natDegree * (-1) ^ (P.natDegree - 1)) *
      ((criticalValues P).map fun y => X - C y).prod := by
  rw [discr_fiberFamily hP hs, prod_branch_factors, ← hs.natDegree_eq_card_roots,
    natDegree_derivative]
  simp only [map_mul, map_pow, map_neg, map_one]
  ring

/-- The branch-value polynomial is nonzero. -/
theorem discr_fiberFamily_ne_zero {P : K[X]} (hP : P.Monic) (hs : P.derivative.Splits) :
    (fiberFamily P).discr ≠ 0 := by
  rw [discr_fiberFamily_eq_prod_X_sub_C hP hs]
  exact mul_ne_zero (C_ne_zero.mpr (branch_leadingCoeff_ne_zero _))
    (monic_multiset_prod_of_monic _ _ fun y _ => monic_X_sub_C y).ne_zero

/-- The degree clause of `polynomial:thm:branchvalues`: the branch-value polynomial has
degree `n - 1` in `Y`. -/
theorem natDegree_discr_fiberFamily {P : K[X]} (hP : P.Monic) (hs : P.derivative.Splits) :
    (fiberFamily P).discr.natDegree = P.natDegree - 1 := by
  rw [discr_fiberFamily_eq_prod_X_sub_C hP hs, natDegree_C_mul (branch_leadingCoeff_ne_zero _),
    natDegree_multiset_prod_X_sub_C_eq_card, criticalValues, Multiset.card_map,
    ← hs.natDegree_eq_card_roots, natDegree_derivative]

/-- Its leading coefficient in `Y` is `(-1)^(n(n-1)/2) n^n (-1)^(n-1)`, nonzero in
characteristic zero. -/
theorem leadingCoeff_discr_fiberFamily {P : K[X]} (hP : P.Monic) (hs : P.derivative.Splits) :
    (fiberFamily P).discr.leadingCoeff = (-1) ^ (P.natDegree * (P.natDegree - 1) / 2) *
      (P.natDegree : K) ^ P.natDegree * (-1) ^ (P.natDegree - 1) := by
  rw [discr_fiberFamily_eq_prod_X_sub_C hP hs, Polynomial.leadingCoeff_mul, leadingCoeff_C,
    (monic_multiset_prod_of_monic _ _ fun y _ => monic_X_sub_C y).leadingCoeff, mul_one]

/-- The zeros of the branch-value polynomial, with multiplicity, are exactly the critical
values: its root multiset is `P(c_1), …, P(c_{n-1})`. -/
theorem roots_discr_fiberFamily {P : K[X]} (hP : P.Monic) (hs : P.derivative.Splits) :
    (fiberFamily P).discr.roots = criticalValues P := by
  rw [discr_fiberFamily_eq_prod_X_sub_C hP hs, roots_C_mul _ (branch_leadingCoeff_ne_zero _),
    roots_multiset_prod_X_sub_C]

/-- The multiplicity of `y` as a branch value is the number of `j` with `P(c_j) = y`. -/
theorem rootMultiplicity_discr_fiberFamily [DecidableEq K] {P : K[X]} (hP : P.Monic)
    (hs : P.derivative.Splits) (y : K) :
    (fiberFamily P).discr.rootMultiplicity y =
      (P.derivative.roots.filter fun c => P.eval c = y).card := by
  rw [← count_roots, roots_discr_fiberFamily hP hs, criticalValues, Multiset.count_map]
  congr 1
  exact Multiset.filter_congr fun c _ => eq_comm

/-- For nonconstant monic `P`, the zeros of the branch-value polynomial are exactly the
critical values of `P`. -/
theorem isRoot_discr_fiberFamily_iff {P : K[X]} (hP : P.Monic) (hn : 0 < P.natDegree)
    (hs : P.derivative.Splits) (y : K) :
    (fiberFamily P).discr.IsRoot y ↔ ∃ c, P.derivative.IsRoot c ∧ P.eval c = y := by
  have hP' : P.derivative ≠ 0 := derivative_ne_zero.mpr hn.ne'
  rw [← mem_roots (discr_fiberFamily_ne_zero hP hs), roots_discr_fiberFamily hP hs,
    criticalValues, Multiset.mem_map]
  simp only [mem_roots hP']

/-- For nonconstant monic `P`, a value is a branch value exactly when its fiber `P - y` has
a multiple root. -/
theorem isRoot_discr_fiberFamily_iff_multiple_root {P : K[X]} (hP : P.Monic)
    (hn : 0 < P.natDegree) (hs : P.derivative.Splits) (y : K) :
    (fiberFamily P).discr.IsRoot y ↔ ∃ α, 1 < (P - C y).rootMultiplicity α := by
  rw [isRoot_discr_fiberFamily_iff hP hn hs]
  simp only [one_lt_rootMultiplicity_iff_isRoot (sub_C_ne_zero hn y), derivative_sub,
    derivative_C, sub_zero, IsRoot.def, eval_sub, eval_C, sub_eq_zero]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, rfl, hc⟩
  · rintro ⟨c, hc, hc'⟩
    exact ⟨c, hc', hc⟩

/-- For nonconstant monic `P`, the branch-value polynomial specializes: its value at `y` is
the discriminant of the fiber `P - y`. -/
theorem eval_discr_fiberFamily {P : K[X]} (hP : P.Monic) (hn : 0 < P.natDegree)
    (hs : P.derivative.Splits) (y : K) :
    (fiberFamily P).discr.eval y = (P - C y).discr := by
  have hQd : (P - C y).derivative = P.derivative := by simp
  rw [discr_eq_sign_mul_prod_eval_roots_derivative (monic_sub_C hP hn y)
      (by rw [hQd, natDegree_sub_C, natDegree_derivative]) (by rw [hQd]; exact hs),
    hQd, natDegree_sub_C, leadingCoeff_derivative_of_monic hP, discr_fiberFamily hP hs]
  simp [eval_multiset_prod, Multiset.map_map]

/-- The zero-set clause of `polynomial:thm:branchvalues` in its literal form, for
nonconstant monic `P`: `y` is a branch value exactly when the fiber algebra
`K[z]/(P(z) - y)` is not reduced. -/
theorem isRoot_discr_fiberFamily_iff_not_isReduced {P : K[X]} (hP : P.Monic)
    (hn : 0 < P.natDegree) (hs : P.derivative.Splits) (y : K) :
    (fiberFamily P).discr.IsRoot y ↔ ¬ IsReduced (AdjoinRoot (P - C y)) := by
  rw [IsRoot.def, eval_discr_fiberFamily hP hn hs y,
    isReduced_adjoinRoot_iff_squarefree (sub_C_ne_zero hn y),
    ← FinitePolynomial.discr_ne_zero_iff_squarefree _ (sub_C_ne_zero hn y), not_not]

/-- The Taylor step of `polynomial:prop:ramification`: the multiplicity of `α` as a root
of `P'` is `e_α - 1`. -/
theorem localIndex_sub_one (P : K[X]) (α : K) :
    localIndex P α - 1 = P.derivative.rootMultiplicity α := by
  have h := derivative_rootMultiplicity_of_root (p := P - C (P.eval α)) (t := α) (by simp)
  rw [derivative_sub, derivative_C, sub_zero] at h
  rw [localIndex, h]

/-- The nonzero summands `e_α - 1` occur only at critical points. -/
theorem support_localIndex_sub_one_subset [DecidableEq K] (P : K[X]) :
    (Function.support fun α => localIndex P α - 1) ⊆ ↑P.derivative.roots.toFinset := by
  intro α hα
  simp only [Function.mem_support, localIndex_sub_one] at hα
  have hP' : P.derivative ≠ 0 := by
    rintro h
    simp [h] at hα
  simp only [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hP']
  exact (rootMultiplicity_pos hP').mp (Nat.pos_of_ne_zero hα)

/-- Only finitely many summands `e_α - 1` are nonzero. -/
theorem finite_support_localIndex_sub_one (P : K[X]) :
    (Function.support fun α => localIndex P α - 1).Finite := by
  classical
  exact P.derivative.roots.toFinset.finite_toSet.subset (support_localIndex_sub_one_subset P)

/-- The finite ramification formula `polynomial:eq:finiteRH`:
`∑_{α ∈ K} (e_α - 1) = n - 1`, for every `P` whose derivative splits (for constant `P`
both sides are `0` by truncated subtraction). -/
theorem finsum_localIndex_sub_one {P : K[X]} (hs : P.derivative.Splits) :
    ∑ᶠ α, (localIndex P α - 1) = P.natDegree - 1 := by
  classical
  rw [finsum_eq_finsetSum_of_support_subset _ (support_localIndex_sub_one_subset P),
    ← natDegree_derivative, hs.natDegree_eq_card_roots, ← Multiset.toFinset_sum_count_eq]
  exact Finset.sum_congr rfl fun α _ => by rw [localIndex_sub_one, count_roots]

/-- The total ramification on the projective line, infinity included, is `2n - 2`. This is
stated for every `P ≠ 0`; for a nonzero constant `P` it holds only through truncated
subtraction (`0 + (0 - 1) = 2 · 0 - 2 = 0`). The source concerns nonconstant `P`, as in the
bundled `ramification`. -/
theorem ramification_total {P : K[X]} (hP : P ≠ 0) (hs : P.derivative.Splits) :
    ((∑ᶠ α, (localIndex P α - 1) : ℕ) : ℕ∞) + ((infinityChart P).order - 1) =
      ((2 * P.natDegree - 2 : ℕ) : ℕ∞) := by
  rw [finsum_localIndex_sub_one hs, order_infinityChart hP]
  rw [show ((P.natDegree : ℕ∞) - 1) = ((P.natDegree - 1 : ℕ) : ℕ∞) by norm_cast,
    ← Nat.cast_add]
  congr 1
  omega

end Field

section AlgClosed

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- The surjectivity clause of `polynomial:cor:polynomialmaps`. -/
theorem eval_surjective {P : K[X]} (hn : 0 < P.natDegree) :
    Function.Surjective fun x => P.eval x := by
  intro y
  have hd : 0 < P.degree := natDegree_pos_iff_degree_pos.mp hn
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (P - C y) (by rw [degree_sub_C hd]; exact hd.ne')
  refine ⟨z, ?_⟩
  simpa [sub_eq_zero] using hz

variable [CharZero K]

/-- The injectivity clause of `polynomial:cor:polynomialmaps`: a polynomial map is
injective exactly when it has degree one. For degree at least two, a value outside the
finite set of critical values has a fiber of `n ≥ 2` distinct points. -/
theorem eval_injective_iff (P : K[X]) :
    Function.Injective (fun x => P.eval x) ↔ P.natDegree = 1 := by
  constructor
  · intro hinj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h0 | h2
    · have h0 : P.natDegree = 0 := by omega
      rw [eq_C_of_natDegree_eq_zero h0] at hinj
      exact zero_ne_one (hinj (by simp))
    · classical
      have hn : 0 < P.natDegree := by omega
      have hP' : P.derivative ≠ 0 := derivative_ne_zero.mpr hn.ne'
      obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (criticalValues P).toFinset
      have hQ0 := sub_C_ne_zero hn y
      have hnodup : (P - C y).roots.Nodup := by
        rw [Multiset.nodup_iff_count_le_one]
        intro α
        rw [count_roots]
        by_contra hlt
        push Not at hlt
        obtain ⟨h1, h2⟩ := (one_lt_rootMultiplicity_iff_isRoot hQ0).mp hlt
        simp only [derivative_sub, derivative_C, sub_zero] at h2
        simp only [IsRoot.def, eval_sub, eval_C, sub_eq_zero] at h1
        apply hy
        rw [Multiset.mem_toFinset, criticalValues, Multiset.mem_map]
        exact ⟨α, (mem_roots hP').mpr h2, h1⟩
      have hcard : (P - C y).roots.card = P.natDegree := by
        rw [← (IsAlgClosed.splits (P - C y)).natDegree_eq_card_roots, natDegree_sub_C]
      have hlt : 1 < (P - C y).roots.toFinset.card := by
        rw [Multiset.toFinset_card_of_nodup hnodup, hcard]
        omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlt
      simp only [Multiset.mem_toFinset, mem_roots hQ0, IsRoot.def, eval_sub, eval_C,
        sub_eq_zero] at ha hb
      exact hab (hinj (by simp only [ha, hb]))
  · intro h1 x x' hxx'
    obtain ⟨a, ha, b, hab⟩ := natDegree_eq_one.mp h1
    have e : eval x (C a * X + C b) = eval x' (C a * X + C b) := by
      rw [hab]
      exact hxx'
    simp only [eval_add, eval_mul, eval_C, eval_X] at e
    exact mul_left_cancel₀ ha (add_right_cancel e)

/-- The injective polynomial maps are exactly the affine maps with nonzero slope. -/
theorem eval_injective_iff_affine (P : K[X]) :
    Function.Injective (fun x => P.eval x) ↔ ∃ a b : K, a ≠ 0 ∧ P = C a * X + C b := by
  rw [eval_injective_iff, natDegree_eq_one]
  constructor
  · rintro ⟨a, ha, b, rfl⟩
    exact ⟨a, b, ha, rfl⟩
  · rintro ⟨a, b, ha, rfl⟩
    exact ⟨a, ha, b, rfl⟩

/-- Over an algebraically closed field of characteristic zero, `P'` has `n - 1` roots
counted with multiplicity. -/
theorem card_roots_derivative {P : K[X]} :
    P.derivative.roots.card = P.natDegree - 1 := by
  rw [← (IsAlgClosed.splits P.derivative).natDegree_eq_card_roots, natDegree_derivative]

/-- `polynomial:thm:branchvalues` over an algebraically closed field of characteristic
zero: `P'` has roots `c_1, …, c_{n-1}` with multiplicity; the identity
`polynomial:eq:branchvalues`; degree `n - 1` in `Y`; specialization to the fiber
discriminants; the zeros are exactly the critical values, exactly the values with a
multiple root in the fiber, and exactly the values with a nonreduced fiber algebra; and
the root multiset is `P(c_1), …, P(c_{n-1})`, giving the multiplicities indicated by the
product. The source's hypothesis `n ≥ 2` is weakened to `n ≥ 1`. -/
theorem branchValues {P : K[X]} (hP : P.Monic) (hn : 0 < P.natDegree) :
    P.derivative.roots.card = P.natDegree - 1 ∧
    (fiberFamily P).discr = C ((-1) ^ (P.natDegree * (P.natDegree - 1) / 2) *
      (P.natDegree : K) ^ P.natDegree) *
      (P.derivative.roots.map fun c => C (P.eval c) - X).prod ∧
    (fiberFamily P).discr.natDegree = P.natDegree - 1 ∧
    (∀ y, (fiberFamily P).discr.eval y = (P - C y).discr) ∧
    (∀ y, (fiberFamily P).discr.IsRoot y ↔ ∃ c, P.derivative.IsRoot c ∧ P.eval c = y) ∧
    (∀ y, (fiberFamily P).discr.IsRoot y ↔ ∃ α, 1 < (P - C y).rootMultiplicity α) ∧
    (∀ y, (fiberFamily P).discr.IsRoot y ↔ ¬ IsReduced (AdjoinRoot (P - C y))) ∧
    (fiberFamily P).discr.roots = P.derivative.roots.map P.eval := by
  have hs := IsAlgClosed.splits P.derivative
  exact ⟨card_roots_derivative, discr_fiberFamily hP hs, natDegree_discr_fiberFamily hP hs,
    eval_discr_fiberFamily hP hn hs, isRoot_discr_fiberFamily_iff hP hn hs,
    isRoot_discr_fiberFamily_iff_multiple_root hP hn hs,
    isRoot_discr_fiberFamily_iff_not_isReduced hP hn hs, roots_discr_fiberFamily hP hs⟩

/-- `polynomial:prop:ramification` over an algebraically closed field of characteristic
zero, for a nonconstant `P`: every `e_α ≥ 1`, only finitely many `e_α - 1` are nonzero,
`∑_{α ∈ K} (e_α - 1) = n - 1`, the local index at infinity is `n`, and the total over
the projective line is `2n - 2`. -/
theorem ramification {P : K[X]} (hn : 0 < P.natDegree) :
    (∀ α, 1 ≤ localIndex P α) ∧
    (Function.support fun α => localIndex P α - 1).Finite ∧
    ∑ᶠ α, (localIndex P α - 1) = P.natDegree - 1 ∧
    (infinityChart P).order = P.natDegree ∧
    ((∑ᶠ α, (localIndex P α - 1) : ℕ) : ℕ∞) + ((infinityChart P).order - 1) =
      ((2 * P.natDegree - 2 : ℕ) : ℕ∞) := by
  have hs := IsAlgClosed.splits P.derivative
  have hP : P ≠ 0 := ne_zero_of_natDegree_gt hn
  exact ⟨localIndex_pos hn, finite_support_localIndex_sub_one P, finsum_localIndex_sub_one hs,
    order_infinityChart hP, ramification_total hP hs⟩

/-- `polynomial:cor:polynomialmaps` over an algebraically closed field of characteristic
zero: nonconstant polynomial maps are surjective, and the injective ones are exactly the
affine maps with nonzero slope. -/
theorem polynomialMaps :
    (∀ P : K[X], 0 < P.natDegree → Function.Surjective fun x => P.eval x) ∧
    (∀ P : K[X], Function.Injective (fun x => P.eval x) ↔
      ∃ a b : K, a ≠ 0 ∧ P = C a * X + C b) :=
  ⟨fun _ hn => eval_surjective hn, eval_injective_iff_affine⟩

end AlgClosed

section Workspace

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [DivisibleBy Γ ℕ]

/-- `polynomial:thm:branchvalues` over the complex Hahn workspace `K = ℂ((t^Γ))`. -/
theorem workspace_branchValues {P : (HahnSeries Γ ℂ)[X]} (hP : P.Monic)
    (hn : 0 < P.natDegree) :
    P.derivative.roots.card = P.natDegree - 1 ∧
    (fiberFamily P).discr = C ((-1) ^ (P.natDegree * (P.natDegree - 1) / 2) *
      (P.natDegree : HahnSeries Γ ℂ) ^ P.natDegree) *
      (P.derivative.roots.map fun c => C (P.eval c) - X).prod ∧
    (fiberFamily P).discr.natDegree = P.natDegree - 1 ∧
    (∀ y, (fiberFamily P).discr.eval y = (P - C y).discr) ∧
    (∀ y, (fiberFamily P).discr.IsRoot y ↔ ∃ c, P.derivative.IsRoot c ∧ P.eval c = y) ∧
    (∀ y, (fiberFamily P).discr.IsRoot y ↔ ∃ α, 1 < (P - C y).rootMultiplicity α) ∧
    (∀ y, (fiberFamily P).discr.IsRoot y ↔ ¬ IsReduced (AdjoinRoot (P - C y))) ∧
    (fiberFamily P).discr.roots = P.derivative.roots.map P.eval :=
  branchValues hP hn

/-- `polynomial:prop:ramification` over the complex Hahn workspace `K = ℂ((t^Γ))`. -/
theorem workspace_ramification {P : (HahnSeries Γ ℂ)[X]} (hn : 0 < P.natDegree) :
    (∀ α, 1 ≤ localIndex P α) ∧
    (Function.support fun α => localIndex P α - 1).Finite ∧
    ∑ᶠ α, (localIndex P α - 1) = P.natDegree - 1 ∧
    (infinityChart P).order = P.natDegree ∧
    ((∑ᶠ α, (localIndex P α - 1) : ℕ) : ℕ∞) + ((infinityChart P).order - 1) =
      ((2 * P.natDegree - 2 : ℕ) : ℕ∞) :=
  ramification hn

/-- `polynomial:cor:polynomialmaps` over the complex Hahn workspace `K = ℂ((t^Γ))`. -/
theorem workspace_polynomialMaps :
    (∀ P : (HahnSeries Γ ℂ)[X], 0 < P.natDegree → Function.Surjective fun x => P.eval x) ∧
    (∀ P : (HahnSeries Γ ℂ)[X], Function.Injective (fun x => P.eval x) ↔
      ∃ a b : HahnSeries Γ ℂ, a ≠ 0 ∧ P = C a * X + C b) :=
  polynomialMaps

end Workspace

section Surcomplex

/-- `polynomial:thm:branchvalues` over the actual surcomplex field `SC = No[i]`. -/
theorem surcomplex_branchValues {P : Surcomplex.{u}[X]} (hP : P.Monic)
    (hn : 0 < P.natDegree) :
    P.derivative.roots.card = P.natDegree - 1 ∧
    (fiberFamily P).discr = C ((-1) ^ (P.natDegree * (P.natDegree - 1) / 2) *
      (P.natDegree : Surcomplex.{u}) ^ P.natDegree) *
      (P.derivative.roots.map fun c => C (P.eval c) - X).prod ∧
    (fiberFamily P).discr.natDegree = P.natDegree - 1 ∧
    (∀ y, (fiberFamily P).discr.eval y = (P - C y).discr) ∧
    (∀ y, (fiberFamily P).discr.IsRoot y ↔ ∃ c, P.derivative.IsRoot c ∧ P.eval c = y) ∧
    (∀ y, (fiberFamily P).discr.IsRoot y ↔ ∃ α, 1 < (P - C y).rootMultiplicity α) ∧
    (∀ y, (fiberFamily P).discr.IsRoot y ↔ ¬ IsReduced (AdjoinRoot (P - C y))) ∧
    (fiberFamily P).discr.roots = P.derivative.roots.map P.eval :=
  branchValues hP hn

/-- `polynomial:prop:ramification` over the actual surcomplex field `SC = No[i]`. -/
theorem surcomplex_ramification {P : Surcomplex.{u}[X]} (hn : 0 < P.natDegree) :
    (∀ α, 1 ≤ localIndex P α) ∧
    (Function.support fun α => localIndex P α - 1).Finite ∧
    ∑ᶠ α, (localIndex P α - 1) = P.natDegree - 1 ∧
    (infinityChart P).order = P.natDegree ∧
    ((∑ᶠ α, (localIndex P α - 1) : ℕ) : ℕ∞) + ((infinityChart P).order - 1) =
      ((2 * P.natDegree - 2 : ℕ) : ℕ∞) :=
  ramification hn

/-- `polynomial:cor:polynomialmaps` for the actual surcomplex field: every nonconstant
polynomial map `SC → SC` is surjective, and the injective ones are exactly the affine
maps with nonzero slope. -/
theorem surcomplex_polynomialMaps :
    (∀ P : Surcomplex.{u}[X], 0 < P.natDegree → Function.Surjective fun x => P.eval x) ∧
    (∀ P : Surcomplex.{u}[X], Function.Injective (fun x => P.eval x) ↔
      ∃ a b : Surcomplex.{u}, a ≠ 0 ∧ P = C a * X + C b) :=
  polynomialMaps

end Surcomplex

end

end Surreal.BranchValues
