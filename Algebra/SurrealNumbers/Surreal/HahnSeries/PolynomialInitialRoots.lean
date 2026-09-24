import Surreal.HahnSeries.PolynomialGaussValuation
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.Algebra.Polynomial.Roots

/-!
# Weighted initial polynomials of split Hahn polynomials

The linear-factor calculations underlying `polynomial:eq:profileproduct`
and `polynomial:eq:initialroots` are valid over every coefficient field and
ordered abelian exponent group. The finite split factorization is an explicit
hypothesis; no algebraic closedness or divisibility of the exponent group is
assumed. A root at the center has order `⊤`, and the minimum convention is
therefore part of the formulas.

The exact initial product includes an explicit nonzero scalar and quotient-based
standard-part residues. Its degree, trailing degree, and root multiplicities
give the closed-ball, open-ball, shell, and residue-direction counts in
`polynomial:thm:initialroots`. The existing active-support characterization
identifies these degrees with the extremal active indices.
-/

namespace Surreal.HahnSeries

open Polynomial
open scoped _root_.HahnSeries Classical

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [Field K]

@[simp] theorem gaussExpansion_C (ρ : Γ) (c : K⟦Γ⟧) :
    gaussExpansion ρ (C c) = mapCoeffsToPolynomial c := by
  simp [gaussExpansion]

@[simp] theorem gaussExpansion_X (ρ : Γ) :
    gaussExpansion (K := K) ρ X = _root_.HahnSeries.single ρ X := by
  simp [gaussExpansion]

@[simp] theorem centeredGaussExpansion_C (a : K⟦Γ⟧) (ρ : Γ) (c : K⟦Γ⟧) :
    centeredGaussExpansion a ρ (C c) = mapCoeffsToPolynomial c := by
  simp [centeredGaussExpansion_apply]

/-- Translation of a linear factor before its weighted normalization. -/
theorem centeredGaussExpansion_X_sub_C (a : K⟦Γ⟧) (ρ : Γ) (α : K⟦Γ⟧) :
    centeredGaussExpansion a ρ (X - C α) =
      _root_.HahnSeries.single ρ X - mapCoeffsToPolynomial (α - a) := by
  simp only [centeredGaussExpansion_apply, map_sub, taylor_X, taylor_C,
    map_add, gaussExpansion_X, gaussExpansion_C]
  abel

/-- The linear-factor valuation used in `polynomial:eq:profileproduct`.
In particular `α = a` contributes `min ρ ⊤ = ρ`. -/
theorem weightedGaussVal_X_sub_C (a : K⟦Γ⟧) (ρ : Γ) (α : K⟦Γ⟧) :
    weightedGaussVal a ρ (X - C α) =
      min (ρ : WithTop Γ) (α - a).orderTop := by
  rw [weightedGaussVal_apply, centeredGaussExpansion_X_sub_C]
  apply le_antisymm
  · apply le_min
    · apply _root_.HahnSeries.orderTop_le_of_coeff_ne_zero
      intro h
      have := congrArg (fun p : K[X] => p.coeff 1) h
      simp at this
    · by_cases h : α - a = 0
      · simp [h]
      · rw [← _root_.HahnSeries.order_eq_orderTop_of_ne_zero h]
        apply _root_.HahnSeries.orderTop_le_of_coeff_ne_zero
        intro hc
        have := congrArg (fun p : K[X] => p.coeff 0) hc
        have hcoeff := _root_.HahnSeries.coeff_order_eq_zero.not.mpr h
        apply hcoeff
        simpa only [_root_.HahnSeries.coeff_sub, coeff_mapCoeffsToPolynomial,
          Polynomial.coeff_sub, Polynomial.coeff_C_zero,
          _root_.HahnSeries.coeff_single, apply_ite (fun p : K[X] => p.coeff 0),
          Polynomial.coeff_X_zero, Polynomial.coeff_zero, ite_self, zero_sub, neg_eq_zero] using this
  · simpa only [_root_.HahnSeries.orderTop_single Polynomial.X_ne_zero,
      orderTop_mapCoeffsToPolynomial] using
      (_root_.HahnSeries.min_orderTop_le_orderTop_sub
        (x := _root_.HahnSeries.single ρ (X : K[X]))
        (y := mapCoeffsToPolynomial (α - a)))

/-- Coefficient embeddings preserve leading coefficients as constants. -/
@[simp] theorem leadingCoeff_mapCoeffsToPolynomial (x : K⟦Γ⟧) :
    (mapCoeffsToPolynomial x).leadingCoeff = C x.leadingCoeff := by
  by_cases hx : x = 0
  · simp [hx]
  have hm : mapCoeffsToPolynomial x ≠ 0 := by
    intro h
    have := congrArg _root_.HahnSeries.orderTop h
    simp [hx] at this
  have ho : (mapCoeffsToPolynomial x).order = x.order := by
    apply WithTop.coe_injective
    rw [_root_.HahnSeries.order_eq_orderTop_of_ne_zero hm,
      _root_.HahnSeries.order_eq_orderTop_of_ne_zero hx,
      orderTop_mapCoeffsToPolynomial]
  simp only [_root_.HahnSeries.leadingCoeff_eq, ho, coeff_mapCoeffsToPolynomial]

@[simp] theorem weightedGaussVal_C (a : K⟦Γ⟧) (ρ : Γ) (c : K⟦Γ⟧) :
    weightedGaussVal a ρ (C c) = c.orderTop := by
  simp [weightedGaussVal_apply]

@[simp] theorem gaussInitial_C (a : K⟦Γ⟧) (ρ : Γ) (c : K⟦Γ⟧) :
    gaussInitial a ρ (C c) = C c.leadingCoeff := by
  simp [gaussInitial]

/-- An inside-ball linear factor has its normalized residue as its initial
root. The coefficient version is identified with standard part below. -/
theorem gaussInitial_X_sub_C_of_le (a : K⟦Γ⟧) (ρ : Γ) (α : K⟦Γ⟧)
    (h : (ρ : WithTop Γ) ≤ (α - a).orderTop) :
    gaussInitial a ρ (X - C α) = X - C ((α - a).coeff ρ) := by
  have hE : centeredGaussExpansion a ρ (X - C α) ≠ 0 := by
    exact (map_ne_zero_iff _ (centeredGaussExpansion_injective a ρ)).mpr
      (monic_X_sub_C α).ne_zero
  have ho : (centeredGaussExpansion a ρ (X - C α)).order = ρ := by
    apply WithTop.coe_injective
    rw [_root_.HahnSeries.order_eq_orderTop_of_ne_zero hE]
    change weightedGaussVal a ρ (X - C α) = _
    rw [weightedGaussVal_X_sub_C, min_eq_left h]
  rw [gaussInitial, _root_.HahnSeries.leadingCoeff_eq, ho,
    centeredGaussExpansion_X_sub_C]
  simp

/-- An outside-ball linear factor contributes a nonzero constant initial
polynomial, as in the proof of `polynomial:eq:initialroots`. -/
theorem gaussInitial_X_sub_C_of_lt (a : K⟦Γ⟧) (ρ : Γ) (α : K⟦Γ⟧)
    (h : (α - a).orderTop < (ρ : WithTop Γ)) :
    gaussInitial a ρ (X - C α) = C (-(α - a).leadingCoeff) := by
  rw [gaussInitial, centeredGaussExpansion_X_sub_C, sub_eq_add_neg,
    _root_.HahnSeries.leadingCoeff_add_eq_right]
  · rw [_root_.HahnSeries.leadingCoeff_neg, leadingCoeff_mapCoeffsToPolynomial,
      map_neg]
  · simpa only [_root_.HahnSeries.orderTop_neg, orderTop_mapCoeffsToPolynomial,
      _root_.HahnSeries.orderTop_single Polynomial.X_ne_zero] using h

/-- At the center, the infinite valuation of the zero displacement
contributes the finite weight. -/
@[simp] theorem weightedGaussVal_X_sub_C_center (a : K⟦Γ⟧) (ρ : Γ) :
    weightedGaussVal a ρ (X - C a) = (ρ : WithTop Γ) := by
  rw [weightedGaussVal_X_sub_C]
  simp

/-- A centered root has initial factor `X` at every scale. -/
@[simp] theorem gaussInitial_X_sub_C_center (a : K⟦Γ⟧) (ρ : Γ) :
    gaussInitial a ρ (X - C a) = (X : K[X]) := by
  simpa using gaussInitial_X_sub_C_of_le a ρ a (by simp)

/-- Division by `t^ρ` puts each root in the closed valuation ball into the
nonnegative-order subring. -/
theorem normalizedRoot_nonnegative (a : K⟦Γ⟧) (ρ : Γ) (α : K⟦Γ⟧)
    (h : (ρ : WithTop Γ) ≤ (α - a).orderTop) :
    0 ≤ ((α - a) / _root_.HahnSeries.single ρ (1 : K)).orderTop := by
  rw [div_eq_mul_inv, _root_.HahnSeries.inv_single, inv_one,
    _root_.HahnSeries.orderTop_mul, _root_.HahnSeries.orderTop_single one_ne_zero]
  have hh := add_le_add h (le_refl ((-ρ : Γ) : WithTop Γ))
  simpa only [← WithTop.coe_add, add_neg_cancel, WithTop.coe_zero] using hh

/-- The residue coordinate `st((α-a)/t^ρ)` in
`polynomial:eq:initialroots`, with membership in the valuation ring proved. -/
def normalizedRootResidue (a : K⟦Γ⟧) (ρ : Γ) (α : K⟦Γ⟧)
    (h : (ρ : WithTop Γ) ≤ (α - a).orderTop) : K :=
  standardPart Γ K ⟨(α - a) / _root_.HahnSeries.single ρ 1,
    (mem_nonnegativeSubring _).mpr (normalizedRoot_nonnegative a ρ α h)⟩

@[simp] theorem normalizedRootResidue_eq_coeff (a : K⟦Γ⟧) (ρ : Γ) (α : K⟦Γ⟧)
    (h : (ρ : WithTop Γ) ≤ (α - a).orderTop) :
    normalizedRootResidue a ρ α h = (α - a).coeff ρ := by
  simp [normalizedRootResidue, div_eq_mul_inv, _root_.HahnSeries.inv_single,
    _root_.HahnSeries.coeff_mul_single]

/-- The exact standard-part form of the inside-ball factor in
`polynomial:eq:initialroots`. -/
theorem gaussInitial_X_sub_C_of_le_standardPart (a : K⟦Γ⟧) (ρ : Γ) (α : K⟦Γ⟧)
    (h : (ρ : WithTop Γ) ≤ (α - a).orderTop) :
    gaussInitial a ρ (X - C α) = X - C (normalizedRootResidue a ρ α h) := by
  simpa using gaussInitial_X_sub_C_of_le a ρ α h

/-- An inside normalized root has residue zero exactly in the open ball. -/
theorem normalizedRootResidue_eq_zero_iff (a : K⟦Γ⟧) (ρ : Γ) (α : K⟦Γ⟧)
    (h : (ρ : WithTop Γ) ≤ (α - a).orderTop) :
    normalizedRootResidue a ρ α h = 0 ↔ (ρ : WithTop Γ) < (α - a).orderTop := by
  rw [normalizedRootResidue_eq_coeff]
  constructor
  · intro hc
    exact lt_of_le_of_ne h (_root_.HahnSeries.orderTop_ne_of_coeff_eq_zero hc).symm
  · exact _root_.HahnSeries.coeff_eq_zero_of_lt_orderTop

variable {ι : Type*}

/-- Weighted valuations add across finite products. -/
theorem weightedGaussVal_prod (a : K⟦Γ⟧) (ρ : Γ) (s : Finset ι)
    (P : ι → K⟦Γ⟧[X]) :
    weightedGaussVal a ρ (∏ i ∈ s, P i) = ∑ i ∈ s, weightedGaussVal a ρ (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.prod_insert hi, Finset.sum_insert hi,
      weightedGaussVal_mul, ih]

/-- Initial polynomials multiply across finite products. -/
theorem gaussInitial_prod (a : K⟦Γ⟧) (ρ : Γ) (s : Finset ι)
    (P : ι → K⟦Γ⟧[X]) :
    gaussInitial a ρ (∏ i ∈ s, P i) = ∏ i ∈ s, gaussInitial a ρ (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gaussInitial]
  | @insert i s hi ih => simp only [Finset.prod_insert hi, gaussInitial_mul, ih]

/-- The exact product profile `polynomial:eq:profileproduct` for an indexed
split polynomial. Indices need not give distinct roots. Zero leading scalar
is also permitted: both sides then have value `⊤`. -/
theorem weightedGaussVal_split (a : K⟦Γ⟧) (ρ : Γ) (c : K⟦Γ⟧)
    (s : Finset ι) (α : ι → K⟦Γ⟧) :
    weightedGaussVal a ρ (C c * ∏ i ∈ s, (X - C (α i))) =
      c.orderTop + ∑ i ∈ s, min (ρ : WithTop Γ) (α i - a).orderTop := by
  rw [weightedGaussVal_mul, weightedGaussVal_C, weightedGaussVal_prod]
  simp only [weightedGaussVal_X_sub_C]

/-- Root indices in the closed valuation ball, retaining multiplicity. -/
def closedRootIndices (a : K⟦Γ⟧) (ρ : Γ) (s : Finset ι) (α : ι → K⟦Γ⟧) : Finset ι :=
  s.filter (fun i => (ρ : WithTop Γ) ≤ (α i - a).orderTop)

/-- The explicit nonzero scalar in `polynomial:eq:initialroots`: the leading
coefficient of the scalar factor times the initials of all outside roots. -/
def initialRootScalar (a : K⟦Γ⟧) (ρ : Γ) (c : K⟦Γ⟧)
    (s : Finset ι) (α : ι → K⟦Γ⟧) : K :=
  c.leadingCoeff * ∏ i ∈ s.filter (fun i => (α i - a).orderTop < (ρ : WithTop Γ)),
    -(α i - a).leadingCoeff

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
theorem initialRootScalar_ne_zero (a : K⟦Γ⟧) (ρ : Γ) (c : K⟦Γ⟧) (hc : c ≠ 0)
    (s : Finset ι) (α : ι → K⟦Γ⟧) : initialRootScalar a ρ c s α ≠ 0 := by
  classical
  apply mul_ne_zero (_root_.HahnSeries.leadingCoeff_ne_zero.mpr hc)
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply neg_ne_zero.mpr
  apply _root_.HahnSeries.leadingCoeff_ne_zero.mpr
  intro hzero
  have hlt := (Finset.mem_filter.mp hi).2
  simp [hzero] at hlt

/-- `polynomial:eq:initialroots` with residue coordinates written as their
coefficient values. `normalizedRootResidue_eq_coeff` identifies every listed
value with the standard part of `(α i - a) / t^ρ`. -/
theorem gaussInitial_split (a : K⟦Γ⟧) (ρ : Γ) (c : K⟦Γ⟧)
    (s : Finset ι) (α : ι → K⟦Γ⟧) :
    gaussInitial a ρ (C c * ∏ i ∈ s, (X - C (α i))) =
      C (initialRootScalar a ρ c s α) *
        ∏ i ∈ closedRootIndices a ρ s α, (X - C ((α i - a).coeff ρ)) := by
  classical
  rw [gaussInitial_mul, gaussInitial_C, gaussInitial_prod]
  have hi (i : ι) : gaussInitial a ρ (X - C (α i)) =
      if (ρ : WithTop Γ) ≤ (α i - a).orderTop then
        X - C ((α i - a).coeff ρ) else C (-(α i - a).leadingCoeff) := by
    split_ifs with h
    · exact gaussInitial_X_sub_C_of_le a ρ (α i) h
    · exact gaussInitial_X_sub_C_of_lt a ρ (α i) (lt_of_not_ge h)
  simp_rw [hi]
  rw [Finset.prod_ite]
  simp only [not_le, ← map_prod, initialRootScalar, closedRootIndices, map_mul]
  ring

/-- The exact standard-part product in `polynomial:eq:initialroots`, with
membership proofs carried by the filtered indices. -/
theorem gaussInitial_split_standardPart (a : K⟦Γ⟧) (ρ : Γ) (c : K⟦Γ⟧)
    (s : Finset ι) (α : ι → K⟦Γ⟧) :
    gaussInitial a ρ (C c * ∏ i ∈ s, (X - C (α i))) =
      C (initialRootScalar a ρ c s α) *
        ∏ i ∈ (closedRootIndices a ρ s α).attach,
          (X - C (normalizedRootResidue a ρ (α i)
            (Finset.mem_filter.mp i.property).2)) := by
  rw [gaussInitial_split]
  simp only [normalizedRootResidue_eq_coeff]
  congr 1
  exact (Finset.prod_attach (closedRootIndices a ρ s α)
    (fun i => (X : K[X]) - C ((α i - a).coeff ρ))).symm

/-- Closed-ball roots counted with multiplicity equal the degree of the
initial polynomial (`polynomial:eq:closedcount`). -/
theorem natDegree_gaussInitial_split (a : K⟦Γ⟧) (ρ : Γ) (c : K⟦Γ⟧) (hc : c ≠ 0)
    (s : Finset ι) (α : ι → K⟦Γ⟧) :
    (gaussInitial a ρ (C c * ∏ i ∈ s, (X - C (α i)))).natDegree =
      (closedRootIndices a ρ s α).card := by
  rw [gaussInitial_split, natDegree_C_mul (initialRootScalar_ne_zero a ρ c hc s α),
    natDegree_finsetProd_X_sub_C_eq_card]

private theorem rootMultiplicity_prod_linear (s : Finset ι) (β : ι → K) (d : K) :
    (∏ i ∈ s, (X - C (β i))).rootMultiplicity d = (s.filter (fun i => β i = d)).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, rootMultiplicity_mul]
    · rw [rootMultiplicity_X_sub_C, ih]
      by_cases hd : β i = d
      · simp [hd, Finset.filter_insert, hi, Nat.add_comm]
      · simp [hd, Ne.symm hd, Finset.filter_insert]
    · exact mul_ne_zero (monic_X_sub_C (β i)).ne_zero
        (Finset.prod_ne_zero_iff.mpr (fun j _ => (monic_X_sub_C (β j)).ne_zero))

/-- Residue-direction multiplicity in `polynomial:thm:initialroots`, using
an explicit finite split factorization and coefficient residue coordinates. -/
theorem rootMultiplicity_gaussInitial_split (a : K⟦Γ⟧) (ρ : Γ) (c : K⟦Γ⟧)
    (hc : c ≠ 0) (s : Finset ι) (α : ι → K⟦Γ⟧) (d : K) :
    (gaussInitial a ρ (C c * ∏ i ∈ s, (X - C (α i)))).rootMultiplicity d =
      (s.filter (fun i => (ρ : WithTop Γ) ≤ (α i - a).orderTop ∧
        (α i - a).coeff ρ = d)).card := by
  classical
  rw [gaussInitial_split, ← count_roots, roots_C_mul _
    (initialRootScalar_ne_zero a ρ c hc s α), count_roots,
    rootMultiplicity_prod_linear]
  simp only [closedRootIndices, Finset.filter_filter]

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
/-- A residue-direction ball can be described without a quotient or a
membership witness: subtracting its lifted residue raises the order exactly
when the root is in the closed ball with that residue. -/
theorem orderTop_sub_single_gt_iff (β : K⟦Γ⟧) (ρ : Γ) (d : K) :
    (ρ : WithTop Γ) < (β - _root_.HahnSeries.single ρ d).orderTop ↔
      (ρ : WithTop Γ) ≤ β.orderTop ∧ β.coeff ρ = d := by
  constructor
  · intro h
    constructor
    · have hb : β = (β - _root_.HahnSeries.single ρ d) +
          _root_.HahnSeries.single ρ d := (sub_add_cancel _ _).symm
      rw [hb]
      exact (le_min h.le _root_.HahnSeries.orderTop_single_le).trans
        _root_.HahnSeries.min_orderTop_le_orderTop_add
    · have hc := _root_.HahnSeries.coeff_eq_zero_of_lt_orderTop h
      simpa only [_root_.HahnSeries.coeff_sub, _root_.HahnSeries.coeff_single_same,
        sub_eq_zero] using hc
  · rintro ⟨h, hc⟩
    have hle : (ρ : WithTop Γ) ≤ (β - _root_.HahnSeries.single ρ d).orderTop :=
      (le_min h _root_.HahnSeries.orderTop_single_le).trans
        _root_.HahnSeries.min_orderTop_le_orderTop_sub
    apply lt_of_le_of_ne hle
    apply (_root_.HahnSeries.orderTop_ne_of_coeff_eq_zero _).symm
    simp [hc]

/-- The last assertion of `polynomial:thm:initialroots`: the multiplicity
of `d` in the initial polynomial counts roots in the open ball centered at
`a + t^ρ d` of radius exponent `ρ`. This is precisely the residue direction
`a + t^ρ (d + maximalIdeal)`, expressed directly by its valuation. -/
theorem rootMultiplicity_gaussInitial_split_direction (a : K⟦Γ⟧) (ρ : Γ)
    (c : K⟦Γ⟧) (hc : c ≠ 0) (s : Finset ι) (α : ι → K⟦Γ⟧) (d : K) :
    (gaussInitial a ρ (C c * ∏ i ∈ s, (X - C (α i)))).rootMultiplicity d =
      (s.filter (fun i => (ρ : WithTop Γ) <
        (α i - (a + _root_.HahnSeries.single ρ d)).orderTop)).card := by
  classical
  rw [rootMultiplicity_gaussInitial_split a ρ c hc s α]
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [sub_add_eq_sub_sub, orderTop_sub_single_gt_iff]

/-- Open-ball roots counted with multiplicity equal the order at zero of
the initial polynomial (`polynomial:eq:opencount`). A root at the center,
whose order is `⊤`, belongs to every such open ball. -/
theorem natTrailingDegree_gaussInitial_split (a : K⟦Γ⟧) (ρ : Γ)
    (c : K⟦Γ⟧) (hc : c ≠ 0) (s : Finset ι) (α : ι → K⟦Γ⟧) :
    (gaussInitial a ρ (C c * ∏ i ∈ s, (X - C (α i)))).natTrailingDegree =
      (s.filter (fun i => (ρ : WithTop Γ) < (α i - a).orderTop)).card := by
  rw [← rootMultiplicity_eq_natTrailingDegree',
    rootMultiplicity_gaussInitial_split_direction a ρ c hc s α 0]
  simp

/-- Shell-root count as degree minus trailing degree
(`polynomial:eq:shellcount`). -/
theorem shell_count_gaussInitial_split (a : K⟦Γ⟧) (ρ : Γ)
    (c : K⟦Γ⟧) (hc : c ≠ 0) (s : Finset ι) (α : ι → K⟦Γ⟧) :
    (s.filter (fun i => (α i - a).orderTop = (ρ : WithTop Γ))).card =
      (gaussInitial a ρ (C c * ∏ i ∈ s, (X - C (α i)))).natDegree -
        (gaussInitial a ρ (C c * ∏ i ∈ s, (X - C (α i)))).natTrailingDegree := by
  classical
  rw [natDegree_gaussInitial_split a ρ c hc s α,
    natTrailingDegree_gaussInitial_split a ρ c hc s α]
  have hcard := Finset.card_filter_add_card_filter_not
    (s := closedRootIndices a ρ s α)
    (fun i => (ρ : WithTop Γ) < (α i - a).orderTop)
  have hlt : (closedRootIndices a ρ s α).filter
      (fun i => (ρ : WithTop Γ) < (α i - a).orderTop) =
      s.filter (fun i => (ρ : WithTop Γ) < (α i - a).orderTop) := by
    ext i
    simp only [closedRootIndices, Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.le⟩, h.2⟩⟩
  have heq : (closedRootIndices a ρ s α).filter
      (fun i => ¬ (ρ : WithTop Γ) < (α i - a).orderTop) =
      s.filter (fun i => (α i - a).orderTop = (ρ : WithTop Γ)) := by
    ext i
    simp only [closedRootIndices, Finset.mem_filter, not_lt]
    exact ⟨fun h => ⟨h.1.1, le_antisymm h.2 h.1.2⟩,
      fun h => ⟨⟨h.1, h.2.ge⟩, h.2.le⟩⟩
  rw [hlt, heq] at hcard
  omega

end

end Surreal.HahnSeries
