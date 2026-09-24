import Surreal.HahnSeries.PolynomialSimpleRootLifting
import Mathlib.Algebra.Polynomial.Identities
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.LinearCombination

/-!
# Exact branch metric for expanding polynomial maps

This file formalizes `epd:prop:branches` of
`docs/surcomplex/expanding-polynomial-dynamics/article.tex`, for the family
`epd:eq:polynomial`, in the Hahn workspace `K = k⟦Γ⟧` with integral ring
`𝒪 = nonnegativeSubring Γ k`, valuation `orderTop` (so `v(0) = ⊤`) and residue map
`st = standardPart Γ k`.

Generic statements, for a polynomial `P` over `𝒪` and a residue value `c`:
* `exists_divided_difference` and `orderTop_eval_sub_eval`: a divided-difference factor `D`
  with `P(x) - P(y) = (x - y) D` has residue `P̄'(c)` on the residue class of `c`, so
  `v(P(x) - P(y)) = v(x - y)` whenever `P̄'(c) ≠ 0`. No leading-coefficient hypothesis is used.
* `existsUnique_eval_eq`: if `P` has unit leading coefficient and `P̄'(c) ≠ 0`, every `b ∈ 𝒪` with
  `st b = P̄(c)` has exactly one preimage in the residue class of `c`. Existence reuses the
  simple-root lift `existsUnique_root_of_simple_standardPart`.
* `branch` is the inverse branch `Φ_c(w)`, the unique `y ∈ 𝒪` with `st y = c` and
  `P(y) = q w`, for any `q ∈ 𝔪` (`q = 0` is allowed). `orderTop_branch_sub` is
  `epd:eq:branch-metric`, `v(Φ_c(w) - Φ_c(z)) = v(q) + v(w - z)`.
* `forwardMap P q` is `F = q⁻¹ P` on `K`; `orderTop_forwardMap_sub` is `epd:eq:forward-metric`,
  `v(F(x) - F(y)) = v(x - y) - v(q)`, in `WithTop Γ` with `⊤ - κ = ⊤`, for every nonzero
  `q ∈ K` (`orderTop_forwardMap_sub_add` is the additive form). `forwardMap_branch` and
  `branch_injective` record that `F` inverts each branch.

`branches` is `epd:prop:branches` for `P = P₀ + ∑_{j ≤ d} e_j X^j` with
`P₀ = a_d ∏_{i=1}^d (X - c_i)`, `a_d ≠ 0`, distinct `c_i ∈ k`, `e_j ∈ 𝔪`, and `q ∈ 𝔪 \ {0}`:
all three clauses (unique integral branches, the branch metric, the forward metric) are proved.
`natDegree_perturbedPolynomial` and `isUnit_leadingCoeff_perturbedPolynomial` give the remark
that `P` has degree `d` and unit leading coefficient.

Generality: `k` is an arbitrary field (the source takes `ℝ` or `ℂ`), `Γ` is any ordered abelian
group, and the hypothesis `d ≥ 2` is not used. The source's existence proof, through the
universal formal branch `Ψ_i` of `epd:lem:formalbranch` and strong evaluation
`epd:lem:evaluation`, is not formalized here; existence comes from the Hahn simple-root lift.
No clause of `epd:prop:branches` remains pending.
-/

namespace Surreal.BranchMetric

open Polynomial
open scoped _root_.HahnSeries
open Surreal.HahnSeries

noncomputable section

variable {Γ k : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field k]

local notation "𝒪" => nonnegativeSubring Γ k

/-! ### Residues and valuations -/

/-- An integral element with nonzero residue has valuation exactly zero. -/
theorem orderTop_eq_zero_of_standardPart_ne_zero {D : 𝒪} (hD : standardPart Γ k D ≠ 0) :
    (D : k⟦Γ⟧).orderTop = 0 := by
  have h : (D : k⟦Γ⟧).coeff 0 ≠ 0 := hD
  exact le_antisymm (by simpa using _root_.HahnSeries.orderTop_le_of_coeff_ne_zero h)
    ((mem_nonnegativeSubring _).mp D.property)

/-- Elements of the maximal ideal `𝔪` have residue zero. -/
theorem standardPart_eq_zero_of_orderTop_pos {q : 𝒪} (hq : 0 < (q : k⟦Γ⟧).orderTop) :
    standardPart Γ k q = 0 :=
  (coeff_zero_eq_zero_iff_orderTop_pos _ ((mem_nonnegativeSubring _).mp q.property)).mpr hq

/-! ### The divided difference -/

/-- A divided-difference factor for `P(x) - P(y) = (x - y) D`, as in the proof of
`epd:prop:branches`: some `D ∈ 𝒪` satisfies this identity, and when `st x = st y` its residue is
the derivative of the residue polynomial at `st y`. -/
theorem exists_divided_difference (P : Polynomial 𝒪) (x y : 𝒪) :
    ∃ D : 𝒪, P.eval x - P.eval y = (x - y) * D ∧
      (standardPart Γ k x = standardPart Γ k y →
        standardPart Γ k D =
          (P.map (standardPart Γ k)).derivative.eval (standardPart Γ k y)) := by
  obtain ⟨m, hm⟩ := binomExpansion P y (x - y)
  rw [add_sub_cancel] at hm
  refine ⟨P.derivative.eval y + m * (x - y), by linear_combination hm, fun hxy => ?_⟩
  rw [map_add, map_mul, map_sub, hxy, sub_self, mul_zero, add_zero, derivative_map,
    eval_map_apply]

/-- `epd:prop:branches`, the key step of its proof: on a residue class where the residue
derivative is nonzero, `v(P(x) - P(y)) = v(x - y)`. Equal inputs give `⊤` on both sides. -/
theorem orderTop_eval_sub_eval (P : Polynomial 𝒪) {x y : 𝒪}
    (hxy : standardPart Γ k x = standardPart Γ k y)
    (hd : (P.map (standardPart Γ k)).derivative.eval (standardPart Γ k y) ≠ 0) :
    ((P.eval x - P.eval y : 𝒪) : k⟦Γ⟧).orderTop = ((x - y : 𝒪) : k⟦Γ⟧).orderTop := by
  obtain ⟨D, hD, hDst⟩ := exists_divided_difference P x y
  rw [hD, Subring.coe_mul, _root_.HahnSeries.orderTop_mul,
    orderTop_eq_zero_of_standardPart_ne_zero ((hDst hxy).trans_ne hd), add_zero]

/-! ### Unique integral branches -/

/-- A polynomial over `𝒪` with unit leading coefficient and a residue value `c` at which the
residue derivative is nonzero takes every value `b` with `st b = P̄(c)` at exactly one integral
point of residue `c`. -/
theorem existsUnique_eval_eq (P : Polynomial 𝒪) (hlead : IsUnit P.leadingCoeff) {c : k}
    (hd : (P.map (standardPart Γ k)).derivative.eval c ≠ 0) {b : 𝒪}
    (hb : standardPart Γ k b = (P.map (standardPart Γ k)).eval c) :
    ∃! y : 𝒪, standardPart Γ k y = c ∧ P.eval y = b := by
  have hdeg : 0 < P.natDegree := by
    refine Nat.pos_of_ne_zero fun h0 => hd ?_
    rw [derivative_map, derivative_of_natDegree_zero h0, Polynomial.map_zero, eval_zero]
  have hlc : (P - C b).leadingCoeff = P.leadingCoeff :=
    leadingCoeff_sub_of_degree_lt (degree_C_le.trans_lt (natDegree_pos_iff_degree_pos.mp hdeg))
  obtain ⟨u, hu⟩ := hlead
  have hH : (C (↑u⁻¹ : 𝒪) * (P - C b)).Monic := by
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [hlc, ← hu, Units.inv_mul]
  have hmap : (C (↑u⁻¹ : 𝒪) * (P - C b)).map (standardPart Γ k) =
      C (standardPart Γ k ↑u⁻¹) * (P.map (standardPart Γ k) - C (standardPart Γ k b)) := by
    rw [Polynomial.map_mul, Polynomial.map_sub, map_C, map_C]
  have hunit : standardPart Γ k ↑u⁻¹ ≠ 0 := (u⁻¹.isUnit.map (standardPart Γ k)).ne_zero
  have hroot : ((C (↑u⁻¹ : 𝒪) * (P - C b)).map (standardPart Γ k)).IsRoot c := by
    rw [IsRoot.def, hmap, eval_mul, eval_sub, eval_C, eval_C, hb, sub_self, mul_zero]
  have hder : ((C (↑u⁻¹ : 𝒪) * (P - C b)).map (standardPart Γ k)).derivative.eval c ≠ 0 := by
    rw [hmap, derivative_C_mul, derivative_sub, derivative_C, sub_zero, eval_mul, eval_C]
    exact mul_ne_zero hunit hd
  obtain ⟨z, ⟨hz, hzc⟩, huniq⟩ := existsUnique_root_of_simple_standardPart _ hH c hroot hder
  have hHeval : ∀ y : 𝒪, (C (↑u⁻¹ : 𝒪) * (P - C b)).eval y = ↑u⁻¹ * (P.eval y - b) := by
    intro y
    rw [eval_mul, eval_sub, eval_C, eval_C]
  refine ⟨z, ⟨hzc, ?_⟩, fun y hy => huniq y ⟨?_, hy.1⟩⟩
  · have h := hz.eq_zero
    rwa [hHeval, Units.mul_right_eq_zero, sub_eq_zero] at h
  · rw [IsRoot.def, hHeval, hy.2, sub_self, mul_zero]

/-- The standing hypotheses of `epd:prop:branches` at one residue root `c`: the polynomial has
unit leading coefficient and `c` is a simple root of its residue polynomial. -/
structure SimpleResidueRoot (P : Polynomial 𝒪) (c : k) : Prop where
  isUnit_leadingCoeff : IsUnit P.leadingCoeff
  isRoot : (P.map (standardPart Γ k)).IsRoot c
  eval_derivative_ne_zero : (P.map (standardPart Γ k)).derivative.eval c ≠ 0

/-- `epd:prop:branches`, first clause: for `q ∈ 𝔪` and every `w ∈ 𝒪` there is a unique
`y ∈ 𝒪` with `st y = c` and `P(y) = q w`. -/
theorem SimpleResidueRoot.existsUnique {P : Polynomial 𝒪} {c : k}
    (h : SimpleResidueRoot P c) {q : 𝒪} (hq : 0 < (q : k⟦Γ⟧).orderTop) (w : 𝒪) :
    ∃! y : 𝒪, standardPart Γ k y = c ∧ P.eval y = q * w :=
  existsUnique_eval_eq P h.isUnit_leadingCoeff h.eval_derivative_ne_zero
    (by rw [map_mul, standardPart_eq_zero_of_orderTop_pos hq, zero_mul, h.isRoot.eq_zero])

/-- The integral inverse branch `Φ_i(w)` of `epd:prop:branches`: the unique `y ∈ 𝒪` with
`st y = c` and `P(y) = q w`. -/
def branch {P : Polynomial 𝒪} {c : k} (h : SimpleResidueRoot P c) {q : 𝒪}
    (hq : 0 < (q : k⟦Γ⟧).orderTop) (w : 𝒪) : 𝒪 :=
  (h.existsUnique hq w).exists.choose

theorem standardPart_branch {P : Polynomial 𝒪} {c : k} (h : SimpleResidueRoot P c) {q : 𝒪}
    (hq : 0 < (q : k⟦Γ⟧).orderTop) (w : 𝒪) : standardPart Γ k (branch h hq w) = c :=
  (h.existsUnique hq w).exists.choose_spec.1

theorem eval_branch {P : Polynomial 𝒪} {c : k} (h : SimpleResidueRoot P c) {q : 𝒪}
    (hq : 0 < (q : k⟦Γ⟧).orderTop) (w : 𝒪) : P.eval (branch h hq w) = q * w :=
  (h.existsUnique hq w).exists.choose_spec.2

/-- Uniqueness of the branch value. -/
theorem eq_branch {P : Polynomial 𝒪} {c : k} (h : SimpleResidueRoot P c) {q : 𝒪}
    (hq : 0 < (q : k⟦Γ⟧).orderTop) {w y : 𝒪} (hyc : standardPart Γ k y = c)
    (hy : P.eval y = q * w) : y = branch h hq w :=
  (h.existsUnique hq w).unique ⟨hyc, hy⟩ ⟨standardPart_branch h hq w, eval_branch h hq w⟩

/-- `epd:eq:branch-metric`: `v(Φ_i(w) - Φ_i(z)) = κ + v(w - z)` with `κ = v(q)`. -/
theorem orderTop_branch_sub {P : Polynomial 𝒪} {c : k} (h : SimpleResidueRoot P c) {q : 𝒪}
    (hq : 0 < (q : k⟦Γ⟧).orderTop) (w z : 𝒪) :
    ((branch h hq w - branch h hq z : 𝒪) : k⟦Γ⟧).orderTop =
      (q : k⟦Γ⟧).orderTop + ((w - z : 𝒪) : k⟦Γ⟧).orderTop := by
  have hxy : standardPart Γ k (branch h hq w) = standardPart Γ k (branch h hq z) := by
    rw [standardPart_branch, standardPart_branch]
  have hd : (P.map (standardPart Γ k)).derivative.eval (standardPart Γ k (branch h hq z)) ≠ 0 := by
    rw [standardPart_branch]
    exact h.eval_derivative_ne_zero
  rw [← orderTop_eval_sub_eval P hxy hd, eval_branch, eval_branch, ← mul_sub, Subring.coe_mul,
    _root_.HahnSeries.orderTop_mul]

/-! ### The forward map -/

/-- The expanding map `F = q⁻¹ P` on the Hahn field `K`. -/
def forwardMap (P : Polynomial 𝒪) (q x : k⟦Γ⟧) : k⟦Γ⟧ :=
  q⁻¹ * (P.map (nonnegativeSubring Γ k).subtype).eval x

theorem forwardMap_coe (P : Polynomial 𝒪) (q : k⟦Γ⟧) (x : 𝒪) :
    forwardMap P q x = q⁻¹ * ((P.eval x : 𝒪) : k⟦Γ⟧) :=
  congrArg (q⁻¹ * ·) (eval_map_apply (p := P) (f := (nonnegativeSubring Γ k).subtype) x)

/-- `epd:eq:forward-metric`, additive form: `v(F(x) - F(y)) + v(q) = v(x - y)` on a residue
class where the residue derivative is nonzero. Here `q` is any nonzero element of `K`. -/
theorem orderTop_forwardMap_sub_add (P : Polynomial 𝒪) {q : k⟦Γ⟧} (hq : q ≠ 0) {x y : 𝒪}
    (hxy : standardPart Γ k x = standardPart Γ k y)
    (hd : (P.map (standardPart Γ k)).derivative.eval (standardPart Γ k y) ≠ 0) :
    (forwardMap P q x - forwardMap P q y).orderTop + q.orderTop =
      ((x : k⟦Γ⟧) - y).orderTop := by
  have hinv : q⁻¹.orderTop + q.orderTop = 0 := by
    rw [← _root_.HahnSeries.orderTop_mul, inv_mul_cancel₀ hq, _root_.HahnSeries.orderTop_one]
  have hsub : forwardMap P q x - forwardMap P q y =
      q⁻¹ * ((P.eval x - P.eval y : 𝒪) : k⟦Γ⟧) := by
    rw [forwardMap_coe, forwardMap_coe, AddSubgroupClass.coe_sub, mul_sub]
  rw [hsub, _root_.HahnSeries.orderTop_mul, add_right_comm, hinv, zero_add,
    orderTop_eval_sub_eval P hxy hd, AddSubgroupClass.coe_sub]

/-- `epd:eq:forward-metric`: `v(F(x) - F(y)) = v(x - y) - κ` with `κ = v(q)`, on a residue
class where the residue derivative is nonzero. Equal inputs give `⊤ - κ = ⊤`. -/
theorem orderTop_forwardMap_sub (P : Polynomial 𝒪) {q : k⟦Γ⟧} (hq : q ≠ 0) {x y : 𝒪}
    (hxy : standardPart Γ k x = standardPart Γ k y)
    (hd : (P.map (standardPart Γ k)).derivative.eval (standardPart Γ k y) ≠ 0) :
    (forwardMap P q x - forwardMap P q y).orderTop =
      ((x : k⟦Γ⟧) - y).orderTop - q.orderTop := by
  rw [← orderTop_forwardMap_sub_add P hq hxy hd]
  exact ((sub_eq_add_neg _ _).trans
    (LinearOrderedAddCommGroupWithTop.add_neg_cancel_right_of_ne_top
      (_root_.HahnSeries.orderTop_ne_top.mpr hq) _)).symm

/-- `F` inverts each integral branch: `F(Φ_i(w)) = w` when `q ≠ 0`. -/
theorem forwardMap_branch {P : Polynomial 𝒪} {c : k} (h : SimpleResidueRoot P c) {q : 𝒪}
    (hq : 0 < (q : k⟦Γ⟧).orderTop) (hq0 : q ≠ 0) (w : 𝒪) :
    forwardMap P q (branch h hq w) = w := by
  rw [forwardMap_coe, eval_branch, Subring.coe_mul,
    inv_mul_cancel_left₀ (mt (Subring.coe_eq_zero_iff _).mp hq0)]

/-- Each integral branch is injective when `q ≠ 0`. -/
theorem branch_injective {P : Polynomial 𝒪} {c : k} (h : SimpleResidueRoot P c) {q : 𝒪}
    (hq : 0 < (q : k⟦Γ⟧).orderTop) (hq0 : q ≠ 0) : Function.Injective (branch h hq) := by
  intro w z hwz
  apply Subtype.ext
  rw [← forwardMap_branch h hq hq0 w, ← forwardMap_branch h hq hq0 z, hwz]

/-! ### The family `epd:eq:polynomial` -/

/-- The split residue polynomial `P₀ = a_d ∏_{i=1}^d (X - c_i)` of `epd:eq:polynomial`. -/
def residuePolynomial {d : ℕ} (a : k) (c : Fin d → k) : k[X] :=
  C a * ∏ i, (X - C (c i))

/-- The polynomial `P = P₀ + ∑_{j=0}^d e_j X^j` of `epd:eq:polynomial`, with the coefficients
of `P₀` embedded as constants. -/
def perturbedPolynomial {d : ℕ} (a : k) (c : Fin d → k) (e : Fin (d + 1) → 𝒪) :
    Polynomial 𝒪 :=
  (residuePolynomial a c).map (constantNonnegative (Γ := Γ)) + ∑ j, C (e j) * X ^ (j : ℕ)

theorem residuePolynomial_ne_zero {d : ℕ} {a : k} (ha : a ≠ 0) (c : Fin d → k) :
    residuePolynomial a c ≠ 0 :=
  mul_ne_zero (C_ne_zero.mpr ha) (monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (c i)).ne_zero

theorem natDegree_residuePolynomial {d : ℕ} {a : k} (ha : a ≠ 0) (c : Fin d → k) :
    (residuePolynomial a c).natDegree = d := by
  rw [residuePolynomial, natDegree_C_mul ha, natDegree_finsetProd_X_sub_C_eq_card,
    Finset.card_univ, Fintype.card_fin]

theorem isRoot_residuePolynomial {d : ℕ} (a : k) (c : Fin d → k) (i : Fin d) :
    (residuePolynomial a c).IsRoot (c i) := by
  rw [IsRoot.def, residuePolynomial, eval_mul, ← Lagrange.nodal_eq,
    Lagrange.eval_nodal_at_node (Finset.mem_univ i), mul_zero]

/-- Distinct residue roots are simple: `P₀'(c_i) = a_d ∏_{j ≠ i} (c_i - c_j) ≠ 0`. -/
theorem eval_derivative_residuePolynomial_ne_zero {d : ℕ} {a : k} (ha : a ≠ 0) {c : Fin d → k}
    (hc : Function.Injective c) (i : Fin d) :
    (residuePolynomial a c).derivative.eval (c i) ≠ 0 := by
  rw [residuePolynomial, derivative_C_mul, eval_mul, eval_C, ← Lagrange.nodal_eq,
    Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ i)]
  exact mul_ne_zero ha (Lagrange.eval_nodal_not_at_node fun j hj =>
    hc.ne (Finset.ne_of_mem_erase hj).symm)

/-- The residue polynomial of `P` is `P₀`, since every `e_j` lies in `𝔪`. -/
theorem map_perturbedPolynomial {d : ℕ} (a : k) (c : Fin d → k) {e : Fin (d + 1) → 𝒪}
    (he : ∀ j, 0 < ((e j : 𝒪) : k⟦Γ⟧).orderTop) :
    (perturbedPolynomial a c e).map (standardPart Γ k) = residuePolynomial a c := by
  have he0 : ∀ j, standardPart Γ k (e j) = 0 := fun j =>
    standardPart_eq_zero_of_orderTop_pos (he j)
  simp only [perturbedPolynomial, Polynomial.map_add, Polynomial.map_map,
    standardPart_comp_constantNonnegative, Polynomial.map_id, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_pow, map_C, map_X, he0, map_zero, zero_mul,
    Finset.sum_const_zero, add_zero]

theorem natDegree_perturbedPolynomial_le {d : ℕ} (a : k) (c : Fin d → k)
    (e : Fin (d + 1) → 𝒪) : (perturbedPolynomial a c e).natDegree ≤ d := by
  refine natDegree_add_le_of_degree_le (natDegree_map_le.trans ?_) ?_
  · have h := natDegree_C_mul_le a (∏ i, (X - C (c i)))
    rw [natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ, Fintype.card_fin] at h
    exact h
  · exact natDegree_sum_le_of_forall_le _ _ fun j _ =>
      (natDegree_C_mul_X_pow_le _ _).trans j.is_le

/-- If reduction does not lower the degree of a polynomial over `𝒪` with nonzero reduction,
its leading coefficient is a unit. -/
theorem isUnit_leadingCoeff_of_natDegree_le {Q : Polynomial 𝒪}
    (hQ : Q.map (standardPart Γ k) ≠ 0)
    (hdeg : Q.natDegree ≤ (Q.map (standardPart Γ k)).natDegree) : IsUnit Q.leadingCoeff := by
  have heq : (Q.map (standardPart Γ k)).natDegree = Q.natDegree :=
    le_antisymm natDegree_map_le hdeg
  rw [isUnit_iff_standardPart_ne_zero, Polynomial.leadingCoeff, ← heq, ← coeff_map]
  exact leadingCoeff_ne_zero.mpr hQ

/-- The remark after `epd:eq:polynomial`: `P` has degree `d`. -/
theorem natDegree_perturbedPolynomial {d : ℕ} {a : k} (ha : a ≠ 0) (c : Fin d → k)
    {e : Fin (d + 1) → 𝒪} (he : ∀ j, 0 < ((e j : 𝒪) : k⟦Γ⟧).orderTop) :
    (perturbedPolynomial a c e).natDegree = d := by
  refine le_antisymm (natDegree_perturbedPolynomial_le a c e) ?_
  have h := natDegree_map_le (p := perturbedPolynomial a c e) (f := standardPart Γ k)
  rwa [map_perturbedPolynomial a c he, natDegree_residuePolynomial ha c] at h

/-- The remark after `epd:eq:polynomial`: `P` has unit leading coefficient. -/
theorem isUnit_leadingCoeff_perturbedPolynomial {d : ℕ} {a : k} (ha : a ≠ 0) (c : Fin d → k)
    {e : Fin (d + 1) → 𝒪} (he : ∀ j, 0 < ((e j : 𝒪) : k⟦Γ⟧).orderTop) :
    IsUnit (perturbedPolynomial a c e).leadingCoeff := by
  refine isUnit_leadingCoeff_of_natDegree_le ?_ ?_ <;> rw [map_perturbedPolynomial a c he]
  · exact residuePolynomial_ne_zero ha c
  · rw [natDegree_residuePolynomial ha c]
    exact natDegree_perturbedPolynomial_le a c e

/-- Each `c_i` is a simple residue root of the polynomial of `epd:eq:polynomial`. -/
theorem simpleResidueRoot_perturbedPolynomial {d : ℕ} {a : k} (ha : a ≠ 0) {c : Fin d → k}
    (hc : Function.Injective c) {e : Fin (d + 1) → 𝒪}
    (he : ∀ j, 0 < ((e j : 𝒪) : k⟦Γ⟧).orderTop) (i : Fin d) :
    SimpleResidueRoot (perturbedPolynomial a c e) (c i) where
  isUnit_leadingCoeff := isUnit_leadingCoeff_perturbedPolynomial ha c he
  isRoot := by
    rw [map_perturbedPolynomial a c he]
    exact isRoot_residuePolynomial a c i
  eval_derivative_ne_zero := by
    rw [map_perturbedPolynomial a c he]
    exact eval_derivative_residuePolynomial_ne_zero ha hc i

/-- `epd:prop:branches` for the family `epd:eq:polynomial`, with `κ = v(q)`: for every `i`,
(1) each `w ∈ 𝒪` has a unique `y ∈ 𝒪` with `st y = c_i` and `P(y) = q w`; this `y` is
`Φ_i(w) = branch _ hq w` by `standardPart_branch`, `eval_branch` and `eq_branch`;
(2) `v(Φ_i(w) - Φ_i(z)) = κ + v(w - z)`; (3) for `x, y ∈ 𝒪` with residue `c_i`,
`v(F(x) - F(y)) = v(x - y) - κ` where `F = q⁻¹ P`. Equal inputs give `⊤`. -/
theorem branches {d : ℕ} {a : k} (ha : a ≠ 0) {c : Fin d → k} (hc : Function.Injective c)
    {e : Fin (d + 1) → 𝒪} (he : ∀ j, 0 < ((e j : 𝒪) : k⟦Γ⟧).orderTop)
    {q : 𝒪} (hq : 0 < (q : k⟦Γ⟧).orderTop) (hq0 : q ≠ 0) (i : Fin d) :
    (∀ w : 𝒪, ∃! y : 𝒪, standardPart Γ k y = c i ∧
        (perturbedPolynomial a c e).eval y = q * w) ∧
      (∀ w z : 𝒪,
        ((branch (simpleResidueRoot_perturbedPolynomial ha hc he i) hq w -
            branch (simpleResidueRoot_perturbedPolynomial ha hc he i) hq z : 𝒪) :
              k⟦Γ⟧).orderTop =
          (q : k⟦Γ⟧).orderTop + ((w - z : 𝒪) : k⟦Γ⟧).orderTop) ∧
      (∀ x y : 𝒪, standardPart Γ k x = c i → standardPart Γ k y = c i →
        (forwardMap (perturbedPolynomial a c e) q x -
            forwardMap (perturbedPolynomial a c e) q y).orderTop =
          ((x : k⟦Γ⟧) - y).orderTop - (q : k⟦Γ⟧).orderTop) := by
  have h := simpleResidueRoot_perturbedPolynomial ha hc he i
  refine ⟨h.existsUnique hq, orderTop_branch_sub h hq, fun x y hx hy => ?_⟩
  refine orderTop_forwardMap_sub _ (mt (Subring.coe_eq_zero_iff _).mp hq0) (hx.trans hy.symm) ?_
  rw [hy]
  exact h.eval_derivative_ne_zero

end

end Surreal.BranchMetric
