import Surreal.Algebra.Modulus
import Surreal.Surcomplex.AlgebraicallyClosed
import Surreal.Surcomplex.Modulus
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Convex.Combination

/-!
# Jensen disks and weighted incomplete polynomials

This module proves `polynomial:thm:jensen` (the surcomplex Jensen disk theorem,
including the computation `polynomial:eq:jensencalc` and the real-root step of
its proof) and `polynomial:prop:weighted` (weighted incomplete polynomials and
their converse to Gauss--Lucas) from
`docs/surcomplex/polynomial-algebra/article.tex`.

The coefficient field is an arbitrary ordered field `F` and `K = F[i]` is its
quadratic complexification `Complexify F`; no Archimedean or topological
assumption is used.

* `polynomial:prop:weighted` is proved over every ordered field, without square
  roots: every root of `Q_λ(z) = ∑_j λ_j ∏_{k ≠ j} (z - α_k)` with `λ_j ≥ 0`,
  `∑ λ_j > 0` lies in the `F`-convex hull of the nodes, and, for at least two
  nodes, every point of that hull is such a root. The index type is an
  arbitrary finite type; the source's `n ≥ 2` is `Nontrivial`, with a `Fin n`
  form. For one node the root set is empty, so that hypothesis is needed.
* `polynomial:thm:jensen` is proved for every nonconstant `P ∈ F[z]` whose image
  in `K[z]` splits: every nonreal critical point lies in the closed order disk
  whose diameter has endpoints a pair `a, conj a` of conjugate nonreal roots.
  The square-root-free (`normSq`) form `(x - Re a)² + y² ≤ (Im a)²` holds over
  every ordered field; the modulus and diameter-disk forms use nonnegative
  square roots in `F`. The first step of the proof, that conjugation preserves
  the root multiset, is `aroots_map_star` (with the membership form
  `star_mem_aroots`). The constant polynomial `1` shows that nonconstancy cannot
  be dropped, and a real-rooted polynomial has only real critical points.
* On the actual surcomplex numbers, splitting is automatic
  (`Surcomplex.surcomplexIsAlgClosed`), so both results hold unconditionally
  for surreal coefficients.

The splitting hypothesis is the only assumption beyond the source: the report
takes `K` algebraically closed. The generic theorems are not instantiated at
the source's Hahn workspace `F_Γ = ℝ((t^Γ))`. Nonnegative square roots in the
ordered Hahn field are already available (`Surreal.HahnSeries.hahnLexHasNonnegSquareRoots`,
for divisible `Γ` and coefficients with nonnegative square roots), so the only
missing ingredient for that instantiation is splitting over
`Complexify (Lex ℝ⟦Γ⟧)`.
-/

universe u

namespace Surreal.PolynomialJensen

open Polynomial Finset Surreal.Complexify

noncomputable section

section OrderedField

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-! ### Conjugation and real polynomials -/

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- Conjugation fixes the embedded base field. -/
theorem star_algebraMap (r : F) :
    star (algebraMap F (Complexify F) r) = algebraMap F (Complexify F) r := by
  ext <;> simp

/-- A polynomial with coefficients in `F` commutes with conjugation. -/
theorem aeval_star (P : F[X]) (z : Complexify F) :
    aeval (star z) P = star (aeval z P) := by
  have hcomp : (starRingEnd (Complexify F)).comp (algebraMap F (Complexify F)) =
      algebraMap F (Complexify F) := by
    refine RingHom.ext fun r => ?_
    simp only [RingHom.comp_apply, starRingEnd_apply, star_algebraMap]
  have h := hom_eval₂ (p := P) (f := algebraMap F (Complexify F))
    (g := starRingEnd (Complexify F)) (x := z)
  rw [hcomp, starRingEnd_apply, starRingEnd_apply] at h
  rw [aeval_def, aeval_def, h]

/-- The roots in `F[i]` of a polynomial over `F` are closed under conjugation. -/
theorem star_mem_aroots {P : F[X]} {a : Complexify F} (ha : a ∈ P.aroots (Complexify F)) :
    star a ∈ P.aroots (Complexify F) := by
  rw [mem_aroots] at ha ⊢
  exact ⟨ha.1, by rw [aeval_star, ha.2, star_zero]⟩

/-- Conjugation fixes the image of a polynomial over `F` in `F[i][z]`. -/
theorem map_starRingEnd_map (P : F[X]) :
    (P.map (algebraMap F (Complexify F))).map (starRingEnd (Complexify F)) =
      P.map (algebraMap F (Complexify F)) := by
  rw [Polynomial.map_map]
  congr 1
  refine RingHom.ext fun r => ?_
  simp only [RingHom.comp_apply, starRingEnd_apply, star_algebraMap]

/-- The first step of the proof of `polynomial:thm:jensen`: conjugation preserves
the root multiset in `F[i]` of a polynomial over `F`, multiplicities included. -/
theorem aroots_map_star (P : F[X]) :
    (P.aroots (Complexify F)).map star = P.aroots (Complexify F) := by
  have hle := map_roots_le_of_injective (P.map (algebraMap F (Complexify F)))
    (starRingEnd (Complexify F)).injective
  rw [map_starRingEnd_map] at hle
  have hf : ((starRingEnd (Complexify F) : Complexify F → Complexify F)) = star :=
    funext fun z => starRingEnd_apply z
  rw [hf] at hle
  rw [aroots_def]
  exact Multiset.eq_of_le_of_card_le hle (by rw [Multiset.card_map])

/-! ### The disk computation -/

/-- `polynomial:eq:jensencalc`: for a nonreal point `w = x + iy` and a root pair
`a, conj a`, the imaginary part of the pair's contribution to the logarithmic
derivative, divided by `y`, is `-2((x - Re a)² + y² - (Im a)²)` over the product
of the two squared distances. -/
theorem jensen_calc (w a : Complexify F) (hw : w.im ≠ 0) (h₁ : w ≠ a) (h₂ : w ≠ star a) :
    ((w - a)⁻¹ + (w - star a)⁻¹).im / w.im =
      -2 * ((w.re - a.re) ^ 2 + w.im ^ 2 - a.im ^ 2) /
        (normSq (w - a) * normSq (w - star a)) := by
  have hN₁ : normSq (w - a) ≠ 0 := (normSq_pos (sub_ne_zero.mpr h₁)).ne'
  have hN₂ : normSq (w - star a) ≠ 0 := (normSq_pos (sub_ne_zero.mpr h₂)).ne'
  rw [QuadraticAlgebra.im_add, Complexify.inv_im, Complexify.inv_im,
    div_add_div _ _ hN₁ hN₂, div_div,
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hN₁ hN₂) hw) (mul_ne_zero hN₁ hN₂)]
  simp only [normSq, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, conj_re, conj_im]
  ring

/-- The real-root step of the proof of `polynomial:thm:jensen`: for a real root
`r` and a nonreal point `w = x + iy`, `y⁻¹ Im (w - r)⁻¹ = -|w - r|⁻²`. -/
theorem jensen_calc_real (w r : Complexify F) (hw : w.im ≠ 0) (hr : r.im = 0) :
    (w - r)⁻¹.im / w.im = -(normSq (w - r))⁻¹ := by
  have hN : normSq (w - r) ≠ 0 := by
    apply (normSq_pos _).ne'
    intro h
    apply hw
    have := congrArg QuadraticAlgebra.im h
    simpa [hr] using this
  rw [Complexify.inv_im, QuadraticAlgebra.im_sub, hr, sub_zero, div_div,
    div_eq_iff (mul_ne_zero hN hw)]
  field_simp

/-- The sign recorded in the real-root step of the proof of `polynomial:thm:jensen`:
for a real root `r` and a nonreal point `w = x + iy`, `y⁻¹ Im (w - r)⁻¹ < 0`. -/
theorem jensen_calc_real_neg (w r : Complexify F) (hw : w.im ≠ 0) (hr : r.im = 0) :
    (w - r)⁻¹.im / w.im < 0 := by
  have hne : w - r ≠ 0 := by
    intro h
    apply hw
    have := congrArg QuadraticAlgebra.im h
    simpa [hr] using this
  rw [jensen_calc_real w r hw hr, neg_lt_zero, inv_pos]
  exact normSq_pos hne

/-- The sign used in the proof: outside the closed disk on the root pair
`a, conj a`, the pair contributes negatively to `y Im (P'/P)(w)`. -/
theorem im_mul_pair_neg (w a : Complexify F) (hw : w.im ≠ 0) (h₁ : w ≠ a) (h₂ : w ≠ star a)
    (hout : a.im ^ 2 < (w.re - a.re) ^ 2 + w.im ^ 2) :
    w.im * ((w - a)⁻¹ + (w - star a)⁻¹).im < 0 := by
  have hcalc := jensen_calc w a hw h₁ h₂
  rw [div_eq_iff hw] at hcalc
  rw [hcalc]
  have hN : 0 < normSq (w - a) * normSq (w - star a) :=
    mul_pos (normSq_pos (sub_ne_zero.mpr h₁)) (normSq_pos (sub_ne_zero.mpr h₂))
  have hy : 0 < w.im ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hw))
  have hneg : -2 * ((w.re - a.re) ^ 2 + w.im ^ 2 - a.im ^ 2) /
      (normSq (w - a) * normSq (w - star a)) < 0 :=
    div_neg_of_neg_of_pos (by linarith) hN
  have : w.im * (-2 * ((w.re - a.re) ^ 2 + w.im ^ 2 - a.im ^ 2) /
      (normSq (w - a) * normSq (w - star a)) * w.im) =
      w.im ^ 2 * (-2 * ((w.re - a.re) ^ 2 + w.im ^ 2 - a.im ^ 2) /
      (normSq (w - a) * normSq (w - star a))) := by ring
  rw [this]
  exact mul_neg_of_pos_of_neg hy hneg

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- The imaginary part of a finite multiset sum is the sum of imaginary parts. -/
theorem multiset_sum_map_im (s : Multiset (Complexify F)) (g : Complexify F → Complexify F) :
    (s.map fun z => (g z).im).sum = ((s.map g).sum).im := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih]

/-! ### The Jensen disk theorem -/

/-- `polynomial:thm:jensen`, square-root-free (`normSq`) form over any ordered
field: a nonreal critical point `w = x + iy` of a nonconstant `P ∈ F[z]` whose
image in `F[i][z]` splits satisfies `(x - Re a)² + y² ≤ (Im a)²` for some root
`a` with `Im a ≠ 0`; its conjugate is also a root. -/
theorem jensen_normSq (P : F[X]) (hP : 0 < P.natDegree)
    (hs : (P.map (algebraMap F (Complexify F))).Splits) {w : Complexify F}
    (hw : w.im ≠ 0) (hd : aeval w (derivative P) = 0) :
    ∃ a ∈ P.aroots (Complexify F), a.im ≠ 0 ∧ star a ∈ P.aroots (Complexify F) ∧
      (w.re - a.re) ^ 2 + w.im ^ 2 ≤ a.im ^ 2 := by
  classical
  have hP0 : P ≠ 0 := ne_zero_of_natDegree_gt hP
  have hmem : ∀ z, z ∈ P.aroots (Complexify F) ↔ aeval z P = 0 := fun z => by
    rw [mem_aroots]
    exact ⟨fun h => h.2, fun h => ⟨hP0, h⟩⟩
  have heval : ∀ z, (P.map (algebraMap F (Complexify F))).eval z = aeval z P := fun z => by
    rw [aeval_def, eval_map]
  have hdeval : ∀ z, (P.map (algebraMap F (Complexify F))).derivative.eval z =
      aeval z (derivative P) := fun z => by
    rw [derivative_map, aeval_def, eval_map]
  have hy : 0 < w.im ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hw))
  suffices h : ∃ a ∈ P.aroots (Complexify F), (w.re - a.re) ^ 2 + w.im ^ 2 ≤ a.im ^ 2 by
    obtain ⟨a, ha, hle⟩ := h
    refine ⟨a, ha, ?_, star_mem_aroots ha, hle⟩
    intro h0
    rw [h0] at hle
    nlinarith [sq_nonneg (w.re - a.re)]
  by_cases hw0 : aeval w P = 0
  · exact ⟨w, (hmem w).2 hw0, by simp⟩
  by_contra H
  push Not at H
  have hsum₁ : ((P.aroots (Complexify F)).map fun z => (w - z)⁻¹).sum = 0 := by
    have h := hs.eval_derivative_div_eval_of_ne_zero (x := w) (by rwa [heval])
    rw [hdeval, hd, zero_div] at h
    simpa only [one_div] using h.symm
  have hsw : aeval (star w) P ≠ 0 := by
    rw [aeval_star]
    exact star_ne_zero.mpr hw0
  have hsd : aeval (star w) (derivative P) = 0 := by rw [aeval_star, hd, star_zero]
  have hsum₂ : ((P.aroots (Complexify F)).map fun z => (w - star z)⁻¹).sum = 0 := by
    have h := hs.eval_derivative_div_eval_of_ne_zero (x := star w) (by rwa [heval])
    rw [hdeval, hsd, zero_div] at h
    have h' := congrArg (starRingEnd (Complexify F)) h
    rw [map_zero, map_multiset_sum, Multiset.map_map] at h'
    rw [h']
    congr 1
    apply Multiset.map_congr rfl
    intro z _
    simp only [Function.comp_apply, one_div, starRingEnd_apply, star_inv₀, star_sub, star_star]
  have hne : P.aroots (Complexify F) ≠ ∅ := by
    rw [Multiset.empty_eq_zero, ← Multiset.card_pos, ← hs.natDegree_eq_card_roots,
      natDegree_map]
    exact hP
  have hlt := Multiset.sum_lt_sum_of_nonempty hne
    (f := fun z => w.im * ((w - z)⁻¹ + (w - star z)⁻¹).im) (g := fun _ => (0 : F))
    (fun z hz => by
      have hz0 := (hmem z).1 hz
      have hsz := (hmem (star z)).1 (star_mem_aroots hz)
      have h₁ : w ≠ z := fun h => hw0 (h ▸ hz0)
      have h₂ : w ≠ star z := fun h => hw0 (h ▸ hsz)
      exact im_mul_pair_neg w z hw h₁ h₂ (H z hz))
  rw [Multiset.sum_map_mul_left, multiset_sum_map_im, Multiset.sum_map_add, hsum₁, hsum₂,
    add_zero, QuadraticAlgebra.im_zero, mul_zero] at hlt
  simp at hlt

/-- The source remark after `polynomial:thm:jensen`: a nonconstant split
real-rooted polynomial has only real critical points. -/
theorem critical_point_im_eq_zero_of_roots_real (P : F[X]) (hP : 0 < P.natDegree)
    (hs : (P.map (algebraMap F (Complexify F))).Splits)
    (hreal : ∀ a ∈ P.aroots (Complexify F), a.im = 0) {w : Complexify F}
    (hd : aeval w (derivative P) = 0) : w.im = 0 := by
  by_contra hw
  obtain ⟨a, ha, him, -⟩ := jensen_normSq P hP hs hw hd
  exact him (hreal a ha)

/-- The source remark that nonconstancy is necessary in `polynomial:thm:jensen`:
for `P = 1` the nonreal point `i` is a zero of `P'`, but `P` has no roots. -/
theorem jensen_constant_counterexample :
    aeval (I : Complexify F) (derivative (1 : F[X])) = 0 ∧ (I : Complexify F).im ≠ 0 ∧
      (1 : F[X]).aroots (Complexify F) = 0 := by
  refine ⟨by simp, by simp, ?_⟩
  simp [aroots_def]

/-! ### Weighted incomplete polynomials -/

section Weighted

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The weighted incomplete polynomial `Q_λ(z) = ∑_j λ_j ∏_{k ≠ j} (z - α_k)`
of `polynomial:prop:weighted`, with nodes in `F[i]` and weights in `F`. -/
def incompletePoly (α : ι → Complexify F) (lam : ι → F) : (Complexify F)[X] :=
  ∑ j, C (algebraMap F (Complexify F) (lam j)) * ∏ k ∈ univ.erase j, (X - C (α k))

/-- Evaluation of `Q_λ` at a point: `Q_λ(z) = ∑_j λ_j ∏_{k ≠ j} (z - α_k)`. -/
theorem eval_incompletePoly (α : ι → Complexify F) (lam : ι → F) (z : Complexify F) :
    (incompletePoly α lam).eval z =
      ∑ j, algebraMap F (Complexify F) (lam j) * ∏ k ∈ univ.erase j, (z - α k) := by
  simp only [incompletePoly, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_sub, eval_X]

/-- Away from the nodes, `Q_λ(z) = ∏_k (z - α_k) · ∑_j λ_j / (z - α_j)`. -/
theorem eval_incompletePoly_eq_prod_mul_sum (α : ι → Complexify F) (lam : ι → F)
    {z : Complexify F} (hz : ∀ k, z ≠ α k) :
    (incompletePoly α lam).eval z =
      (∏ k, (z - α k)) * ∑ j, algebraMap F (Complexify F) (lam j) * (z - α j)⁻¹ := by
  rw [eval_incompletePoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : z - α j ≠ 0 := sub_ne_zero.mpr (hz j)
  have h : (∏ k ∈ univ.erase j, (z - α k)) * (z - α j) = ∏ k, (z - α k) :=
    Finset.prod_erase_mul _ _ (Finset.mem_univ j)
  rw [← h, mul_mul_mul_comm, mul_inv_cancel₀ hj, mul_one, mul_comm]

/-- Conjugating `λ / u` gives the positive multiple `(λ / |u|²) u`. -/
theorem star_algebraMap_mul_inv (r : F) (u : Complexify F) :
    star (algebraMap F (Complexify F) r * u⁻¹) = (r / normSq u) • u := by
  ext
  · simp only [conj_re, Complexify.mul_re, QuadraticAlgebra.algebraMap_re,
      QuadraticAlgebra.algebraMap_im, Complexify.inv_re, Complexify.inv_im, zero_mul, sub_zero,
      QuadraticAlgebra.re_smul, smul_eq_mul]
    ring
  · simp only [conj_im, Complexify.mul_im, QuadraticAlgebra.algebraMap_re,
      QuadraticAlgebra.algebraMap_im, Complexify.inv_re, Complexify.inv_im, zero_mul, add_zero,
      QuadraticAlgebra.im_smul, smul_eq_mul]
    ring

/-- `polynomial:prop:weighted`, first assertion: for nonnegative weights with
positive sum, every root of `Q_λ` lies in the `F`-convex hull of the nodes. -/
theorem incompletePoly_root_mem_convexHull (α : ι → Complexify F) {lam : ι → F}
    (hlam : ∀ j, 0 ≤ lam j) (hsum : 0 < ∑ j, lam j) {z : Complexify F}
    (hz : (incompletePoly α lam).IsRoot z) : z ∈ convexHull F (Set.range α) := by
  by_cases hnode : ∃ i, z = α i
  · obtain ⟨i, rfl⟩ := hnode
    exact subset_convexHull F _ (Set.mem_range_self i)
  push Not at hnode
  have hprod : (∏ k, (z - α k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => sub_ne_zero.mpr (hnode k)
  have hS : ∑ j, algebraMap F (Complexify F) (lam j) * (z - α j)⁻¹ = 0 := by
    have h := hz.eq_zero
    rw [eval_incompletePoly_eq_prod_mul_sum α lam hnode] at h
    exact (mul_eq_zero.mp h).resolve_left hprod
  set μ : ι → F := fun j => lam j / normSq (z - α j)
  have hμ0 : ∀ j, 0 ≤ μ j := fun j =>
    div_nonneg (hlam j) (normSq_nonneg _)
  have hμpos : 0 < ∑ j, μ j := by
    obtain ⟨j, hj⟩ : ∃ j, 0 < lam j := by
      by_contra hneg
      push Not at hneg
      exact absurd hsum (not_lt.mpr (Finset.sum_nonpos fun j _ => hneg j))
    exact Finset.sum_pos' (fun j _ => hμ0 j)
      ⟨j, Finset.mem_univ j, div_pos hj (normSq_pos (sub_ne_zero.mpr (hnode j)))⟩
  have hbal : ∑ j, μ j • (z - α j) = 0 := by
    have h := congrArg (starRingEnd (Complexify F)) hS
    rw [map_sum, map_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [starRingEnd_apply, star_algebraMap_mul_inv]
  have hcm : (∑ j, μ j) • z = ∑ j, μ j • α j := by
    simp only [smul_sub, Finset.sum_sub_distrib, sub_eq_zero, ← Finset.sum_smul] at hbal
    exact hbal
  have hz' : z = univ.centerMass μ α := by
    rw [Finset.centerMass, ← hcm, inv_smul_smul₀ hμpos.ne']
  rw [hz']
  exact Finset.centerMass_mem_convexHull _ (fun j _ => hμ0 j) hμpos
    (fun j _ => Set.mem_range_self j)

/-- `polynomial:prop:weighted`, converse: with at least two nodes, every point of
the `F`-convex hull is a root of some admissible `Q_λ`. -/
theorem exists_incompletePoly_root_of_mem_convexHull [Nontrivial ι] (α : ι → Complexify F)
    {z : Complexify F} (hz : z ∈ convexHull F (Set.range α)) :
    ∃ lam : ι → F, (∀ j, 0 ≤ lam j) ∧ 0 < ∑ j, lam j ∧ (incompletePoly α lam).IsRoot z := by
  by_cases hnode : ∃ i, z = α i
  · obtain ⟨i, rfl⟩ := hnode
    obtain ⟨j, hji⟩ := exists_ne i
    refine ⟨fun k => if k = j then 1 else 0, fun k => ?_, ?_, ?_⟩
    · dsimp only
      split_ifs <;> norm_num
    · rw [Finset.sum_ite_eq' univ j (fun _ => (1 : F))]
      simp
    · rw [IsRoot.def, eval_incompletePoly]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k = j
      · subst hk
        rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hji, Finset.mem_univ i⟩)
          (sub_self _), mul_zero]
      · simp [hk]
  push Not at hnode
  rw [convexHull_range_eq_exists_affineCombination] at hz
  obtain ⟨s, θ, hθ0, hθ1, hθz⟩ := hz
  rw [Finset.affineCombination_eq_linear_combination s α θ hθ1] at hθz
  set θ' : ι → F := fun i => if i ∈ s then θ i else 0 with hθ'
  have hθ'0 : ∀ i, 0 ≤ θ' i := fun i => by
    simp only [hθ']
    split_ifs with h
    · exact hθ0 i h
    · exact le_rfl
  have hθ'1 : ∑ i, θ' i = 1 := by
    simp only [hθ']
    rw [Fintype.sum_ite_mem, hθ1]
  have hθ'z : ∑ i, θ' i • α i = z := by
    simp only [hθ', ite_smul, zero_smul]
    rw [Fintype.sum_ite_mem, hθz]
  refine ⟨fun j => θ' j * normSq (z - α j), fun j => mul_nonneg (hθ'0 j) (normSq_nonneg _),
    ?_, ?_⟩
  · obtain ⟨j, hj⟩ : ∃ j, 0 < θ' j := by
      by_contra hneg
      push Not at hneg
      have := Finset.sum_nonpos (s := univ) fun j _ => hneg j
      rw [hθ'1] at this
      exact absurd this (not_le.mpr one_pos)
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hθ'0 j) (normSq_nonneg _))
      ⟨j, Finset.mem_univ j, mul_pos hj (normSq_pos (sub_ne_zero.mpr (hnode j)))⟩
  · rw [IsRoot.def, eval_incompletePoly_eq_prod_mul_sum α _ hnode]
    apply mul_eq_zero_of_right
    apply star_eq_zero.mp
    rw [← starRingEnd_apply, map_sum]
    have hterm : ∀ j, starRingEnd (Complexify F)
        (algebraMap F (Complexify F) (θ' j * normSq (z - α j)) * (z - α j)⁻¹) =
        θ' j • (z - α j) := fun j => by
      rw [starRingEnd_apply, star_algebraMap_mul_inv,
        mul_div_cancel_right₀ _ (normSq_pos (sub_ne_zero.mpr (hnode j))).ne']
    simp only [hterm, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hθ'1, one_smul,
      hθ'z, sub_self]

/-- `polynomial:prop:weighted`: with at least two nodes, the union over all
admissible weights of the root sets of `Q_λ` is exactly the `F`-convex hull. -/
theorem incompletePoly_roots_union_eq_convexHull [Nontrivial ι] (α : ι → Complexify F) :
    {z | ∃ lam : ι → F, (∀ j, 0 ≤ lam j) ∧ 0 < ∑ j, lam j ∧
      (incompletePoly α lam).IsRoot z} = convexHull F (Set.range α) := by
  ext z
  constructor
  · rintro ⟨lam, hlam, hsum, hz⟩
    exact incompletePoly_root_mem_convexHull α hlam hsum hz
  · exact exists_incompletePoly_root_of_mem_convexHull α

/-- The `n ≥ 2` hypothesis of the converse in `polynomial:prop:weighted` is needed:
with a single node, an admissible `Q_λ` is a nonzero constant and has no roots, so
the union of root sets is empty while the hull `{α_1}` is not. -/
theorem incompletePoly_not_isRoot_of_subsingleton [Subsingleton ι] (α : ι → Complexify F)
    {lam : ι → F} (hsum : 0 < ∑ j, lam j) (z : Complexify F) :
    ¬ (incompletePoly α lam).IsRoot z := by
  rw [IsRoot.def, eval_incompletePoly]
  have hempty : ∀ j : ι, univ.erase j = ∅ := fun j => by
    ext k
    simp [Subsingleton.elim k j]
  simp only [hempty, Finset.prod_empty, mul_one, ← map_sum]
  rw [map_eq_zero_iff _ (algebraMap F (Complexify F)).injective]
  exact hsum.ne'

end Weighted

/-- `polynomial:prop:weighted` indexed by `Fin n`, with the source's `n ≥ 2`. -/
theorem incompletePoly_roots_union_eq_convexHull_fin {n : ℕ} (hn : 2 ≤ n)
    (α : Fin n → Complexify F) :
    {z | ∃ lam : Fin n → F, (∀ j, 0 ≤ lam j) ∧ 0 < ∑ j, lam j ∧
      (incompletePoly α lam).IsRoot z} = convexHull F (Set.range α) := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  exact incompletePoly_roots_union_eq_convexHull α

end OrderedField

/-! ### Modulus form -/

section SquareRoots

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [HasNonnegSquareRoots F]

/-- The closed order disk having `u` and `v` as the endpoints of a diameter:
center `(u + v)/2` and radius `|u - v|/2`. -/
def diameterDisk (u v : Complexify F) : Set (Complexify F) :=
  {z | modulus (z - (2 : F)⁻¹ • (u + v)) ≤ modulus (u - v) / 2}

/-- The diameter disk on a conjugate pair `a, conj a` is the order disk of center
`Re a` and radius `|Im a|`. -/
theorem diameterDisk_star (a : Complexify F) :
    diameterDisk a (star a) =
      {z | modulus (z - algebraMap F (Complexify F) a.re) ≤ |a.im|} := by
  have hc : (2 : F)⁻¹ • (a + star a) = algebraMap F (Complexify F) a.re := by
    ext
    · simp only [QuadraticAlgebra.re_smul, QuadraticAlgebra.re_add, conj_re, smul_eq_mul,
        QuadraticAlgebra.algebraMap_re]
      ring
    · simp
  have hr : modulus (a - star a) = 2 * |a.im| := by
    apply modulus_eq_of_nonneg_sq (by positivity)
    simp only [normSq, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, conj_re, conj_im,
      mul_pow, sq_abs]
    ring
  ext z
  simp only [diameterDisk, Set.mem_setOf_eq, hc, hr]
  rw [mul_div_cancel_left₀ _ two_ne_zero]

/-- `polynomial:thm:jensen`: every nonreal critical point of a nonconstant
`P ∈ F[z]` whose image in `F[i][z]` splits lies in a closed order disk having a
pair `a, conj a` of conjugate nonreal roots as endpoints of a diameter;
equivalently `|w - Re a| ≤ |Im a|`. -/
theorem jensen (P : F[X]) (hP : 0 < P.natDegree)
    (hs : (P.map (algebraMap F (Complexify F))).Splits) {w : Complexify F}
    (hw : w.im ≠ 0) (hd : aeval w (derivative P) = 0) :
    ∃ a ∈ P.aroots (Complexify F), a.im ≠ 0 ∧ star a ∈ P.aroots (Complexify F) ∧
      w ∈ diameterDisk a (star a) ∧
      modulus (w - algebraMap F (Complexify F) a.re) ≤ |a.im| := by
  obtain ⟨a, ha, him, hstar, hle⟩ := jensen_normSq P hP hs hw hd
  have hmod : modulus (w - algebraMap F (Complexify F) a.re) ≤ |a.im| := by
    apply (sq_le_sq₀ (modulus_nonneg _) (abs_nonneg _)).mp
    simpa [normSq, sq_abs] using hle
  refine ⟨a, ha, him, hstar, ?_, hmod⟩
  rw [diameterDisk_star]
  exact hmod

end SquareRoots

/-! ### Actual surcomplex numbers -/

open Foundations

/-- `polynomial:thm:jensen` for surreal coefficients: surcomplex algebraic
closedness discharges splitting. -/
theorem surcomplex_jensen (P : SignSequence.{u}[X]) (hP : 0 < P.natDegree)
    {w : Surcomplex.{u}} (hw : w.im ≠ 0) (hd : aeval w (derivative P) = 0) :
    ∃ a ∈ P.aroots Surcomplex.{u}, a.im ≠ 0 ∧ star a ∈ P.aroots Surcomplex.{u} ∧
      w ∈ diameterDisk a (star a) ∧
      Surcomplex.modulus (w - algebraMap SignSequence.{u} Surcomplex.{u} a.re) ≤ |a.im| :=
  jensen P hP (Surcomplex.polynomial_splits _) hw hd

/-- The source remark after `polynomial:thm:jensen` for surreal coefficients: a
nonconstant real-rooted surreal polynomial has only real critical points. -/
theorem surcomplex_critical_point_im_eq_zero_of_roots_real (P : SignSequence.{u}[X])
    (hP : 0 < P.natDegree) (hreal : ∀ a ∈ P.aroots Surcomplex.{u}, a.im = 0)
    {w : Surcomplex.{u}} (hd : aeval w (derivative P) = 0) : w.im = 0 :=
  critical_point_im_eq_zero_of_roots_real P hP (Surcomplex.polynomial_splits _) hreal hd

/-- `polynomial:prop:weighted` on actual surcomplex nodes with surreal weights. -/
theorem surcomplex_incompletePoly_roots_union_eq_convexHull {n : ℕ} (hn : 2 ≤ n)
    (α : Fin n → Surcomplex.{u}) :
    {z | ∃ lam : Fin n → SignSequence.{u}, (∀ j, 0 ≤ lam j) ∧ 0 < ∑ j, lam j ∧
      (incompletePoly α lam).IsRoot z} = convexHull SignSequence.{u} (Set.range α) :=
  incompletePoly_roots_union_eq_convexHull_fin hn α

end

end Surreal.PolynomialJensen
