import Mathlib.LinearAlgebra.Matrix.Stochastic
import Surreal.Algebra.MarkovForest
import Surreal.Algebra.MarkovEffective
import Surreal.HahnSeries.StandardPart

/-!
# Residue shadows of Hahn rate-matrix resolvents

This file proves `markov:lem:resolvent` of
`docs/surreal/markov-generators-at-every-scale/article.tex` in full, for the literal residue
shadows `K_α(c) = res R_L(c t^α)`. It also proves the stochasticity and leading-form clauses of
`markov:thm:leading`, and reduces the `IsCrossover` hypothesis package of
`Surreal/Algebra/MarkovEffective.lean` for the literal shadow to the two endpoint limits of
`markov:thm:flag`, with the limits identified as shadows at scales in the adjacent plateau
intervals.

**Setting.** `Γ` is any linearly ordered abelian group and `F = Lex ℝ⟦Γ⟧` is `ℝ((t^Γ))`. The
source assumes `Γ` nonzero and divisible; no step below uses either assumption. The rates are
a matrix `q` with nonnegative off-diagonal entries, and `L = rowLaplacian q` is the row
Laplacian `markov:eq:laplacian` (`Surreal/Algebra/MarkovForest.lean`). The source's rates are
positive on the edges of a strongly connected graph and zero elsewhere, which is a special
case: neither irreducibility nor strict positivity is used. `rowLaplacian_neg` shows that every
matrix with `L𝟙 = 0` is the row Laplacian of its negated off-diagonal entries, so the results
cover every matrix with zero row sums and nonpositive off-diagonal entries. The resolvent is
`R_L(s) = s(sI + L)⁻¹` (`Surreal.Markov.resolvent`).

**Residue.** `mono α c` is the monomial `c t^α` and `res x` is the coefficient of `t^0`. It is
additive on `F`, and multiplicative on the valuation ring `𝒪 = {x : v(x) ≥ 0}` (`res_mul`,
from `Surreal.HahnSeries.coeff_zero_mul_of_nonnegative`). `res.mapMatrix` applies it
entrywise, and `shadowAt L s = res R_L(s)`, `shadow L α c = K_α(c) = shadowAt L (c t^α)`. For
`s > 0` every entry of `R_L(s)` lies in `[0, 1]`, hence in `𝒪` (`orderTop_resolvent_nonneg`,
from `markov:prop:forest`), so these residues are the source's.

**`markov:lem:resolvent`.**
* `resolvent_identity`: `markov:eq:resolvent-identity`,
  `R_L(s)R_L(u) = (uR_L(s) - sR_L(u))/(u - s)` for positive `s ≠ u`, over any linearly
  ordered field. `resolvent_commute`: the two resolvents commute.
* `shadow_same_scale`: `markov:eq:same-scale` in multiplied-out form,
  `(e - c)K_α(c)K_α(e) = eK_α(c) - cK_α(e)` for all real `c, e > 0`; `shadow_mul_shadow`
  is the quotient form for `c ≠ e`. The proof substitutes `s = ct^α`, `u = et^α`, multiplies
  by `t^{-α}` and takes residues, as in the source.
* `shadow_cross_scale`: `markov:eq:cross-scale`,
  `K_α(c)K_β(e) = K_β(e)K_α(c) = K_β(e)` for `α < β`. The proof multiplies the identity by
  `c⁻¹t^{-α}`: the factor `(e/c)t^{β-α}` is infinitesimal and every resolvent entry is
  bounded.
* `resolvent_compatibility`: the three displays together, for any `L` over `F` with `L𝟙 = 0`
  and nonpositive off-diagonal entries.

The residue computations are done entrywise from `mul_resolvent_mul_apply`, the resolvent
identity multiplied by a scalar, stated over an arbitrary field.

**`markov:thm:leading`, two clauses.**
* `shadow_mem_rowStochastic`: each `K_α(c)`, `c > 0`, is real, nonnegative and
  row-stochastic (more generally `res R_L(s)` for every positive `s`,
  `shadowAt_mem_rowStochastic`).
* `eq_mono_mul_one_add` and `leading_form_unique`: every positive `s` has a unique form
  `s = ct^α(1 + η)` with real `c > 0` and `v(η) > 0`, namely `α = v(s)` and `c = lc(s)`
  (uniqueness holds among all real `c ≠ 0`).
  `shadowAt_mono_mul_one_add`: its resolvent has residue `K_α(c)`; hence
  `shadowAt_eq_shadow`: `res R_L(s) = K_{v(s)}(lc(s))` for every positive `s`. The proof
  uses the resolvent identity rather than forests: with `s = u(1 + η)`, the difference
  `R_L(s) - R_L(u)` is `η` times a bounded matrix.

**`IsCrossover`.** `isCrossover_shadow`: if `K_α(c) → K_β(e₁)` as `c → ∞` and
`K_α(c) → K_γ(e₂)` as `c → 0⁺`, for scales `β < α < γ` and reals `e₁, e₂ > 0`, then the
literal shadow family `c ↦ K_α(c)` satisfies `MarkovEffective.IsCrossover` with these
endpoints. Stochasticity and the same-scale identity come from the results above, and the four
endpoint relations `markov:eq:endpoint-relations` from `markov:eq:cross-scale`, as in the
source proof of `markov:thm:flag`. Consequently `MarkovEffective.effective_reconstruction`
applies to the literal shadow at every scale where these two limits exist and are such
shadows.

**Pending.** The rational formula `K_α(c) = N_α(c)/D_α(c)` (`markov:eq:shadow-formula`), the
marked-entry valuations and leading coefficients (`markov:eq:marked-valuation`,
`markov:eq:marked-leading-coeff`) of `markov:thm:leading`, `markov:prop:remainder`, and
`markov:thm:flag` itself. The remaining hypotheses `hfast` and `hslow` of `isCrossover_shadow`
are the endpoint limits `markov:eq:fast-endpoint` and `markov:eq:slow-endpoint` together with
the plateau identification of `markov:thm:flag`: the limits are shadows `K_β(e₁)` and
`K_γ(e₂)` at scales `β < α < γ` in the adjacent plateau intervals. The closed forms
`B_{k±}/b_{k±}` of these limits are not needed for `isCrossover_shadow`.
-/

namespace Surreal.MarkovShadow

open Matrix Finset Filter Topology
open _root_.HahnSeries
open Surreal.MarkovForest (rowLaplacian)

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

section Ring

variable {R : Type*} [CommRing R]

/-- Every matrix with zero row sums is the row Laplacian `markov:eq:laplacian` of its negated
off-diagonal entries. Its rates are nonnegative exactly when its off-diagonal entries are
nonpositive. -/
theorem rowLaplacian_neg {L : Matrix n n R} (hL : L *ᵥ (fun _ => (1 : R)) = 0) :
    rowLaplacian (fun i j => -L i j) = L := by
  ext i j
  rw [MarkovForest.rowLaplacian, of_apply]
  split_ifs with hij
  · subst hij
    have h := congrFun hL i
    simp only [mulVec, dotProduct, mul_one, Pi.zero_apply] at h
    rw [← Finset.add_sum_erase _ _ (mem_univ i)] at h
    rw [Finset.sum_neg_distrib]
    linear_combination -h
  · exact neg_neg _

end Ring

section Field

variable {K : Type*} [Field K]

/-- `markov:eq:resolvent-identity` entrywise, multiplied by a scalar `w`:
`w(u - s)(R_L(s)R_L(u))_{ij} = wu R_L(s)_{ij} - ws R_L(u)_{ij}`. -/
theorem mul_resolvent_mul_apply {L : Matrix n n K} {s u : K}
    (hs : IsUnit (s • (1 : Matrix n n K) + L).det)
    (hu : IsUnit (u • (1 : Matrix n n K) + L).det) (w : K) (i j : n) :
    w * (u - s) * (Markov.resolvent L s * Markov.resolvent L u) i j =
      w * u * Markov.resolvent L s i j - w * s * Markov.resolvent L u i j := by
  have h := congrFun (congrFun (Markov.resolvent_mul_resolvent hs hu) i) j
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at h
  rw [mul_assoc, h]
  ring

end Field

section Ordered

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {q : n → n → K}

/-- For nonnegative off-diagonal rates and `s > 0`, the matrix `sI + L` is invertible. -/
theorem isUnit_det (hq : ∀ i j, i ≠ j → 0 ≤ q i j) {s : K} (hs : 0 < s) :
    IsUnit (s • (1 : Matrix n n K) + rowLaplacian q).det := by
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [det_isEmpty]
    exact isUnit_one
  · exact MarkovForest.isUnit_det_smul_one_add_rowLaplacian hq hs

/-- `markov:eq:resolvent-identity`: for a row Laplacian with nonnegative rates and positive
`s ≠ u`, `R_L(s)R_L(u) = (uR_L(s) - sR_L(u))/(u - s)`. -/
theorem resolvent_identity (hq : ∀ i j, i ≠ j → 0 ≤ q i j) {s u : K} (hs : 0 < s)
    (hu : 0 < u) (hsu : s ≠ u) :
    Markov.resolvent (rowLaplacian q) s * Markov.resolvent (rowLaplacian q) u =
      (u - s)⁻¹ • (u • Markov.resolvent (rowLaplacian q) s -
        s • Markov.resolvent (rowLaplacian q) u) :=
  Markov.resolvent_mul_resolvent_eq hsu (isUnit_det hq hs) (isUnit_det hq hu)

/-- The resolvents at two positive parameters commute. -/
theorem resolvent_commute (hq : ∀ i j, i ≠ j → 0 ≤ q i j) {s u : K} (hs : 0 < s)
    (hu : 0 < u) :
    Markov.resolvent (rowLaplacian q) s * Markov.resolvent (rowLaplacian q) u =
      Markov.resolvent (rowLaplacian q) u * Markov.resolvent (rowLaplacian q) s :=
  Markov.resolvent_commute (isUnit_det hq hs) (isUnit_det hq hu)

/-- For nonnegative off-diagonal rates and `s > 0`, `R_L(s)` is row-stochastic
(`markov:prop:forest`, with no irreducibility assumption). -/
theorem resolvent_mem_rowStochastic (hq : ∀ i j, i ≠ j → 0 ≤ q i j) {s : K} (hs : 0 < s) :
    Markov.resolvent (rowLaplacian q) s ∈ rowStochastic K n := by
  refine mem_rowStochastic_iff_sum.mpr ⟨fun i j => ?_, fun i => ?_⟩
  · haveI : Nonempty n := ⟨i⟩
    exact MarkovForest.resolvent_nonneg hq hs i j
  · haveI : Nonempty n := ⟨i⟩
    exact MarkovForest.sum_resolvent hq hs i

end Ordered

section Hahn

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

section Residue

/-- The monomial `c t^α` of `F = ℝ((t^Γ))`. -/
def mono (α : Γ) (c : ℝ) : Lex ℝ⟦Γ⟧ :=
  toLex (single α c)

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
@[simp] theorem ofLex_mono (α : Γ) (c : ℝ) : ofLex (mono α c) = single α c :=
  rfl

theorem mono_mul_mono (α β : Γ) (a b : ℝ) : mono α a * mono β b = mono (α + β) (a * b) := by
  show toLex (single α a * single β b) = toLex (single (α + β) (a * b))
  rw [single_mul_single]

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
theorem mono_sub (α : Γ) (a b : ℝ) : mono α a - mono α b = mono α (a - b) := by
  show toLex (single α a - single α b) = toLex (single α (a - b))
  rw [single_sub]

omit [IsOrderedAddMonoid Γ] in
theorem mono_zero_one : mono (0 : Γ) 1 = 1 :=
  rfl

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
theorem mono_pos {α : Γ} {c : ℝ} (hc : 0 < c) : 0 < mono α c :=
  leadingCoeff_pos_iff.mp (by rwa [ofLex_mono, leadingCoeff_of_single])

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
theorem mono_ne_zero {α : Γ} {c : ℝ} (hc : c ≠ 0) : mono α c ≠ 0 := fun h =>
  single_ne_zero hc (congrArg ofLex h)

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
theorem orderTop_mono {α : Γ} {c : ℝ} (hc : c ≠ 0) : (ofLex (mono α c)).orderTop = α :=
  orderTop_single hc

/-- The residue `res x`, the coefficient of `t^0`. It is additive on all of `F`; on the
valuation ring it is the standard part. -/
def res : Lex ℝ⟦Γ⟧ →+ ℝ where
  toFun x := (ofLex x).coeff 0
  map_zero' := rfl
  map_add' _ _ := rfl

omit [IsOrderedAddMonoid Γ] in
theorem res_apply (x : Lex ℝ⟦Γ⟧) : res x = (ofLex x).coeff 0 :=
  rfl

omit [IsOrderedAddMonoid Γ] in
theorem res_one : res (1 : Lex ℝ⟦Γ⟧) = 1 := by
  rw [res_apply, ofLex_one, coeff_one, if_pos rfl]

/-- The residue is multiplicative on the valuation ring `𝒪`. -/
theorem res_mul {x y : Lex ℝ⟦Γ⟧} (hx : 0 ≤ (ofLex x).orderTop)
    (hy : 0 ≤ (ofLex y).orderTop) : res (x * y) = res x * res y :=
  Surreal.HahnSeries.coeff_zero_mul_of_nonnegative (ofLex x) (ofLex y) hx hy

omit [IsOrderedAddMonoid Γ] in
/-- Infinitesimals have residue zero. -/
theorem res_eq_zero {x : Lex ℝ⟦Γ⟧} (hx : 0 < (ofLex x).orderTop) : res x = 0 :=
  coeff_eq_zero_of_lt_orderTop hx

/-- The product of an infinitesimal and an element of `𝒪` has residue zero. -/
theorem res_mul_eq_zero {ε x : Lex ℝ⟦Γ⟧} (hε : 0 < (ofLex ε).orderTop)
    (hx : 0 ≤ (ofLex x).orderTop) : res (ε * x) = 0 := by
  rw [res_mul hε.le hx, res_eq_zero hε, zero_mul]

theorem res_mono_zero_mul (a : ℝ) (x : Lex ℝ⟦Γ⟧) : res (mono (0 : Γ) a * x) = a * res x :=
  coeff_single_zero_mul

omit [IsOrderedAddMonoid Γ] in
/-- A nonnegative element of `𝒪` has nonnegative residue. -/
theorem res_nonneg {x : Lex ℝ⟦Γ⟧} (h0 : 0 ≤ x) (hx : 0 ≤ (ofLex x).orderTop) :
    0 ≤ res x := by
  by_cases hc : (ofLex x).coeff 0 = 0
  · rw [res_apply, hc]
  have ho : (ofLex x).order = 0 :=
    le_antisymm (order_le_of_coeff_ne_zero hc) (zero_le_orderTop_iff.mp hx)
  have h := leadingCoeff_nonneg_iff.mpr h0
  rwa [leadingCoeff_eq, ho] at h

theorem orderTop_mul_nonneg {x y : Lex ℝ⟦Γ⟧} (hx : 0 ≤ (ofLex x).orderTop)
    (hy : 0 ≤ (ofLex y).orderTop) : 0 ≤ (ofLex (x * y)).orderTop := by
  show 0 ≤ (ofLex x * ofLex y).orderTop
  rw [orderTop_mul]
  exact add_nonneg hx hy

omit [IsOrderedAddMonoid Γ] in
theorem orderTop_sum_nonneg {ι : Type*} (s : Finset ι) (f : ι → Lex ℝ⟦Γ⟧)
    (h : ∀ i ∈ s, 0 ≤ (ofLex (f i)).orderTop) : 0 ≤ (ofLex (∑ i ∈ s, f i)).orderTop :=
  Finset.sum_induction f (fun x => 0 ≤ (ofLex x).orderTop)
    (fun _ _ ha hb => (le_min ha hb).trans min_orderTop_le_orderTop_add) (by simp) h

/-- An infinitesimal perturbation of one is positive. -/
theorem one_add_pos_of_orderTop_pos {η : Lex ℝ⟦Γ⟧} (hη : 0 < (ofLex η).orderTop) :
    0 < 1 + η := by
  have h : |η| < |1| := abs_lt_abs_of_orderTop_ofLex (by rwa [ofLex_one, orderTop_one])
  rw [abs_one] at h
  linarith [neg_abs_le η]

end Residue

section MatrixResidue

omit [Fintype n] [DecidableEq n] [IsOrderedAddMonoid Γ] in
theorem resMap_apply (A : Matrix n n (Lex ℝ⟦Γ⟧)) (i j : n) :
    res.mapMatrix A i j = res (A i j) :=
  rfl

omit [DecidableEq n] in
/-- The entrywise residue is multiplicative on matrices with entries in `𝒪`. -/
theorem resMap_mul {A B : Matrix n n (Lex ℝ⟦Γ⟧)} (hA : ∀ i j, 0 ≤ (ofLex (A i j)).orderTop)
    (hB : ∀ i j, 0 ≤ (ofLex (B i j)).orderTop) :
    res.mapMatrix (A * B) = res.mapMatrix A * res.mapMatrix B := by
  ext i j
  rw [resMap_apply, mul_apply, mul_apply, map_sum]
  exact Finset.sum_congr rfl fun k _ => res_mul (hA i k) (hB k j)

omit [DecidableEq n] in
theorem mul_apply_orderTop_nonneg {A B : Matrix n n (Lex ℝ⟦Γ⟧)}
    (hA : ∀ i j, 0 ≤ (ofLex (A i j)).orderTop) (hB : ∀ i j, 0 ≤ (ofLex (B i j)).orderTop)
    (i j : n) : 0 ≤ (ofLex ((A * B) i j)).orderTop := by
  rw [mul_apply]
  exact orderTop_sum_nonneg _ _ fun k _ => orderTop_mul_nonneg (hA i k) (hB k j)

end MatrixResidue

section Shadow

variable {q : n → n → Lex ℝ⟦Γ⟧}

/-- For nonnegative off-diagonal rates and `s > 0`, every entry of `R_L(s)` lies in the
valuation ring `𝒪` (`markov:prop:forest`). -/
theorem orderTop_resolvent_nonneg (hq : ∀ i j, i ≠ j → 0 ≤ q i j) {s : Lex ℝ⟦Γ⟧}
    (hs : 0 < s) (i j : n) :
    0 ≤ (ofLex (Markov.resolvent (rowLaplacian q) s i j)).orderTop := by
  haveI : Nonempty n := ⟨i⟩
  exact MarkovForest.orderTop_resolvent_nonneg hq hs i j

/-- The residue matrix `res R_L(s)` of the normalized resolvent at `s`. -/
def shadowAt (L : Matrix n n (Lex ℝ⟦Γ⟧)) (s : Lex ℝ⟦Γ⟧) : Matrix n n ℝ :=
  res.mapMatrix (Markov.resolvent L s)

/-- The shadow `K_α(c) = res R_L(c t^α)`. -/
def shadow (L : Matrix n n (Lex ℝ⟦Γ⟧)) (α : Γ) (c : ℝ) : Matrix n n ℝ :=
  shadowAt L (mono α c)

/-- `markov:thm:leading`: for every positive `s`, the residue `res R_L(s)` is a real,
nonnegative, row-stochastic matrix. -/
theorem shadowAt_mem_rowStochastic (hq : ∀ i j, i ≠ j → 0 ≤ q i j) {s : Lex ℝ⟦Γ⟧}
    (hs : 0 < s) : shadowAt (rowLaplacian q) s ∈ rowStochastic ℝ n := by
  have hR := mem_rowStochastic_iff_sum.mp (resolvent_mem_rowStochastic hq hs)
  refine mem_rowStochastic_iff_sum.mpr
    ⟨fun i j => res_nonneg (hR.1 i j) (orderTop_resolvent_nonneg hq hs i j), fun i => ?_⟩
  simp only [shadowAt, resMap_apply]
  rw [← map_sum, hR.2 i, res_one]

/-- `markov:thm:leading`: each shadow `K_α(c)`, `c > 0`, is a real, nonnegative,
row-stochastic matrix. -/
theorem shadow_mem_rowStochastic (hq : ∀ i j, i ≠ j → 0 ≤ q i j) (α : Γ) {c : ℝ}
    (hc : 0 < c) : shadow (rowLaplacian q) α c ∈ rowStochastic ℝ n :=
  shadowAt_mem_rowStochastic hq (mono_pos hc)

/-- `markov:eq:same-scale` in multiplied-out form: for all real `c, e > 0`,
`(e - c)K_α(c)K_α(e) = eK_α(c) - cK_α(e)`. -/
theorem shadow_same_scale (hq : ∀ i j, i ≠ j → 0 ≤ q i j) (α : Γ) {c e : ℝ} (hc : 0 < c)
    (he : 0 < e) :
    (e - c) • (shadow (rowLaplacian q) α c * shadow (rowLaplacian q) α e) =
      e • shadow (rowLaplacian q) α c - c • shadow (rowLaplacian q) α e := by
  have hs := mono_pos (α := α) hc
  have hu := mono_pos (α := α) he
  have hRs := orderTop_resolvent_nonneg hq hs
  have hRu := orderTop_resolvent_nonneg hq hu
  ext i j
  have h := congrArg res
    (mul_resolvent_mul_apply (isUnit_det hq hs) (isUnit_det hq hu) (mono (-α) 1) i j)
  simp only [mono_sub, mono_mul_mono, neg_add_cancel, one_mul, map_sub, res_mono_zero_mul] at h
  simp only [shadow, shadowAt, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
    ← resMap_mul hRs hRu, resMap_apply]
  exact h

/-- `markov:eq:same-scale`: for real `c, e > 0` with `c ≠ e`,
`K_α(c)K_α(e) = (eK_α(c) - cK_α(e))/(e - c)`. -/
theorem shadow_mul_shadow (hq : ∀ i j, i ≠ j → 0 ≤ q i j) (α : Γ) {c e : ℝ} (hc : 0 < c)
    (he : 0 < e) (hce : c ≠ e) :
    shadow (rowLaplacian q) α c * shadow (rowLaplacian q) α e =
      (e - c)⁻¹ • (e • shadow (rowLaplacian q) α c - c • shadow (rowLaplacian q) α e) := by
  rw [← shadow_same_scale hq α hc he, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hce.symm),
    one_smul]

/-- `markov:eq:cross-scale`, first equation: for `α < β` and real `c, e > 0`,
`K_α(c)K_β(e) = K_β(e)`. -/
theorem shadow_mul_shadow_of_lt (hq : ∀ i j, i ≠ j → 0 ≤ q i j) {α β : Γ} (hαβ : α < β)
    {c e : ℝ} (hc : 0 < c) (he : 0 < e) :
    shadow (rowLaplacian q) α c * shadow (rowLaplacian q) β e =
      shadow (rowLaplacian q) β e := by
  have hs := mono_pos (α := α) hc
  have hu := mono_pos (α := β) he
  have hRs := orderTop_resolvent_nonneg hq hs
  have hRu := orderTop_resolvent_nonneg hq hu
  have hε : 0 < (ofLex (mono (-α + β) (c⁻¹ * e))).orderTop := by
    rw [orderTop_mono (mul_ne_zero (inv_ne_zero hc.ne') he.ne'), WithTop.coe_pos,
      neg_add_eq_sub]
    exact sub_pos.mpr hαβ
  ext i j
  have h := congrArg res
    (mul_resolvent_mul_apply (isUnit_det hq hs) (isUnit_det hq hu) (mono (-α) c⁻¹) i j)
  simp only [mul_sub, sub_mul, mono_mul_mono, neg_add_cancel, inv_mul_cancel₀ hc.ne',
    mono_zero_one, one_mul, map_sub, res_mul_eq_zero hε (hRs i j),
    res_mul_eq_zero hε (mul_apply_orderTop_nonneg hRs hRu i j), zero_sub, neg_inj] at h
  simp only [shadow, shadowAt, ← resMap_mul hRs hRu, resMap_apply]
  exact h

/-- `markov:eq:cross-scale`, second equation: for `α < β` and real `c, e > 0`,
`K_β(e)K_α(c) = K_β(e)`. -/
theorem shadow_mul_shadow_of_lt' (hq : ∀ i j, i ≠ j → 0 ≤ q i j) {α β : Γ} (hαβ : α < β)
    {c e : ℝ} (hc : 0 < c) (he : 0 < e) :
    shadow (rowLaplacian q) β e * shadow (rowLaplacian q) α c =
      shadow (rowLaplacian q) β e := by
  have hs := mono_pos (α := α) hc
  have hu := mono_pos (α := β) he
  have hRs := orderTop_resolvent_nonneg hq hs
  have hRu := orderTop_resolvent_nonneg hq hu
  calc shadow (rowLaplacian q) β e * shadow (rowLaplacian q) α c
      = res.mapMatrix (Markov.resolvent (rowLaplacian q) (mono β e) *
          Markov.resolvent (rowLaplacian q) (mono α c)) := (resMap_mul hRu hRs).symm
    _ = res.mapMatrix (Markov.resolvent (rowLaplacian q) (mono α c) *
          Markov.resolvent (rowLaplacian q) (mono β e)) := by
        rw [resolvent_commute hq hu hs]
    _ = shadow (rowLaplacian q) α c * shadow (rowLaplacian q) β e := resMap_mul hRs hRu
    _ = shadow (rowLaplacian q) β e := shadow_mul_shadow_of_lt hq hαβ hc he

/-- `markov:eq:cross-scale`: for `α < β` and real `c, e > 0`,
`K_α(c)K_β(e) = K_β(e)K_α(c) = K_β(e)`. -/
theorem shadow_cross_scale (hq : ∀ i j, i ≠ j → 0 ≤ q i j) {α β : Γ} (hαβ : α < β)
    {c e : ℝ} (hc : 0 < c) (he : 0 < e) :
    shadow (rowLaplacian q) α c * shadow (rowLaplacian q) β e =
        shadow (rowLaplacian q) β e * shadow (rowLaplacian q) α c ∧
      shadow (rowLaplacian q) β e * shadow (rowLaplacian q) α c =
        shadow (rowLaplacian q) β e :=
  ⟨(shadow_mul_shadow_of_lt hq hαβ hc he).trans (shadow_mul_shadow_of_lt' hq hαβ hc he).symm,
    shadow_mul_shadow_of_lt' hq hαβ hc he⟩

/-- `markov:thm:leading`, last clause: replacing `ct^α` by `ct^α(1 + η)` with `v(η) > 0`
does not change the residue of the resolvent. -/
theorem shadowAt_mono_mul_one_add (hq : ∀ i j, i ≠ j → 0 ≤ q i j) {α : Γ} {c : ℝ}
    (hc : 0 < c) {η : Lex ℝ⟦Γ⟧} (hη : 0 < (ofLex η).orderTop) :
    shadowAt (rowLaplacian q) (mono α c * (1 + η)) = shadow (rowLaplacian q) α c := by
  have hu := mono_pos (α := α) hc
  have hs : 0 < mono α c * (1 + η) := mul_pos hu (one_add_pos_of_orderTop_pos hη)
  have hRs := orderTop_resolvent_nonneg hq hs
  have hRu := orderTop_resolvent_nonneg hq hu
  have hw : mono (-α) c⁻¹ * mono α c = 1 := by
    rw [mono_mul_mono, neg_add_cancel, inv_mul_cancel₀ hc.ne', mono_zero_one]
  have e1 : mono (-α) c⁻¹ * (mono α c - mono α c * (1 + η)) = -η := by
    rw [mul_sub, hw, ← mul_assoc, hw, one_mul]
    abel
  have e2 : mono (-α) c⁻¹ * (mono α c * (1 + η)) = 1 + η := by
    rw [← mul_assoc, hw, one_mul]
  have hε : 0 < (ofLex (mono (-α) c⁻¹ * (mono α c - mono α c * (1 + η)))).orderTop := by
    rw [e1]
    show 0 < (-ofLex η).orderTop
    rwa [orderTop_neg]
  ext i j
  have h := congrArg res
    (mul_resolvent_mul_apply (isUnit_det hq hs) (isUnit_det hq hu) (mono (-α) c⁻¹) i j)
  rw [res_mul_eq_zero hε (mul_apply_orderTop_nonneg hRs hRu i j), hw, e2, one_mul, add_mul,
    one_mul, sub_add_eq_sub_sub, map_sub, map_sub, res_mul_eq_zero hη (hRu i j),
    sub_zero] at h
  exact sub_eq_zero.mp h.symm

/-- The coefficients of `ct^α(1 + η)`, `v(η) > 0`, up to `t^α`: zero below `α` and `c` at
`α`. -/
theorem coeff_mono_mul_one_add {α : Γ} {c : ℝ} {η : Lex ℝ⟦Γ⟧}
    (hη : 0 < (ofLex η).orderTop) {g : Γ} (hg : g ≤ α) :
    (ofLex (mono α c * (1 + η))).coeff g = if g = α then c else 0 := by
  have hlt : ((g - α : Γ) : WithTop Γ) < (ofLex η).orderTop :=
    lt_of_le_of_lt (WithTop.coe_le_zero.mpr (sub_nonpos.mpr hg)) hη
  show (single α c * (1 + ofLex η)).coeff g = _
  rw [coeff_single_mul, coeff_add, coeff_one, coeff_eq_zero_of_lt_orderTop hlt, add_zero]
  simp only [sub_eq_zero, mul_ite, mul_one, mul_zero]

/-- `markov:thm:leading`: every positive `s` has the form `s = ct^α(1 + η)` with
`α = v(s)`, `c = lc(s) > 0` and `v(η) > 0`. -/
theorem eq_mono_mul_one_add {s : Lex ℝ⟦Γ⟧} (hs : 0 < s) :
    0 < (ofLex s).leadingCoeff ∧ ∃ η : Lex ℝ⟦Γ⟧, 0 < (ofLex η).orderTop ∧
      s = mono (ofLex s).order (ofLex s).leadingCoeff * (1 + η) := by
  set α := (ofLex s).order
  set c := (ofLex s).leadingCoeff
  have hc : 0 < c := leadingCoeff_pos_iff.mpr hs
  have hw : mono α c * mono (-α) c⁻¹ = 1 := by
    rw [mono_mul_mono, add_neg_cancel, mul_inv_cancel₀ hc.ne', mono_zero_one]
  refine ⟨hc, mono (-α) c⁻¹ * s - 1, ?_, ?_⟩
  · have hcoeff : ∀ g : Γ, g ≤ 0 → (ofLex (mono (-α) c⁻¹ * s - 1)).coeff g = 0 := by
      intro g hg
      show (single (-α) c⁻¹ * ofLex s - 1).coeff g = 0
      rw [coeff_sub, coeff_single_mul, coeff_one, sub_neg_eq_add]
      rcases hg.lt_or_eq with hg | rfl
      · have hgα : g + α < α := by simpa using hg
        rw [coeff_eq_zero_of_lt_order (x := ofLex s) hgα, if_neg hg.ne, mul_zero, sub_zero]
      · rw [zero_add, if_pos rfl, ← leadingCoeff_eq, inv_mul_cancel₀ hc.ne', sub_self]
    refine lt_of_le_of_ne (le_orderTop_iff_forall.mpr fun g hg => hcoeff g ?_) ?_
    · exact_mod_cast hg.le
    · exact (orderTop_ne_of_coeff_eq_zero (hcoeff 0 le_rfl)).symm
  · rw [add_sub_cancel, ← mul_assoc, hw, one_mul]

/-- `markov:thm:leading`: the form `s = ct^α(1 + η)` with real `c ≠ 0` and `v(η) > 0` is
unique. -/
theorem leading_form_unique {α α' : Γ} {c c' : ℝ} {η η' : Lex ℝ⟦Γ⟧} (hc : c ≠ 0)
    (hc' : c' ≠ 0) (hη : 0 < (ofLex η).orderTop) (hη' : 0 < (ofLex η').orderTop)
    (h : mono α c * (1 + η) = mono α' c' * (1 + η')) : α = α' ∧ c = c' ∧ η = η' := by
  have key : ∀ {α α' : Γ} {c c' : ℝ} {η η' : Lex ℝ⟦Γ⟧}, c ≠ 0 → 0 < (ofLex η).orderTop →
      0 < (ofLex η').orderTop → mono α c * (1 + η) = mono α' c' * (1 + η') → ¬α < α' := by
    intro α α' c c' η η' hc hη hη' h hlt
    have h1 := coeff_mono_mul_one_add (c := c) hη (le_refl α)
    rw [h, coeff_mono_mul_one_add hη' hlt.le, if_neg hlt.ne, if_pos rfl] at h1
    exact hc h1.symm
  obtain rfl : α = α' :=
    le_antisymm (not_lt.mp (key hc' hη' hη h.symm)) (not_lt.mp (key hc hη hη' h))
  obtain rfl : c = c' := by
    have h1 := coeff_mono_mul_one_add (c := c) hη (le_refl α)
    rwa [h, coeff_mono_mul_one_add hη' le_rfl, if_pos rfl, if_pos rfl, eq_comm] at h1
  exact ⟨rfl, rfl, add_left_cancel (mul_left_cancel₀ (mono_ne_zero hc) h)⟩

/-- `markov:thm:leading`: for every positive `s`, `res R_L(s) = K_{v(s)}(lc(s))`. -/
theorem shadowAt_eq_shadow (hq : ∀ i j, i ≠ j → 0 ≤ q i j) {s : Lex ℝ⟦Γ⟧} (hs : 0 < s) :
    shadowAt (rowLaplacian q) s =
      shadow (rowLaplacian q) (ofLex s).order (ofLex s).leadingCoeff := by
  obtain ⟨hc, η, hη, hsη⟩ := eq_mono_mul_one_add hs
  exact (congrArg (shadowAt (rowLaplacian q)) hsη).trans (shadowAt_mono_mul_one_add hq hc hη)

/-- The literal shadow family `c ↦ K_α(c)` satisfies the hypothesis package
`MarkovEffective.IsCrossover` of `markov:thm:effective` as soon as it tends to a shadow
`K_β(e₁)` at a smaller scale `β < α` as `c → ∞` and to a shadow `K_γ(e₂)` at a larger scale
`γ > α` as `c → 0⁺` (the limits `markov:eq:fast-endpoint` and `markov:eq:slow-endpoint`,
identified with shadows in the adjacent plateaux as in `markov:thm:flag`). The endpoint
relations `markov:eq:endpoint-relations` follow from `markov:eq:cross-scale`. -/
theorem isCrossover_shadow (hq : ∀ i j, i ≠ j → 0 ≤ q i j) {α β γ : Γ} (hβ : β < α)
    (hγ : α < γ) {e₁ e₂ : ℝ} (he₁ : 0 < e₁) (he₂ : 0 < e₂)
    (hfast : Tendsto (shadow (rowLaplacian q) α) atTop (𝓝 (shadow (rowLaplacian q) β e₁)))
    (hslow : Tendsto (shadow (rowLaplacian q) α) (𝓝[>] 0)
      (𝓝 (shadow (rowLaplacian q) γ e₂))) :
    MarkovEffective.IsCrossover (shadow (rowLaplacian q) α) (shadow (rowLaplacian q) β e₁)
      (shadow (rowLaplacian q) γ e₂) where
  stochastic _ hc := shadow_mem_rowStochastic hq α hc
  resolvent_identity _ _ hc he _ := shadow_same_scale hq α hc he
  tendsto_atTop := hfast
  tendsto_zero := hslow
  fast_mul _ hc := shadow_mul_shadow_of_lt hq hβ he₁ hc
  mul_fast _ hc := shadow_mul_shadow_of_lt' hq hβ he₁ hc
  mul_slow _ hc := shadow_mul_shadow_of_lt hq hγ hc he₂
  slow_mul _ hc := shadow_mul_shadow_of_lt' hq hγ hc he₂

/-- `markov:lem:resolvent` for a row Laplacian given by its matrix properties, `L𝟙 = 0` and
nonpositive off-diagonal entries: `markov:eq:resolvent-identity` for positive `s ≠ u`,
`markov:eq:same-scale` for real `c, e > 0` with `c ≠ e`, and `markov:eq:cross-scale` for
`α < β` and real `c, e > 0`. -/
theorem resolvent_compatibility {L : Matrix n n (Lex ℝ⟦Γ⟧)} (hL1 : L *ᵥ (fun _ => 1) = 0)
    (hL : ∀ i j, i ≠ j → L i j ≤ 0) :
    (∀ s u : Lex ℝ⟦Γ⟧, 0 < s → 0 < u → s ≠ u →
      Markov.resolvent L s * Markov.resolvent L u =
        (u - s)⁻¹ • (u • Markov.resolvent L s - s • Markov.resolvent L u)) ∧
    (∀ (α : Γ) (c e : ℝ), 0 < c → 0 < e → c ≠ e →
      shadow L α c * shadow L α e = (e - c)⁻¹ • (e • shadow L α c - c • shadow L α e)) ∧
    (∀ (α β : Γ) (c e : ℝ), α < β → 0 < c → 0 < e →
      shadow L α c * shadow L β e = shadow L β e * shadow L α c ∧
        shadow L β e * shadow L α c = shadow L β e) := by
  have hq : ∀ i j, i ≠ j → 0 ≤ -L i j := fun i j h => neg_nonneg.mpr (hL i j h)
  rw [← rowLaplacian_neg hL1]
  exact ⟨fun s u hs hu hsu => resolvent_identity hq hs hu hsu,
    fun α c e hc he hce => shadow_mul_shadow hq α hc he hce,
    fun α β c e hαβ hc he => shadow_cross_scale hq hαβ hc he⟩

end Shadow

end Hahn

end

end Surreal.MarkovShadow
