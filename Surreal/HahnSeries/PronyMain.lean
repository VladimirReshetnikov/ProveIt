import Surreal.HahnSeries.PronyWeight

/-!
# Optimal uniform Prony reconstruction and last-moment sharpness

This file proves `prony:thm:main`, with `prony:eq:strictballs`, `prony:eq:nodebound`,
`prony:eq:weightbound`, the sharpness assertions and `prony:eq:leadingnode`, of
`docs/surcomplex/prony-reconstruction-at-surreal-scales/article.tex`. It assembles the
formalized lemmas `prony:prop:prony` and `prony:prop:last` (`Surreal.Prony`),
`prony:lem:cofactorbound` (`Surreal.PronyBound.cofactorbound`), `prony:lem:localroots`
(`Surreal.PronyLocal.localroots`), `prony:lem:pade` (`Surreal.Prony.moment_padeResidues`) and
`prony:lem:weight` (`Surreal.PronyWeight.weight_bound`), following the source's proofs.

## Setting

Work over `R((t^Γ))`, with `R` any field and `Γ` any linearly ordered abelian group; the source
takes `R = ℝ` or `ℂ` and `Γ` nontrivial, and neither restriction is used. The nodes `a_i` are
integral and distinct and the weights `w_i` are nonzero. `d_i = sepSum a i`, and
`E_i = nodeLoss a w i = v(w_i) + 2 d_i`. The perturbed moments are `m̂ = m + ε` with
`v(ε_k) ≥ κ ∈ Γ` for `k < 2n`.

The general statements take for `δ_i` any `δ_i ≥ 0` bounding every `v(a_i - a_j)`, `j ≠ i`, and
assume `κ > E_i + δ_i` for every `i`. The sharpness lemmas `orderTop_node_error_lastPerturbed`,
`not_exists_strictBall_realization` and `leading_node_lastPerturbed` need neither integral
nodes nor `δ_i ≥ 0`: of the configuration they use only a `δ` bounding every `v(a_i - a_j)`,
`j ≠ i` (which forces distinct nodes), and nonzero weights. `leading_node_lastPerturbed` still
assumes `e ≠ 0` and `v(e) > E_j + δ_j` for every `j`. The source's normalization is
`δ_i = max_{j ≠ i} v(a_i - a_j)`, with `δ_i = 0` when `n = 1`. For integral distinct nodes this
is `Surreal.PronyRows.sepMax` (`sepMax_eq_sup'`, `sepMax_fin_one`); in general
`sepMax a i = max(0, max_{j ≠ i} v(a_i - a_j))`.
The source's threshold `Θ = max_i (E_i + δ_i)` is `threshold` (for `n ≥ 1`), and
`κ > E_i + δ_i` for every `i` is exactly `κ > Θ` (`threshold_lt_iff`).
`exists_reconstruction_sepMax`, `lastMoment_sharp_threshold` and `forall_exists_strictBall_iff`
take `δ_i = sepMax a i` and assume integral nodes, so they are in the source's normalization;
`not_exists_strictBall_realization_of_le_threshold` also takes `δ_i = sepMax a i` but does not
need integral nodes.

## Contents

* `Reconstruction` collects the conclusions of `prony:thm:main` for a labelled realization
  `(â, ŵ)` of the first `2n` perturbed moments. They are: regularity; every `n`-node
  realization, regular or not, is a permutation of `(â, ŵ)`; the strict balls
  `v(â_i - a_i) > δ_i` (`prony:eq:strictballs`), with exactly one such labelling of every
  realization, and `(â, ŵ)` is the only realization labelled this way;
  `v(â_i - a_i) ≥ κ - E_i` (`prony:eq:nodebound`); `v(ŵ_i - w_i) ≥ κ - 2d_i - δ_i > v(w_i)`
  (`prony:eq:weightbound`); and the leading terms of the weights and of the pairwise node
  differences are preserved (`ŵ_i/w_i ∈ 1 + 𝔪` and `prony:eq:separation`).
* `exists_reconstruction` (`prony:thm:main`, reconstruction assertions): under the hypotheses
  above such a realization exists. Its nodes are the ball roots of the corrected annihilator
  `P̂ = P + ∑ b_j Q_j` of `prony:lem:cofactorbound`, located by `prony:lem:localroots`. Its
  weights are the Padé residues `ŵ_i = Â(â_i)/P̂'(â_i)` of `prony:lem:pade` (`padeWeights`),
  bounded by `prony:lem:weight`. `exists_reconstruction_sepMax` is the source's normalization,
  with `κ > Θ`.
* `nodePoly_eq_lastMomentPoly`: every `n`-node realization of the moments with only `m_{2n-1}`
  perturbed by `e`, regular or not, has node polynomial `P_e` (`prony:prop:prony` and
  `prony:prop:last`).
* `orderTop_node_error_lastPerturbed`: every realization of those moments satisfying the strict
  balls has `v(â_i - a_i) + E_i = v(e)`, whatever `e` is. This is the source's comparison of
  `v(P_e(a_i))` with the factorization `P_e(a_i) = ∏_k (a_i - â_k)`.
* `not_exists_strictBall_realization` (final clause of `prony:thm:main`): if
  `v(e) ≤ E_i + δ_i` for some `i`, no `n`-node realization, regular or not, satisfies the
  strict balls. `not_exists_strictBall_realization_of_le_threshold` is the source's form, for
  every `v(e) ≤ Θ` and in particular `v(e) = Θ`, with `δ_i = sepMax a i`; it does not need
  integral nodes.
* `leading_node_lastPerturbed` (`prony:eq:leadingnode`): for `e ≠ 0` with `v(e) > E_j + δ_j`
  for every `j`, every strict-ball realization has
  `(â_i - a_i)/(e/(w_i P'(a_i)²)) ∈ 1 + 𝔪`.
* `lastMoment_sharp` and `lastMoment_sharp_threshold` (sharpness clause of `prony:thm:main`):
  for `e ≠ 0` with `v(e) = κ > Θ`, the realization of `exists_reconstruction` has
  `v(â_i - a_i) = κ - E_i` for every `i` (equality in `prony:eq:nodebound`) and satisfies
  `prony:eq:leadingnode`.
* `forall_exists_strictBall_iff` (the remark after the sharpness proof): the strict-ball
  guarantee at precision `κ`, for every error vector with `v(ε_k) ≥ κ`, holds if and only if
  `κ > Θ`.

## Pending

Nothing in `prony:thm:main` remains pending. The instantiation `prony:cor:actual` to actual
surreal and surcomplex data and `prony:cor:positive` are not formalized here.
-/

namespace Surreal.PronyMain

open Polynomial Finset Surreal.Prony Surreal.PronyBound Surreal.PronyLocal Surreal.PronyRows
  Surreal.PronyWeight

noncomputable section

section Field

variable {K : Type*} [Field K] {n : ℕ}

/-- The Padé residue weights `ŵ_i = Â(â_i)/P̂'(â_i)` of `prony:lem:pade`, where
`P̂ = ∏ (X - â_j)` and `Â` is its Padé numerator for the moments `m̂` (`prony:eq:numerators`). -/
def padeWeights (mh : ℕ → K) (â : Fin n → K) (i : Fin n) : K :=
  (padeNumerator (2 * n) mh (nodePoly â)).eval (â i) / (nodePoly â).derivative.eval (â i)

/-- The node polynomial of any `n`-node realization of the first `2n` moments `m̂` annihilates
`1, X, …, X^{n-1}` for `m̂` (`prony:eq:orthog`). -/
theorem momentLinear_nodePoly_mul_X_pow {b u : Fin n → K} {mh : ℕ → K}
    (hm : ∀ r < 2 * n, moment b u r = mh r) {r : ℕ} (hr : r < n) :
    momentLinear mh (nodePoly b * X ^ r) = 0 := by
  have hdeg : (nodePoly b * X ^ r).natDegree < 2 * n := by
    rw [natDegree_mul_X_pow _ (nodePoly_monic b).ne_zero, natDegree_nodePoly]
    omega
  rw [← momentLinear_congr hdeg hm, momentLinear_moment, momentFunctional_nodePoly_mul]

/-- The cofactor coordinates `β_j = -e/c_j`, `c_j = w_j P'(a_j)²`, of the last-moment
annihilator `P_e` (the proof of `prony:prop:last`). -/
def lastCoords (a w : Fin n → K) (e : K) (j : Fin n) : K :=
  -(e / cofactorWeight a w j)

/-- `prony:eq:Pe` in cofactor coordinates: `P_e = P + ∑ β_j Q_j` with `β_j = -e/c_j`. -/
theorem lastMomentPoly_eq_perturbedPoly (a w : Fin n → K) (e : K) :
    lastMomentPoly a w e = perturbedPoly a (lastCoords a w e) := by
  simp only [lastMomentPoly, perturbedPoly, lastCoords, cofactorWeight, map_neg, neg_mul,
    Finset.sum_neg_distrib, sub_eq_add_neg]

/-- The step of the sharpness proof of `prony:thm:main` that uses `prony:prop:prony` and
`prony:prop:last`: every `n`-node realization of the moments with only `m_{2n-1}` perturbed,
regular or not, has node polynomial `P_e`. -/
theorem nodePoly_eq_lastMomentPoly {a w b u : Fin n → K} (ha : Function.Injective a)
    (hw : ∀ i, w i ≠ 0) (e : K) (hn : 0 < n)
    (hm : ∀ r < 2 * n, moment b u r = lastPerturbed a w e r) :
    nodePoly b = lastMomentPoly a w e :=
  lastMomentPoly_unique ha hw e hn (nodePoly_monic b) (natDegree_nodePoly b)
    fun _ hr => momentLinear_nodePoly_mul_X_pow hm hr

/-- The last-perturbed moments are `m + ε` with `ε_k = e` for `k = 2n - 1` and `0` otherwise. -/
theorem lastPerturbed_eq_add (a w : Fin n → K) (e : K) :
    lastPerturbed a w e = moment a w + fun r => if r = 2 * n - 1 then e else 0 :=
  rfl

end Field

section Hahn

open scoped _root_.HahnSeries

variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field R]
  {n : ℕ}

/-- The conclusions of `prony:thm:main` for a labelled realization `(â, ŵ)` of the moments `m̂`,
relative to the configuration `(a, w)`, the ball radii `δ` and the precision `κ`. -/
structure Reconstruction (a w : Fin n → R⟦Γ⟧) (δ : Fin n → Γ) (mh : ℕ → R⟦Γ⟧) (κ : Γ)
    (â ŵ : Fin n → R⟦Γ⟧) : Prop where
  /-- `(â, ŵ)` realizes the first `2n` moments `m̂`. -/
  realizes : ∀ r < 2 * n, moment â ŵ r = mh r
  /-- The realization is regular: its nodes are distinct, … -/
  injective : Function.Injective â
  /-- … and its weights are nonzero. -/
  weight_ne_zero : ∀ i, ŵ i ≠ 0
  /-- Uniqueness up to permutation: every `n`-node realization of the first `2n` moments,
  regular or not, is a permutation of `(â, ŵ)`. -/
  eq_perm : ∀ b u : Fin n → R⟦Γ⟧, (∀ r < 2 * n, moment b u r = mh r) →
    ∃ σ : Equiv.Perm (Fin n), b = â ∘ σ ∧ u = ŵ ∘ σ
  /-- `prony:eq:strictballs`: `v(â_i - a_i) > δ_i`. -/
  strictBall : ∀ i, (δ i : WithTop Γ) < (â i - a i).orderTop
  /-- The labelling `prony:eq:strictballs` of every realization exists and is unique. -/
  existsUnique_labelling : ∀ b u : Fin n → R⟦Γ⟧, (∀ r < 2 * n, moment b u r = mh r) →
    ∃! σ : Equiv.Perm (Fin n), ∀ i, (δ i : WithTop Γ) < (b (σ i) - a i).orderTop
  /-- `(â, ŵ)` is the only realization labelled by `prony:eq:strictballs`. -/
  eq_of_strictBall : ∀ b u : Fin n → R⟦Γ⟧, (∀ r < 2 * n, moment b u r = mh r) →
    (∀ i, (δ i : WithTop Γ) < (b i - a i).orderTop) → b = â ∧ u = ŵ
  /-- `prony:eq:nodebound`: `v(â_i - a_i) ≥ κ - E_i`. -/
  nodebound : ∀ i, ((κ - nodeLoss a w i : Γ) : WithTop Γ) ≤ (â i - a i).orderTop
  /-- `prony:eq:weightbound`: `v(ŵ_i - w_i) ≥ κ - 2 d_i - δ_i`. -/
  weightbound : ∀ i, ((κ - 2 • sepSum a i - δ i : Γ) : WithTop Γ) ≤ (ŵ i - w i).orderTop
  /-- `prony:eq:weightbound`: `κ - 2 d_i - δ_i > v(w_i)`. -/
  order_lt_weightbound : ∀ i, (w i).order < κ - 2 • sepSum a i - δ i
  /-- The leading terms of the weights are preserved: `ŵ_i` has the valuation and the leading
  coefficient of `w_i`, and `ŵ_i/w_i ∈ 1 + 𝔪`. -/
  weight_leading : ∀ i, (ŵ i).orderTop = (w i).orderTop ∧
    (ŵ i).leadingCoeff = (w i).leadingCoeff ∧ 0 < (ŵ i / w i - 1).orderTop
  /-- The leading terms of the pairwise node differences are preserved (`prony:eq:separation`):
  `â_i - â_j` has the valuation and the leading coefficient of `a_i - a_j`, and
  `(â_i - â_j)/(a_i - a_j) ∈ 1 + 𝔪`. -/
  separation : ∀ i j, i ≠ j → (â i - â j).orderTop = (a i - a j).orderTop ∧
    (â i - â j).leadingCoeff = (a i - a j).leadingCoeff ∧
    0 < ((â i - â j) / (a i - a j) - 1).orderTop

/-- Cancel a finite summand in `WithTop Γ`: `x + E = g` gives `x = g - E`. -/
theorem eq_coe_sub_of_add_eq {x : WithTop Γ} {g E : Γ} (h : x + E = g) :
    x = ((g - E : Γ) : WithTop Γ) := by
  induction x using WithTop.recTopCoe with
  | top => simp at h
  | coe x =>
    rw [← WithTop.coe_add, WithTop.coe_inj] at h
    rw [WithTop.coe_inj]
    exact eq_sub_of_add_eq h

variable {a : Fin n → R⟦Γ⟧} {δ : Fin n → Γ}

/-- Unique labelling in `prony:thm:main`: if `(â, ŵ)` is regular with `â_i` in the strict ball
`B_i = {x : v(x - a_i) > δ_i}`, every realization of the same first `2n` moments has exactly
one labelling that puts its `i`-th node in `B_i`. The balls are disjoint. -/
theorem existsUnique_labelling (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i)
    {â ŵ b u : Fin n → R⟦Γ⟧} (hinj : Function.Injective â) (hŵ : ∀ i, ŵ i ≠ 0)
    (hâ : ∀ i, (δ i : WithTop Γ) < (â i - a i).orderTop)
    (hm : ∀ r < 2 * n, moment â ŵ r = moment b u r) :
    ∃! σ : Equiv.Perm (Fin n), ∀ i, (δ i : WithTop Γ) < (b (σ i) - a i).orderTop := by
  obtain ⟨τ, hbτ, -⟩ := exists_perm_of_moment_eq hinj hŵ hm
  subst hbτ
  refine ⟨τ.symm, fun i => ?_, fun σ hσ => Equiv.ext fun i => ?_⟩
  · simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hâ i
  · have h1 := hσ i
    simp only [Function.comp_apply] at h1
    have hτ : τ (σ i) = i := by
      by_contra hne
      exact not_mem_ball_of_ne hδ hne (hâ (τ (σ i))) h1
    exact (τ.symm_apply_eq.mpr hτ.symm).symm

/-- The strict-ball realization in `prony:thm:main` is unique: a realization of the moments of a
regular strict-ball realization `(â, ŵ)` whose nodes also lie in the strict balls is
`(â, ŵ)` itself. -/
theorem eq_of_strictBall (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i)
    {â ŵ b u : Fin n → R⟦Γ⟧} (hinj : Function.Injective â) (hŵ : ∀ i, ŵ i ≠ 0)
    (hâ : ∀ i, (δ i : WithTop Γ) < (â i - a i).orderTop)
    (hm : ∀ r < 2 * n, moment â ŵ r = moment b u r)
    (hb : ∀ i, (δ i : WithTop Γ) < (b i - a i).orderTop) : b = â ∧ u = ŵ := by
  obtain ⟨τ, hbτ, huτ⟩ := exists_perm_of_moment_eq hinj hŵ hm
  have hτ : ∀ i, τ i = i := fun i => by
    by_contra hne
    have h1 := hb i
    rw [hbτ, Function.comp_apply] at h1
    exact not_mem_ball_of_ne hδ hne (hâ (τ i)) h1
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩
  · rw [hbτ, Function.comp_apply, hτ i]
  · rw [huτ, Function.comp_apply, hτ i]

/-- `prony:thm:main`, reconstruction assertions. Let the nodes be integral, let `δ_i ≥ 0` bound
`v(a_i - a_j)` for every `j ≠ i` (which forces distinct nodes), let the weights be nonzero, let
`v(ε_k) ≥ κ` for `k < 2n`, and let `κ > E_i + δ_i` for every `i`. Then the perturbed moments
`m + ε` have a regular labelled realization `(â, ŵ)` with all the properties of
`Reconstruction`: uniqueness up to permutation, the unique strict-ball labelling,
`prony:eq:nodebound`, `prony:eq:weightbound` and the preserved leading terms. -/
theorem exists_reconstruction {w : Fin n → R⟦Γ⟧} {ε : ℕ → R⟦Γ⟧} {κ : Γ}
    (ha0 : ∀ i, 0 ≤ (a i).orderTop)
    (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i) (hδ0 : ∀ i, 0 ≤ δ i)
    (hw : ∀ i, w i ≠ 0) (hε : ∀ r < 2 * n, (κ : WithTop Γ) ≤ (ε r).orderTop)
    (hκ : ∀ i, nodeLoss a w i + δ i < κ) :
    ∃ â ŵ : Fin n → R⟦Γ⟧, Reconstruction a w δ (moment a w + ε) κ â ŵ := by
  have ha : Function.Injective a := injective_of_le_scale hδ
  have hκE : ∀ j, nodeLoss a w j < κ := fun j =>
    (le_add_of_nonneg_right (hδ0 j)).trans_lt (hκ j)
  -- `prony:lem:cofactorbound`: the corrected annihilator `P̂ = P + ∑ b_j Q_j`.
  obtain ⟨⟨b, hb, -⟩, hbd⟩ := cofactorbound ha0 ha hw hε hκE
  have hbδ : ∀ i, (δ i : WithTop Γ) < (b i).orderTop := fun i =>
    (WithTop.coe_lt_coe.mpr (lt_sub_iff_add_lt'.mpr (hκ i))).trans_le (hbd b hb i).2
  -- `prony:lem:localroots`: one simple root of `P̂` in each strict ball.
  obtain ⟨â, hinj, hP, hball, -, hdisp, -, -, hsep⟩ := localroots hδ hbδ
  have hann : ∀ r < n, momentLinear (moment a w + ε) (nodePoly â * X ^ r) = 0 := by
    intro r hr
    rw [← hP]
    exact (annihilates_iff_X_pow _ _).mp hb r hr
  have hroot : ∀ i, (nodePoly â).eval (â i) = 0 := fun i =>
    (eval_nodePoly_eq_zero_iff â _).mpr ⟨i, rfl⟩
  -- `prony:lem:pade`: the residues realize all `2n` moments.
  have hreal : ∀ r < 2 * n,
      moment â (padeWeights (moment a w + ε) â) r = (moment a w + ε) r := fun r hr =>
    moment_padeResidues (nodePoly_monic â) (natDegree_nodePoly â) hann hinj hroot hr
  have hε' : ∀ k < 2 * n, (κ : WithTop Γ) ≤ ((moment a w + ε) k - moment a w k).orderTop := by
    intro k hk
    rw [Pi.add_apply, add_sub_cancel_left]
    exact hε k hk
  -- `prony:lem:weight`.
  have hwb : ∀ i, ((κ - 2 • sepSum a i - δ i : Γ) : WithTop Γ) ≤
      (padeWeights (moment a w + ε) â i - w i).orderTop := fun i =>
    weight_bound ha0 hδ hδ0 hball hann hε' i
  have hwlt : ∀ i, (w i).order < κ - 2 • sepSum a i - δ i := fun i => by
    have h := hκ i
    rw [nodeLoss_eq] at h
    rw [sub_sub, lt_sub_iff_add_lt, ← add_assoc]
    exact h
  have hlt : ∀ i, (w i).orderTop < (padeWeights (moment a w + ε) â i - w i).orderTop :=
    fun i => by
      rw [← _root_.HahnSeries.order_eq_orderTop_of_ne_zero (hw i)]
      exact (WithTop.coe_lt_coe.mpr (hwlt i)).trans_le (hwb i)
  have hlead : ∀ i, (padeWeights (moment a w + ε) â i).orderTop = (w i).orderTop ∧
      (padeWeights (moment a w + ε) â i).leadingCoeff = (w i).leadingCoeff := fun i => by
    have h1 := _root_.HahnSeries.orderTop_add_eq_left (hlt i)
    have h2 := _root_.HahnSeries.leadingCoeff_add_eq_left (hlt i)
    rw [add_sub_cancel] at h1 h2
    exact ⟨h1, h2⟩
  have hŵ0 : ∀ i, padeWeights (moment a w + ε) â i ≠ 0 := fun i h0 => by
    have h := (hlead i).1
    rw [h0, _root_.HahnSeries.orderTop_zero] at h
    exact _root_.HahnSeries.orderTop_ne_top.mpr (hw i) h.symm
  have hratio : ∀ i, 0 < (padeWeights (moment a w + ε) â i / w i - 1).orderTop := fun i => by
    rw [div_sub_one (hw i)]
    exact orderTop_div_pos (hw i) (hlt i)
  refine ⟨â, padeWeights (moment a w + ε) â,
    { realizes := hreal
      injective := hinj
      weight_ne_zero := hŵ0
      eq_perm := fun b' u' hm' =>
        exists_perm_of_moment_eq hinj hŵ0 fun r hr => (hreal r hr).trans (hm' r hr).symm
      strictBall := hball
      existsUnique_labelling := fun b' u' hm' =>
        existsUnique_labelling hδ hinj hŵ0 hball fun r hr => (hreal r hr).trans (hm' r hr).symm
      eq_of_strictBall := fun b' u' hm' hb' =>
        eq_of_strictBall hδ hinj hŵ0 hball (fun r hr => (hreal r hr).trans (hm' r hr).symm) hb'
      nodebound := fun i => by
        rw [hdisp i]
        exact (hbd b hb i).2
      weightbound := hwb
      order_lt_weightbound := hwlt
      weight_leading := fun i => ⟨(hlead i).1, (hlead i).2, hratio i⟩
      separation := fun i j hij => ⟨(orderTop_leadingCoeff_sub_of_mem_balls hδ hij (hball i)
        (hball j)).1, (orderTop_leadingCoeff_sub_of_mem_balls hδ hij (hball i) (hball j)).2,
        hsep i j hij⟩ }⟩

/-- The threshold `Θ = max_i (E_i + δ_i)` of `prony:eq:geometry`, for `n ≥ 1`, with
`δ_i = sepMax a i` (the source's `max_{j ≠ i} v(a_i - a_j)` for integral distinct nodes, and
`0` for `n = 1`). -/
def threshold [NeZero n] (a w : Fin n → R⟦Γ⟧) : Γ :=
  univ.sup' ⟨0, mem_univ _⟩ fun i => nodeLoss a w i + sepMax a i

omit [IsOrderedAddMonoid Γ] in
/-- `κ > Θ` if and only if `κ > E_i + δ_i` for every `i`. -/
theorem threshold_lt_iff [NeZero n] (a w : Fin n → R⟦Γ⟧) (κ : Γ) :
    threshold a w < κ ↔ ∀ i, nodeLoss a w i + sepMax a i < κ := by
  rw [threshold, Finset.sup'_lt_iff]
  simp

omit [IsOrderedAddMonoid Γ] in
/-- The maximum defining `Θ` is attained. -/
theorem exists_eq_threshold [NeZero n] (a w : Fin n → R⟦Γ⟧) :
    ∃ i, nodeLoss a w i + sepMax a i = threshold a w := by
  obtain ⟨i, -, hi⟩ := univ.exists_mem_eq_sup' ⟨0, mem_univ _⟩
    fun i => nodeLoss a w i + sepMax a i
  exact ⟨i, hi.symm⟩

omit [IsOrderedAddMonoid Γ] in
/-- For distinct nodes, `δ_i = sepMax a i` bounds every `v(a_i - a_j)`, `j ≠ i`. -/
theorem orderTop_sub_le_sepMax (ha : Function.Injective a) (i j : Fin n) (hji : j ≠ i) :
    (a i - a j).orderTop ≤ ((sepMax a i : Γ) : WithTop Γ) := by
  rw [orderTop_sub_of_ne ha hji]
  exact WithTop.coe_le_coe.mpr (order_sub_le_sepMax a hji)

/-- `prony:thm:main`, reconstruction assertions, in the source's normalization: integral
distinct nodes, nonzero weights, `v(ε_k) ≥ κ` for `k < 2n` and `κ > Θ`, with
`δ_i = max_{j ≠ i} v(a_i - a_j)` (`0` for `n = 1`). -/
theorem exists_reconstruction_sepMax [NeZero n] {w : Fin n → R⟦Γ⟧} {ε : ℕ → R⟦Γ⟧} {κ : Γ}
    (ha0 : ∀ i, 0 ≤ (a i).orderTop) (ha : Function.Injective a) (hw : ∀ i, w i ≠ 0)
    (hε : ∀ r < 2 * n, (κ : WithTop Γ) ≤ (ε r).orderTop) (hκ : threshold a w < κ) :
    ∃ â ŵ : Fin n → R⟦Γ⟧, Reconstruction a w (sepMax a) (moment a w + ε) κ â ŵ :=
  exists_reconstruction ha0 (orderTop_sub_le_sepMax ha) (sepMax_nonneg a) hw hε
    ((threshold_lt_iff a w κ).mp hκ)

/-- The sharpness proof of `prony:thm:main`: every `n`-node realization of the moments with only
`m_{2n-1}` perturbed by `e`, regular or not, whose nodes lie in the strict balls, satisfies
`v(â_i - a_i) + E_i = v(e)`. No hypothesis on `e` is needed (for `e = 0` both sides are `⊤`).
Indeed `v(P_e(a_i)) = v(e) - E_i + d_i` by `prony:eq:Pe`, while the factorization
`P_e(a_i) = ∏_k (a_i - â_k)` gives `v(a_i - â_i) + d_i`. -/
theorem orderTop_node_error_lastPerturbed {w : Fin n → R⟦Γ⟧}
    (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i) (hw : ∀ i, w i ≠ 0) {e : R⟦Γ⟧}
    {b u : Fin n → R⟦Γ⟧} (hm : ∀ r < 2 * n, moment b u r = lastPerturbed a w e r)
    (hball : ∀ k, (δ k : WithTop Γ) < (b k - a k).orderTop) (i : Fin n) :
    (b i - a i).orderTop + ((nodeLoss a w i : Γ) : WithTop Γ) = e.orderTop := by
  have ha := injective_of_le_scale hδ
  have hev := congrArg (eval (a i)) (nodePoly_eq_lastMomentPoly ha hw e (Fin.pos i) hm)
  rw [eval_lastMomentPoly, nodePoly, eval_prod] at hev
  simp only [eval_sub, eval_X, eval_C] at hev
  have hsplit : (∏ k, (a i - b k)).orderTop =
      (b i - a i).orderTop + ((sepSum a i : Γ) : WithTop Γ) := by
    rw [Surreal.HahnSeries.orderTop_finset_prod, ← Finset.add_sum_erase _ _ (mem_univ i),
      orderTop_sub_comm (a i) (b i), sepSum, WithTop.coe_sum]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have hki : k ≠ i := ne_of_mem_erase hk
    rw [(orderTop_leadingCoeff_sub_of_mem_balls hδ (Ne.symm hki) (mem_ball_self i)
      (hball k)).1, orderTop_sub_of_ne ha hki]
  have h1 : (b i - a i).orderTop = (e / (w i * (cofactor a i).eval (a i) ^ 2)).orderTop := by
    refine WithTop.add_right_cancel (z := ((sepSum a i : Γ) : WithTop Γ)) WithTop.coe_ne_top ?_
    rw [← hsplit, hev, _root_.HahnSeries.orderTop_neg, _root_.HahnSeries.orderTop_mul,
      orderTop_eval_cofactor_self ha i]
  rw [h1, ← orderTop_cofactorWeight ha hw i]
  exact orderTop_div_add (cofactorWeight_ne_zero ha hw i)

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
/-- The errors of the last-moment perturbation, `ε_k = e` for `k = 2n - 1` and `0` otherwise,
all have valuation at least any lower bound for `v(e)`. -/
theorem le_orderTop_lastError {e : R⟦Γ⟧} {κ : WithTop Γ} (he : κ ≤ e.orderTop) (r : ℕ) :
    κ ≤ (if r = 2 * n - 1 then e else 0 : R⟦Γ⟧).orderTop := by
  split_ifs
  · exact he
  · rw [_root_.HahnSeries.orderTop_zero]
    exact le_top

/-- The final clause of `prony:thm:main`, in a stronger form: if only `m_{2n-1}` is perturbed,
by `e` with `v(e) ≤ E_i + δ_i` for some `i`, then no `n`-node realization of these moments,
regular or not, has its nodes in the strict balls `v(â_k - a_k) > δ_k`. -/
theorem not_exists_strictBall_realization {w : Fin n → R⟦Γ⟧}
    (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i) (hw : ∀ i, w i ≠ 0) {e : R⟦Γ⟧}
    {i : Fin n} (hle : e.orderTop ≤ ((nodeLoss a w i + δ i : Γ) : WithTop Γ)) :
    ¬ ∃ b u : Fin n → R⟦Γ⟧, (∀ r < 2 * n, moment b u r = lastPerturbed a w e r) ∧
      ∀ k, (δ k : WithTop Γ) < (b k - a k).orderTop := by
  rintro ⟨b, u, hm, hball⟩
  have h := orderTop_node_error_lastPerturbed hδ hw hm hball i
  have h3 := WithTop.add_lt_add_right (WithTop.coe_ne_top (a := nodeLoss a w i)) (hball i)
  rw [h, ← WithTop.coe_add, add_comm] at h3
  exact lt_irrefl _ (h3.trans_le hle)

/-- The final clause of `prony:thm:main` with `δ_i = sepMax a i`, which is the source's `δ_i` for
integral nodes; integrality is not needed for this clause. For distinct nodes and nonzero
weights, if only `m_{2n-1}` is perturbed, by `e` with `v(e) ≤ Θ = threshold a w` (in particular
`v(e) = Θ`), no `n`-node realization, regular or not, satisfies `v(â_k - a_k) > sepMax a k` for
every `k` (`prony:eq:strictballs`). -/
theorem not_exists_strictBall_realization_of_le_threshold [NeZero n] {w : Fin n → R⟦Γ⟧}
    (ha : Function.Injective a) (hw : ∀ i, w i ≠ 0) {e : R⟦Γ⟧}
    (he : e.orderTop ≤ ((threshold a w : Γ) : WithTop Γ)) :
    ¬ ∃ b u : Fin n → R⟦Γ⟧, (∀ r < 2 * n, moment b u r = lastPerturbed a w e r) ∧
      ∀ k, ((sepMax a k : Γ) : WithTop Γ) < (b k - a k).orderTop := by
  obtain ⟨i, hi⟩ := exists_eq_threshold a w
  exact not_exists_strictBall_realization (orderTop_sub_le_sepMax ha) hw (i := i)
    (by rw [hi]; exact he)

/-- `prony:eq:leadingnode`: if only `m_{2n-1}` is perturbed, by `e ≠ 0` with `v(e) > E_j + δ_j`
for every `j`, every realization whose nodes lie in the strict balls satisfies
`(â_i - a_i)/(e/(w_i P'(a_i)²)) ∈ 1 + 𝔪`, written with `P'(a_i) = Q_i(a_i)`
(`Surreal.Prony.eval_derivative_nodePoly`). By `prony:prop:last` its node polynomial is
`P_e = P + ∑ β_j Q_j` with `β_j = -e/c_j`, and `prony:lem:localroots` gives
`(â_i - a_i)/β_i ∈ -1 + 𝔪`. -/
theorem leading_node_lastPerturbed {w : Fin n → R⟦Γ⟧}
    (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i) (hw : ∀ i, w i ≠ 0) {e : R⟦Γ⟧}
    (he : e ≠ 0) (hκ : ∀ j, nodeLoss a w j + δ j < e.order) {b u : Fin n → R⟦Γ⟧}
    (hm : ∀ r < 2 * n, moment b u r = lastPerturbed a w e r)
    (hball : ∀ k, (δ k : WithTop Γ) < (b k - a k).orderTop) (i : Fin n) :
    0 < ((b i - a i) / (e / (w i * (cofactor a i).eval (a i) ^ 2)) - 1).orderTop := by
  have ha := injective_of_le_scale hδ
  have hβv : ∀ j, (lastCoords a w e j).orderTop =
      ((e.order - nodeLoss a w j : Γ) : WithTop Γ) := fun j => by
    have h := orderTop_div_add (x := e) (cofactorWeight_ne_zero ha hw j)
    rw [orderTop_cofactorWeight ha hw j,
      ← _root_.HahnSeries.order_eq_orderTop_of_ne_zero he] at h
    rw [lastCoords, _root_.HahnSeries.orderTop_neg]
    exact eq_coe_sub_of_add_eq h
  have hβδ : ∀ j, (δ j : WithTop Γ) < (lastCoords a w e j).orderTop := fun j => by
    rw [hβv j]
    exact WithTop.coe_lt_coe.mpr (lt_sub_iff_add_lt'.mpr (hκ j))
  have hroot : (perturbedPoly a (lastCoords a w e)).IsRoot (b i) := by
    rw [← lastMomentPoly_eq_perturbedPoly, ← nodePoly_eq_lastMomentPoly ha hw e (Fin.pos i) hm,
      IsRoot.def, eval_nodePoly_eq_zero_iff]
    exact ⟨i, rfl⟩
  have hβ0 : lastCoords a w e i ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero he (cofactorWeight_ne_zero ha hw i))
  have hr := orderTop_displacement_ratio hδ hβδ (hball i) hroot hβ0
  have heq : (b i - a i) / (e / (w i * (cofactor a i).eval (a i) ^ 2)) - 1 =
      -((b i - a i) / lastCoords a w e i + 1) := by
    rw [lastCoords, cofactorWeight, div_neg]
    ring
  rw [heq, _root_.HahnSeries.orderTop_neg]
  exact hr

/-- The sharpness clause of `prony:thm:main`: if only `m_{2n-1}` is perturbed, by `e ≠ 0` with
`κ = v(e) > E_i + δ_i` for every `i`, the labelled realization of `exists_reconstruction` has
`v(â_i - a_i) = κ - E_i` for every `i` (equality in `prony:eq:nodebound`), and
`(â_i - a_i)/(e/(w_i P'(a_i)²)) ∈ 1 + 𝔪` (`prony:eq:leadingnode`). -/
theorem lastMoment_sharp {w : Fin n → R⟦Γ⟧} (ha0 : ∀ i, 0 ≤ (a i).orderTop)
    (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i) (hδ0 : ∀ i, 0 ≤ δ i)
    (hw : ∀ i, w i ≠ 0) {e : R⟦Γ⟧} (he : e ≠ 0) (hκ : ∀ i, nodeLoss a w i + δ i < e.order) :
    ∃ â ŵ : Fin n → R⟦Γ⟧, Reconstruction a w δ (lastPerturbed a w e) e.order â ŵ ∧
      (∀ i, (â i - a i).orderTop = ((e.order - nodeLoss a w i : Γ) : WithTop Γ)) ∧
      ∀ i, 0 < ((â i - a i) / (e / (w i * (cofactor a i).eval (a i) ^ 2)) - 1).orderTop := by
  have hε : ∀ r < 2 * n, (e.order : WithTop Γ) ≤
      ((fun r => if r = 2 * n - 1 then e else 0) r).orderTop := fun r _ =>
    le_orderTop_lastError (_root_.HahnSeries.order_eq_orderTop_of_ne_zero he).le r
  obtain ⟨â, ŵ, hR⟩ := exists_reconstruction ha0 hδ hδ0 hw hε hκ
  rw [← lastPerturbed_eq_add] at hR
  refine ⟨â, ŵ, hR, fun i => eq_coe_sub_of_add_eq ?_, fun i =>
    leading_node_lastPerturbed hδ hw he hκ hR.realizes hR.strictBall i⟩
  rw [orderTop_node_error_lastPerturbed hδ hw hR.realizes hR.strictBall i,
    _root_.HahnSeries.order_eq_orderTop_of_ne_zero he]

/-- The sharpness clause of `prony:thm:main` in the source's normalization: for `e ≠ 0` with
`κ = v(e) > Θ`, the labelled realization of the last-perturbed moments has
`v(â_i - a_i) = κ - E_i` for every `i` and satisfies `prony:eq:leadingnode`. -/
theorem lastMoment_sharp_threshold [NeZero n] {w : Fin n → R⟦Γ⟧}
    (ha0 : ∀ i, 0 ≤ (a i).orderTop) (ha : Function.Injective a) (hw : ∀ i, w i ≠ 0)
    {e : R⟦Γ⟧} (he : e ≠ 0) (hκ : threshold a w < e.order) :
    ∃ â ŵ : Fin n → R⟦Γ⟧, Reconstruction a w (sepMax a) (lastPerturbed a w e) e.order â ŵ ∧
      (∀ i, (â i - a i).orderTop = ((e.order - nodeLoss a w i : Γ) : WithTop Γ)) ∧
      ∀ i, 0 < ((â i - a i) / (e / (w i * (cofactor a i).eval (a i) ^ 2)) - 1).orderTop :=
  lastMoment_sharp ha0 (orderTop_sub_le_sepMax ha) (sepMax_nonneg a) hw he
    ((threshold_lt_iff a w _).mp hκ)

/-- The remark after the sharpness proof of `prony:thm:main`: the universal strict-ball guarantee
at precision `κ` holds if and only if `κ > Θ`. The guarantee asks that every error vector with
`v(ε_k) ≥ κ` for `k < 2n` have an `n`-node realization of `m + ε` with `v(â_i - a_i) > δ_i`
for every `i`. Sufficiency is `exists_reconstruction_sepMax`; for `κ ≤ Θ` the last-moment
perturbation by `t^κ` is a counterexample (`not_exists_strictBall_realization_of_le_threshold`).
-/
theorem forall_exists_strictBall_iff [NeZero n] {w : Fin n → R⟦Γ⟧}
    (ha0 : ∀ i, 0 ≤ (a i).orderTop) (ha : Function.Injective a) (hw : ∀ i, w i ≠ 0) (κ : Γ) :
    (∀ ε : ℕ → R⟦Γ⟧, (∀ r < 2 * n, (κ : WithTop Γ) ≤ (ε r).orderTop) →
      ∃ b u : Fin n → R⟦Γ⟧, (∀ r < 2 * n, moment b u r = (moment a w + ε) r) ∧
        ∀ k, ((sepMax a k : Γ) : WithTop Γ) < (b k - a k).orderTop) ↔ threshold a w < κ := by
  refine ⟨fun h => ?_, fun hκ ε hε => ?_⟩
  · by_contra hle
    rw [not_lt] at hle
    have hev : (_root_.HahnSeries.single κ (1 : R)).orderTop = κ :=
      _root_.HahnSeries.orderTop_single one_ne_zero
    obtain ⟨b, u, hm, hball⟩ :=
      h (fun r => if r = 2 * n - 1 then _root_.HahnSeries.single κ (1 : R) else 0)
        fun r _ => le_orderTop_lastError hev.ge r
    exact not_exists_strictBall_realization_of_le_threshold ha hw
      (by rw [hev]; exact WithTop.coe_le_coe.mpr hle) ⟨b, u, hm, hball⟩
  · obtain ⟨â, ŵ, hR⟩ := exists_reconstruction_sepMax ha0 ha hw hε hκ
    exact ⟨â, ŵ, hR.realizes, hR.strictBall⟩

end Hahn

end

end Surreal.PronyMain
