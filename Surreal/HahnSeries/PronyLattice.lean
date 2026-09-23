import Surreal.HahnSeries.PronyMain
import Surreal.HahnSeries.ChartIsometry
import Surreal.HahnSeries.CoefficientMapping
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.HahnSeries.Lex
import Mathlib.Order.Zorn
import Mathlib.Tactic.LinearCombination

/-!
# The finite coefficient criterion and real positive Prony data

This file proves `prony:prop:lattice`, with `prony:eq:Cexpand`, `prony:eq:latticecriterion` and
`prony:eq:latticeimage`, and `prony:cor:positive` for real Hahn data (the clause about actual
surreal inputs is pending; see below) of
`docs/surcomplex/prony-reconstruction-at-surreal-scales/article.tex`.

## `prony:prop:lattice`

Let `K = R((t^Γ))`, where `R` is any commutative ring (the source takes `ℝ` or `ℂ`) and `Γ` is
any linearly ordered abelian group. The coordinates are indexed by any finite type `σ` (the
source's `{1, …, N}`), and `t^κ 𝒪^σ = {Z : v(Z_l) ≥ κ for every l}` is `latticeBall κ`, for any
`κ ∈ Γ`, positive or not.

* `jacobian F x` is `J = dF_x`, `J_{jl} = ∂F_j/∂Z_l (x)` (Mathlib's `pderiv`), and
  `expansion F x M` is the polynomial `G(Z) = F(x + M Z) - F(x)` (`eval_expansion`). It has no
  constant term (`coeff_zero_expansion`) and linear part `J M` (`coeff_single_expansion`), so for
  `M = J^{-1}` its linear part is `Z` (`coeff_single_expansion_inv`). Hence
  `F(x + J^{-1} Z) - F(x) = Z + (∑_{|ν| ≥ 2} C_{j,ν} Z^ν)_j` with finite sums
  (`expansion_eq_X_add`, `prony:eq:Cexpand`); the `C_{j,ν}` are the coefficients of the
  expansion. The linear part is computed from the chain rule `pderiv_bind₁_eq`.
* `LatticeCriterion G κ` is `prony:eq:latticecriterion`:
  `v(C_{j,ν}) + (|ν| - 1) κ > 0` for every nonzero `C_{j,ν}` with `|ν| ≥ 2`.
* `lattice`: if `J` is invertible and the criterion holds for `F(x + J^{-1} Z) - F(x)`, then `F`
  is a bijection from `x + J^{-1} t^κ 𝒪^σ` onto `F(x) + t^κ 𝒪^σ`; `lattice_image` is
  `prony:eq:latticeimage`, and `lattice_isometry` is the isometry
  `v_min(F(x + J^{-1} Z) - F(x + J^{-1} Z')) = v_min(Z - Z')` behind injectivity.
* The generic statements behind it: `bijOn_latticeBall` (a polynomial map with zero constant
  term, identity linear part and the criterion is a bijection of `t^κ 𝒪^σ`), with its isometry
  `vecOrderTop_eval_sub_eval`, and `bijOn_of_expansion` (any `M` for which the linear part of
  `F(x + M Z) - F(x)` is `Z`; such an `M` is `J^{-1}` and `J` is invertible, by
  `eq_jacobian_inv_of_coeff_single_expansion` and `isUnit_jacobian_of_coeff_single_expansion`).

Injectivity follows the source: the nonlinear part moves by strictly more than `v_min(Z - Z')`.
It is bounded monomial by monomial (`lt_orderTop_eval_nonlinear_sub`) instead of by a matrix of
divided differences, and the estimates carry `κ` directly instead of rescaling `Z = t^κ Y`.
For surjectivity the source invokes the system clause of `prony:lem:hensel`, whose existence
half (a formal construction evaluated by `prony:lem:support`) is not formalized. We use instead
the spherical completeness of `R((t^Γ))` (`exists_forall_le_orderTop_sub`, a coefficientwise
construction) and a fixed-point theorem for strict contractions of `t^κ 𝒪^σ`
(`exists_fixedPoint`, by Zorn's lemma on the balls `{W : v_min(W - Z) ≥ v_min(Z - Φ Z)}`), applied
to `Φ(Z) = c - (G(Z) - Z)`. As in the source, no Cauchy sequence or convergence argument occurs.

## `prony:cor:positive`

Here `R` is a linearly ordered field (the source's `ℝ`) and `R((t^Γ))` carries Mathlib's
lexicographic order (`toLex`), in which a series is positive iff its leading coefficient is.
* `toLex_pos_of_orderTop_sub_one_pos`: `1 + 𝔪` consists of positive elements.
* For every labelled realization with the properties `Surreal.PronyMain.Reconstruction` of
  `prony:thm:main`: every positive weight stays positive (`weight_pos`, by the source's ratio
  argument, and `weight_pos_iff`), and the node order is preserved (`node_lt_iff`).
* Reality: for a field embedding `f : R → S` (the source's `ℝ → ℂ`), every `n`-node
  realization over `S((t^Γ))` of the embedded perturbed moments is a permutation of the image of
  the reconstruction over `R((t^Γ))` (`eq_perm_mapCoefficients`), and the one in the strict
  balls is that image (`eq_mapCoefficients_of_strictBall`). This is the source's first proof
  (the construction takes place over the real coefficient field); the complex-conjugation
  argument is not needed.
* `positive`, `positive_threshold` (the source's normalization `κ > Θ`), `real_positive`,
  `real_positive_threshold` (the source's normalization) and `real_positive_complex` (with
  `ℝ → ℂ`) assemble these conclusions under the hypotheses of `prony:thm:main`.

## Pending

Nothing of `prony:prop:lattice` is pending. For `prony:cor:positive` the clause about actual
surreal inputs is pending: it needs the instantiation `prony:cor:actual` of `prony:thm:main` to
finite configurations in `No`, which is not formalized. The existence half of the system clause
of `prony:lem:hensel` itself remains pending; it is bypassed here, not proved.
-/

namespace Surreal.PronyLattice

open MvPolynomial Surreal.ChartIsometry

open scoped Matrix

noncomputable section

section Spherical

open _root_.HahnSeries

variable {Γ R σ : Type*} [LinearOrder Γ] [CommRing R]

/-- Spherical completeness of `R((t^Γ))`: a family of balls `{w : v(w - c_i) ≥ r_i}` that pairwise
intersect (`v(c_i - c_j) ≥ min(r_i, r_j)`) has a common point. It is built coefficientwise: below
`r_i` its coefficients are those of `c_i`. -/
theorem exists_forall_le_orderTop_sub {ι : Type*} (c : ι → R⟦Γ⟧) (r : ι → WithTop Γ)
    (h : ∀ i j, min (r i) (r j) ≤ (c i - c j).orderTop) :
    ∃ w : R⟦Γ⟧, ∀ i, r i ≤ (w - c i).orderTop := by
  classical
  let f : Γ → R := fun g => if hg : ∃ i, (g : WithTop Γ) < r i then (c hg.choose).coeff g else 0
  have hf : ∀ i (g : Γ), (g : WithTop Γ) < r i → f g = (c i).coeff g := by
    intro i g hgi
    have hex : ∃ i, (g : WithTop Γ) < r i := ⟨i, hgi⟩
    have hlt : (g : WithTop Γ) < (c hex.choose - c i).orderTop :=
      (lt_min hex.choose_spec hgi).trans_le (h _ _)
    have h0 := coeff_eq_zero_of_lt_orderTop hlt
    rw [_root_.HahnSeries.coeff_sub, sub_eq_zero] at h0
    simp only [f, dif_pos hex]
    exact h0
  have hwf : (Function.support f).IsPWO := by
    refine Set.IsWF.isPWO ?_
    rw [Set.isWF_iff_no_descending_seq]
    intro s hs hmem
    have hex : ∃ i, ((s 0 : Γ) : WithTop Γ) < r i := by
      by_contra hne
      exact hmem 0 (by simp only [f, dif_neg hne])
    obtain ⟨i, hi⟩ := hex
    have hsupp : ∀ n, s n ∈ (c i).support := fun n => by
      have hlt : ((s n : Γ) : WithTop Γ) < r i :=
        (WithTop.coe_le_coe.mpr (hs.antitone (Nat.zero_le n))).trans_lt hi
      have hn := hmem n
      rw [Function.mem_support, hf i _ hlt] at hn
      exact hn
    exact (Set.isWF_iff_no_descending_seq.mp (c i).isWF_support) s hs hsupp
  refine ⟨⟨f, hwf⟩, fun i => le_orderTop_iff_forall.mpr fun g hg => ?_⟩
  rw [_root_.HahnSeries.coeff_sub]
  exact sub_eq_zero.mpr (hf i g hg)

variable [Fintype σ]

theorem vecOrderTop_zero : vecOrderTop (0 : σ → R⟦Γ⟧) = ⊤ := by
  simp [vecOrderTop]

theorem vecOrderTop_eq_top_iff {a : σ → R⟦Γ⟧} : vecOrderTop a = ⊤ ↔ a = 0 := by
  simp [vecOrderTop, funext_iff]

theorem min_le_vecOrderTop_add (a b : σ → R⟦Γ⟧) :
    min (vecOrderTop a) (vecOrderTop b) ≤ vecOrderTop (a + b) :=
  le_vecOrderTop_iff.mpr fun j =>
    (min_le_min (vecOrderTop_le a j) (vecOrderTop_le b j)).trans min_orderTop_le_orderTop_add

theorem vecOrderTop_neg (a : σ → R⟦Γ⟧) : vecOrderTop (-a) = vecOrderTop a := by
  simp [vecOrderTop, orderTop_neg]

theorem vecOrderTop_sub_comm (a b : σ → R⟦Γ⟧) : vecOrderTop (a - b) = vecOrderTop (b - a) := by
  rw [← neg_sub, vecOrderTop_neg]

theorem coe_lt_vecOrderTop_iff {a : σ → R⟦Γ⟧} {g : Γ} :
    (g : WithTop Γ) < vecOrderTop a ↔ ∀ j, (g : WithTop Γ) < (a j).orderTop := by
  simp [vecOrderTop, Finset.lt_inf_iff (WithTop.coe_lt_top g)]

/-- Spherical completeness of `R((t^Γ))^σ` for the vector valuation. -/
theorem exists_forall_le_vecOrderTop_sub {ι : Type*} (c : ι → σ → R⟦Γ⟧) (r : ι → WithTop Γ)
    (h : ∀ i j, min (r i) (r j) ≤ vecOrderTop (c i - c j)) :
    ∃ W : σ → R⟦Γ⟧, ∀ i, r i ≤ vecOrderTop (W - c i) := by
  choose W hW using fun l => exists_forall_le_orderTop_sub (fun i => c i l) r
    fun i j => (h i j).trans (vecOrderTop_le (c i - c j) l)
  exact ⟨W, fun i => le_vecOrderTop_iff.mpr fun l => hW l i⟩

/-- A fixed-point theorem for strict contractions of `{Z : v_min(Z) ≥ κ}` over `R((t^Γ))^σ`: if
`Φ` maps this set into itself and `v_min(Φ Z - Φ W) > v_min(Z - W)` for `Z ≠ W` in it, then `Φ`
has a fixed point there. The proof applies Zorn's lemma to the balls
`B_Z = {W : v_min(W - Z) ≥ v_min(Z - Φ Z)}`, which are nested along the contraction; spherical
completeness bounds every chain, and a minimal ball is centred at a fixed point. -/
theorem exists_fixedPoint {κ : WithTop Γ} (Φ : (σ → R⟦Γ⟧) → σ → R⟦Γ⟧)
    (hmaps : ∀ Z, κ ≤ vecOrderTop Z → κ ≤ vecOrderTop (Φ Z))
    (hcontr : ∀ Z W, κ ≤ vecOrderTop Z → κ ≤ vecOrderTop W → Z ≠ W →
      vecOrderTop (Z - W) < vecOrderTop (Φ Z - Φ W)) :
    ∃ Z, κ ≤ vecOrderTop Z ∧ Φ Z = Z := by
  classical
  let ρ : (σ → R⟦Γ⟧) → WithTop Γ := fun Z => vecOrderTop (Z - Φ Z)
  let B : (σ → R⟦Γ⟧) → Set (σ → R⟦Γ⟧) := fun Z => {W | ρ Z ≤ vecOrderTop (W - Z)}
  have hself : ∀ Z, Z ∈ B Z := fun Z => by
    simp only [B, Set.mem_setOf_eq, sub_self, vecOrderTop_zero]
    exact le_top
  have hnonexp : ∀ Z W, κ ≤ vecOrderTop Z → κ ≤ vecOrderTop W →
      vecOrderTop (Z - W) ≤ vecOrderTop (Φ Z - Φ W) := by
    intro Z W hZ hW
    by_cases h : Z = W
    · subst h
      rw [sub_self, sub_self]
    · exact (hcontr Z W hZ hW h).le
  have hρ : ∀ Z, κ ≤ vecOrderTop Z → κ ≤ ρ Z := fun Z hZ => by
    have h := min_le_vecOrderTop_add Z (-Φ Z)
    rw [vecOrderTop_neg, ← sub_eq_add_neg] at h
    exact (le_min hZ (hmaps Z hZ)).trans h
  have hBD : ∀ Z, κ ≤ vecOrderTop Z → ∀ W ∈ B Z, κ ≤ vecOrderTop W := by
    intro Z hZ W hW
    have h := min_le_vecOrderTop_add (W - Z) Z
    rw [sub_add_cancel] at h
    exact (le_min ((hρ Z hZ).trans hW) hZ).trans h
  have hsub : ∀ Z, κ ≤ vecOrderTop Z → ∀ W ∈ B Z, B W ⊆ B Z := by
    intro Z hZ W hW U hU
    have hWD := hBD Z hZ W hW
    have hΦ : ρ Z ≤ vecOrderTop (Φ Z - Φ W) := by
      refine (hW.trans ?_).trans (hnonexp Z W hZ hWD)
      rw [vecOrderTop_sub_comm]
    have hρW : ρ Z ≤ ρ W := by
      have heq : W - Φ W = (W - Z) + ((Z - Φ Z) + (Φ Z - Φ W)) := by abel
      have h1 := min_le_vecOrderTop_add (Z - Φ Z) (Φ Z - Φ W)
      have h2 := min_le_vecOrderTop_add (W - Z) ((Z - Φ Z) + (Φ Z - Φ W))
      rw [← heq] at h2
      exact (le_min hW ((le_min le_rfl hΦ).trans h1)).trans h2
    have h3 := min_le_vecOrderTop_add (U - W) (W - Z)
    rw [sub_add_sub_cancel] at h3
    exact (le_min (hρW.trans hU) hW).trans h3
  obtain ⟨m, hm⟩ := zorn_superset {s | ∃ Z, κ ≤ vecOrderTop Z ∧ B Z = s} (by
    intro c hcS hchain
    rcases c.eq_empty_or_nonempty with rfl | ⟨s₀, hs₀⟩
    · refine ⟨B 0, ⟨0, ?_, rfl⟩, by simp⟩
      rw [vecOrderTop_zero]
      exact le_top
    have hc' : ∀ s ∈ c, ∃ Z, κ ≤ vecOrderTop Z ∧ B Z = s := fun s hs => hcS hs
    choose! ctr hctrD hctr using hc'
    have hmemc : ∀ s ∈ c, ctr s ∈ s := fun s hs => by
      have h := hself (ctr s)
      rwa [hctr s hs] at h
    have hcompat : ∀ s s' : c, min (ρ (ctr s)) (ρ (ctr s')) ≤ vecOrderTop (ctr s - ctr s') := by
      intro s s'
      rcases hchain.total s.2 s'.2 with h | h
      · have hmem : ctr s ∈ B (ctr s') := by
          rw [hctr s' s'.2]
          exact h (hmemc s s.2)
        exact (min_le_right _ _).trans hmem
      · have hmem : ctr s' ∈ B (ctr s) := by
          rw [hctr s s.2]
          exact h (hmemc s' s'.2)
        rw [vecOrderTop_sub_comm]
        exact (min_le_left _ _).trans hmem
    obtain ⟨W, hW⟩ := exists_forall_le_vecOrderTop_sub (fun s : c => ctr s)
      (fun s => ρ (ctr s)) hcompat
    have hWD : κ ≤ vecOrderTop W := hBD _ (hctrD s₀ hs₀) W (hW ⟨s₀, hs₀⟩)
    refine ⟨B W, ⟨W, hWD, rfl⟩, fun s hs => ?_⟩
    rw [← hctr s hs]
    exact hsub _ (hctrD s hs) W (hW ⟨s, hs⟩))
  obtain ⟨Z, hZD, rfl⟩ := hm.1
  refine ⟨Z, hZD, ?_⟩
  by_contra hne
  have hΦZ : Φ Z ∈ B Z := by
    show ρ Z ≤ vecOrderTop (Φ Z - Z)
    rw [vecOrderTop_sub_comm]
  have hge : B Z ⊆ B (Φ Z) := hm.2 ⟨Φ Z, hmaps Z hZD, rfl⟩ (hsub Z hZD (Φ Z) hΦZ)
  have hZmem : ρ (Φ Z) ≤ vecOrderTop (Z - Φ Z) := hge (hself Z)
  exact lt_irrefl _ ((hcontr Z (Φ Z) hZD (hmaps Z hZD) (Ne.symm hne)).trans_le hZmem)

end Spherical

/-! ### Differences of monomials -/

section Monomial

open _root_.HahnSeries

variable {Γ R σ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [CommRing R]

/-- A difference of two products of `m` factors: if every `a_j - b_j` has order at least `ρ` and
every `a_j, b_j` has order at least `κ`, then `v(∏ a_j - ∏ b_j) + κ ≥ ρ + m κ`. No sign condition
on `κ` is needed. -/
theorem coe_add_card_nsmul_le_orderTop_prod_map_sub (a b : σ → R⟦Γ⟧) {ρ κ : Γ}
    (ha : ∀ j, (κ : WithTop Γ) ≤ (a j).orderTop) (hb : ∀ j, (κ : WithTop Γ) ≤ (b j).orderTop)
    (hab : ∀ j, (ρ : WithTop Γ) ≤ (a j - b j).orderTop) (m : Multiset σ) :
    ((ρ + Multiset.card m • κ : Γ) : WithTop Γ) ≤
      ((m.map a).prod - (m.map b).prod).orderTop + κ := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons j m ih =>
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons,
      Multiset.card_cons]
    have key : a j * (m.map a).prod - b j * (m.map b).prod =
        a j * ((m.map a).prod - (m.map b).prod) + (a j - b j) * (m.map b).prod := by ring
    rw [key]
    have h1 : ((ρ + (Multiset.card m + 1) • κ : Γ) : WithTop Γ) ≤
        (a j * ((m.map a).prod - (m.map b).prod)).orderTop + κ :=
      calc ((ρ + (Multiset.card m + 1) • κ : Γ) : WithTop Γ)
          = (κ : WithTop Γ) + ((ρ + Multiset.card m • κ : Γ) : WithTop Γ) := by
            rw [← WithTop.coe_add, succ_nsmul]
            congr 1
            abel
        _ ≤ (a j).orderTop + (((m.map a).prod - (m.map b).prod).orderTop + κ) :=
            add_le_add (ha j) ih
        _ = ((a j).orderTop + ((m.map a).prod - (m.map b).prod).orderTop) + κ :=
            (add_assoc _ _ _).symm
        _ ≤ _ := add_le_add_left orderTop_add_le_mul _
    have h2 : ((ρ + (Multiset.card m + 1) • κ : Γ) : WithTop Γ) ≤
        ((a j - b j) * (m.map b).prod).orderTop + κ :=
      calc ((ρ + (Multiset.card m + 1) • κ : Γ) : WithTop Γ)
          = ((ρ : WithTop Γ) + ((Multiset.card m • κ : Γ) : WithTop Γ)) + κ := by
            rw [← WithTop.coe_add, ← WithTop.coe_add, succ_nsmul, add_assoc]
        _ ≤ ((a j - b j).orderTop + ((m.map b).prod).orderTop) + κ := by
            refine add_le_add_left (add_le_add (hab j) ?_) _
            rw [WithTop.coe_nsmul]
            exact card_nsmul_le_orderTop_prod_map b hb m
        _ ≤ _ := add_le_add_left orderTop_add_le_mul _
    calc ((ρ + (Multiset.card m + 1) • κ : Γ) : WithTop Γ)
        ≤ min ((a j * ((m.map a).prod - (m.map b).prod)).orderTop + κ)
          (((a j - b j) * (m.map b).prod).orderTop + κ) := le_min h1 h2
      _ = min (a j * ((m.map a).prod - (m.map b).prod)).orderTop
          ((a j - b j) * (m.map b).prod).orderTop + κ := min_add_add_right _ _ _
      _ ≤ _ := add_le_add_left min_orderTop_le_orderTop_add _

omit [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [CommRing R] in
/-- The total degree `|ν|` of an exponent vector is the cardinality of its multiset. -/
theorem card_toMultiset_eq_degree (ν : σ →₀ ℕ) : Multiset.card ν.toMultiset = ν.degree := by
  rw [Finsupp.card_toMultiset, Finsupp.degree_apply]
  rfl

/-- A substituted monomial `Z^ν` of total degree `|ν| ≥ 1` moves by at least
`ρ + (|ν| - 1) κ` between two vectors of order at least `κ` whose coordinates differ by order at
least `ρ`. -/
theorem coe_add_le_orderTop_prod_pow_sub [Fintype σ] (a b : σ → R⟦Γ⟧) {ρ κ : Γ}
    (ha : ∀ j, (κ : WithTop Γ) ≤ (a j).orderTop) (hb : ∀ j, (κ : WithTop Γ) ≤ (b j).orderTop)
    (hab : ∀ j, (ρ : WithTop Γ) ≤ (a j - b j).orderTop) (ν : σ →₀ ℕ) (hν : 1 ≤ ν.degree) :
    ((ρ + (ν.degree - 1) • κ : Γ) : WithTop Γ) ≤
      (∏ i, a i ^ ν i - ∏ i, b i ^ ν i).orderTop := by
  rw [prod_pow_eq_prod_map_toMultiset, prod_pow_eq_prod_map_toMultiset]
  have h := coe_add_card_nsmul_le_orderTop_prod_map_sub a b ha hb hab ν.toMultiset
  rw [card_toMultiset_eq_degree] at h
  rw [← WithTop.add_le_add_iff_right (WithTop.coe_ne_top (a := κ)), ← WithTop.coe_add]
  obtain ⟨k, hk⟩ : ∃ k, ν.degree = k + 1 := ⟨ν.degree - 1, by omega⟩
  rw [hk, succ_nsmul] at h
  rw [hk, Nat.add_sub_cancel, add_assoc]
  exact h

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
/-- A strict lower bound on the orders of finitely many Hahn series bounds their sum. -/
theorem coe_lt_orderTop_finset_sum {ι : Type*} (s : Finset ι) (f : ι → R⟦Γ⟧) {g : Γ}
    (h : ∀ i ∈ s, (g : WithTop Γ) < (f i).orderTop) : (g : WithTop Γ) < (∑ i ∈ s, f i).orderTop :=
  Finset.sum_induction f (fun x => (g : WithTop Γ) < x.orderTop)
    (fun _ _ hx hy => (lt_min hx hy).trans_le min_orderTop_le_orderTop_add)
    (by simp) h

end Monomial

/-! ### The finite coefficient criterion for a polynomial map with identity linear part -/

section Criterion

open _root_.HahnSeries

variable {Γ R σ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [CommRing R]
  [Fintype σ]

/-- The lattice `t^κ 𝒪^σ = {Z : v(Z_l) ≥ κ for every l}`. -/
def latticeBall (κ : Γ) : Set (σ → R⟦Γ⟧) :=
  {Z | ∀ l, (κ : WithTop Γ) ≤ (Z l).orderTop}

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
theorem mem_latticeBall_iff {κ : Γ} {Z : σ → R⟦Γ⟧} :
    Z ∈ latticeBall κ ↔ (κ : WithTop Γ) ≤ vecOrderTop Z :=
  le_vecOrderTop_iff.symm

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [Fintype σ] in
theorem zero_mem_latticeBall (κ : Γ) : (0 : σ → R⟦Γ⟧) ∈ latticeBall κ := fun l => by
  simp

/-- The finite coefficient criterion `prony:eq:latticecriterion` for a polynomial map
`G = (G_j)_j`: `v(C_{j,ν}) + (|ν| - 1) κ > 0` for every nonzero coefficient `C_{j,ν}` of `G_j`
with `|ν| ≥ 2`. -/
def LatticeCriterion (G : σ → MvPolynomial σ R⟦Γ⟧) (κ : Γ) : Prop :=
  ∀ j (ν : σ →₀ ℕ), 2 ≤ ν.degree → coeff ν (G j) ≠ 0 →
    0 < (coeff ν (G j)).order + (ν.degree - 1) • κ

variable {G : σ → MvPolynomial σ R⟦Γ⟧}

omit [Fintype σ] in
theorem eval_zero_eq_zero (h0 : ∀ j, coeff 0 (G j) = 0) (j : σ) : eval 0 (G j) = 0 := by
  rw [MvPolynomial.eval_zero]
  exact h0 j

variable [DecidableEq σ]

/-- The nonlinear part `G_j - Z_j` is a strict contraction on `t^κ 𝒪^σ`: if every coordinate of
`Z - Z'` has order at least `ρ`, then `v((G_j - Z_j)(Z) - (G_j - Z_j)(Z')) > ρ`. -/
theorem lt_orderTop_eval_nonlinear_sub (h0 : ∀ j, coeff 0 (G j) = 0)
    (h1 : ∀ j l, coeff (Finsupp.single l 1) (G j) = if l = j then 1 else 0) {κ : Γ}
    (hcrit : LatticeCriterion G κ) {Z Z' : σ → R⟦Γ⟧} (hZ : Z ∈ latticeBall κ)
    (hZ' : Z' ∈ latticeBall κ) {ρ : Γ} (hρ : ∀ l, (ρ : WithTop Γ) ≤ (Z l - Z' l).orderTop)
    (j : σ) : (ρ : WithTop Γ) < (eval Z (G j - X j) - eval Z' (G j - X j)).orderTop := by
  classical
  rw [eval_eq', eval_eq', ← Finset.sum_sub_distrib]
  refine coe_lt_orderTop_finset_sum _ _ fun ν hν => ?_
  rw [← mul_sub]
  have hc : coeff ν (G j - X j) ≠ 0 := mem_support_iff.mp hν
  have hν0 : ν ≠ 0 := by
    rintro rfl
    apply hc
    rw [MvPolynomial.coeff_sub, h0, coeff_zero_X, sub_zero]
  have hν1 : ∀ l, ν ≠ Finsupp.single l 1 := by
    rintro l rfl
    apply hc
    rw [MvPolynomial.coeff_sub, h1, coeff_X]
    by_cases hl : l = j
    · subst hl
      simp
    · rw [if_neg hl, if_neg fun h => hl (Finsupp.single_left_injective one_ne_zero h).symm,
        sub_zero]
  have hcG : coeff ν (G j - X j) = coeff ν (G j) := by
    rw [MvPolynomial.coeff_sub, coeff_X, if_neg fun h => hν1 j h.symm, sub_zero]
  have hdeg : 2 ≤ ν.degree := card_toMultiset_eq_degree ν ▸ two_le_card_toMultiset hν0 hν1
  rw [hcG] at hc ⊢
  have hcrit' := hcrit j ν hdeg hc
  calc (ρ : WithTop Γ)
      < (((coeff ν (G j)).order + (ν.degree - 1) • κ + ρ : Γ) : WithTop Γ) :=
        WithTop.coe_lt_coe.mpr (lt_add_of_pos_left ρ hcrit')
    _ = (coeff ν (G j)).orderTop + ((ρ + (ν.degree - 1) • κ : Γ) : WithTop Γ) := by
        rw [← order_eq_orderTop_of_ne_zero hc, ← WithTop.coe_add]
        congr 1
        abel
    _ ≤ (coeff ν (G j)).orderTop + (∏ i, Z i ^ ν i - ∏ i, Z' i ^ ν i).orderTop :=
        add_le_add_right (coe_add_le_orderTop_prod_pow_sub Z Z' hZ hZ' hρ ν (by omega)) _
    _ ≤ _ := orderTop_add_le_mul

/-- The nonlinear part maps `t^κ 𝒪^σ` into itself. -/
theorem le_orderTop_eval_nonlinear (h0 : ∀ j, coeff 0 (G j) = 0)
    (h1 : ∀ j l, coeff (Finsupp.single l 1) (G j) = if l = j then 1 else 0) {κ : Γ}
    (hcrit : LatticeCriterion G κ) {Z : σ → R⟦Γ⟧} (hZ : Z ∈ latticeBall κ) (j : σ) :
    (κ : WithTop Γ) ≤ (eval Z (G j - X j)).orderTop := by
  have h := lt_orderTop_eval_nonlinear_sub h0 h1 hcrit hZ (zero_mem_latticeBall κ)
    (ρ := κ) (fun l => by simpa using hZ l) j
  rw [map_sub (eval 0), eval_zero_eq_zero h0, eval_X, Pi.zero_apply, sub_zero, sub_zero] at h
  exact h.le

/-- The isometry in the proof of `prony:prop:lattice`: for a polynomial map `G` with zero constant
term, identity linear part and the criterion `prony:eq:latticecriterion`,
`v_min(G(Z) - G(Z')) = v_min(Z - Z')` for all `Z, Z' ∈ t^κ 𝒪^σ`. -/
theorem vecOrderTop_eval_sub_eval (h0 : ∀ j, coeff 0 (G j) = 0)
    (h1 : ∀ j l, coeff (Finsupp.single l 1) (G j) = if l = j then 1 else 0) {κ : Γ}
    (hcrit : LatticeCriterion G κ) {Z Z' : σ → R⟦Γ⟧} (hZ : Z ∈ latticeBall κ)
    (hZ' : Z' ∈ latticeBall κ) :
    vecOrderTop (fun j => eval Z (G j) - eval Z' (G j)) = vecOrderTop (Z - Z') := by
  by_cases hZZ : Z = Z'
  · subst hZZ
    simp only [sub_self]
    rfl
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Γ, (ρ : WithTop Γ) = vecOrderTop (Z - Z') :=
    WithTop.ne_top_iff_exists.mp fun h => hZZ (sub_eq_zero.mp (vecOrderTop_eq_top_iff.mp h))
  have hρl : ∀ l, (ρ : WithTop Γ) ≤ (Z l - Z' l).orderTop := fun l =>
    hρ ▸ vecOrderTop_le (Z - Z') l
  have hNL := lt_orderTop_eval_nonlinear_sub h0 h1 hcrit hZ hZ' hρl
  have hsplit : ∀ j, eval Z (G j) - eval Z' (G j) =
      (Z j - Z' j) + (eval Z (G j - X j) - eval Z' (G j - X j)) := fun j => by
    simp only [map_sub, eval_X]
    ring
  rw [← hρ]
  refine le_antisymm ?_ (le_vecOrderTop_iff.mpr fun j => ?_)
  · have : Nonempty σ := by
      obtain ⟨l, -⟩ := Function.ne_iff.mp hZZ
      exact ⟨l⟩
    obtain ⟨l, -, hl⟩ := Finset.exists_mem_eq_inf Finset.univ Finset.univ_nonempty
      fun l => (Z l - Z' l).orderTop
    have hl' : (Z l - Z' l).orderTop = ρ := hl.symm.trans hρ.symm
    calc vecOrderTop (fun j => eval Z (G j) - eval Z' (G j))
        ≤ (eval Z (G l) - eval Z' (G l)).orderTop := vecOrderTop_le _ l
      _ = ρ := by
        rw [hsplit l, orderTop_add_eq_left (by rw [hl']; exact hNL l), hl']
  · rw [hsplit j]
    exact (le_min (hρl j) (hNL j).le).trans min_orderTop_le_orderTop_add

/-- `prony:prop:lattice` for a polynomial map with zero constant term and identity linear part:
under `prony:eq:latticecriterion`, `G` is a bijection of `t^κ 𝒪^σ` onto itself. Injectivity is
the isometry `vecOrderTop_eval_sub_eval`; surjectivity is the fixed point of the strict
contraction `Z ↦ c - (G - Z)(Z)` (`exists_fixedPoint`). -/
theorem bijOn_latticeBall (h0 : ∀ j, coeff 0 (G j) = 0)
    (h1 : ∀ j l, coeff (Finsupp.single l 1) (G j) = if l = j then 1 else 0) {κ : Γ}
    (hcrit : LatticeCriterion G κ) :
    Set.BijOn (fun Z j => eval Z (G j)) (latticeBall κ) (latticeBall κ) := by
  refine ⟨fun Z hZ => ?_, fun Z hZ Z' hZ' h => ?_, fun c hc => ?_⟩
  · have h := vecOrderTop_eval_sub_eval h0 h1 hcrit hZ (zero_mem_latticeBall κ)
    simp only [eval_zero_eq_zero h0, sub_zero] at h
    rw [mem_latticeBall_iff] at hZ ⊢
    exact hZ.trans_eq h.symm
  · have h' := vecOrderTop_eval_sub_eval h0 h1 hcrit hZ hZ'
    have hj : ∀ j, eval Z (G j) = eval Z' (G j) := fun j => congrFun h j
    simp only [hj, sub_self] at h'
    exact sub_eq_zero.mp (vecOrderTop_eq_top_iff.mp (h'.symm.trans vecOrderTop_zero))
  have hmaps : ∀ Z : σ → R⟦Γ⟧, (κ : WithTop Γ) ≤ vecOrderTop Z →
      (κ : WithTop Γ) ≤ vecOrderTop (fun j => c j - eval Z (G j - X j)) := fun Z hZ =>
    le_vecOrderTop_iff.mpr fun j => (le_min (hc j) (le_orderTop_eval_nonlinear h0 h1 hcrit
      (mem_latticeBall_iff.mpr hZ) j)).trans min_orderTop_le_orderTop_sub
  have hcontr : ∀ Z W : σ → R⟦Γ⟧, (κ : WithTop Γ) ≤ vecOrderTop Z →
      (κ : WithTop Γ) ≤ vecOrderTop W → Z ≠ W →
      vecOrderTop (Z - W) < vecOrderTop ((fun j => c j - eval Z (G j - X j)) -
        fun j => c j - eval W (G j - X j)) := by
    intro Z W hZ hW hZW
    obtain ⟨ρ, hρ⟩ : ∃ ρ : Γ, (ρ : WithTop Γ) = vecOrderTop (Z - W) :=
      WithTop.ne_top_iff_exists.mp fun h => hZW (sub_eq_zero.mp (vecOrderTop_eq_top_iff.mp h))
    rw [← hρ, coe_lt_vecOrderTop_iff]
    intro j
    have h := lt_orderTop_eval_nonlinear_sub h0 h1 hcrit (mem_latticeBall_iff.mpr hZ)
      (mem_latticeBall_iff.mpr hW) (fun l => hρ ▸ vecOrderTop_le (Z - W) l) j
    rw [Pi.sub_apply, sub_sub_sub_cancel_left, ← neg_sub, orderTop_neg]
    exact h
  obtain ⟨Z, hZ, hfix⟩ := exists_fixedPoint _ hmaps hcontr
  refine ⟨Z, mem_latticeBall_iff.mpr hZ, funext fun j => ?_⟩
  have h := congrFun hfix j
  simp only [map_sub, eval_X] at h ⊢
  linear_combination -h

end Criterion

/-! ### The expansion `F(x + M Z) - F(x)` and the Jacobian -/

section Expansion

variable {K σ : Type*} [CommRing K]

/-- Evaluation after substitution: `(bind₁ g P)(Z) = P(g(Z))`. -/
theorem eval_bind₁_eq (Z : σ → K) (g : σ → MvPolynomial σ K) (P : MvPolynomial σ K) :
    eval Z (bind₁ g P) = eval (fun k => eval Z (g k)) P :=
  eval₂Hom_bind₁ _ _ _ _

/-- The constant coefficient of a substitution. -/
theorem constantCoeff_bind₁_eq (g : σ → MvPolynomial σ K) (P : MvPolynomial σ K) :
    constantCoeff (bind₁ g P) = eval (fun k => constantCoeff (g k)) P := by
  have h := eval_bind₁_eq 0 g P
  simp only [MvPolynomial.eval_zero] at h
  exact h

/-- The coefficient of `Z_l` is the constant term of `∂P/∂Z_l`. -/
theorem coeff_single_eq_constantCoeff_pderiv [DecidableEq σ] (P : MvPolynomial σ K) (l : σ) :
    coeff (Finsupp.single l 1) P = constantCoeff (pderiv l P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [coeff_monomial, pderiv_monomial, constantCoeff_monomial]
    by_cases hs : s = Finsupp.single l 1
    · subst hs
      simp
    · rw [if_neg hs]
      split_ifs with h
      · have hle : s ≤ Finsupp.single l 1 := tsub_eq_zero_iff_le.mp h
        have hsl : s l = 0 := by
          by_contra hne
          apply hs
          ext i
          have hi := hle i
          by_cases hil : i = l
          · subst hil
            simp only [Finsupp.single_eq_same] at hi ⊢
            omega
          · simp only [Finsupp.single_apply, Ne.symm hil, if_false] at hi ⊢
            omega
        simp [hsl]
      · rfl
  | add p q hp hq => rw [coeff_add, hp, hq, map_add, map_add]

/-- The chain rule for a polynomial substitution:
`∂(P ∘ g)/∂Z_l = ∑_k (∂P/∂Z_k ∘ g) ∂g_k/∂Z_l`. -/
theorem pderiv_bind₁_eq [Fintype σ] (g : σ → MvPolynomial σ K) (P : MvPolynomial σ K) (l : σ) :
    pderiv l (bind₁ g P) = ∑ k, bind₁ g (pderiv k P) * pderiv l (g k) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p n hp =>
    have hX : ∀ k, bind₁ g (pderiv k (X n : MvPolynomial σ K)) = if n = k then 1 else 0 :=
      fun k => by
        rw [pderiv_X, Pi.single_apply]
        split_ifs <;> simp
    have hsum : ∑ k, bind₁ g p * bind₁ g (pderiv k (X n : MvPolynomial σ K)) * pderiv l (g k) =
        bind₁ g p * pderiv l (g n) := by
      simp only [hX, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
    rw [map_mul, bind₁_X_right, Derivation.leibniz, hp]
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, bind₁_X_right, add_mul,
      Finset.sum_add_distrib, hsum, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm

variable [Fintype σ]

/-- The polynomial `G_j(Z) = F_j(x + M Z) - F_j(x)` in the variables `Z` (`prony:eq:Cexpand`, with
`M = J^{-1}` in the source). -/
def expansion (F : σ → MvPolynomial σ K) (x : σ → K) (M : Matrix σ σ K) (j : σ) :
    MvPolynomial σ K :=
  bind₁ (fun l => C (x l) + ∑ k, C (M l k) * X k) (F j) - C (eval x (F j))

/-- The Jacobian `J = dF_x`, `J_{jl} = ∂F_j/∂Z_l (x)`. -/
def jacobian (F : σ → MvPolynomial σ K) (x : σ → K) : Matrix σ σ K :=
  Matrix.of fun j l => eval x (pderiv l (F j))

/-- `prony:eq:Cexpand`: evaluating the expansion gives `F(x + M Z) - F(x)`. -/
theorem eval_expansion (F : σ → MvPolynomial σ K) (x : σ → K) (M : Matrix σ σ K)
    (Z : σ → K) (j : σ) :
    eval Z (expansion F x M j) = eval (x + M *ᵥ Z) (F j) - eval x (F j) := by
  have h : (fun l => eval Z (C (x l) + ∑ k, C (M l k) * X k)) = x + M *ᵥ Z := by
    funext l
    simp [Matrix.mulVec, dotProduct]
  rw [expansion, map_sub, eval_C, eval_bind₁_eq, h]

/-- The shift `Z ↦ x + M Z` has constant term `x`. -/
theorem constantCoeff_shift (x : σ → K) (M : Matrix σ σ K) :
    (fun l => constantCoeff (C (x l) + ∑ k, C (M l k) * X k : MvPolynomial σ K)) = x := by
  funext l
  simp

/-- The expansion has no constant term. -/
theorem coeff_zero_expansion (F : σ → MvPolynomial σ K) (x : σ → K) (M : Matrix σ σ K)
    (j : σ) : coeff 0 (expansion F x M j) = 0 := by
  change constantCoeff (expansion F x M j) = 0
  rw [expansion, map_sub, constantCoeff_bind₁_eq, constantCoeff_shift, constantCoeff_C,
    sub_self]

variable [DecidableEq σ]

/-- The linear part of the expansion is `J M`: the coefficient of `Z_l` in `G_j` is
`(J M)_{jl}`. -/
theorem coeff_single_expansion (F : σ → MvPolynomial σ K) (x : σ → K) (M : Matrix σ σ K)
    (j l : σ) : coeff (Finsupp.single l 1) (expansion F x M j) = (jacobian F x * M) j l := by
  have hpd : ∀ k, pderiv l (C (x k) + ∑ m, C (M k m) * X m : MvPolynomial σ K) = C (M k l) := by
    intro k
    simp [Pi.single_apply]
  rw [expansion, MvPolynomial.coeff_sub, coeff_C,
    if_neg (Finsupp.single_ne_zero.mpr one_ne_zero).symm, sub_zero,
    coeff_single_eq_constantCoeff_pderiv, pderiv_bind₁_eq, map_sum]
  simp only [map_mul, constantCoeff_bind₁_eq, constantCoeff_shift, hpd, constantCoeff_C,
    jacobian, Matrix.mul_apply, Matrix.of_apply]

/-- `prony:eq:Cexpand`: for `M = J^{-1}` the linear part of `F(x + J^{-1} Z) - F(x)` is `Z`. -/
theorem coeff_single_expansion_inv (F : σ → MvPolynomial σ K) (x : σ → K)
    (hJ : IsUnit (jacobian F x)) (j l : σ) :
    coeff (Finsupp.single l 1) (expansion F x (jacobian F x)⁻¹ j) = if l = j then 1 else 0 := by
  rw [coeff_single_expansion, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hJ),
    Matrix.one_apply]
  exact if_congr eq_comm rfl rfl

/-- If the linear part of `F(x + M Z) - F(x)` is `Z`, then `M` is a right inverse of the
Jacobian: `J M = 1`. -/
theorem jacobian_mul_eq_one_of_coeff_single_expansion (F : σ → MvPolynomial σ K) (x : σ → K)
    (M : Matrix σ σ K)
    (h1 : ∀ j l, coeff (Finsupp.single l 1) (expansion F x M j) = if l = j then 1 else 0) :
    jacobian F x * M = 1 := by
  ext j l
  rw [← coeff_single_expansion, h1, Matrix.one_apply]
  exact if_congr eq_comm rfl rfl

/-- If the linear part of `F(x + M Z) - F(x)` is `Z`, then the Jacobian `J` is invertible. -/
theorem isUnit_jacobian_of_coeff_single_expansion (F : σ → MvPolynomial σ K) (x : σ → K)
    (M : Matrix σ σ K)
    (h1 : ∀ j l, coeff (Finsupp.single l 1) (expansion F x M j) = if l = j then 1 else 0) :
    IsUnit (jacobian F x) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_det_of_right_inverse (jacobian_mul_eq_one_of_coeff_single_expansion F x M h1))

/-- If the linear part of `F(x + M Z) - F(x)` is `Z`, then `M = J^{-1}`: over a commutative ring
`J M = 1` forces `M J = 1`. -/
theorem eq_jacobian_inv_of_coeff_single_expansion (F : σ → MvPolynomial σ K) (x : σ → K)
    (M : Matrix σ σ K)
    (h1 : ∀ j l, coeff (Finsupp.single l 1) (expansion F x M j) = if l = j then 1 else 0) :
    M = (jacobian F x)⁻¹ :=
  (Matrix.inv_eq_right_inv (jacobian_mul_eq_one_of_coeff_single_expansion F x M h1)).symm

omit [Fintype σ] in
/-- A polynomial with zero constant term and linear part `Z_j` is `Z_j` plus the finite sum of
its monomials of total degree at least two. -/
theorem eq_X_add_sum_of_coeff (G : MvPolynomial σ K) (j : σ) (h0 : coeff 0 G = 0)
    (h1 : ∀ l, coeff (Finsupp.single l 1) G = if l = j then 1 else 0) :
    G = X j + ∑ ν ∈ G.support.filter (fun ν => 2 ≤ ν.degree), monomial ν (coeff ν G) := by
  ext ν
  rw [coeff_add, coeff_X, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases hν0 : ν = 0
  · subst hν0
    rw [h0, if_neg (Finsupp.single_ne_zero.mpr one_ne_zero), if_neg (by simp), add_zero]
  by_cases hν1 : ∃ l, ν = Finsupp.single l 1
  · obtain ⟨l, rfl⟩ := hν1
    have hnot : Finsupp.single l 1 ∉ G.support.filter (fun ν => 2 ≤ ν.degree) := by simp
    rw [if_neg hnot, add_zero, h1]
    by_cases hl : l = j
    · subst hl
      simp
    · rw [if_neg hl, if_neg fun h => hl (Finsupp.single_left_injective one_ne_zero h).symm]
  · have hν1' : ∀ l, ν ≠ Finsupp.single l 1 := not_exists.mp hν1
    have hdeg : 2 ≤ ν.degree := card_toMultiset_eq_degree ν ▸ two_le_card_toMultiset hν0 hν1'
    rw [if_neg fun h => hν1' j h.symm, zero_add]
    by_cases hs : ν ∈ G.support
    · rw [if_pos (Finset.mem_filter.mpr ⟨hs, hdeg⟩)]
    · rw [if_neg fun h => hs (Finset.mem_filter.mp h).1, notMem_support_iff.mp hs]

/-- `prony:eq:Cexpand`: `F(x + J^{-1} Z) - F(x) = Z + (∑_{|ν| ≥ 2} C_{j,ν} Z^ν)_j`, a finite
sum, with `C_{j,ν}` the coefficients of `expansion F x J^{-1}`. -/
theorem expansion_eq_X_add (F : σ → MvPolynomial σ K) (x : σ → K)
    (hJ : IsUnit (jacobian F x)) (j : σ) :
    expansion F x (jacobian F x)⁻¹ j = X j +
      ∑ ν ∈ (expansion F x (jacobian F x)⁻¹ j).support.filter (fun ν => 2 ≤ ν.degree),
        monomial ν (coeff ν (expansion F x (jacobian F x)⁻¹ j)) :=
  eq_X_add_sum_of_coeff _ j (coeff_zero_expansion F x _ j)
    fun l => coeff_single_expansion_inv F x hJ j l

end Expansion

/-! ### The finite coefficient criterion -/

section Lattice

open _root_.HahnSeries

variable {Γ R σ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [CommRing R]
  [Fintype σ] [DecidableEq σ]

/-- `prony:prop:lattice` for any matrix `M` for which the expansion `F(x + M Z) - F(x)` has linear
part `Z` (which forces `M = J^{-1}`, `eq_jacobian_inv_of_coeff_single_expansion`): under
`prony:eq:latticecriterion`, `F` maps `x + M t^κ 𝒪^σ` bijectively onto `F(x) + t^κ 𝒪^σ`. -/
theorem bijOn_of_expansion (F : σ → MvPolynomial σ R⟦Γ⟧) (x : σ → R⟦Γ⟧)
    (M : Matrix σ σ R⟦Γ⟧)
    (h1 : ∀ j l, coeff (Finsupp.single l 1) (expansion F x M j) = if l = j then 1 else 0)
    {κ : Γ} (hcrit : LatticeCriterion (expansion F x M) κ) :
    Set.BijOn (fun y j => eval y (F j)) ((fun Z => x + M *ᵥ Z) '' latticeBall κ)
      ((fun z => (fun j => eval x (F j)) + z) '' latticeBall κ) := by
  have hB := bijOn_latticeBall (coeff_zero_expansion F x M) h1 hcrit
  have hev : ∀ Z, (fun j => eval (x + M *ᵥ Z) (F j)) =
      (fun j => eval x (F j)) + fun j => eval Z (expansion F x M j) := fun Z => by
    funext j
    rw [Pi.add_apply, eval_expansion, add_sub_cancel]
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨Z, hZ, rfl⟩
    exact ⟨_, hB.mapsTo hZ, (hev Z).symm⟩
  · rintro _ ⟨Z, hZ, rfl⟩ _ ⟨Z', hZ', rfl⟩ h
    have h' : (fun j => eval Z (expansion F x M j)) = fun j => eval Z' (expansion F x M j) := by
      have h2 : (fun j => eval (x + M *ᵥ Z) (F j)) = fun j => eval (x + M *ᵥ Z') (F j) := h
      rw [hev, hev] at h2
      exact add_left_cancel h2
    rw [hB.injOn hZ hZ' h']
  · rintro _ ⟨c, hc, rfl⟩
    obtain ⟨Z, hZ, hZc⟩ := hB.surjOn hc
    refine ⟨x + M *ᵥ Z, ⟨Z, hZ, rfl⟩, ?_⟩
    change (fun j => eval (x + M *ᵥ Z) (F j)) = _
    rw [hev, ← hZc]

/-- **Finite coefficient criterion** (`prony:prop:lattice`). Let `F : K^σ → K^σ` be polynomial,
`K = R((t^Γ))`, let `x ∈ K^σ` with invertible Jacobian `J = dF_x`, and let `κ ∈ Γ` satisfy
`prony:eq:latticecriterion` for the coefficients `C_{j,ν}` (`|ν| ≥ 2`) of the expansion
`F(x + J^{-1} Z) - F(x) = Z + (∑ C_{j,ν} Z^ν)_j` (`prony:eq:Cexpand`, see `eval_expansion`,
`coeff_zero_expansion` and `coeff_single_expansion_inv`). Then `F` is a bijection from
`x + J^{-1} t^κ 𝒪^σ` onto `F(x) + t^κ 𝒪^σ`. -/
theorem lattice (F : σ → MvPolynomial σ R⟦Γ⟧) (x : σ → R⟦Γ⟧) (hJ : IsUnit (jacobian F x))
    {κ : Γ} (hcrit : LatticeCriterion (expansion F x (jacobian F x)⁻¹) κ) :
    Set.BijOn (fun y j => eval y (F j)) ((fun Z => x + (jacobian F x)⁻¹ *ᵥ Z) '' latticeBall κ)
      ((fun z => (fun j => eval x (F j)) + z) '' latticeBall κ) :=
  bijOn_of_expansion F x _ (coeff_single_expansion_inv F x hJ) hcrit

/-- `prony:eq:latticeimage`: `F(x + J^{-1} t^κ 𝒪^σ) = F(x) + t^κ 𝒪^σ`. -/
theorem lattice_image (F : σ → MvPolynomial σ R⟦Γ⟧) (x : σ → R⟦Γ⟧)
    (hJ : IsUnit (jacobian F x)) {κ : Γ}
    (hcrit : LatticeCriterion (expansion F x (jacobian F x)⁻¹) κ) :
    (fun y j => eval y (F j)) '' ((fun Z => x + (jacobian F x)⁻¹ *ᵥ Z) '' latticeBall κ) =
      (fun z => (fun j => eval x (F j)) + z) '' latticeBall κ :=
  (lattice F x hJ hcrit).image_eq

/-- The isometry behind `prony:prop:lattice`: for `Z, Z' ∈ t^κ 𝒪^σ`,
`v_min(F(x + J^{-1} Z) - F(x + J^{-1} Z')) = v_min(Z - Z')`. -/
theorem lattice_isometry (F : σ → MvPolynomial σ R⟦Γ⟧) (x : σ → R⟦Γ⟧)
    (hJ : IsUnit (jacobian F x)) {κ : Γ}
    (hcrit : LatticeCriterion (expansion F x (jacobian F x)⁻¹) κ) {Z Z' : σ → R⟦Γ⟧}
    (hZ : Z ∈ latticeBall κ) (hZ' : Z' ∈ latticeBall κ) :
    vecOrderTop (fun j => eval (x + (jacobian F x)⁻¹ *ᵥ Z) (F j) -
      eval (x + (jacobian F x)⁻¹ *ᵥ Z') (F j)) = vecOrderTop (Z - Z') := by
  have h := vecOrderTop_eval_sub_eval (coeff_zero_expansion F x _)
    (coeff_single_expansion_inv F x hJ) hcrit hZ hZ'
  simp only [eval_expansion, sub_sub_sub_cancel_right] at h
  exact h

end Lattice

/-! ### Real and positive data (`prony:cor:positive`) -/

section Positive

open _root_.HahnSeries Surreal.Prony Surreal.PronyBound Surreal.PronyRows Surreal.PronyMain

variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field R]
  [LinearOrder R] [IsStrictOrderedRing R] {n : ℕ}

omit [IsOrderedAddMonoid Γ] in
/-- `1 + 𝔪` consists of positive elements of `R((t^Γ))` (for the lexicographic order). -/
theorem toLex_pos_of_orderTop_sub_one_pos {y : R⟦Γ⟧} (hy : 0 < (y - 1).orderTop) :
    0 < toLex y := by
  have h1 : (1 : R⟦Γ⟧).orderTop < (y - 1).orderTop := by
    rw [orderTop_one]
    exact hy
  have hlc := leadingCoeff_add_eq_left h1
  rw [add_sub_cancel, leadingCoeff_one] at hlc
  exact leadingCoeff_pos_iff.mp (by rw [ofLex_toLex, hlc]; exact one_pos)

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [IsStrictOrderedRing R] in
/-- Two Hahn series with the same leading coefficient have the same sign. -/
theorem toLex_pos_iff_of_leadingCoeff_eq {x y : R⟦Γ⟧} (h : x.leadingCoeff = y.leadingCoeff) :
    0 < toLex x ↔ 0 < toLex y := by
  rw [← leadingCoeff_pos_iff, ← leadingCoeff_pos_iff, ofLex_toLex, ofLex_toLex, h]

variable {a w : Fin n → R⟦Γ⟧} {δ : Fin n → Γ} {mh : ℕ → R⟦Γ⟧} {κ : Γ} {â ŵ : Fin n → R⟦Γ⟧}

omit [IsStrictOrderedRing R] in
/-- `prony:cor:positive`, weights, in both directions: `ŵ_i` and `w_i` have the same leading
coefficient, hence the same sign. -/
theorem weight_pos_iff (hR : Reconstruction a w δ mh κ â ŵ) (i : Fin n) :
    0 < toLex (ŵ i) ↔ 0 < toLex (w i) :=
  toLex_pos_iff_of_leadingCoeff_eq (hR.weight_leading i).2.1

/-- `prony:cor:positive`, weights, by the source's argument: `ŵ_i = w_i (ŵ_i/w_i)` with
`ŵ_i/w_i ∈ 1 + 𝔪` positive. -/
theorem weight_pos (hR : Reconstruction a w δ mh κ â ŵ) {i : Fin n} (hi : 0 < toLex (w i)) :
    0 < toLex (ŵ i) := by
  have hw0 : w i ≠ 0 := fun h => by
    rw [h, toLex_zero] at hi
    exact lt_irrefl _ hi
  have hratio := toLex_pos_of_orderTop_sub_one_pos (hR.weight_leading i).2.2
  rw [← mul_div_cancel₀ (ŵ i) hw0, toLex_mul]
  exact mul_pos hi hratio

/-- `prony:cor:positive`, nodes: the ordering of the nodes is preserved, since
`(â_i - â_j)/(a_i - a_j) ∈ 1 + 𝔪` (`prony:eq:separation`). -/
theorem node_lt_iff (hR : Reconstruction a w δ mh κ â ŵ) (i j : Fin n) :
    toLex (â i) < toLex (â j) ↔ toLex (a i) < toLex (a j) := by
  by_cases hij : i = j
  · subst hij
    simp
  have e1 : toLex (â i) < toLex (â j) ↔ 0 < toLex (â j - â i) := by rw [toLex_sub, sub_pos]
  have e2 : toLex (a i) < toLex (a j) ↔ 0 < toLex (a j - a i) := by rw [toLex_sub, sub_pos]
  rw [e1, e2]
  exact toLex_pos_iff_of_leadingCoeff_eq (hR.separation j i (Ne.symm hij)).2.1

/-- `prony:cor:positive` over `R((t^Γ))`, `R` a linearly ordered field (for example `ℝ`): under
the hypotheses of `prony:thm:main`, the reconstruction lies in `R((t^Γ))`, every positive weight
stays positive and the order of the nodes is preserved. -/
theorem positive {ε : ℕ → R⟦Γ⟧} (ha0 : ∀ i, 0 ≤ (a i).orderTop)
    (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i) (hδ0 : ∀ i, 0 ≤ δ i)
    (hw : ∀ i, w i ≠ 0) (hε : ∀ r < 2 * n, (κ : WithTop Γ) ≤ (ε r).orderTop)
    (hκ : ∀ i, nodeLoss a w i + δ i < κ) :
    ∃ â ŵ : Fin n → R⟦Γ⟧, Reconstruction a w δ (moment a w + ε) κ â ŵ ∧
      (∀ i, 0 < toLex (w i) → 0 < toLex (ŵ i)) ∧
      ∀ i j, toLex (â i) < toLex (â j) ↔ toLex (a i) < toLex (a j) := by
  obtain ⟨â, ŵ, hR⟩ := exists_reconstruction ha0 hδ hδ0 hw hε hκ
  exact ⟨â, ŵ, hR, fun i hi => weight_pos hR hi, node_lt_iff hR⟩

/-- `prony:cor:positive` in the source's normalization: integral distinct nodes, nonzero weights,
`v(ε_k) ≥ κ` for `k < 2n` and `κ > Θ`, with `δ_i = max_{j ≠ i} v(a_i - a_j)`. -/
theorem positive_threshold [NeZero n] {ε : ℕ → R⟦Γ⟧} (ha0 : ∀ i, 0 ≤ (a i).orderTop)
    (ha : Function.Injective a) (hw : ∀ i, w i ≠ 0)
    (hε : ∀ r < 2 * n, (κ : WithTop Γ) ≤ (ε r).orderTop) (hκ : threshold a w < κ) :
    ∃ â ŵ : Fin n → R⟦Γ⟧, Reconstruction a w (sepMax a) (moment a w + ε) κ â ŵ ∧
      (∀ i, 0 < toLex (w i) → 0 < toLex (ŵ i)) ∧
      ∀ i j, toLex (â i) < toLex (â j) ↔ toLex (a i) < toLex (a j) := by
  obtain ⟨â, ŵ, hR⟩ := exists_reconstruction_sepMax ha0 ha hw hε hκ
  exact ⟨â, ŵ, hR, fun i hi => weight_pos hR hi, node_lt_iff hR⟩

end Positive

section Real

open _root_.HahnSeries Surreal.HahnSeries Surreal.Prony Surreal.PronyMain

variable {Γ R S : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field R]
  [Field S] {n : ℕ}

/-- An injective coefficient map preserves the order of a Hahn series. -/
theorem orderTop_mapCoefficients_eq (f : R →+* S) (x : R⟦Γ⟧) :
    (mapCoefficients f x).orderTop = x.orderTop := by
  refine le_antisymm (le_orderTop_iff_forall.mpr fun g hg => ?_) (orderTop_le_mapCoefficients f x)
  have h := coeff_eq_zero_of_lt_orderTop hg
  rw [coeff_mapCoefficients] at h
  exact (map_eq_zero_iff f f.injective).mp h

/-- A field embedding `f : R → S` induces an injective map `R((t^Γ)) → S((t^Γ))` (the field case
of `Surreal.FiniteBaseChange.mapCoefficients_injective`, restated here to keep the imports of
this file small). -/
theorem mapCoefficients_injective (f : R →+* S) :
    Function.Injective (mapCoefficients (Γ := Γ) f) := fun x y h => by
  ext g
  have h' := congrArg (fun z => z.coeff g) h
  simp only [coeff_mapCoefficients] at h'
  exact f.injective h'

theorem moment_mapCoefficients (f : R →+* S) (a w : Fin n → R⟦Γ⟧) (r : ℕ) :
    moment (mapCoefficients f ∘ a) (mapCoefficients f ∘ w) r =
      mapCoefficients f (moment a w r) := by
  simp [moment, map_sum, map_mul, map_pow]

variable {a w : Fin n → R⟦Γ⟧} {δ : Fin n → Γ} {mh : ℕ → R⟦Γ⟧} {κ : Γ} {â ŵ : Fin n → R⟦Γ⟧}

/-- `prony:cor:positive`, reality: if the data lie in `R((t^Γ))` and `f : R → S` is a field
embedding (for example `ℝ → ℂ`), every `n`-node realization over `S((t^Γ))` of the perturbed
moments, regular or not, is a permutation of the image of the reconstruction over `R((t^Γ))`;
in particular its nodes and weights are real. -/
theorem eq_perm_mapCoefficients (f : R →+* S) (hR : Reconstruction a w δ mh κ â ŵ)
    {b u : Fin n → S⟦Γ⟧} (hm : ∀ r < 2 * n, moment b u r = mapCoefficients f (mh r)) :
    ∃ τ : Equiv.Perm (Fin n),
      b = (mapCoefficients f ∘ â) ∘ τ ∧ u = (mapCoefficients f ∘ ŵ) ∘ τ :=
  exists_perm_of_moment_eq ((mapCoefficients_injective f).comp hR.injective)
    (fun i => (map_ne_zero_iff _ (mapCoefficients_injective f)).mpr (hR.weight_ne_zero i))
    fun r hr => by rw [moment_mapCoefficients, hR.realizes r hr, hm r hr]

/-- `prony:cor:positive`, reality of the labelled output: over `S((t^Γ))` the unique realization
with `v(b_i - a_i) > δ_i` is the image of the reconstruction over `R((t^Γ))`. -/
theorem eq_mapCoefficients_of_strictBall (f : R →+* S)
    (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i) (hR : Reconstruction a w δ mh κ â ŵ)
    {b u : Fin n → S⟦Γ⟧} (hm : ∀ r < 2 * n, moment b u r = mapCoefficients f (mh r))
    (hb : ∀ i, (δ i : WithTop Γ) < (b i - mapCoefficients f (a i)).orderTop) :
    b = mapCoefficients f ∘ â ∧ u = mapCoefficients f ∘ ŵ := by
  have hsub : ∀ x y : R⟦Γ⟧, (mapCoefficients f x - mapCoefficients f y).orderTop =
      (x - y).orderTop := fun x y => by
    rw [← map_sub, orderTop_mapCoefficients_eq]
  exact eq_of_strictBall (a := mapCoefficients f ∘ a)
    (fun i j hji => (hsub _ _).trans_le (hδ i j hji))
    ((mapCoefficients_injective f).comp hR.injective)
    (fun i => (map_ne_zero_iff _ (mapCoefficients_injective f)).mpr (hR.weight_ne_zero i))
    (fun i => (hR.strictBall i).trans_eq (hsub _ _).symm)
    (fun r hr => by rw [moment_mapCoefficients, hR.realizes r hr, hm r hr]) hb

end Real

section RealPositive

open _root_.HahnSeries Surreal.HahnSeries Surreal.Prony Surreal.PronyBound Surreal.PronyRows
  Surreal.PronyMain

variable {Γ R S : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field R]
  [LinearOrder R] [IsStrictOrderedRing R] [Field S] {n : ℕ}

/-- **Real and positive data** (`prony:cor:positive`). Let the data `a, w, ε` of `prony:thm:main`
lie in `R((t^Γ))`, `R` a linearly ordered field (the source's `ℝ`), and let `f : R → S` be a
field embedding (the source's `ℝ → ℂ`). Then the reconstruction `(â, ŵ)` over `R((t^Γ))` exists;
over `S((t^Γ))` every `n`-node realization of the embedded perturbed moments is a permutation
of the embedded `(â, ŵ)`, and the one in the strict balls is the embedded `(â, ŵ)` itself, so the
recovered nodes and weights are real; every positive weight stays positive; and the order of the
nodes is preserved. -/
theorem real_positive (f : R →+* S) {a w : Fin n → R⟦Γ⟧} {δ : Fin n → Γ} {ε : ℕ → R⟦Γ⟧}
    {κ : Γ} (ha0 : ∀ i, 0 ≤ (a i).orderTop) (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i)
    (hδ0 : ∀ i, 0 ≤ δ i) (hw : ∀ i, w i ≠ 0)
    (hε : ∀ r < 2 * n, (κ : WithTop Γ) ≤ (ε r).orderTop)
    (hκ : ∀ i, nodeLoss a w i + δ i < κ) :
    ∃ â ŵ : Fin n → R⟦Γ⟧, Reconstruction a w δ (moment a w + ε) κ â ŵ ∧
      (∀ b u : Fin n → S⟦Γ⟧,
        (∀ r < 2 * n, moment b u r = mapCoefficients f ((moment a w + ε) r)) →
        ∃ τ : Equiv.Perm (Fin n),
          b = (mapCoefficients f ∘ â) ∘ τ ∧ u = (mapCoefficients f ∘ ŵ) ∘ τ) ∧
      (∀ b u : Fin n → S⟦Γ⟧,
        (∀ r < 2 * n, moment b u r = mapCoefficients f ((moment a w + ε) r)) →
        (∀ i, (δ i : WithTop Γ) < (b i - mapCoefficients f (a i)).orderTop) →
        b = mapCoefficients f ∘ â ∧ u = mapCoefficients f ∘ ŵ) ∧
      (∀ i, 0 < toLex (w i) → 0 < toLex (ŵ i)) ∧
      ∀ i j, toLex (â i) < toLex (â j) ↔ toLex (a i) < toLex (a j) := by
  obtain ⟨â, ŵ, hR⟩ := exists_reconstruction ha0 hδ hδ0 hw hε hκ
  exact ⟨â, ŵ, hR, fun _ _ hm => eq_perm_mapCoefficients f hR hm,
    fun _ _ hm hb => eq_mapCoefficients_of_strictBall f hδ hR hm hb,
    fun i hi => weight_pos hR hi, node_lt_iff hR⟩

/-- **Real and positive data** (`prony:cor:positive`) in the source's normalization of
`prony:thm:main`: integral distinct nodes, nonzero weights, `v(ε_k) ≥ κ` for `k < 2n` and
`κ > Θ`, with `δ_i = max_{j ≠ i} v(a_i - a_j)`. The conclusions are those of `real_positive`. -/
theorem real_positive_threshold [NeZero n] (f : R →+* S) {a w : Fin n → R⟦Γ⟧} {ε : ℕ → R⟦Γ⟧}
    {κ : Γ} (ha0 : ∀ i, 0 ≤ (a i).orderTop) (ha : Function.Injective a) (hw : ∀ i, w i ≠ 0)
    (hε : ∀ r < 2 * n, (κ : WithTop Γ) ≤ (ε r).orderTop) (hκ : threshold a w < κ) :
    ∃ â ŵ : Fin n → R⟦Γ⟧, Reconstruction a w (sepMax a) (moment a w + ε) κ â ŵ ∧
      (∀ b u : Fin n → S⟦Γ⟧,
        (∀ r < 2 * n, moment b u r = mapCoefficients f ((moment a w + ε) r)) →
        ∃ τ : Equiv.Perm (Fin n),
          b = (mapCoefficients f ∘ â) ∘ τ ∧ u = (mapCoefficients f ∘ ŵ) ∘ τ) ∧
      (∀ b u : Fin n → S⟦Γ⟧,
        (∀ r < 2 * n, moment b u r = mapCoefficients f ((moment a w + ε) r)) →
        (∀ i, ((sepMax a i : Γ) : WithTop Γ) < (b i - mapCoefficients f (a i)).orderTop) →
        b = mapCoefficients f ∘ â ∧ u = mapCoefficients f ∘ ŵ) ∧
      (∀ i, 0 < toLex (w i) → 0 < toLex (ŵ i)) ∧
      ∀ i j, toLex (â i) < toLex (â j) ↔ toLex (a i) < toLex (a j) :=
  real_positive f ha0 (orderTop_sub_le_sepMax ha) (sepMax_nonneg a) hw hε
    ((threshold_lt_iff a w κ).mp hκ)

/-- `prony:cor:positive` for real Hahn data inside `ℂ((t^Γ))`. -/
theorem real_positive_complex {a w : Fin n → ℝ⟦Γ⟧} {δ : Fin n → Γ} {ε : ℕ → ℝ⟦Γ⟧} {κ : Γ}
    (ha0 : ∀ i, 0 ≤ (a i).orderTop) (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i)
    (hδ0 : ∀ i, 0 ≤ δ i) (hw : ∀ i, w i ≠ 0)
    (hε : ∀ r < 2 * n, (κ : WithTop Γ) ≤ (ε r).orderTop)
    (hκ : ∀ i, nodeLoss a w i + δ i < κ) :
    ∃ â ŵ : Fin n → ℝ⟦Γ⟧, Reconstruction a w δ (moment a w + ε) κ â ŵ ∧
      (∀ b u : Fin n → ℂ⟦Γ⟧,
        (∀ r < 2 * n, moment b u r = mapCoefficients Complex.ofRealHom ((moment a w + ε) r)) →
        ∃ τ : Equiv.Perm (Fin n), b = (mapCoefficients Complex.ofRealHom ∘ â) ∘ τ ∧
          u = (mapCoefficients Complex.ofRealHom ∘ ŵ) ∘ τ) ∧
      (∀ b u : Fin n → ℂ⟦Γ⟧,
        (∀ r < 2 * n, moment b u r = mapCoefficients Complex.ofRealHom ((moment a w + ε) r)) →
        (∀ i, (δ i : WithTop Γ) < (b i - mapCoefficients Complex.ofRealHom (a i)).orderTop) →
        b = mapCoefficients Complex.ofRealHom ∘ â ∧ u = mapCoefficients Complex.ofRealHom ∘ ŵ) ∧
      (∀ i, 0 < toLex (w i) → 0 < toLex (ŵ i)) ∧
      ∀ i j, toLex (â i) < toLex (â j) ↔ toLex (a i) < toLex (a j) :=
  real_positive Complex.ofRealHom ha0 hδ hδ0 hw hε hκ

end RealPositive

end

end Surreal.PronyLattice
