import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Surreal.Algebra.PronyHankel
import Surreal.HahnSeries.FiniteVisibility

/-!
# The exact strong moment criterion

This file formalizes `meas:lem:prony` and `meas:thm:momentcriterion` of
`docs/surreal/hahn-valued-measures-and-probability/article.tex`.

## `meas:lem:prony`

Over an arbitrary field `K` (the source uses `ℝ`) and for any `Ω ⊆ K`, a sequence `a` is a
finite exponential sum `a_n = ∑_{x ∈ F} c_x x^n` with `F ⊆ Ω` finite exactly when a monic
polynomial `r` with distinct roots, all in `Ω`, annihilates it under the forward shift,
`(r(E) a)_n = ∑_i r_i a_{n+i} = 0` (`prony_iff`). "Monic with distinct roots, all in `Ω`"
is read in its standard sense: `r` splits, `#roots r = deg r`, with simple roots in `Ω`. The
constant `r = 1` acts as the identity and so corresponds to the zero sequence
(`shiftApply_one`). The proof uses the linear functional
`L_a(p) = ∑_j p_j a_j` of `Surreal.Prony.momentLinear`: the recurrence says that `L_a` kills
the multiples of `r`, and then `L_a(p) = L_a(p mod r)` is computed by Lagrange interpolation at
the roots. After zero coefficients are removed the representation is unique
(`prony_unique`); the Vandermonde step is `eq_zero_of_powerSum_eq_zero`, which only needs the
first `|F|` power sums.

## `meas:thm:momentcriterion`

The ordinary real sample set `Ω` is modelled, as in `Surreal.FiniteVisibility`, by a
measurable space `X` with an injective position map `e : X → K`. Here `K` is the coefficient
field, which is `ℝ` in the source; it may be any field (ordered for the positivity statements).
The Hahn field `K⟦Γ⟧` plays the role of the source's `K_ℝ = ℝ((t^Γ))`, with `Γ` any linearly
ordered set of exponents (with a `0` for the probability statement, so that `1 ∈ K⟦Γ⟧`); no
group structure is used. For a strongly summable weight family `w` the moments are
`momentSeq w e n = ∑ˢ_x e(x)^n w_x`, the scalar integral of `meas:prop:integration`(ii).
For a strong Hahn measure on a countably separated space they are
`strongMoment hμ hX e n`, computed from its point weights
(`meas:thm:atomic`).

For `m : ℕ → K⟦Γ⟧` put `S_m = momentSupport m = ⋃_n supp m_n`. Condition (b) is
`HasFiniteRow m e γ`: the row `a_n(γ) = coeff_γ m_n` is `∑_{x ∈ F_γ} c_{γ,x} e(x)^n` with
`F_γ` finite; by `hasFiniteRow_iff_recurrence` this is equivalent to the simple-root
recurrence of `meas:lem:prony` with roots in `Ω = range e`. The coefficients `c_{γ,x}`,
extended by zero, do not depend on the representation (`rowCoeff`, `rowCoeff_eq`), and
`reassembled m e ha x = ∑_{γ ∈ S_m} c_{γ,x} t^γ` is the reassembled weight
`meas:eq:reassemble`, a Hahn series once `S_m` is well ordered (`ha`); its coefficients can be
read from any row representations (`coeff_reassembled_of_row`).

* (a) and (b) are equivalent to the existence of a signed strong Hahn measure with moments
  `m` (`exists_isStrongHahnMeasure_iff`); such a measure is unique on measurable sets
  (`eq_of_strongMoment_eq`), its point weights are the reassembled weights
  (`singleton_eq_reassembled`), and it is positive exactly when (c) holds
  (`nonneg_iff_reassembled`).
* The theorem itself, for `m_0 = 1`: a positive strong Hahn probability with moments `m`
  exists if and only if (a), (b) and (c) hold (`exists_isStrongHahnProbability_iff`), and it
  is unique on measurable sets by `eq_of_strongMoment_eq`, even among signed strong Hahn
  measures; `exists_isStrongHahnProbability_unique` states existence and uniqueness together.
* For `Ω ⊆ ℝ` with any countably separated σ-algebra the statement is
  `real_exists_isStrongHahnProbability_iff`; the relative Borel σ-algebra is one such
  (`isCountablySeparated_real_subtype`), and so is every σ-algebra containing the relative
  Borel sets, the source's hypothesis (`isCountablySeparated_real_subtype_of_le`).

The generic weight-level facts used are: every row of `momentSeq w e` is finite
(`hasFiniteRow_momentSeq`), `S_m` is the union of the supports of the weights
(`iUnion_support_eq_momentSupport`), the weights are determined by the moments
(`eq_of_momentSeq_eq`), and (a), (b) produce a strongly summable reassembled family with
moments `m` (`reassembledFamily`, `momentSeq_reassembledFamily`).

The source assumes that the σ-algebra on `Ω` also contains the relative Borel sets. Only
countable separation is used, so the theorem is stated for every countably separated
σ-algebra; the source's hypothesis implies it (`isCountablySeparated_real_subtype_of_le`).
Nothing in `meas:lem:prony` or `meas:thm:momentcriterion` is left pending. The unlabelled
remarks are not formalized: the remark after `meas:lem:prony` on generating functions,
including its repeated-root example `n b^{n-1}`, and the remark after
`meas:thm:momentcriterion` that compactness is not responsible for uniqueness.
-/

namespace Surreal.MomentCriterion

noncomputable section

section Prony

open Polynomial

variable {K : Type*} [Field K]

/-- Pairing a polynomial with a finite weighted configuration through its power sums:
`∑ c_i p(v_i) = ∑_j p_j ∑ c_i v_i^j`. -/
theorem sum_mul_eval_eq {ι : Type*} (s : Finset ι) (v c : ι → K) {p : K[X]} {N : ℕ}
    (hN : p.natDegree < N) :
    ∑ i ∈ s, c i * p.eval (v i) =
      ∑ j ∈ Finset.range N, p.coeff j * ∑ i ∈ s, c i * v i ^ j := by
  simp only [eval_eq_sum_range' hN, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-- The Vandermonde step of `meas:lem:prony`: weights at finitely many distinct nodes whose
first `|s|` power sums vanish are all zero. The Lagrange basis polynomial of a node, of degree
`|s| - 1`, isolates its weight. -/
theorem eq_zero_of_powerSum_eq_zero {ι : Type*} {s : Finset ι} {v : ι → K} (hv : Set.InjOn v s)
    {c : ι → K} (h : ∀ n < s.card, ∑ i ∈ s, c i * v i ^ n = 0) {i : ι} (hi : i ∈ s) :
    c i = 0 := by
  classical
  have hdeg : (Lagrange.basis s v i).natDegree < s.card := by
    rw [Lagrange.natDegree_basis hv hi]
    exact Nat.sub_lt (Finset.card_pos.mpr ⟨i, hi⟩) one_pos
  have h0 : ∑ j ∈ Finset.range s.card,
      (Lagrange.basis s v i).coeff j * ∑ k ∈ s, c k * v k ^ j = 0 :=
    Finset.sum_eq_zero fun j hj => by rw [h j (Finset.mem_range.mp hj), mul_zero]
  have h1 : ∑ k ∈ s, c k * (Lagrange.basis s v i).eval (v k) = c i := by
    rw [← Finset.add_sum_erase s _ hi, Lagrange.eval_basis_self hv hi, mul_one, add_eq_left]
    exact Finset.sum_eq_zero fun k hk => by
      rw [Lagrange.eval_basis_of_ne (Finset.mem_erase.mp hk).1.symm (Finset.mem_erase.mp hk).2,
        mul_zero]
  rw [← h1, sum_mul_eval_eq s v c hdeg, h0]

/-- `meas:lem:prony`, uniqueness, for nodes given by an injective map: two finite
representations with the same power sums have the same coefficients, once these are
extended by zero at missing nodes. -/
theorem indicator_eq_of_powerSum_eq {ι : Type*} {e : ι → K} (he : Function.Injective e)
    {F G : Finset ι} {c d : ι → K} (h : ∀ n, ∑ x ∈ F, c x * e x ^ n = ∑ x ∈ G, d x * e x ^ n) :
    (↑F : Set ι).indicator c = (↑G : Set ι).indicator d := by
  classical
  have hsub : ∀ (T F : Finset ι) (c : ι → K), F ⊆ T → ∀ n,
      ∑ x ∈ T, (↑F : Set ι).indicator c x * e x ^ n = ∑ x ∈ F, c x * e x ^ n := by
    intro T F c hFT n
    calc ∑ x ∈ T, (↑F : Set ι).indicator c x * e x ^ n
        = ∑ x ∈ F, (↑F : Set ι).indicator c x * e x ^ n := by
          refine (Finset.sum_subset hFT fun x _ hx => ?_).symm
          rw [Set.indicator_of_notMem (by simpa using hx), zero_mul]
      _ = ∑ x ∈ F, c x * e x ^ n :=
          Finset.sum_congr rfl fun x hx => by rw [Set.indicator_of_mem (by simpa using hx)]
  have hzero : ∀ n < (F ∪ G).card, ∑ x ∈ F ∪ G,
      ((↑F : Set ι).indicator c x - (↑G : Set ι).indicator d x) * e x ^ n = 0 := by
    intro n _
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [hsub _ F c Finset.subset_union_left n, hsub _ G d Finset.subset_union_right n, h,
      sub_self]
  funext x
  by_cases hx : x ∈ F ∪ G
  · exact sub_eq_zero.mp (eq_zero_of_powerSum_eq_zero he.injOn hzero hx)
  · rw [Finset.mem_union, not_or] at hx
    rw [Set.indicator_of_notMem (by simpa using hx.1),
      Set.indicator_of_notMem (by simpa using hx.2)]

/-- `meas:lem:prony`, uniqueness: after zero coefficients are removed, the representation
`a_n = ∑_{x ∈ F} c_x x^n` is unique, nodes and coefficients alike. -/
theorem prony_unique {F G : Finset K} {c d : K → K} (hc : ∀ x ∈ F, c x ≠ 0)
    (hd : ∀ x ∈ G, d x ≠ 0) (h : ∀ n, ∑ x ∈ F, c x * x ^ n = ∑ x ∈ G, d x * x ^ n) :
    F = G ∧ ∀ x ∈ F, c x = d x := by
  have hind := indicator_eq_of_powerSum_eq (e := id) Function.injective_id h
  have key : ∀ {F G : Finset K} {c d : K → K}, (∀ x ∈ F, c x ≠ 0) →
      (↑F : Set K).indicator c = (↑G : Set K).indicator d → ∀ x ∈ F, x ∈ G ∧ c x = d x := by
    intro F G c d hc hind x hx
    have h1 := congrFun hind x
    rw [Set.indicator_of_mem (Finset.mem_coe.mpr hx)] at h1
    have hxG : x ∈ G := by
      by_contra hxG
      rw [Set.indicator_of_notMem (by simpa using hxG)] at h1
      exact hc x hx h1
    rw [Set.indicator_of_mem (Finset.mem_coe.mpr hxG)] at h1
    exact ⟨hxG, h1⟩
  exact ⟨Finset.ext fun x => ⟨fun hx => (key hc hind x hx).1, fun hx => (key hd hind.symm x hx).1⟩,
    fun x hx => (key hc hind x hx).2⟩

/-- The forward-shift action of a polynomial on a sequence, `(r(E) a)_n = ∑_i r_i a_{n+i}`,
where `(E a)_n = a_{n+1}`. -/
def shiftApply (r : K[X]) (a : ℕ → K) (n : ℕ) : K :=
  ∑ i ∈ Finset.range (r.natDegree + 1), r.coeff i * a (n + i)

/-- The constant polynomial `r = 1` acts as the identity, so it annihilates exactly the zero
sequence, as allowed in `meas:lem:prony`(ii). -/
theorem shiftApply_one (a : ℕ → K) (n : ℕ) : shiftApply 1 a n = a n := by
  simp [shiftApply]

/-- The shifted recurrence is the moment functional `L_a` applied to `r X^n`. -/
theorem shiftApply_eq_momentLinear (r : K[X]) (a : ℕ → K) (n : ℕ) :
    shiftApply r a n = Prony.momentLinear a (r * X ^ n) := by
  rw [Prony.momentLinear_mul_X_pow a le_rfl n, shiftApply]
  exact Finset.sum_congr rfl fun i _ => by rw [add_comm]

/-- A finite exponential sum pairs with polynomials by evaluation at its nodes. -/
theorem momentLinear_eq_sum_eval {ι : Type*} {s : Finset ι} {v c : ι → K} {a : ℕ → K}
    (ha : ∀ n, a n = ∑ i ∈ s, c i * v i ^ n) (p : K[X]) :
    Prony.momentLinear a p = ∑ i ∈ s, c i * p.eval (v i) := by
  rw [Prony.momentLinear_eq_sum a p (Nat.lt_succ_self _),
    sum_mul_eval_eq s v c (Nat.lt_succ_self _)]
  simp only [ha]

/-- The moment functional reads off the moments: `L_a(X^n) = a_n`. -/
theorem momentLinear_X_pow (a : ℕ → K) (n : ℕ) : Prony.momentLinear a (X ^ n) = a n := by
  simpa using Prony.momentLinear_C_mul_X_pow a 1 n

/-- `meas:lem:prony`: a sequence is a finite signed exponential sum `a_n = ∑_{x ∈ F} c_x x^n`
with nodes in `Ω` exactly when a monic polynomial with distinct roots, all in `Ω`, annihilates
it under the forward shift. "Distinct roots" includes splitting: `#roots r = deg r`. The
constant polynomial `r = 1` is allowed and corresponds to the zero sequence. -/
theorem prony_iff (Ω : Set K) (a : ℕ → K) :
    (∃ (F : Finset K) (c : K → K), ↑F ⊆ Ω ∧ ∀ n, a n = ∑ x ∈ F, c x * x ^ n) ↔
      ∃ r : K[X], r.Monic ∧ Multiset.card r.roots = r.natDegree ∧ r.roots.Nodup ∧
        (∀ x ∈ r.roots, x ∈ Ω) ∧ ∀ n, shiftApply r a n = 0 := by
  classical
  constructor
  · rintro ⟨F, c, hFΩ, ha⟩
    have hroots : (∏ x ∈ F, (X - C x)).roots = F.val := roots_prod_X_sub_C F
    refine ⟨∏ x ∈ F, (X - C x), monic_prod_X_sub_C (fun x => x) F, ?_, ?_, ?_, fun n => ?_⟩
    · rw [hroots, natDegree_finsetProd_X_sub_C_eq_card]
      rfl
    · rw [hroots]
      exact F.nodup
    · rw [hroots]
      intro x hx
      exact hFΩ (Finset.mem_coe.mpr (Finset.mem_val.mp hx))
    · rw [shiftApply_eq_momentLinear, momentLinear_eq_sum_eval (v := fun x => x) ha]
      exact Finset.sum_eq_zero fun x hx => by
        rw [eval_mul, eval_prod, Finset.prod_eq_zero hx (by simp), zero_mul, mul_zero]
  · rintro ⟨r, hmonic, hcard, hnodup, hΩ, hann⟩
    set F := r.roots.toFinset with hF
    have hFcard : F.card = r.natDegree := by
      rw [hF, Multiset.toFinset_card_of_nodup hnodup, hcard]
    have hroot : ∀ x ∈ F, r.eval x = 0 := fun x hx =>
      ((mem_roots hmonic.ne_zero).mp (Multiset.mem_toFinset.mp hx)).eq_zero
    have hmul : ∀ q : K[X], Prony.momentLinear a (r * q) = 0 := by
      intro q
      induction q using Polynomial.induction_on' with
      | add p q hp hq => rw [mul_add, map_add, hp, hq, add_zero]
      | monomial k b =>
        rw [← C_mul_X_pow_eq_monomial, mul_left_comm, ← smul_eq_C_mul, map_smul,
          ← shiftApply_eq_momentLinear, hann, smul_zero]
    have key : ∀ p : K[X], Prony.momentLinear a p =
        ∑ x ∈ F, Prony.momentLinear a (Lagrange.basis F id x) * p.eval x := by
      intro p
      have hdeg : (p %ₘ r).degree < F.card := by
        rw [hFcard, ← degree_eq_natDegree hmonic.ne_zero]
        exact degree_modByMonic_lt p hmonic
      have hint := Lagrange.eq_interpolate (v := id) Function.injective_id.injOn hdeg
      conv_lhs => rw [← modByMonic_add_div p r]
      rw [map_add, hmul, add_zero, hint, Lagrange.interpolate_apply, map_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hev : (p %ₘ r).eval (id x) = p.eval x := by
        rw [id, modByMonic_eq_sub_mul_div p r, eval_sub, eval_mul, hroot x hx, zero_mul,
          sub_zero]
      rw [← smul_eq_C_mul, map_smul, smul_eq_mul, hev, mul_comm]
    refine ⟨F, fun x => Prony.momentLinear a (Lagrange.basis F id x),
      fun x hx => hΩ x (Multiset.mem_toFinset.mp hx), fun n => ?_⟩
    rw [← momentLinear_X_pow a n, key (X ^ n)]
    simp only [eval_pow, eval_X]

/-- Nodes given by an injective map `e : ι → K`: a representation over `ι` is the same as a
representation over `K` with nodes in `range e`. -/
theorem exists_finset_iff_of_injective {ι : Type*} {e : ι → K} (he : Function.Injective e)
    (a : ℕ → K) :
    (∃ (F : Finset ι) (c : ι → K), ∀ n, a n = ∑ x ∈ F, c x * e x ^ n) ↔
      ∃ (F : Finset K) (c : K → K), ↑F ⊆ Set.range e ∧ ∀ n, a n = ∑ y ∈ F, c y * y ^ n := by
  classical
  constructor
  · rintro ⟨F, c, ha⟩
    refine ⟨F.image e, Function.extend e c 0, fun y hy => ?_, fun n => ?_⟩
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
      exact ⟨x, rfl⟩
    · rw [ha n, Finset.sum_image he.injOn]
      exact Finset.sum_congr rfl fun x _ => by rw [he.extend_apply]
  · rintro ⟨F, c, hF, ha⟩
    refine ⟨F.preimage e he.injOn, fun x => c (e x), fun n => ?_⟩
    rw [ha n]
    exact (Finset.sum_preimage e F he.injOn (fun y => c y * y ^ n)
      fun y hy hy' => absurd (hF (Finset.mem_coe.mpr hy)) hy').symm

end Prony

section Rows

open _root_.HahnSeries Surreal.HahnSeries

variable {Γ K X : Type*} [LinearOrder Γ] [Field K]

/-- `S_m = ⋃_n supp m_n`, the union of the supports of the moments. -/
def momentSupport (m : ℕ → K⟦Γ⟧) : Set Γ :=
  ⋃ n, (m n).support

theorem mem_momentSupport {m : ℕ → K⟦Γ⟧} {γ : Γ} :
    γ ∈ momentSupport m ↔ ∃ n, (m n).coeff γ ≠ 0 := by
  simp [momentSupport]

theorem coeff_eq_zero_of_notMem_momentSupport {m : ℕ → K⟦Γ⟧} {γ : Γ}
    (hγ : γ ∉ momentSupport m) (n : ℕ) : (m n).coeff γ = 0 := by
  by_contra h
  exact hγ (mem_momentSupport.mpr ⟨n, h⟩)

/-- Condition (b) of `meas:thm:momentcriterion`, `meas:eq:rows`: the coefficient row
`a_n(γ) = coeff_γ m_n` is a finite signed combination `∑_{x ∈ F_γ} c_{γ,x} e(x)^n` of powers of
sample points. -/
def HasFiniteRow (m : ℕ → K⟦Γ⟧) (e : X → K) (γ : Γ) : Prop :=
  ∃ (F : Finset X) (c : X → K), ∀ n, (m n).coeff γ = ∑ x ∈ F, c x * e x ^ n

/-- The equivalent form of (b) in `meas:thm:momentcriterion`: a finite row is exactly a row
satisfying the simple-root recurrence of `meas:lem:prony` with roots in `Ω = range e`. -/
theorem hasFiniteRow_iff_recurrence {e : X → K} (he : Function.Injective e) (m : ℕ → K⟦Γ⟧)
    (γ : Γ) :
    HasFiniteRow m e γ ↔ ∃ r : Polynomial K, r.Monic ∧ Multiset.card r.roots = r.natDegree ∧
      r.roots.Nodup ∧ (∀ y ∈ r.roots, y ∈ Set.range e) ∧
        ∀ n, shiftApply r (fun n => (m n).coeff γ) n = 0 :=
  (exists_finset_iff_of_injective he fun n => (m n).coeff γ).trans (prony_iff _ _)

open Classical in
/-- The coefficients `c_{γ,x}` of `meas:eq:rows`, extended by zero at missing nodes, taken from
a chosen representation (and zero if the row has none). For injective `e` they do not depend on
the representation (`rowCoeff_eq`). -/
def rowCoeff (m : ℕ → K⟦Γ⟧) (e : X → K) (γ : Γ) : X → K :=
  if h : HasFiniteRow m e γ then (↑h.choose : Set X).indicator h.choose_spec.choose else 0

/-- The chosen coefficients represent the row and vanish off a finite set. -/
theorem exists_rowCoeff {m : ℕ → K⟦Γ⟧} {e : X → K} {γ : Γ} (h : HasFiniteRow m e γ) :
    ∃ F : Finset X, (∀ x, rowCoeff m e γ x ≠ 0 → x ∈ F) ∧
      ∀ n, (m n).coeff γ = ∑ x ∈ F, rowCoeff m e γ x * e x ^ n := by
  refine ⟨h.choose, fun x hx => ?_, fun n => ?_⟩
  · rw [rowCoeff, dif_pos h] at hx
    exact Set.mem_of_indicator_ne_zero hx
  · rw [rowCoeff, dif_pos h, h.choose_spec.choose_spec n]
    exact Finset.sum_congr rfl fun x hx => by
      rw [Set.indicator_of_mem (Finset.mem_coe.mpr hx)]

/-- `meas:lem:prony`, uniqueness, at one exponent: any representation of the row gives the
coefficients `c_{γ,x}`, extended by zero. -/
theorem rowCoeff_eq {m : ℕ → K⟦Γ⟧} {e : X → K} (he : Function.Injective e) {γ : Γ}
    {F : Finset X} {c : X → K} (hrow : ∀ n, (m n).coeff γ = ∑ x ∈ F, c x * e x ^ n) :
    rowCoeff m e γ = (↑F : Set X).indicator c := by
  have h : HasFiniteRow m e γ := ⟨F, c, hrow⟩
  rw [rowCoeff, dif_pos h]
  exact indicator_eq_of_powerSum_eq he fun n => (h.choose_spec.choose_spec n).symm.trans (hrow n)

/-- `meas:eq:reassemble`: the reassembled weight `w_x = ∑_{γ ∈ S_m} c_{γ,x} t^γ`. It is a
Hahn series because `S_m` is well ordered, condition (a). -/
def reassembled (m : ℕ → K⟦Γ⟧) (e : X → K) (ha : (momentSupport m).IsWF) (x : X) : K⟦Γ⟧ where
  coeff := (momentSupport m).indicator fun γ => rowCoeff m e γ x
  isPWO_support' := ha.isPWO.mono Set.support_indicator_subset

theorem coeff_reassembled (m : ℕ → K⟦Γ⟧) (e : X → K) (ha : (momentSupport m).IsWF) (x : X)
    (γ : Γ) :
    (reassembled m e ha x).coeff γ = (momentSupport m).indicator (fun γ => rowCoeff m e γ x) γ :=
  rfl

/-- The reassembled weights do not depend on the chosen row representations: at `γ ∈ S_m`
their coefficient is `c_{γ,x}` from any representation, with `c_{γ,x} = 0` at missing nodes. -/
theorem coeff_reassembled_of_row {m : ℕ → K⟦Γ⟧} {e : X → K} (he : Function.Injective e)
    (ha : (momentSupport m).IsWF) {γ : Γ} (hγ : γ ∈ momentSupport m) {F : Finset X}
    {c : X → K} (hrow : ∀ n, (m n).coeff γ = ∑ x ∈ F, c x * e x ^ n) (x : X) :
    (reassembled m e ha x).coeff γ = (↑F : Set X).indicator c x := by
  rw [coeff_reassembled, Set.indicator_of_mem hγ, rowCoeff_eq he hrow]

end Rows

section Weights

open _root_.HahnSeries Surreal.HahnSeries

variable {Γ K X : Type*} [LinearOrder Γ] [Field K]

/-- The power moments `∫ e(x)^n dμ = ∑ˢ_x e(x)^n w_x` of the atomic measure with strongly
summable weights `w` (`meas:prop:integration`(ii)). -/
def momentSeq (w : SummableFamily Γ K X) (e : X → K) (n : ℕ) : K⟦Γ⟧ :=
  atomicIntegral w fun x => e x ^ n

/-- Each coefficient of a moment is a finite sum over any finite set containing the points
of nonzero weight coefficient. -/
theorem coeff_momentSeq (w : SummableFamily Γ K X) (e : X → K) {γ : Γ} {T : Finset X}
    (hT : ∀ x, (w x).coeff γ ≠ 0 → x ∈ T) (n : ℕ) :
    (momentSeq w e n).coeff γ = ∑ x ∈ T, (w x).coeff γ * e x ^ n := by
  have hsub : (Function.support fun x => e x ^ n * (w x).coeff γ) ⊆ ↑T := fun x hx =>
    Finset.mem_coe.mpr (hT x (right_ne_zero_of_mul (Function.mem_support.mp hx)))
  rw [momentSeq, coeff_atomicIntegral, finsum_eq_sum_of_support_subset _ hsub]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

theorem coeff_momentSeq_eq_sum_support (w : SummableFamily Γ K X) (e : X → K) (γ : Γ) (n : ℕ) :
    (momentSeq w e n).coeff γ = ∑ x ∈ (w.coeff γ).support, (w x).coeff γ * e x ^ n :=
  coeff_momentSeq w e (fun x hx => by simpa using hx) n

/-- Condition (b) is necessary: every row of an atomic moment sequence is finite. -/
theorem hasFiniteRow_momentSeq (w : SummableFamily Γ K X) (e : X → K) (γ : Γ) :
    HasFiniteRow (momentSeq w e) e γ :=
  ⟨(w.coeff γ).support, fun x => (w x).coeff γ, coeff_momentSeq_eq_sum_support w e γ⟩

/-- `S_m ⊆ S_w`: every exponent of a moment is an exponent of some weight. -/
theorem momentSupport_momentSeq_subset (w : SummableFamily Γ K X) (e : X → K) :
    momentSupport (momentSeq w e) ⊆ ⋃ x, (w x).support := by
  intro γ hγ
  obtain ⟨n, hn⟩ := mem_momentSupport.mp hγ
  rw [coeff_momentSeq_eq_sum_support] at hn
  obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  exact Set.mem_iUnion.mpr ⟨x, (mem_support _ _).mpr (left_ne_zero_of_mul hx)⟩

/-- Condition (a) is necessary: `S_m` is well ordered. -/
theorem isWF_momentSupport_momentSeq (w : SummableFamily Γ K X) (e : X → K) :
    (momentSupport (momentSeq w e)).IsWF :=
  w.isPWO_iUnion_support.isWF.mono (momentSupport_momentSeq_subset w e)

/-- The coefficient of a weight at `γ` is read off from any representation of the row of the
moments at `γ`: the Vandermonde argument of `meas:lem:prony`. -/
theorem coeff_eq_indicator {e : X → K} (he : Function.Injective e) {w : SummableFamily Γ K X}
    {m : ℕ → K⟦Γ⟧} (hw : ∀ n, momentSeq w e n = m n) {γ : Γ} {F : Finset X} {c : X → K}
    (hrow : ∀ n, (m n).coeff γ = ∑ x ∈ F, c x * e x ^ n) (x : X) :
    (w x).coeff γ = (↑F : Set X).indicator c x := by
  have h := indicator_eq_of_powerSum_eq he (F := (w.coeff γ).support)
    (c := fun y => (w y).coeff γ) (G := F) (d := c) fun n => by
      rw [← coeff_momentSeq_eq_sum_support w e γ n, hw, hrow]
  rw [← congrFun h x]
  by_cases hx : (w x).coeff γ = 0
  · rw [hx, Set.indicator_of_notMem (by simpa using hx)]
  · rw [Set.indicator_of_mem (by simpa using hx)]

/-- `S_w = S_m`, as in the proof of `meas:thm:momentcriterion`: at an exponent of `S_w` the
coefficient measure is a nonzero finite point measure, so not all of its moments vanish. -/
theorem iUnion_support_eq_momentSupport {e : X → K} (he : Function.Injective e)
    (w : SummableFamily Γ K X) : ⋃ x, (w x).support = momentSupport (momentSeq w e) := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun x γ hγ => ?_)
    (momentSupport_momentSeq_subset w e)
  by_contra hγm
  have h0 := coeff_eq_indicator he (fun n => rfl) (F := ∅) (c := 0)
    (fun n => by rw [Finset.sum_empty, coeff_eq_zero_of_notMem_momentSupport hγm n]) x
  exact (mem_support _ _).mp hγ (by simpa using h0)

/-- Uniqueness in `meas:thm:momentcriterion`: for injective positions, strongly summable
weights are determined by their moments. -/
theorem eq_of_momentSeq_eq {e : X → K} (he : Function.Injective e) {w w' : SummableFamily Γ K X}
    (h : ∀ n, momentSeq w e n = momentSeq w' e n) : w = w' := by
  refine SummableFamily.ext fun x => ?_
  ext γ
  rw [coeff_eq_indicator he (fun n => rfl) (coeff_momentSeq_eq_sum_support w e γ) x,
    coeff_eq_indicator he (fun n => (h n).symm) (coeff_momentSeq_eq_sum_support w e γ) x]

/-- The weights of an atomic moment sequence are the reassembled weights of `meas:eq:reassemble`
of its moments. -/
theorem eq_reassembled {e : X → K} (he : Function.Injective e) {w : SummableFamily Γ K X}
    {m : ℕ → K⟦Γ⟧} (hw : ∀ n, momentSeq w e n = m n) (ha : (momentSupport m).IsWF) (x : X) :
    w x = reassembled m e ha x := by
  ext γ
  rw [coeff_reassembled]
  by_cases hγ : γ ∈ momentSupport m
  · rw [Set.indicator_of_mem hγ]
    have hrow : ∀ n, (m n).coeff γ = ∑ y ∈ (w.coeff γ).support, (w y).coeff γ * e y ^ n :=
      fun n => by rw [← hw n, coeff_momentSeq_eq_sum_support]
    rw [rowCoeff_eq he hrow, coeff_eq_indicator he hw hrow x]
  · rw [Set.indicator_of_notMem hγ, coeff_eq_indicator he hw (F := ∅) (c := 0)
      (fun n => by rw [Finset.sum_empty, coeff_eq_zero_of_notMem_momentSupport hγ n]) x]
    simp

/-- Conditions (a) and (b) make the reassembled weights a strongly summable family: its
supports lie in `S_m`, and at each exponent only the finitely many nodes of the row
contribute. -/
def reassembledFamily (m : ℕ → K⟦Γ⟧) (e : X → K) (ha : (momentSupport m).IsWF)
    (hb : ∀ γ ∈ momentSupport m, HasFiniteRow m e γ) : SummableFamily Γ K X where
  toFun := reassembled m e ha
  isPWO_iUnion_support' :=
    ha.isPWO.mono (Set.iUnion_subset fun _ => Set.support_indicator_subset)
  finite_co_support' γ := by
    by_cases hγ : γ ∈ momentSupport m
    · obtain ⟨F, hF, -⟩ := exists_rowCoeff (hb γ hγ)
      refine F.finite_toSet.subset fun x hx => hF x ?_
      simpa [coeff_reassembled, Set.indicator_of_mem hγ] using hx
    · simp [coeff_reassembled, Set.indicator_of_notMem hγ]

theorem reassembledFamily_apply (m : ℕ → K⟦Γ⟧) (e : X → K) (ha : (momentSupport m).IsWF)
    (hb : ∀ γ ∈ momentSupport m, HasFiniteRow m e γ) (x : X) :
    reassembledFamily m e ha hb x = reassembled m e ha x :=
  rfl

/-- The reassembled family has the prescribed moments, coefficientwise by `meas:eq:rows`. -/
theorem momentSeq_reassembledFamily (m : ℕ → K⟦Γ⟧) (e : X → K) (ha : (momentSupport m).IsWF)
    (hb : ∀ γ ∈ momentSupport m, HasFiniteRow m e γ) (n : ℕ) :
    momentSeq (reassembledFamily m e ha hb) e n = m n := by
  ext γ
  by_cases hγ : γ ∈ momentSupport m
  · obtain ⟨F, hF, hrep⟩ := exists_rowCoeff (hb γ hγ)
    have hT : ∀ x, (reassembledFamily m e ha hb x).coeff γ ≠ 0 → x ∈ F := fun x hx => hF x (by
      rwa [reassembledFamily_apply, coeff_reassembled, Set.indicator_of_mem hγ] at hx)
    rw [coeff_momentSeq _ e hT n, hrep n]
    exact Finset.sum_congr rfl fun x _ => by
      rw [reassembledFamily_apply, coeff_reassembled, Set.indicator_of_mem hγ]
  · have hT : ∀ x, (reassembledFamily m e ha hb x).coeff γ ≠ 0 → x ∈ (∅ : Finset X) :=
      fun x hx => by
        rw [reassembledFamily_apply, coeff_reassembled, Set.indicator_of_notMem hγ] at hx
        exact absurd rfl hx
    rw [coeff_momentSeq _ e hT n, Finset.sum_empty,
      coeff_eq_zero_of_notMem_momentSupport hγ n]

end Weights

section Measure

open _root_.HahnSeries Surreal.HahnSeries

variable {Γ K X : Type*} [LinearOrder Γ] [Field K] [MeasurableSpace X] {μ ν : Set X → K⟦Γ⟧}
  {e : X → K}

/-- `meas:eq:momentrep`: the power moments `∫ x^n dμ = ∑ˢ_x e(x)^n μ({x})` of a strong Hahn
measure on a countably separated sample set, computed from its point weights
(`meas:thm:atomic`, `meas:prop:integration`(ii)). -/
def strongMoment (hμ : IsStrongHahnMeasure μ) (hX : IsCountablySeparated X) (e : X → K)
    (n : ℕ) : K⟦Γ⟧ :=
  momentSeq (strongWeights hμ hX) e n

/-- The point weights of the atomic measure of a strongly summable family are the family. -/
theorem strongWeights_atomicMeasure (hX : IsCountablySeparated X) (w : SummableFamily Γ K X) :
    strongWeights (isStrongHahnMeasure_atomicMeasure w) hX = w :=
  SummableFamily.ext fun x => by rw [strongWeights_apply, atomicMeasure_singleton]

/-- `meas:thm:momentcriterion`, signed form: conditions (a) and (b) alone are equivalent to the
existence of a signed strong Hahn measure with moments `m`. No injectivity of the positions is
needed here. -/
theorem exists_isStrongHahnMeasure_iff (hX : IsCountablySeparated X) (e : X → K)
    (m : ℕ → K⟦Γ⟧) :
    (∃ μ : Set X → K⟦Γ⟧, ∃ hμ : IsStrongHahnMeasure μ, ∀ n, strongMoment hμ hX e n = m n) ↔
      (momentSupport m).IsWF ∧ ∀ γ ∈ momentSupport m, HasFiniteRow m e γ := by
  constructor
  · rintro ⟨μ, hμ, hm⟩
    obtain rfl : momentSeq (strongWeights hμ hX) e = m := funext hm
    exact ⟨isWF_momentSupport_momentSeq _ e, fun γ _ => hasFiniteRow_momentSeq _ e γ⟩
  · rintro ⟨ha, hb⟩
    refine ⟨atomicMeasure (reassembledFamily m e ha hb),
      isStrongHahnMeasure_atomicMeasure _, fun n => ?_⟩
    rw [strongMoment, strongWeights_atomicMeasure, momentSeq_reassembledFamily]

/-- `meas:thm:momentcriterion`, uniqueness: two signed strong Hahn measures on a countably
separated sample set with the same moments agree on every event. No positivity and no
compactness is used. -/
theorem eq_of_strongMoment_eq (hX : IsCountablySeparated X) (he : Function.Injective e)
    (hμ : IsStrongHahnMeasure μ) (hν : IsStrongHahnMeasure ν)
    (h : ∀ n, strongMoment hμ hX e n = strongMoment hν hX e n) {A : Set X}
    (hA : MeasurableSet A) : μ A = ν A := by
  rw [eq_atomicMeasure_strongWeights hμ hX hA, eq_atomicMeasure_strongWeights hν hX hA,
    eq_of_momentSeq_eq (w := strongWeights hμ hX) (w' := strongWeights hν hX) he h]

/-- `meas:thm:momentcriterion`: the singleton weights of a signed strong Hahn measure with
moments `m` are the reassembled weights `meas:eq:reassemble`. -/
theorem singleton_eq_reassembled (hX : IsCountablySeparated X) (he : Function.Injective e)
    (hμ : IsStrongHahnMeasure μ) {m : ℕ → K⟦Γ⟧} (hm : ∀ n, strongMoment hμ hX e n = m n)
    (ha : (momentSupport m).IsWF) (x : X) : μ {x} = reassembled m e ha x := by
  rw [← strongWeights_apply hμ hX x]
  exact eq_reassembled he (w := strongWeights hμ hX) hm ha x

/-- `meas:thm:momentcriterion`: condition (c) is exactly the positivity of the signed strong
Hahn measure with moments `m`. -/
theorem nonneg_iff_reassembled [LinearOrder K] [IsStrictOrderedRing K]
    (hX : IsCountablySeparated X) (he : Function.Injective e) (hμ : IsStrongHahnMeasure μ)
    {m : ℕ → K⟦Γ⟧} (hm : ∀ n, strongMoment hμ hX e n = m n) (ha : (momentSupport m).IsWF) :
    (∀ A, MeasurableSet A → 0 ≤ toLex (μ A)) ↔ ∀ x, 0 ≤ toLex (reassembled m e ha x) := by
  rw [FiniteVisibility.nonneg_iff_strongWeights hμ hX]
  simp only [strongWeights_apply, singleton_eq_reassembled hX he hμ hm ha]

/-- `meas:thm:momentcriterion`, the exact strong moment criterion: for `m_0 = 1` there is a
positive strong Hahn probability on the sample set with `m_n = ∫ x^n dμ` for all `n` if and
only if (a) `S_m` is well ordered, (b) every row at an exponent of `S_m` is a finite signed
exponential sum with nodes in the sample set, and (c) every reassembled weight
`w_x = ∑_{γ ∈ S_m} c_{γ,x} t^γ` is nonnegative. The representing measure is unique on events
by `eq_of_strongMoment_eq`. -/
theorem exists_isStrongHahnProbability_iff [Zero Γ] [LinearOrder K] [IsStrictOrderedRing K]
    (hX : IsCountablySeparated X) (he : Function.Injective e) (m : ℕ → K⟦Γ⟧) (hm0 : m 0 = 1) :
    (∃ μ : Set X → K⟦Γ⟧, ∃ hμ : IsStrongHahnProbability μ,
        ∀ n, strongMoment hμ.toIsStrongHahnMeasure hX e n = m n) ↔
      ∃ ha : (momentSupport m).IsWF, (∀ γ ∈ momentSupport m, HasFiniteRow m e γ) ∧
        ∀ x, 0 ≤ toLex (reassembled m e ha x) := by
  constructor
  · rintro ⟨μ, hμ, hm⟩
    obtain ⟨ha, hb⟩ :=
      (exists_isStrongHahnMeasure_iff hX e m).mp ⟨μ, hμ.toIsStrongHahnMeasure, hm⟩
    exact ⟨ha, hb, (nonneg_iff_reassembled hX he hμ.toIsStrongHahnMeasure hm ha).mp hμ.nonneg⟩
  · rintro ⟨ha, hb, hc⟩
    obtain ⟨μ, hμ, hm⟩ := (exists_isStrongHahnMeasure_iff hX e m).mpr ⟨ha, hb⟩
    have huniv : μ Set.univ = 1 := by
      rw [eq_atomicMeasure_strongWeights hμ hX MeasurableSet.univ, ← atomicIntegral_indicator,
        ← hm0, ← hm 0, strongMoment, momentSeq]
      congr 1
      funext x
      simp
    exact ⟨μ, ⟨hμ, (nonneg_iff_reassembled hX he hμ hm ha).mpr hc, huniv⟩, hm⟩

/-- `meas:thm:momentcriterion`, existence with uniqueness: under (a), (b) and (c), for
`m_0 = 1`, there is a positive strong Hahn probability with moments `m`, and every signed
strong Hahn measure with moments `m` agrees with it on every event. -/
theorem exists_isStrongHahnProbability_unique [Zero Γ] [LinearOrder K] [IsStrictOrderedRing K]
    (hX : IsCountablySeparated X) (he : Function.Injective e) {m : ℕ → K⟦Γ⟧} (hm0 : m 0 = 1)
    (ha : (momentSupport m).IsWF) (hb : ∀ γ ∈ momentSupport m, HasFiniteRow m e γ)
    (hc : ∀ x, 0 ≤ toLex (reassembled m e ha x)) :
    ∃ μ : Set X → K⟦Γ⟧, ∃ hμ : IsStrongHahnProbability μ,
      (∀ n, strongMoment hμ.toIsStrongHahnMeasure hX e n = m n) ∧
        ∀ (ν : Set X → K⟦Γ⟧) (hν : IsStrongHahnMeasure ν),
          (∀ n, strongMoment hν hX e n = m n) → ∀ A, MeasurableSet A → ν A = μ A := by
  obtain ⟨μ, hμ, hm⟩ := (exists_isStrongHahnProbability_iff hX he m hm0).mpr ⟨ha, hb, hc⟩
  exact ⟨μ, hμ, hm, fun ν hν hνm _ hA =>
    eq_of_strongMoment_eq hX he hν hμ.toIsStrongHahnMeasure
      (fun n => (hνm n).trans (hm n).symm) hA⟩

end Measure

section Real

open _root_.HahnSeries Surreal.HahnSeries

/-- A measurable space that is countably separated in Mathlib's sense is countably separated
in the sense of `meas:def:separated`. -/
theorem isCountablySeparated_of_countablySeparated (X : Type*) [MeasurableSpace X]
    [MeasurableSpace.CountablySeparated X] : IsCountablySeparated X := by
  obtain ⟨E, hE, hsep⟩ := exists_seq_separating X MeasurableSet.empty Set.univ
  exact ⟨E, hE, fun x y hxy => hsep x trivial y trivial hxy⟩

/-- Every subset of `ℝ` with its relative Borel σ-algebra is countably separated, as stated
after `meas:def:separated`; so it is an admissible sample set in `meas:thm:momentcriterion`. -/
theorem isCountablySeparated_real_subtype (Ω : Set ℝ) : IsCountablySeparated Ω :=
  isCountablySeparated_of_countablySeparated Ω

/-- The standing hypothesis of `meas:thm:momentcriterion`: every σ-algebra on `Ω ⊆ ℝ` that
contains the relative Borel sets is countably separated. -/
theorem isCountablySeparated_real_subtype_of_le (Ω : Set ℝ) {m : MeasurableSpace Ω}
    (hm : MeasurableSpace.comap (Subtype.val : Ω → ℝ) inferInstance ≤ m) :
    @IsCountablySeparated Ω m :=
  isCountablySeparated_of_le hm (isCountablySeparated_real_subtype Ω)

/-- `meas:thm:momentcriterion` for a sample set `Ω ⊆ ℝ` carrying any countably separated
σ-algebra and real Hahn-series moments. The source's σ-algebras, those containing the relative
Borel sets, are countably separated by `isCountablySeparated_real_subtype_of_le`. -/
theorem real_exists_isStrongHahnProbability_iff {Γ : Type*} [LinearOrder Γ] [Zero Γ]
    (Ω : Set ℝ) [MeasurableSpace Ω] (hΩ : IsCountablySeparated Ω) (m : ℕ → ℝ⟦Γ⟧)
    (hm0 : m 0 = 1) :
    (∃ μ : Set Ω → ℝ⟦Γ⟧, ∃ hμ : IsStrongHahnProbability μ,
        ∀ n, strongMoment hμ.toIsStrongHahnMeasure hΩ Subtype.val n = m n) ↔
      ∃ ha : (momentSupport m).IsWF,
        (∀ γ ∈ momentSupport m, HasFiniteRow m (Subtype.val : Ω → ℝ) γ) ∧
          ∀ x : Ω, 0 ≤ toLex (reassembled m Subtype.val ha x) :=
  exists_isStrongHahnProbability_iff hΩ Subtype.val_injective m hm0

end Real

end

end Surreal.MomentCriterion
