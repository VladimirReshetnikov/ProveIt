import Lib.Analytic.Primes
import New.Spanning.RemainingTerms.Size
import New.UpperBound.Objects.LabelsAndIndexTypes

/-!
# The share of non-allowed polynomials and the bad share

This file bounds the share of the bad types for tuples of polynomials over fields with q elements.
A label is a monic squarefree polynomial of degree `r` that does not vanish at `0`. The file
counts the monic polynomials that are not allowed and the primitive polynomials. It then bounds
the coefficient at the identity of one minus the sum of the idempotents of the good tuples.

## Main definitions and results

* `New.card_not_primitive_mul_le`: for `1 < r < q`, with every polynomial weighted by
  `(1 - r / q) / q ^ r`, the monic polynomials of degree `r` that are not primitive polynomials
  weigh at most `exp (-1 / (2 r (2 r log q + 1)))` in total.
* `New.re_coeff_one_sub_sum_tupleIdem_le`: the bound on the coefficient at the identity of one minus
  the sum of the idempotents of the good tuples.

Notions from other files:
* `New.tupleIdem`: For a tuple (c_w) of polynomials over the fields k_w, the tensor product of the
  polynomial idempotents e_{c_w} in the group algebra of ∏ GL_n(k_w).

## Relation to the literature

In the regular representation of a product of groups GL_r(F_q), types that are not good have share
at most a multiple of 1/q per factor plus a term decaying exponentially in the number of factors. So
the projection to good types discards little when translates of the Poincaré series fill the rows.
It computes the Plancherel shares for GL_r(F_q) from Green's degree formula and counts of squarefree
and primitive polynomials over F_q, followed by a union bound over the factors. Related work: Green,
The characters of the finite general linear groups, 1955; Dudko, Plancherel measures for GL(n,q),
arXiv 0806.1345, 2008; Lidl–Niederreiter, Finite Fields, ch. 3, 1983.
-/

section BadShare

open Finset Fintype Real Polynomial minpoly Nat ComplexOrder AlgebraicClosure

attribute [local instance low] Fintype.ofFinite

open scoped Classical in
/-- Over a field `k` with `q` elements, at most `(1 + M + r) q ^ (r - 1)` monic polynomials of
degree `r` are not allowed polynomials (`IsAllowedPolynomial M r`). Such a polynomial either fails
to be a label, or has a root `x` in `k` with `x ^ M = 1`. -/
lemma New.card_not_isAllowedPolynomial_le (k : Type*) [Field k] [Finite k] (M : ℕ) [NeZero M]
    (r : ℕ) :
    #{c ∈ monicsOfDegree k r | ¬IsAllowedPolynomial M r c} ≤
      (1 + M + r) * Nat.card k ^ (r - 1) := by
  -- Such a polynomial has a root `a` with `a = 0` or `a ^ M = 1`,
  -- or is `P ^ 2 * B` with `P`, `B` monic and `d = B.natDegree < r`.
  let R : Finset k := insert 0 (nthRoots M (1 : k)).toFinset
  let withRoot : Finset k[X] := R.image₂ (fun a B ↦ (X - C a) * B) (monicsOfDegree k (r - 1))
  let withSquare (d : ℕ) : Finset k[X] :=
    (monicsOfDegree k ((r - d) / 2)).image₂ (fun P B ↦ P ^ 2 * B) (monicsOfDegree k d)
  have mem_monics (d : ℕ) (c : k[X]) : c ∈ monicsOfDegree k d ↔ c.Monic ∧ c.natDegree = d := by
    simp [monicsOfDegree]
  have card_monics (d : ℕ) : #(monicsOfDegree k d) = Nat.card k ^ d := by
    simp [monicsOfDegree, ofEquiv_card]
  have cover : {c ∈ monicsOfDegree k r | ¬IsAllowedPolynomial M r c} ⊆
      withRoot ∪ (range r).biUnion withSquare := by
    intro c hc
    obtain ⟨hc_mem, not_allowed⟩ := mem_filter.mp hc
    obtain ⟨monic, rfl⟩ := (mem_monics r c).mp hc_mem
    by_contra not_covered
    obtain ⟨not_withRoot, not_withSquare⟩ := notMem_union.mp not_covered
    have no_root (a : k) (ha : a ∈ R) (root : c.IsRoot a) : False := by
      obtain ⟨B, rfl⟩ : X - C a ∣ c := dvd_iff_isRoot.mpr root
      have hB : B.Monic := (monic_X_sub_C a).of_mul_monic_left monic
      exact not_withRoot (mem_image₂_of_mem ha
        ((mem_monics _ B).mpr ⟨hB, by simp [(monic_X_sub_C a).natDegree_mul hB]⟩))
    have sqfree : Squarefree c := by
      intro Q hQ
      by_contra not_unit
      obtain ⟨P, hP, irred, hPQ⟩ := Q.exists_monic_irreducible_factor not_unit
      obtain ⟨B, rfl⟩ : P ^ 2 ∣ c := by simpa [sq] using (mul_dvd_mul hPQ hPQ).trans hQ
      have hB : B.Monic := (hP.pow 2).of_mul_monic_left monic
      have deg : (P ^ 2 * B).natDegree = 2 * P.natDegree + B.natDegree := by
        simp [(hP.pow 2).natDegree_mul hB]
      have hP_pos : 0 < P.natDegree := irred.natDegree_pos
      have h_image : P ^ 2 * B ∈ withSquare B.natDegree :=
        mem_image₂_of_mem ((mem_monics _ P).mpr ⟨hP, by lia⟩) ((mem_monics _ B).mpr ⟨hB, rfl⟩)
      exact not_withSquare (mem_biUnion.mpr ⟨B.natDegree, mem_range.mpr (by lia), h_image⟩)
    have label : IsLabel c.natDegree c :=
      ⟨monic, sqfree, rfl, zero_isRoot_iff_coeff_zero_eq_zero.not.mp (no_root 0 (by simp [R]))⟩
    exact not_allowed ⟨label, fun a ha ↦ no_root a (by simp [R, NeZero.pos, ha])⟩
  have card_withRoot : #withRoot ≤ (1 + M) * Nat.card k ^ (r - 1) := by
    grw [card_image₂_le, card_insert_le, Multiset.toFinset_card_le, card_nthRoots, card_monics,
      add_comm M 1]
  have card_withSquare (d : ℕ) (hd : d ∈ range r) : #(withSquare d) ≤ Nat.card k ^ (r - 1) := by
    have deg_le : (r - d) / 2 + d ≤ r - 1 := by grind
    grw [card_image₂_le, card_monics, card_monics, ← pow_add]
    exact Nat.pow_le_pow_right Nat.card_pos deg_le
  grw [card_le_card cover, card_union_le, card_withRoot,
    card_biUnion_le_card_mul (range r) withSquare _ card_withSquare, Finset.card_range, ← add_mul]

open scoped Classical in
/-- Over a field `k` with `q` elements and for `r ≠ 0`, there are at least `φ (q ^ r - 1) / r`
primitive polynomials of degree `r`. These are the irreducible monic polynomials of degree `r`, not
vanishing at `0`, with a root of order `q ^ r - 1`. -/
lemma New.totient_le_mul_card_isPrimitivePolynomial (k : Type*) [Field k] [Finite k] {r : ℕ}
    (hr : r ≠ 0) :
    φ (Nat.card k ^ r - 1) ≤ r * #{c ∈ monicsOfDegree k r | IsPrimitivePolynomial r c} := by
  have hq : 1 < Nat.card k := Finite.one_lt_card
  have hqr : 1 < Nat.card k ^ r := one_lt_pow₀ hq hr
  have : NeZero ((Nat.card k ^ r - 1 : ℕ) : k) := ⟨by simp [Ne.pos, hr]⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : AlgebraicClosure k, IsPrimitiveRoot ζ (Nat.card k ^ r - 1) :=
    (hasEnoughRootsOfUnity k _).prim
  rw [← hζ.card_primitiveRoots]
  refine card_le_mul_card_image_of_maps_to (f := minpoly k) (fun ξ hξ ↦ ?_) r fun c hc ↦ ?_
  · rw [mem_primitiveRoots (by lia)] at hξ
    obtain ⟨ξ_ne, ξ_fixed⟩ := (pow_pred_eq_one_iff hqr).mp hξ.pow_eq_one
    have int : IsIntegral k ξ := Algebra.IsIntegral.isIntegral ξ
    have coeff_ne : (minpoly k ξ).coeff 0 ≠ 0 := coeff_zero_ne_zero int ξ_ne
    set d : ℕ := (minpoly k ξ).natDegree
    -- `q ^ r - 1` and `q ^ d - 1` divide each other, so `d = r`.
    obtain ⟨pow_eq_one, two_le⟩ : ξ ^ (Nat.card k ^ d - 1) = 1 ∧ 2 ≤ Nat.card k ^ d :=
      root_pow_card_pow_pred_eq_one (irreducible int) coeff_ne (aeval k ξ)
    have deg_dvd : d ∣ r := (root_pow_card_pow_eq_self_iff (irreducible int) (aeval k ξ)).mp ξ_fixed
    have pow_eq : Nat.card k ^ r - 1 = Nat.card k ^ d - 1 :=
      (hξ.dvd_of_pow_eq_one _ pow_eq_one).antisymm (pow_sub_one_dvd_pow_sub_one _ deg_dvd)
    have deg : d = r := Nat.pow_right_injective hq (by lia)
    exact mem_filter.mpr ⟨by simp [monicsOfDegree, monic int, d, ← deg],
      ⟨monic int, (irreducible int).squarefree, deg, coeff_ne⟩, irreducible int, ξ, aeval k ξ, hξ⟩
  · -- The `ξ` with minimal polynomial `c` are roots of `c`, which has degree `r`.
    obtain ⟨⟨monic, -, rfl, -⟩, -⟩ : IsPrimitivePolynomial r c := (mem_filter.mp hc).2
    grw [← natDegree_map_le (f := algebraMap k (AlgebraicClosure k))]
    refine card_le_degree_of_subset_roots fun ξ hξ ↦ ?_
    obtain rfl : minpoly k ξ = c := (mem_filter.mp hξ).2
    simp [monic.ne_zero]

open scoped Classical in
/-- Over a field with `q` elements and for `1 < r < q`, weight every polynomial by
`(1 - r / q) / q ^ r`. Then the allowed polynomials of degree `r` (monic, squarefree, no root at `0`
or at an `M`-th root of unity in the field) weigh at least `1 - ε` in total if
`(1 + M + 2 r) / q ≤ ε`. -/
lemma New.one_sub_le_card_allowed_mul (k : Type*) [Field k] [Finite k] {q M r : ℕ} [NeZero M]
    {ε : ℝ} (hq : Nat.card k = q) (hr_one_lt : 1 < r) (hrq : r < q)
    (hε_ge : (1 + M + 2 * r) / q ≤ ε) :
    1 - ε ≤ #{c ∈ monicsOfDegree k r | IsAllowedPolynomial M r c} * ((1 - r / q) / q ^ r) := by
  have hq_pos : 0 < (q : ℝ) := mod_cast (by lia : 0 < q)
  have weight_nonneg : 0 ≤ (1 - r / q : ℝ) / q ^ r := by bound [(mod_cast hrq.le : (r : ℝ) ≤ q)]
  have card_split : (#{c ∈ monicsOfDegree k r | IsAllowedPolynomial M r c} : ℝ) +
      #{c ∈ monicsOfDegree k r | ¬IsAllowedPolynomial M r c} = q ^ r := by
    simp [← cast_add, card_filter_add_card_filter_not, monicsOfDegree, ofEquiv_card, ← hq]
  have card_bad : (#{c ∈ monicsOfDegree k r | ¬IsAllowedPolynomial M r c} : ℝ) ≤
      (1 + M + r) * q ^ (r - 1) := by
    rw [← hq]
    exact_mod_cast card_not_isAllowedPolynomial_le k M r
  calc 1 - ε ≤ 1 - (1 + M + 2 * r) / q := by linarith
    _ ≤ (1 - (1 + M + r) / q) * (1 - r / q : ℝ) := by
      linear_combination (by positivity : 0 ≤ (1 + M + r : ℝ) / q * (r / q))
    _ = (q ^ r - (1 + M + r) * q ^ (r - 1)) * ((1 - r / q) / q ^ r) := by
      rw [pow_sub₀ _ hq_pos.ne' hr_one_lt.le]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) weight_nonneg

open scoped Classical in
/-- Over a field `k` with `q` elements and for `1 < r < q`, weight every polynomial by
`(1 - r / q) / q ^ r`. The monic polynomials of degree `r` that are not primitive polynomials weigh
at most `exp (-1 / (2 r (2 r log q + 1)))` in total. -/
lemma New.card_not_primitive_mul_le (k : Type*) [Field k] [Finite k] {q r : ℕ}
    (hq : Nat.card k = q) (hr_one_lt : 1 < r) (hrq : r < q) :
    #{c ∈ monicsOfDegree k r | ¬IsPrimitivePolynomial r c} * ((1 - r / q) / q ^ r : ℝ) ≤
      exp (-(1 / (2 * r * (2 * (r * Real.log q) + 1)))) := by
  -- `φ (q ^ r - 1)` is at most `r` times the number of primitive polynomials, and
  -- `N ≤ φ N * (2 log N + 1)`.
  set A : ℝ := 2 * r * (2 * (r * Real.log q) + 1)
  have hqr : 1 < q ^ r := one_lt_pow hr_one_lt.ne_bot (hr_one_lt.trans hrq)
  have hqr_pos : 0 < (q : ℝ) ^ r := mod_cast (by lia : 0 < q ^ r)
  have hA_pos : 0 < A := by positivity
  set nPrim : ℕ := #{c ∈ monicsOfDegree k r | IsPrimitivePolynomial r c}
  have log_le : Real.log (q ^ r - 1 : ℕ) ≤ r * Real.log q := by
    grw [sub_le, cast_pow, Real.log_pow]
    exact_mod_cast (by lia : 0 < q ^ r - 1)
  have totient_le : (φ (q ^ r - 1) : ℝ) ≤ r * nPrim := by
    rw [← hq]
    exact_mod_cast totient_le_mul_card_isPrimitivePolynomial k hr_one_lt.ne_zero
  have prim_ge : (q : ℝ) ^ r ≤ A * nPrim := calc
    (q : ℝ) ^ r ≤ (q ^ r - 1 : ℕ) * 2 := mod_cast (by lia : q ^ r ≤ (q ^ r - 1) * 2)
    _ ≤ φ (q ^ r - 1) * (2 * Real.log (q ^ r - 1 : ℕ) + 1) * 2 := by
      gcongr
      exact le_totient_mul_log (by lia)
    _ ≤ r * nPrim * (2 * (r * Real.log q) + 1) * 2 := by gcongr
    _ = A * nPrim := by ring
  have card_split :
      (nPrim : ℝ) + #{c ∈ monicsOfDegree k r | ¬IsPrimitivePolynomial r c} = q ^ r := by
    simp [nPrim, ← cast_add, card_filter_add_card_filter_not, monicsOfDegree, ofEquiv_card, ← hq]
  calc
    _ ≤ (q ^ r - nPrim : ℝ) * (1 / (q : ℝ) ^ r) := by
      rw [← card_split, add_sub_cancel_left]
      bound [(by positivity : 0 ≤ (r : ℝ) / q)]
    _ = 1 - nPrim / (q : ℝ) ^ r := by field_simp
    _ ≤ 1 - 1 / A := by
      rw [sub_le_sub_iff_left, div_le_div_iff₀ hA_pos hqr_pos]
      linarith
    _ ≤ exp (-(1 / A)) := one_sub_le_exp_neg _

/-- Let `k w` be finitely many fields with `q` elements, `r = card n < q`, and `c w` a label of
degree `r` over `k w`: a monic squarefree polynomial of degree `r` that does not vanish at `0`. The
idempotent `tupleIdem n c` is the tensor product over `w` of the `labelIdem n (c w)`; it lies in the
complex group algebra of ∏ GL_n(k w). The real part of its coefficient at the identity element of
that group is at least the product of `(1 - r / q) / q ^ r` over all `w`. -/
lemma New.prod_le_re_tupleIdem_coeff_one {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    [DecidableEq ι] {k : ι → Type*} [∀ w : ι, Field (k w)] [∀ w : ι, Finite (k w)] {q r : ℕ}
    (hq : ∀ w : ι, Nat.card (k w) = q) (hr : Fintype.card n = r) (hrq : r < q)
    {c : ∀ w : ι, (k w)[X]} (hc : ∀ w : ι, IsLabel r (c w)) :
    ∏ _ : ι, ((1 - r / q) / q ^ r : ℝ) ≤ ((tupleIdem n c).coeff 1).re := by
  classical
  subst r
  have weight_nonneg : 0 ≤ (1 - card n / q : ℝ) / q ^ card n := by
    bound [(mod_cast hrq.le : (card n : ℝ) ≤ q)]
  -- each factor of the coefficient at 1 is at least the weight, by labelChar_degree_bounds
  have prod_ge : ∏ _ : ι, (((1 - card n / q) / q ^ card n : ℝ) : ℂ) ≤
      ∏ w, (labelIdem n (c w)).coeff 1 :=
    prod_le_prod₀ (fun _ _ ↦ Complex.zero_le_real.mpr weight_nonneg) fun w _ ↦ by
      simpa [labelIdem, ← hq w, hc w] using (labelChar_degree_bounds _ (hc w)).2
  -- the real parts; the coefficient of a tensor product at `1` is the product of the coefficients
  exact_mod_cast (Complex.le_def.mp prod_ge).1

/-- Let `k w` be `f` fields with `q` elements each and `r = card n`. A tuple `c` of labels is good
if no `c w` vanishes at an `M`-th root of unity of `k w` and some `c w` is primitive: irreducible
with a root of order `q ^ r - 1`. In the complex group algebra of ∏ GL_n(k w), take one minus the
sum over the good tuples of `tupleIdem n c`, the tensor product over `w` of the idempotents
`∑ g, (Ξ(1) / |G|) conj Ξ(g) • g` of ℂ[G], where G = GL_n(k w) and Ξ is the character `labelChar` of
the label `c w`. Its coefficient at the identity has real part at most `f * ε + exp (-L)` if
`1 < r < q`, `(1 + M + 2 r) / q ≤ ε ≤ 1` and `2 r (2 r log q + 1) L ≤ f`. -/
lemma New.re_coeff_one_sub_sum_tupleIdem_le {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    [DecidableEq ι]
    {k : ι → Type*} [∀ w : ι, Field (k w)] [∀ w : ι, Finite (k w)] {q M r f : ℕ} [NeZero M]
    (ε L : ℝ) (hq : ∀ w : ι, Nat.card (k w) = q) (hr : Fintype.card n = r) (hf : Fintype.card ι = f)
    (hr_one_lt : 1 < r) (hrq : r < q) (hε_le : ε ≤ 1) (hε_ge : (1 + M + 2 * r) / q ≤ ε)
    (hL : 2 * r * (2 * (r * Real.log q) + 1) * L ≤ f) :
    ((1 - ∑ c ∈ goodTuples M r, tupleIdem (k := k) n c).coeff 1).re ≤ f * ε + exp (-L) := by
  classical
  -- Each good tuple contributes at least `m ^ f` to the coefficient of the sum at `1`. A tuple of
  -- allowed polynomials is good, or none of its polynomials is primitive. Weighted by `m ^ f`,
  -- allowed tuples count at least `(1 - ε) ^ f`, those without primitive polynomial at most
  -- `exp (-u) ^ f`.
  let u : ℝ := 1 / (2 * r * (2 * (r * Real.log q) + 1))
  let m : ℝ := (1 - r / q) / q ^ r
  let allowed (w : ι) : Finset (k w)[X] := {c ∈ monicsOfDegree (k w) r | IsAllowedPolynomial M r c}
  let nonPrim (w : ι) : Finset (k w)[X] := {c ∈ monicsOfDegree (k w) r | ¬IsPrimitivePolynomial r c}
  set good : Finset (∀ w : ι, (k w)[X]) := goodTuples M r
  have m_nonneg : 0 ≤ m := by bound [(mod_cast hrq.le : (r : ℝ) ≤ q)]
  have nonPrim_le (w : ι) : #(nonPrim w) * m ≤ exp (-u) :=
    card_not_primitive_mul_le (k w) (hq w) hr_one_lt hrq
  have tuple_ge (c : ∀ w : ι, (k w)[X]) (hc : c ∈ good) :
      ∏ _ : ι, m ≤ ((tupleIdem n c).coeff 1).re :=
    prod_le_re_tupleIdem_coeff_one hq hr hrq fun w ↦ ((mem_goodTuples.mp hc).1 w).isLabel
  have cover : piFinset allowed \ piFinset nonPrim ⊆ good := by
    intro c hc
    simp only [mem_sdiff, mem_piFinset, allowed, nonPrim, mem_filter] at hc
    grind [mem_goodTuples]
  have pow_le_sum : (1 - ε) ^ f ≤ ∑ c ∈ good, ((tupleIdem n c).coeff 1).re + exp (-(f * u)) := calc
    _ = ∏ _ : ι, (1 - ε) := by simp [hf]
    _ ≤ ∏ w, #(allowed w) * m := prod_le_prod₀ (by bound) fun w _ ↦
      one_sub_le_card_allowed_mul (k w) (hq w) hr_one_lt hrq hε_ge
    _ = #(piFinset allowed) * ∏ _ : ι, m := by simp [prod_mul_distrib]
    _ ≤ (#good + #(piFinset nonPrim)) * ∏ _ : ι, m := by
      grw [card_le_card_sdiff_add_card, card_le_card cover, cast_add]
    _ = #good • ∏ _ : ι, m + ∏ w, #(nonPrim w) * m := by simp [add_mul, prod_mul_distrib]
    _ ≤ ∑ c ∈ good, ((tupleIdem n c).coeff 1).re + exp (-(f * u)) := by
      grw [card_nsmul_le_sum good _ (∏ _ : ι, m) tuple_ge, nonPrim_le]
      simp [hf, ← exp_nsmul]
  have bernoulli : 1 - f * ε ≤ (1 - ε) ^ f := by
    simpa [sub_eq_add_neg] using one_add_mul_le_pow (show -2 ≤ -ε by linarith) f
  calc _ = 1 - ∑ c ∈ good, ((tupleIdem n c).coeff 1).re := by simp
    _ ≤ f * ε + exp (-(f * u)) := by linarith
    _ ≤ f * ε + exp (-L) := by
      gcongr
      rwa [mul_one_div, le_div_iff₀' (by positivity)]

end BadShare
