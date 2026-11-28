import Lib.General.Algebra.AdicCompletion

/-!
# Power series with prime power exponents, congruences and convergent sums

This file studies power series of the form `∑_{i ∈ I} z ^ p ^ i` and congruences between power
series modulo a constant `π`, with the facts on continuity and convergent sums that are needed to
work with such congruences.

## Main definitions and results

* `New.primePowerSeries`: the series `∑_{i ∈ I} z ^ p ^ i`.
* `New.primePowerSeries_even_pow`: in characteristic `p` the `p`-th power of `∑_{i even} z ^ p ^ i`
  is `∑_{i odd} z ^ p ^ i`.
* `New.exists_eq_pow_add_pow_of_coeff_mul_ne_zero`: a product of two series `∑_{i ∈ I} z ^ p ^ i`
  has only terms of the degrees `p ^ i + p ^ j`.
* `New.dvd_sum_pow_sub_sum`: for a prime `p` the `p ^ j`-th powers are additive modulo a divisor of
  `p`.
* `New.continuous_subst_of_constantCoeff_eq_zero`, `New.continuous_pderiv`: substitution of finitely
  many series without constant term and differentiation are continuous.
* `New.C_dvd_of_hasSum`: over the valuation ring of `ℂ_[p]` a convergent sum of power series
  divisible by `π` is divisible by `π`.

Power series carry the topology of coefficientwise convergence.

## Relation to the literature

Known result: elementary facts on power series in characteristic `p`.

Known result: elementary facts on formal power series with the topology of coefficientwise
convergence. Source: Bourbaki, Algebra II, Chapter IV.
-/

/-! ## Series with prime power exponents -/

section PrimePowerSeries

open PowerSeries Finset

namespace New
variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] {I J : Set ℕ}

variable (R p I) in
open Classical in
/-- The series `∑_{i ∈ I} z ^ p ^ i` over `R`: its coefficient of degree `n` is `1` if `n = p ^ i`
for some `i ∈ I`, and `0` otherwise. -/
noncomputable def primePowerSeries : R⟦X⟧ :=
  mk fun n : ℕ ↦ if ∃ i ∈ I, n = p ^ i then 1 else 0

omit [Fact p.Prime] in
lemma map_primePowerSeries {S : Type*} [CommRing S] (f : R →+* S) :
    (primePowerSeries R p I).map f = primePowerSeries S p I := by
  ext n
  simp only [primePowerSeries, coeff_map, coeff_mk, apply_ite f, map_one, map_zero]

/-- In characteristic `p` the `p`-th power of `∑_{i even} z ^ p ^ i` is `∑_{i odd} z ^ p ^ i`. Here
`primePowerSeries R p I` is the series `∑_{i ∈ I} z ^ p ^ i`. -/
lemma primePowerSeries_even_pow [CharP R p] :
    primePowerSeries R p {i : ℕ | Even i} ^ p = primePowerSeries R p {i : ℕ | Odd i} := by
  classical
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have h_frob : (expand p hp (primePowerSeries R p {i : ℕ | Even i})).map (frobenius R p) =
      primePowerSeries R p {i : ℕ | Even i} ^ p := MvPowerSeries.map_frobenius_expand p hp
  have h_exp (n : ℕ) :
      (p ∣ n ∧ ∃ i : ℕ, Even i ∧ n / p = p ^ i) ↔ ∃ i : ℕ, Odd i ∧ n = p ^ i := by
    constructor
    · rintro ⟨⟨k, rfl⟩, i, hi, hk⟩
      exact ⟨i + 1, hi.add_one, by rw [pow_succ', ← hk, Nat.mul_div_cancel_left k hp.bot_lt]⟩
    · rintro ⟨i, ⟨k, rfl⟩, rfl⟩
      exact ⟨dvd_pow_self p (by omega), 2 * k, even_two_mul k, by simp [pow_succ, hp]⟩
  ext n
  rw [← h_frob, coeff_map, coeff_expand]
  simp only [primePowerSeries, coeff_mk, Set.mem_ofPred_eq, ← h_exp, ← ite_and,
    apply_ite (frobenius R p), map_one, map_zero]

omit [Fact p.Prime] in
/-- The product of `primePowerSeries R p I = ∑_{i ∈ I} z ^ p ^ i` and
`primePowerSeries R p J = ∑_{j ∈ J} z ^ p ^ j` has only terms of the degrees `p ^ i + p ^ j` with
`i ∈ I` and `j ∈ J`. -/
lemma exists_eq_pow_add_pow_of_coeff_mul_ne_zero {n : ℕ}
    (h_coeff : coeff n (primePowerSeries R p I * primePowerSeries R p J) ≠ 0) :
    ∃ i ∈ I, ∃ j ∈ J, n = p ^ i + p ^ j := by
  have h_support {K : Set ℕ} {a : ℕ} (ha : coeff a (primePowerSeries R p K) ≠ 0) :
      ∃ i ∈ K, a = p ^ i := by_contra fun h_not ↦ ha (by simp [primePowerSeries, h_not])
  rw [coeff_mul] at h_coeff
  obtain ⟨⟨a, b⟩, hab, h_ne⟩ := exists_ne_zero_of_sum_ne_zero h_coeff
  obtain ⟨i, hi, rfl⟩ := h_support (left_ne_zero_of_mul h_ne)
  obtain ⟨j, hj, rfl⟩ := h_support (right_ne_zero_of_mul h_ne)
  exact ⟨i, hi, j, hj, (mem_antidiagonal.1 hab).symm⟩

/-- The number `p ^ i + p ^ i'` has the form `(p ^ e + 1) p ^ j` where `e` has the parity of
`i + i'`. -/
lemma exists_pow_add_pow_eq (p i i' : ℕ) :
    ∃ e j : ℕ, (Odd e ↔ Odd (i + i')) ∧ p ^ i + p ^ i' = (p ^ e + 1) * p ^ j := by
  wlog h : i' ≤ i generalizing i i' with h_symm
  · simpa only [add_comm] using h_symm i' i (le_of_not_ge h)
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨e, i', by grind, by ring⟩

/-- For an odd prime `p` the numbers `e` and `j` are determined by `(p ^ e + 1) p ^ j`. -/
lemma injective_pow_add_one_mul_pow (hp : p ≠ 2) :
    Function.Injective fun x : ℕ × ℕ ↦ (p ^ x.1 + 1) * p ^ x.2 := by
  have h_prime : p.Prime := Fact.out
  have h_not_dvd (e : ℕ) : ¬p ∣ p ^ e + 1 := by
    rcases e.eq_zero_or_pos with rfl | he
    · simpa [Nat.prime_dvd_prime_iff_eq h_prime Nat.prime_two] using hp
    · simpa [Nat.dvd_add_right (dvd_pow_self p he.ne')] using h_prime.ne_one
  have h_val (e j : ℕ) : padicValNat p ((p ^ e + 1) * p ^ j) = j := by
    simp [padicValNat.mul, padicValNat.eq_zero_of_not_dvd (h_not_dvd e), h_prime.ne_zero]
  rintro ⟨e, j⟩ ⟨e', j'⟩ (h : (p ^ e + 1) * p ^ j = (p ^ e' + 1) * p ^ j')
  obtain rfl : j = j' := by rw [← h_val e j, h, h_val]
  have h_pow : p ^ e = p ^ e' := by simpa [h_prime.ne_zero] using h
  rw [Nat.pow_right_injective h_prime.two_le h_pow]

/-- For an odd prime `p` one has `p ^ i + p ^ i' = (p ^ e + 1) p ^ j` exactly if `j` is the smaller
and `e + j` the larger of the numbers `i` and `i'`. -/
lemma pow_add_pow_eq_iff (hp : p ≠ 2) {i i' e j : ℕ} :
    p ^ i + p ^ i' = (p ^ e + 1) * p ^ j ↔ (i, i') = (e + j, j) ∨ (i, i') = (j, e + j) := by
  refine ⟨fun h ↦ ?_, by rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩) <;> ring⟩
  wlog h_le : i' ≤ i generalizing i i' with h_symm
  · simpa [and_comm, or_comm] using h_symm ((add_comm _ _).trans h) (le_of_not_ge h_le)
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = k + i' := Nat.exists_eq_add_of_le' h_le
  have h_mul : (p ^ k + 1) * p ^ i' = (p ^ e + 1) * p ^ j := by grind
  obtain ⟨⟩ : (k, i') = (e, j) := injective_pow_add_one_mul_pow hp h_mul
  exact .inl rfl

open scoped Classical in
/-- For an odd prime `p` the coefficient of degree `(p ^ e + 1) p ^ j` in the product of
`primePowerSeries R p I = ∑_{i ∈ I} z ^ p ^ i` and `primePowerSeries R p J = ∑_{i' ∈ J} z ^ p ^ i'`
counts the pairs `(i, i') ∈ I × J` among `(e + j, j)` and `(j, e + j)`. -/
lemma coeff_primePowerSeries_mul (hp : p ≠ 2) (e j : ℕ) :
    coeff ((p ^ e + 1) * p ^ j) (primePowerSeries R p I * primePowerSeries R p J) =
      ∑ x ∈ ({(e + j, j), (j, e + j)} : Finset (ℕ × ℕ)), if x.1 ∈ I ∧ x.2 ∈ J then 1 else 0 := by
  have h_inj : Function.Injective fun i : ℕ ↦ p ^ i :=
    Nat.pow_right_injective (Fact.out : p.Prime).two_le
  have h_mem {i i' : ℕ} : (p ^ i, p ^ i') ∈ antidiagonal ((p ^ e + 1) * p ^ j) ↔
      (i, i') ∈ ({(e + j, j), (j, e + j)} : Finset (ℕ × ℕ)) := by
    simp [pow_add_pow_eq_iff hp]
  rw [coeff_mul]
  refine (sum_of_injOn (fun x : ℕ × ℕ ↦ (p ^ x.1, p ^ x.2)) (h_inj.prodMap h_inj).injOn
    (fun x hx ↦ h_mem.2 hx) ?_ fun x _ ↦ ?_).symm
  · rintro ⟨a, b⟩ hab h_not
    simp only [primePowerSeries, coeff_mk, mul_ite, mul_one, mul_zero, ite_eq_right_iff]
    rintro ⟨i', -, rfl⟩ ⟨i, -, rfl⟩
    exact absurd ⟨(i, i'), h_mem.1 hab, rfl⟩ h_not
  · simp only [primePowerSeries, coeff_mk, h_inj.eq_iff, exists_eq_right', ite_zero_mul_ite_zero,
      mul_one]

/-- For an odd prime `p` and odd `e` the product of `∑_{i odd} z ^ p ^ i` and `∑_{i even} z ^ p ^ i`
has coefficient `1` in degree `(p ^ e + 1) p ^ j`. -/
lemma coeff_primePowerSeries_odd_mul_even (hp : p ≠ 2) {e : ℕ} (he : Odd e) (j : ℕ) :
    coeff ((p ^ e + 1) * p ^ j)
      (primePowerSeries R p {i : ℕ | Odd i} * primePowerSeries R p {i : ℕ | Even i}) = 1 := by
  have h_ne : (e + j, j) ≠ (j, e + j) := by simpa using he.pos.ne'
  rw [coeff_primePowerSeries_mul hp, sum_pair h_ne]
  rcases j.even_or_odd with hj | hj
  · simp [hj, he.add_even hj, Nat.not_odd_iff_even.2 hj]
  · simp [hj, he.add_odd hj, Nat.not_even_iff_odd.2 hj]

/-- For an odd prime `p` the square of `primePowerSeries R p Set.univ = ∑_i z ^ p ^ i` has in degree
`(p ^ e + 1) p ^ j` the coefficient `1` if `e = 0`, and `2` otherwise. -/
lemma coeff_primePowerSeries_univ_sq (hp : p ≠ 2) (e j : ℕ) :
    coeff ((p ^ e + 1) * p ^ j) (primePowerSeries R p Set.univ ^ 2) = if e = 0 then 1 else 2 := by
  rw [sq, coeff_primePowerSeries_mul hp]
  split_ifs with he <;> simp [he]

section Sums
open WithPiTopology
variable [TopologicalSpace R]

/-- Let `p` be an odd prime. A series `f` that has terms only in the degrees `(p ^ e + 1) p ^ j`
with `e ∈ S`, with coefficients `l e j`, is the sum of the `l e j • (z ^ p ^ e z) ^ p ^ j` in the
topology of coefficientwise convergence. -/
lemma hasSum_smul_X_pow_mul_X_pow (hp : p ≠ 2) {S : Set ℕ} {l : ℕ → ℕ → R} {f : R⟦X⟧}
    (h_coeff : ∀ e ∈ S, ∀ j : ℕ, coeff ((p ^ e + 1) * p ^ j) f = l e j)
    (h_support : ∀ n : ℕ, coeff n f ≠ 0 → ∃ e ∈ S, ∃ j : ℕ, n = (p ^ e + 1) * p ^ j) :
    HasSum (fun x : S × ℕ ↦ l x.1 x.2 • (X ^ p ^ (x.1 : ℕ) * X : R⟦X⟧) ^ p ^ x.2) f := by
  let deg (x : S × ℕ) : ℕ := (p ^ (x.1 : ℕ) + 1) * p ^ x.2
  have h_inj : Function.Injective deg :=
    (injective_pow_add_one_mul_pow hp).comp (Subtype.val_injective.prodMap Function.injective_id)
  have h_zero (n : ℕ) (hn : n ∉ Set.range deg) : monomial n (coeff n f) = 0 := by
    by_contra h_ne
    obtain ⟨e, he, j, rfl⟩ := h_support n fun h ↦ h_ne (by simp [h])
    exact hn ⟨(⟨e, he⟩, j), rfl⟩
  have h_term (x : S × ℕ) : l x.1 x.2 • (X ^ p ^ (x.1 : ℕ) * X : R⟦X⟧) ^ p ^ x.2 =
      monomial (deg x) (coeff (deg x) f) := by
    rw [h_coeff _ x.1.property, ← pow_succ, ← pow_mul, X_pow_eq, ← map_smul, smul_eq_mul, mul_one]
  simpa only [h_term, Function.comp_def] using
    (h_inj.hasSum_iff h_zero).2 (hasSum_of_monomials_self f)

/-- For an odd prime `p` and `l ∈ R` the series `l (∑_{i odd} z ^ p ^ i) (∑_{i even} z ^ p ^ i)` is
the sum of the `l (z ^ p ^ e z) ^ p ^ j` over the odd `e` and all `j`. -/
lemma hasSum_primePowerSeries_odd_mul_even (hp : p ≠ 2) (l : R) :
    HasSum (fun x : {e : ℕ | Odd e} × ℕ ↦ l • (X ^ p ^ (x.1 : ℕ) * X : R⟦X⟧) ^ p ^ x.2)
      (l • (primePowerSeries R p {i : ℕ | Odd i} * primePowerSeries R p {i : ℕ | Even i})) := by
  refine hasSum_smul_X_pow_mul_X_pow hp (l := fun _ _ ↦ l) (fun e he j ↦ ?_) fun n hn ↦ ?_
  · simp [coeff_primePowerSeries_odd_mul_even hp he]
  · rw [coeff_smul] at hn
    obtain ⟨i, hi, i', hi', rfl⟩ :=
      exists_eq_pow_add_pow_of_coeff_mul_ne_zero (right_ne_zero_of_smul hn)
    obtain ⟨e, j, he, h_eq⟩ := exists_pow_add_pow_eq p i i'
    exact ⟨e, he.2 (Odd.add_even hi hi'), j, h_eq⟩

/-- Let `p` be an odd prime, let `half` be an inverse of `2` in `R`, let `l ∈ R` and
`P = primePowerSeries R p Set.univ = ∑_i z ^ p ^ i`. Then `l (P ^ 2 - z ^ 2 / 2)` is the sum of the
`l_{e j} (z ^ p ^ e z) ^ p ^ j` over all `e` and `j`, where `l_{0 0} = l / 2`, `l_{0 j} = l` for
`j ≥ 1`, and `l_{e j} = 2 l` for `e ≥ 1`. -/
lemma hasSum_primePowerSeries_univ_sq_sub (hp : p ≠ 2) {half : R} (h_half : 2 * half = 1) (l : R) :
    HasSum (fun x : ↥(Set.univ : Set ℕ) × ℕ ↦
        (if (x.1 : ℕ) = 0 then if x.2 = 0 then l * half else l else 2 * l) •
          (X ^ p ^ (x.1 : ℕ) * X : R⟦X⟧) ^ p ^ x.2)
      (l • (primePowerSeries R p Set.univ ^ 2 - half • X ^ 2)) := by
  have h_two {e j : ℕ} : (p ^ e + 1) * p ^ j = 2 ↔ e = 0 ∧ j = 0 := by
    simpa using (injective_pow_add_one_mul_pow hp).eq_iff (a := (e, j)) (b := (0, 0))
  refine hasSum_smul_X_pow_mul_X_pow hp
    (l := fun e j ↦ if e = 0 then if j = 0 then l * half else l else 2 * l)
    (fun e _ j ↦ ?_) fun n hn ↦ ?_
  · simp only [coeff_smul, map_sub, coeff_primePowerSeries_univ_sq hp, coeff_X_pow, h_two,
      smul_eq_mul, ite_and]
    split_ifs <;> grind
  · obtain rfl | h_ne := eq_or_ne n 2
    · exact ⟨0, Set.mem_univ 0, 0, (h_two.2 ⟨rfl, rfl⟩).symm⟩
    rw [coeff_smul, map_sub, coeff_smul, coeff_X_pow, ite_eq_right h_ne, smul_zero, sub_zero,
      sq] at hn
    obtain ⟨i, -, i', -, rfl⟩ :=
      exists_eq_pow_add_pow_of_coeff_mul_ne_zero (right_ne_zero_of_smul hn)
    obtain ⟨e, j, -, h_eq⟩ := exists_pow_add_pow_eq p i i'
    exact ⟨e, Set.mem_univ e, j, h_eq⟩

end Sums

end New

end PrimePowerSeries

/-! ## Congruences and infinite sums of power series -/

section SeriesCongruences

open MvPowerSeries WithPiTopology

namespace New

variable {R σ τ ι : Type*} [CommRing R]

/-- If `π` divides the prime `p` in `R`, then `p ^ j`-th powers are additive modulo `π`. -/
lemma dvd_sum_pow_sub_sum {p : ℕ} [Fact p.Prime] {π : R} (hπ : π ∣ (p : R)) (t : Finset ι)
    (f : ι → R) (j : ℕ) : π ∣ (∑ i ∈ t, f i) ^ p ^ j - ∑ i ∈ t, f i ^ p ^ j := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
  nontriviality R ⧸ Ideal.span {π}
  have h_char : CharP (R ⧸ Ideal.span {π}) p := by
    rwa [CharP.charP_iff_prime_eq_zero Fact.out, ← map_natCast (Ideal.Quotient.mk _),
      Ideal.Quotient.eq_zero_iff_dvd]
  simp only [map_pow, map_sum, sum_pow_char_pow]

lemma C_dvd_iff_forall_dvd_coeff {π : R} {F : MvPowerSeries σ R} :
    C π ∣ F ↔ ∀ d : σ →₀ ℕ, π ∣ coeff d F := by
  refine ⟨fun ⟨G, hG⟩ d ↦ ⟨coeff d G, by rw [hG, coeff_C_mul]⟩, fun h ↦ ?_⟩
  choose g hg using (h : ∀ d : σ →₀ ℕ, ∃ c : R, coeff d F = π * c)
  exact ⟨g, MvPowerSeries.ext fun d ↦ (hg d).trans (coeff_C_mul d g π).symm⟩

/-- If the series `Z x` have no constant term, then the monomial `∏_x Z x ^ d x` has order at least
the total degree of `d`. -/
lemma degree_le_order_prod_pow {Z : σ → MvPowerSeries τ R}
    (hZ : ∀ x : σ, constantCoeff (Z x) = 0) (d : σ →₀ ℕ) :
    (d.degree : ℕ∞) ≤ (d.prod fun (x : σ) (k : ℕ) ↦ Z x ^ k).order :=
  calc (d.degree : ℕ∞) = ∑ x ∈ d.support, (d x : ℕ∞) := by simp [Finsupp.degree_apply]
    _ ≤ ∑ x ∈ d.support, (Z x ^ d x).order :=
        Finset.sum_le_sum fun x _ ↦ le_order_pow_of_constantCoeff_eq_zero (d x) (hZ x)
    _ ≤ (∏ x ∈ d.support, Z x ^ d x).order := le_order_prod _ _

/-- Substitution of series `Z x` without constant term for finitely many variables `x` is continuous
in the topology of coefficientwise convergence. -/
lemma continuous_subst_of_constantCoeff_eq_zero [Finite σ] [TopologicalSpace R]
    [IsTopologicalRing R] {Z : σ → MvPowerSeries τ R} (hZ : ∀ x : σ, constantCoeff (Z x) = 0) :
    Continuous fun F : MvPowerSeries σ R ↦ F.subst Z := by
  -- Each coefficient of `F.subst Z` is a linear form in finitely many coefficients of `F`.
  have h_fin (n : ℕ) : {d : σ →₀ ℕ | d.degree ≤ n}.Finite := Finsupp.finite_of_degree_le n
  have h_coeff (m : τ →₀ ℕ) (F : MvPowerSeries σ R) : coeff m (F.subst Z) =
      ∑ d ∈ (h_fin m.degree).toFinset, coeff d F * coeff m (d.prod fun x k ↦ Z x ^ k) := by
    rw [coeff_subst (hasSubst_of_constantCoeff_zero hZ)]
    refine finsum_eq_sum_of_support_subset _ fun d hd ↦ ?_
    by_contra h_not_mem
    have h_lt : m.degree < d.degree := by simpa using h_not_mem
    have h_zero : coeff m (d.prod fun x k ↦ Z x ^ k) = 0 :=
      coeff_of_lt_order ((Nat.cast_lt.2 h_lt).trans_le (degree_le_order_prod_pow hZ d))
    exact hd (by simp only [h_zero, smul_zero])
  refine continuous_pi fun m ↦ (continuous_congr (h_coeff m)).2 ?_
  exact continuous_finsetSum _ fun d _ ↦ (continuous_coeff R d).mul continuous_const

/-- Partial differentiation of power series is continuous in the topology of coefficientwise
convergence. -/
lemma continuous_pderiv [TopologicalSpace R] [IsTopologicalRing R] (y : σ) :
    Continuous (pderiv y : MvPowerSeries σ R → MvPowerSeries σ R) := by
  refine continuous_pi fun d ↦ ?_
  change Continuous fun F : MvPowerSeries σ R ↦ coeff d (pderiv y F)
  simp only [coeff_pderiv]
  exact (continuous_coeff R _).mul continuous_const

/-- A family of power series is summable, in the topology of coefficientwise convergence, if for
each `n` only finitely many of its members have order at most `n`. -/
lemma summable_of_finite_order_le [TopologicalSpace R] {f : ι → MvPowerSeries σ R}
    (hf : ∀ n : ℕ, {i : ι | (f i).order ≤ n}.Finite) : Summable f :=
  summable_iff_summable_coeff.2 fun d ↦
    summable_of_hasFiniteSupport ((hf d.degree).subset fun _ hi ↦ order_le hi)

/-- The family `l e j • G e ^ p ^ j`, indexed by `e ∈ S` and `j ∈ ℕ`, is summable if `1 < p` and
each `G e` has order at least `p ^ e + 1`. -/
lemma summable_smul_pow_pow [TopologicalSpace R] {p : ℕ} (hp : 1 < p) {G : ℕ → MvPowerSeries σ R}
    (hG : ∀ e : ℕ, ((p ^ e + 1 : ℕ) : ℕ∞) ≤ (G e).order) (S : Set ℕ) (l : ℕ → ℕ → R) :
    Summable fun x : S × ℕ ↦ l x.1 x.2 • G x.1 ^ p ^ x.2 := by
  have h_fin (n : ℕ) : {x : S × ℕ | (x.1 : ℕ) ≤ n ∧ x.2 ≤ n}.Finite :=
    ((Set.finite_Iic n).preimage Subtype.val_injective.injOn).prod (Set.finite_Iic n)
  refine summable_of_finite_order_le fun n ↦ (h_fin n).subset ?_
  rintro ⟨⟨e, he⟩, j⟩ (hx : (l e j • G e ^ p ^ j).order ≤ n)
  have h_order : ((p ^ j * (p ^ e + 1) : ℕ) : ℕ∞) ≤ n :=
    calc ((p ^ j * (p ^ e + 1) : ℕ) : ℕ∞) = p ^ j • ((p ^ e + 1 : ℕ) : ℕ∞) := by simp [mul_add]
      _ ≤ p ^ j • (G e).order := by grw [hG e]
      _ ≤ (G e ^ p ^ j).order := by grw [← le_order_pow]
      _ ≤ n := le_order_smul.trans hx
  have h_degree : p ^ j * (p ^ e + 1) ≤ n := Nat.cast_le.1 h_order
  have he_lt : e < p ^ e := Nat.lt_pow_self hp
  have hj_lt : j < p ^ j := Nat.lt_pow_self hp
  exact ⟨show e ≤ n by nlinarith, show j ≤ n by nlinarith⟩

variable {p : ℕ} [Fact p.Prime]

/-- In the valuation ring of `ℂ_[p]` the element `x` divides `y` exactly if `‖y‖ ≤ ‖x‖`. -/
lemma dvd_iff_norm_le {x y : valRingCp p} : x ∣ y ↔ ‖(y : ℂ_[p])‖ ≤ ‖(x : ℂ_[p])‖ := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨z, rfl⟩
    simpa using mul_le_of_le_one_right (norm_nonneg _) z.property
  obtain rfl | hx := eq_or_ne x 0
  · simpa using h
  have h_div : ‖(y / x : ℂ_[p])‖ ≤ 1 := by simpa using div_le_one_of_le₀ h (norm_nonneg _)
  exact ⟨⟨y / x, h_div⟩, Subtype.ext (mul_div_cancel₀ _ (by simpa using hx)).symm⟩

/-- In the valuation ring of `ℂ_[p]` the sum of a convergent family of multiples of `π` is a
multiple of `π`. -/
lemma dvd_of_hasSum {π a : valRingCp p} {f : ι → valRingCp p} (h_sum : HasSum f a)
    (hf : ∀ i : ι, π ∣ f i) : π ∣ a := by
  have h_closed : IsClosed {y : valRingCp p | π ∣ y} := by
    simpa only [dvd_iff_norm_le] using isClosed_le continuous_subtype_val.norm continuous_const
  exact h_closed.mem_of_tendsto h_sum (.of_forall fun t ↦ Finset.dvd_sum fun i _ ↦ hf i)

/-- A convergent sum of power series over the valuation ring `valRingCp p` of `ℂ_[p]`, each
divisible by the constant `π`, is divisible by `π`. -/
lemma C_dvd_of_hasSum {π : valRingCp p} {F : MvPowerSeries σ (valRingCp p)}
    {f : ι → MvPowerSeries σ (valRingCp p)} (h_sum : HasSum f F) (hf : ∀ i : ι, C π ∣ f i) :
    C π ∣ F :=
  C_dvd_iff_forall_dvd_coeff.2 fun d ↦ dvd_of_hasSum (hasSum_iff_hasSum_coeff.1 h_sum d) fun i ↦
    C_dvd_iff_forall_dvd_coeff.1 (hf i) d

end New

end SeriesCongruences

/-! ## Congruences in one variable -/

section OneVariable

open PowerSeries

namespace New

lemma C_dvd_iff_dvd_coeff {R : Type*} [CommRing R] {π : R} {F : R⟦X⟧} :
    C π ∣ F ↔ ∀ n : ℕ, π ∣ coeff n F := by
  refine C_dvd_iff_forall_dvd_coeff.trans ⟨fun h n ↦ h (Finsupp.single () n), fun h m ↦ ?_⟩
  -- A multi-index `m` in one variable is the degree `m ()`.
  simpa only [coeff_def (s := m) rfl] using h (m ())

/-- If `F ≡ l G` and `G ≡ H` modulo `D`, then `F ≡ l H` modulo `D`. -/
lemma dvd_sub_smul_of_dvd_sub {R : Type*} [CommRing R] {l : R} {D F G H : R⟦X⟧}
    (hF : D ∣ F - l • G) (hG : D ∣ G - H) : D ∣ F - l • H := by
  have h_eq : F - l • H = (F - l • G) + l • (G - H) := by module
  rw [h_eq, smul_eq_C_mul (G - H)]
  exact hF.add (hG.mul_left _)

/-- In `ℂ_[p]` let `‖t‖ ≤ ‖π‖ < 1` and `‖a‖ ≤ 1`. If `(1 - t) x ≡ a` modulo `π`, then `x ≡ a` modulo
`π`, where `y ≡ y'` means `‖y - y'‖ ≤ ‖π‖`. -/
lemma norm_sub_le_of_norm_one_sub_mul_sub_le {p : ℕ} [Fact p.Prime] {π t x a : ℂ_[p]}
    (hπ : ‖π‖ < 1) (ht : ‖t‖ ≤ ‖π‖) (ha : ‖a‖ ≤ 1) (hx : ‖(1 - t) * x - a‖ ≤ ‖π‖) :
    ‖x - a‖ ≤ ‖π‖ := by
  have h_lt : ‖-t‖ < ‖(1 : ℂ_[p])‖ := by simpa using ht.trans_lt hπ
  have h_unit : ‖1 - t‖ = 1 := by
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_lt.ne',
      max_eq_left h_lt.le, norm_one]
  have h_mul : ‖t * a‖ ≤ ‖π‖ := by grw [norm_mul, ha, mul_one, ht]
  calc ‖x - a‖ = ‖(1 - t) * (x - a)‖ := by rw [norm_mul, h_unit, one_mul]
    _ = ‖((1 - t) * x - a) + t * a‖ := by ring_nf
    _ ≤ ‖π‖ := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx h_mul)

end New

end OneVariable
