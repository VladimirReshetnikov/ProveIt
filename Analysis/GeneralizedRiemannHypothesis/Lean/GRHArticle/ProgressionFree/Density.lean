import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Densities of finite prime-exponent conditions

The counting limit uses the positive integers at most the cutoff. Exact fixed
valuation conditions have the product density of their local geometric masses.
-/

open Filter
open scoped BigOperators Topology

namespace GRHArticle.ProgressionFree

/-- Number of positive integers in `s` at most `N`. -/
noncomputable def countUpTo (s : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).filter (· ∈ s)).card

/-- Proportion of the positive integers at most `N` that lie in `s`. -/
noncomputable def densityUpTo (s : Set ℕ) (N : ℕ) : ℝ :=
  (countUpTo s N : ℝ) / (N : ℝ)

/-- The count of elements in `s` up to the cutoff, divided by that cutoff, tends to `d`. -/
def HasNaturalDensity (s : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (densityUpTo s) atTop (𝓝 d)

theorem countUpTo_dvd (d N : ℕ) (hd : 0 < d) :
    countUpTo {n | d ∣ n} N = N / d := by
  classical
  have hcard :
      (Finset.Icc 1 (N / d)).card = ((Finset.Icc 1 N).filter (fun n => d ∣ n)).card := by
    apply Finset.card_bij (fun k _ => d * k)
    · intro k hk
      obtain ⟨hk₁, hk₂⟩ := Finset.mem_Icc.mp hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨Nat.succ_le_of_lt (Nat.mul_pos hd hk₁),
          mul_comm k d ▸ (Nat.le_div_iff_mul_le hd).mp hk₂⟩, ⟨k, rfl⟩⟩
    · intro a _ b _ h
      exact Nat.eq_of_mul_eq_mul_left hd h
    · intro n hn
      obtain ⟨hi, k, rfl⟩ := Finset.mem_filter.mp hn
      obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hi
      refine ⟨k, Finset.mem_Icc.mpr ⟨?_, (Nat.le_div_iff_mul_le hd).mpr ?_⟩, rfl⟩
      · by_contra h
        have hk : k = 0 := by omega
        simp [hk] at hlo
      · simpa only [mul_comm k d] using hhi
  have hi : (Finset.Icc 1 (N / d)).card = N / d := by simp [Nat.card_Icc]
  calc
    countUpTo {n | d ∣ n} N = ((Finset.Icc 1 N).filter (fun n => d ∣ n)).card := by
      unfold countUpTo
      congr 1
      ext n
      simp
    _ = _ := hcard.symm.trans hi

private theorem tendsto_nat_div_ratio (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => ((N / d : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 (1 / (d : ℝ))) := by
  have hd₀ : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  apply Filter.Tendsto.congr'
  case f₁ => exact fun N : ℕ => (1 - ((N % d : ℕ) : ℝ) / (N : ℝ)) / (d : ℝ)
  · refine (eventually_ne_atTop 0).mono fun N hN => ?_
    have hN₀ : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    have h := congrArg (fun n : ℕ => (n : ℝ)) (Nat.mod_add_div N d)
    push_cast at h
    field_simp [hN₀, hd₀]
    linarith only [h]
  · simpa only [sub_zero] using
      (tendsto_const_nhds.sub (tendsto_mod_div_atTop_nhds_zero_nat hd)).div_const (d : ℝ)

/-- Multiples of a positive integer `d` have natural density `1 / d`. -/
theorem hasNaturalDensity_dvd (d : ℕ) (hd : 0 < d) :
    HasNaturalDensity {n | d ∣ n} (1 / (d : ℝ)) := by
  apply (tendsto_nat_div_ratio d hd).congr
  intro N
  rw [densityUpTo, countUpTo_dvd d N hd]

/-- The positive integers with exact exponents `e p` at the primes in `S`. -/
def valuationCylinder (S : Finset ℕ) (e : ℕ → ℕ) : Set ℕ :=
  {n | n ≠ 0 ∧ ∀ p ∈ S, n.factorization p = e p}

open Classical in
private theorem cast_countUpTo_eq_sum (s : Set ℕ) (N : ℕ) :
    (countUpTo s N : ℝ) = ∑ n ∈ Finset.Icc 1 N, if n ∈ s then 1 else 0 := by
  classical
  rw [countUpTo, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  simp only [Nat.cast_one]

private theorem prod_indicator_forall {ι : Type*} (s : Finset ι) (P : ι → Prop)
    [DecidablePred P] :
    (∏ x ∈ s, if P x then (1 : ℝ) else 0) = if ∀ x ∈ s, P x then 1 else 0 := by
  classical
  split_ifs with h
  · exact Finset.prod_eq_one fun x hx => if_pos (h x hx)
  · push Not at h
    obtain ⟨x, hx, hP⟩ := h
    exact Finset.prod_eq_zero hx (if_neg hP)

private theorem prod_sub_eq_sum_ite {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f g : ι → ℝ) :
    ∏ x ∈ s, (f x - g x) =
      ∑ T ∈ s.powerset, (-1 : ℝ) ^ T.card * ∏ x ∈ s, if x ∈ T then g x else f x := by
  rw [Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro T hT
  have hTs : T ⊆ s := Finset.mem_powerset.mp hT
  have hfilter : s.filter (· ∈ T) = T := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hx => ⟨hTs hx, hx⟩⟩
  have hfilterNot : s.filter (· ∉ T) = s \ T := by
    ext x
    simp
  rw [Finset.prod_ite, hfilter, hfilterNot]
  ac_rfl

private theorem prod_prime_powers_dvd_iff (S : Finset ℕ) (e : ℕ → ℕ)
    (hS : ∀ p ∈ S, p.Prime) (n : ℕ) :
    (∏ p ∈ S, p ^ e p) ∣ n ↔ ∀ p ∈ S, p ^ e p ∣ n := by
  constructor
  · exact fun h p hp => (Finset.dvd_prod_of_mem (fun q => q ^ e q) hp).trans h
  · intro h
    apply Finset.prod_dvd_of_isRelPrime _ h
    intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((((Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq).pow_left _).pow_right _)

private theorem local_exponent_indicator {n p e : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    (if n.factorization p = e then (1 : ℝ) else 0) =
      (if p ^ e ∣ n then 1 else 0) - (if p ^ (e + 1) ∣ n then 1 else 0) := by
  simp only [hp.pow_dvd_iff_le_factorization hn]
  split_ifs <;> norm_num <;> omega

private def shiftedPrimePowerProduct (S T : Finset ℕ) (e : ℕ → ℕ) : ℕ :=
  ∏ p ∈ S, p ^ (if p ∈ T then e p + 1 else e p)

private theorem shiftedPrimePowerProduct_pos (S T : Finset ℕ) (e : ℕ → ℕ)
    (hS : ∀ p ∈ S, p.Prime) : 0 < shiftedPrimePowerProduct S T e := by
  exact Finset.prod_pos fun p hp => pow_pos (hS p hp).pos _

open Classical in
private theorem valuationCylinder_indicator (S : Finset ℕ) (e : ℕ → ℕ)
    (hS : ∀ p ∈ S, p.Prime) {n : ℕ} (hn : n ≠ 0) :
    (if n ∈ valuationCylinder S e then (1 : ℝ) else 0) =
      ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card *
        if shiftedPrimePowerProduct S T e ∣ n then 1 else 0 := by
  classical
  have hlocal :
      (if n ∈ valuationCylinder S e then (1 : ℝ) else 0) =
        ∏ p ∈ S, ((if p ^ e p ∣ n then (1 : ℝ) else 0) -
          (if p ^ (e p + 1) ∣ n then 1 else 0)) := by
    have hmem : n ∈ valuationCylinder S e ↔ ∀ p ∈ S, n.factorization p = e p :=
      ⟨fun h => h.2, fun h => ⟨hn, h⟩⟩
    rw [if_congr hmem rfl rfl, ← prod_indicator_forall]
    exact Finset.prod_congr rfl fun p hp => local_exponent_indicator hn (hS p hp)
  rw [hlocal, prod_sub_eq_sum_ite]
  apply Finset.sum_congr rfl
  intro T _
  congr 1
  unfold shiftedPrimePowerProduct
  simp only [prod_prime_powers_dvd_iff S _ hS]
  rw [← prod_indicator_forall]
  apply Finset.prod_congr rfl
  intro p _
  by_cases h : p ∈ T <;> simp [h]

private theorem cast_countUpTo_valuationCylinder (S : Finset ℕ) (e : ℕ → ℕ)
    (hS : ∀ p ∈ S, p.Prime) (N : ℕ) :
    (countUpTo (valuationCylinder S e) N : ℝ) =
      ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card *
        (countUpTo {n | shiftedPrimePowerProduct S T e ∣ n} N : ℝ) := by
  classical
  rw [cast_countUpTo_eq_sum]
  calc
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card *
        if shiftedPrimePowerProduct S T e ∣ n then 1 else 0 := by
      exact Finset.sum_congr rfl fun n hn =>
        valuationCylinder_indicator S e hS (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro T _
      simp only [cast_countUpTo_eq_sum, Finset.mul_sum, Set.mem_setOf_eq]
      apply Finset.sum_congr rfl
      intro n _
      by_cases h : shiftedPrimePowerProduct S T e ∣ n <;> simp [h]

private theorem sum_reciprocal_prime_power_products (S : Finset ℕ) (e : ℕ → ℕ) :
    ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * (1 / (shiftedPrimePowerProduct S T e : ℝ)) =
      ∏ p ∈ S, (1 - 1 / (p : ℝ)) * (1 / (p : ℝ)) ^ e p := by
  let u (p : ℕ) : ℝ := 1 / (p : ℝ)
  calc
    _ = ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card *
        ∏ p ∈ S, if p ∈ T then u p ^ (e p + 1) else u p ^ e p := by
      apply Finset.sum_congr rfl
      intro T _
      congr 1
      simp only [shiftedPrimePowerProduct, one_div, Nat.cast_prod, Nat.cast_pow]
      rw [← Finset.prod_inv_distrib]
      apply Finset.prod_congr rfl
      intro p _
      by_cases h : p ∈ T <;> simp [h, u, one_div]
    _ = ∏ p ∈ S, (u p ^ e p - u p ^ (e p + 1)) := (prod_sub_eq_sum_ite S _ _).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p _
      change u p ^ e p - u p ^ (e p + 1) = (1 - u p) * u p ^ e p
      rw [pow_succ]
      ring

/-- A fixed valuation cylinder has the product of the exact geometric masses
at its finitely many primes. -/
theorem hasNaturalDensity_valuationCylinder (S : Finset ℕ) (e : ℕ → ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    HasNaturalDensity (valuationCylinder S e)
      (∏ p ∈ S, (1 - 1 / (p : ℝ)) * (1 / (p : ℝ)) ^ e p) := by
  have hlimits := tendsto_finsetSum S.powerset fun T _ =>
    (hasNaturalDensity_dvd (shiftedPrimePowerProduct S T e)
      (shiftedPrimePowerProduct_pos S T e hS)).const_mul ((-1 : ℝ) ^ T.card)
  rw [sum_reciprocal_prime_power_products] at hlimits
  apply hlimits.congr
  intro N
  unfold densityUpTo
  rw [cast_countUpTo_valuationCylinder S e hS N]
  simp only [div_eq_mul_inv, Finset.sum_mul, mul_assoc]

/-- The positive integers whose valuation tuple belongs to a finite family of
patterns on the prime set `S`. -/
def valuationPatterns (S : Finset ℕ) (P : Finset (↥S → ℕ)) : Set ℕ :=
  {n | n ≠ 0 ∧ (fun p : ↥S => n.factorization p.val) ∈ P}

private def extendPattern (S : Finset ℕ) (e : ↥S → ℕ) (p : ℕ) : ℕ :=
  if hp : p ∈ S then e ⟨p, hp⟩ else 0

private theorem mem_valuationCylinder_extendPattern (S : Finset ℕ) (e : ↥S → ℕ) {n : ℕ}
    (hn : n ≠ 0) :
    n ∈ valuationCylinder S (extendPattern S e) ↔ e = fun p : ↥S => n.factorization p.val := by
  constructor
  · intro h
    funext p
    simpa only [extendPattern, dif_pos p.property] using (h.2 p.val p.property).symm
  · intro h
    refine ⟨hn, fun p hp => ?_⟩
    rw [extendPattern, dif_pos hp, congrFun h ⟨p, hp⟩]

private theorem cast_countUpTo_valuationPatterns (S : Finset ℕ) (P : Finset (↥S → ℕ)) (N : ℕ) :
    (countUpTo (valuationPatterns S P) N : ℝ) =
      ∑ e ∈ P, (countUpTo (valuationCylinder S (extendPattern S e)) N : ℝ) := by
  classical
  simp_rw [cast_countUpTo_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  have hpos : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
  have hmem : n ∈ valuationPatterns S P ↔ (fun p : ↥S => n.factorization p.val) ∈ P :=
    ⟨fun h => h.2, fun h => ⟨hpos, h⟩⟩
  simp only [hmem, mem_valuationCylinder_extendPattern S _ hpos, Finset.sum_ite_eq']

/-- A finite disjoint union of valuation cylinders has density given by the
sum of its product weights. -/
theorem hasNaturalDensity_valuationPatterns (S : Finset ℕ) (P : Finset (↥S → ℕ))
    (hS : ∀ p ∈ S, p.Prime) :
    HasNaturalDensity (valuationPatterns S P)
      (∑ e ∈ P, ∏ p : ↥S, (1 - 1 / (p.val : ℝ)) * (1 / (p.val : ℝ)) ^ e p) := by
  have h := tendsto_finsetSum P fun e _ => hasNaturalDensity_valuationCylinder S (extendPattern S e) hS
  have hweights (e : ↥S → ℕ) :
      (∏ p ∈ S, (1 - 1 / (p : ℝ)) * (1 / (p : ℝ)) ^ extendPattern S e p) =
        ∏ p : ↥S, (1 - 1 / (p.val : ℝ)) * (1 / (p.val : ℝ)) ^ e p := by
    rw [Finset.univ_eq_attach, ← Finset.prod_attach S
      (fun p : ℕ => (1 - 1 / (p : ℝ)) * (1 / (p : ℝ)) ^ extendPattern S e p)]
    exact Finset.prod_congr rfl fun p _ => by simp only [extendPattern, dif_pos p.property]
  simp_rw [hweights] at h
  apply h.congr
  intro N
  unfold densityUpTo
  rw [cast_countUpTo_valuationPatterns]
  simp only [div_eq_mul_inv, Finset.sum_mul]

/-- For finitely many primes and finitely many allowed exponents at each, the
local geometric masses multiply. -/
theorem hasNaturalDensity_finite_prime_rules (S : Finset ℕ) (A : ↥S → Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    HasNaturalDensity {n | n ≠ 0 ∧ ∀ p : ↥S, n.factorization p.val ∈ A p}
      (∏ p : ↥S, (1 - 1 / (p.val : ℝ)) * ∑ e ∈ A p, (1 / (p.val : ℝ)) ^ e) := by
  have h := hasNaturalDensity_valuationPatterns S (Fintype.piFinset A) hS
  have hset : valuationPatterns S (Fintype.piFinset A) =
      {n | n ≠ 0 ∧ ∀ p : ↥S, n.factorization p.val ∈ A p} := by
    ext n
    simp only [valuationPatterns, Set.mem_setOf_eq, Fintype.mem_piFinset]
  rw [hset, ← Finset.prod_univ_sum A (fun (p : ↥S) (e : ℕ) =>
    (1 - 1 / (p.val : ℝ)) * (1 / (p.val : ℝ)) ^ e)] at h
  simpa only [Finset.mul_sum] using h

end GRHArticle.ProgressionFree
