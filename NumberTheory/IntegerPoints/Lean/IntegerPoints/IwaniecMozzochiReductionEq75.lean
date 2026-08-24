import IntegerPoints.IwaniecMozzochi
import IntegerPoints.KuzminLandau
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.PSeries

/-!
# Iwaniec--Mozzochi: the reduction from (7.2)--(7.4) to (7.5)

This file isolates the formal bookkeeping needed between Poisson summation and
the long-Farey-cell estimate.  There are two small but important convention
boundaries.

* At integral arguments the trapezoid in (7.2) is the indicator of the
  **inclusive** interval `[L₁, L₂]`.  The sum in (7.5) is over
  `[L₁, L₂)`, so the endpoint `L₂` must be removed explicitly.
* The `finsum` in `psiH` is supported on the complete real-scale shell
  `intRange H (4 * H)`, not merely on a shell whose endpoints happen to be
  integral.

The lemmas below discharge those two boundaries and record the exact
reciprocal-phase factorisation used before applying (7.2).  The remaining
part of the reduction is the quantitative summation argument: average the
Poisson dual sums over the coprime residue classes, dominate the
`min (c / |k|) (c^2 / k^2)` tail by a summable `6/5`-power interpolation,
and absorb the resulting `c^(1/5) + 1` loss on the long-cell range
`c <= mu₀ G`.

The final theorem deliberately has exactly the scope of the present
`iwaniecMozzochi_eq75` statement: its cell centre is assumed to lie in
`InFareySet`.  No claim about boundary Farey cells in an earlier global
decomposition is hidden in this local reduction.
-/

open scoped BigOperators
open Real Finset Set

namespace LeanProofs.IntegerPoints

namespace IMReductionEq75

/-! ## The integral trapezoid is an inclusive-interval indicator -/

/-- At an integer in `[L₁, L₂]`, the trapezoid has value one. -/
theorem trapezoid_int_eq_one {L₁ L₂ l : ℤ} (hl₁ : L₁ ≤ l) (hl₂ : l ≤ L₂) :
    trapezoid L₁ L₂ l = 1 := by
  have hleft : (0 : ℝ) ≤ (l : ℝ) - L₁ := by exact_mod_cast sub_nonneg.mpr hl₁
  have hright : (0 : ℝ) ≤ (L₂ : ℝ) - l := by exact_mod_cast sub_nonneg.mpr hl₂
  unfold trapezoid
  rw [min_eq_right hright, min_eq_right hleft]
  norm_num

/-- To the left of the integral interval, the trapezoid vanishes. -/
theorem trapezoid_int_eq_zero_of_lt {L₁ L₂ l : ℤ} (hl : l < L₁) :
    trapezoid L₁ L₂ l = 0 := by
  have hgap : (l : ℝ) - L₁ ≤ -1 := by exact_mod_cast (show l - L₁ ≤ -1 by omega)
  unfold trapezoid
  rw [max_eq_left]
  linarith [min_le_left ((l : ℝ) - L₁) (min ((L₂ : ℝ) - l) 0)]

/-- To the right of the integral interval, the trapezoid vanishes. -/
theorem trapezoid_int_eq_zero_of_gt {L₁ L₂ l : ℤ} (hl : L₂ < l) :
    trapezoid L₁ L₂ l = 0 := by
  have hgap : (L₂ : ℝ) - l ≤ -1 := by exact_mod_cast (show L₂ - l ≤ -1 by omega)
  unfold trapezoid
  rw [max_eq_left]
  have hinner : min ((L₂ : ℝ) - l) 0 ≤ (L₂ : ℝ) - l := min_le_left _ _
  have houter :
      min ((l : ℝ) - L₁) (min ((L₂ : ℝ) - l) 0) ≤
        min ((L₂ : ℝ) - l) 0 := min_le_right _ _
  linarith

/-- Integral samples of the trapezoid vanish off `Finset.Icc L₁ L₂`. -/
theorem trapezoid_int_eq_zero_of_not_mem {L₁ L₂ l : ℤ}
    (hl : l ∉ Finset.Icc L₁ L₂) : trapezoid L₁ L₂ l = 0 := by
  simp only [Finset.mem_Icc, not_and_or, not_le] at hl
  exact hl.elim trapezoid_int_eq_zero_of_lt trapezoid_int_eq_zero_of_gt

/-- Sampling the trapezoid at all integers gives exactly the finite inclusive
sum.  This is the endpoint convention hidden in the left side of (7.2). -/
theorem finsum_trapezoid_eq_sum_Icc (L₁ L₂ : ℤ) (q : ℤ → ℂ) :
    ∑ᶠ l : ℤ, (trapezoid L₁ L₂ l : ℂ) * q l =
      ∑ l ∈ Finset.Icc L₁ L₂, q l := by
  let f : ℤ → ℂ := fun l => (trapezoid L₁ L₂ l : ℂ) * q l
  have hsupp : Function.support f ⊆ (Finset.Icc L₁ L₂ : Set ℤ) := by
    intro l hl
    by_contra hmem
    have hz : trapezoid L₁ L₂ l = 0 := trapezoid_int_eq_zero_of_not_mem hmem
    exact hl (by simp [f, hz])
  change ∑ᶠ l : ℤ, f l = _
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  refine Finset.sum_congr rfl fun l hl => ?_
  dsimp only [f]
  have hlBounds : L₁ ≤ l ∧ l ≤ L₂ := Finset.mem_Icc.mp hl
  rw [trapezoid_int_eq_one hlBounds.1 hlBounds.2]
  simp

/-- The left side of (7.2), rewritten as the literal inclusive exponential
sum. -/
theorem eq72_as_inclusive_sum (h72 : iwaniecMozzochi_eq72)
    (x m v : ℝ) (a c h : ℕ) (L₁ L₂ : ℤ)
    (hx : 0 < x) (hh : 0 < h) (hm : 0 < m) (hv₀ : 0 ≤ v) (hv₁ : v < 1)
    (hc : 1 ≤ c) (hL : L₁ < L₂) (hpole : -m < (L₁ : ℝ) - 1) :
    ∑ l ∈ Finset.Icc L₁ L₂,
        e (-((a : ℝ) * h * l / c) + rPhase x h m v l) =
      ∑' k : ℤ, if k ≡ -((a : ℤ) * (h : ℤ)) [ZMOD (c : ℤ)] then
        trapezoidIntegral x h m v L₁ L₂ c k else 0 := by
  have hEq := h72 x m v a c h L₁ L₂ hx (by exact_mod_cast hh) hm hv₀ hv₁ hc hL hpole
  rw [finsum_trapezoid_eq_sum_Icc] at hEq
  exact hEq

/-- Removing the right endpoint converts the inclusive sum supplied by
(7.2) into the half-open sum used in (7.5). -/
theorem sum_Ico_eq_sum_Icc_sub_endpoint {E : Type*} [AddCommGroup E]
    (f : ℤ → E) {L₁ L₂ : ℤ} (hL : L₁ < L₂) :
    ∑ l ∈ Finset.Ico L₁ L₂, f l =
      (∑ l ∈ Finset.Icc L₁ L₂, f l) - f L₂ := by
  have hsum :
      (∑ l ∈ Finset.Icc L₁ L₂, f l) =
        f L₂ + ∑ l ∈ Finset.Ico L₁ L₂, f l := by
    rw [← Finset.Ico_insert_right hL.le,
      Finset.sum_insert Finset.right_notMem_Ico]
  rw [hsum]
  abel

/-! ## Exact reciprocal-phase algebra -/

/-- The algebraic identity behind (7.1).  It is deliberately stated with a
generic coefficient `q`; the Farey geometry later supplies
`q = x / (m + v)^2 = a / c`. -/
theorem reciprocal_phase_identity {x h m v l q : ℝ}
    (hm : m ≠ 0) (hmv : m + v ≠ 0) (hml : m + l ≠ 0)
    (hq : q = x / (m + v) ^ 2) :
    x * h / (m + l) = x * h / m - q * h * l + rPhase x h m v l := by
  subst q
  unfold rPhase
  field_simp [hm, hmv, hml]
  all_goals ring

/-- Version of `reciprocal_phase_identity` with the Farey coefficient written
as `a / c`. -/
theorem reciprocal_phase_identity_of_farey {x h m v l a c : ℝ}
    (hm : m ≠ 0) (hmv : m + v ≠ 0) (hml : m + l ≠ 0)
    (hfarey : x / (m + v) ^ 2 = a / c) :
    x * h / (m + l) =
      x * h / m - a * h * l / c + rPhase x h m v l := by
  have hid := reciprocal_phase_identity (h := h) hm hmv hml hfarey.symm
  convert hid using 1
  all_goals ring

/-- Combining the exact phase identity with (7.2) gives the half-open
Poisson formula, including the missing endpoint term.  The hypotheses are
kept algebraic so that the later Farey-geometry lemma has one precise target. -/
theorem eq72_halfOpen_sum (h72 : iwaniecMozzochi_eq72)
    (x m v : ℝ) (a c h : ℕ) (L₁ L₂ : ℤ)
    (hx : 0 < x) (hh : 0 < h) (hm : 0 < m) (hv₀ : 0 ≤ v) (hv₁ : v < 1)
    (hc : 1 ≤ c) (hL : L₁ < L₂) (hpole : -m < (L₁ : ℝ) - 1)
    (hfarey : x / (m + v) ^ 2 = (a : ℝ) / c) :
    ∑ l ∈ Finset.Ico L₁ L₂, e (x * h / (m + l)) =
      e (x * h / m) *
        ((∑' k : ℤ, if k ≡ -((a : ℤ) * (h : ℤ)) [ZMOD (c : ℤ)] then
            trapezoidIntegral x h m v L₁ L₂ c k else 0) -
          e (-((a : ℝ) * h * L₂ / c) + rPhase x h m v L₂)) := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hmv0 : m + v ≠ 0 := by positivity
  have hdenom (l : ℤ) (hl : l ∈ Finset.Icc L₁ L₂) : m + (l : ℝ) ≠ 0 := by
    have hlBounds : L₁ ≤ l ∧ l ≤ L₂ := Finset.mem_Icc.mp hl
    have hlower : (L₁ : ℝ) ≤ l := by exact_mod_cast hlBounds.1
    have : 0 < m + (l : ℝ) := by linarith
    exact ne_of_gt this
  have hphase (l : ℤ) (hl : l ∈ Finset.Icc L₁ L₂) :
      x * h / (m + l) = x * h / m +
        (-((a : ℝ) * h * l / c) + rPhase x h m v l) := by
    have hid := reciprocal_phase_identity_of_farey
      (h := (h : ℝ)) hm0 hmv0 (hdenom l hl) hfarey
    convert hid using 1
    all_goals ring
  have hinclusive := eq72_as_inclusive_sum h72 x m v a c h L₁ L₂
    hx hh hm hv₀ hv₁ hc hL hpole
  calc
    ∑ l ∈ Finset.Ico L₁ L₂, e (x * h / (m + l)) =
        (∑ l ∈ Finset.Icc L₁ L₂, e (x * h / (m + l))) -
          e (x * h / (m + L₂)) :=
      sum_Ico_eq_sum_Icc_sub_endpoint _ hL
    _ = e (x * h / m) *
        (∑ l ∈ Finset.Icc L₁ L₂,
          e (-((a : ℝ) * h * l / c) + rPhase x h m v l)) -
          e (x * h / m) *
            e (-((a : ℝ) * h * L₂ / c) + rPhase x h m v L₂) := by
      rw [Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun l hl => ?_
        rw [← KL.e_add, ← hphase l hl]
      · rw [← KL.e_add, ← hphase L₂ (by simp [hL.le])]
    _ = e (x * h / m) *
        ((∑' k : ℤ, if k ≡ -((a : ℤ) * (h : ℤ)) [ZMOD (c : ℤ)] then
            trapezoidIntegral x h m v L₁ L₂ c k else 0) -
          e (-((a : ℝ) * h * L₂ / c) + rPhase x h m v L₂)) := by
      rw [hinclusive]
      ring

/-! ## The complete real-scale Fourier shell -/

/-- The support axioms turn `psiH` into the literal shell
`intRange H (4 * H)` for every positive real scale `H`. -/
theorem psiH_eq_intRange {chi : ℝ → ℝ} (hchi : IsDyadicPartition chi)
    {H : ℝ} (hH : 0 < H) (t : ℝ) :
    psiH chi H t =
      ∑ h ∈ intRange H (4 * H),
        chi (h / H) * Real.sin (2 * Real.pi * h * t) / (Real.pi * h) := by
  let f : ℕ → ℝ := fun h =>
    chi (h / H) * Real.sin (2 * Real.pi * h * t) / (Real.pi * h)
  have hsupp : Function.support f ⊆ (intRange H (4 * H) : Set ℕ) := by
    intro h hh
    have hchine : chi (h / H) ≠ 0 := by
      intro hz
      apply hh
      simp [f, hz]
    have hlower : H < (h : ℝ) := by
      by_contra hnlt
      have harg : (h : ℝ) / H ≤ 1 := (div_le_one hH).2 (le_of_not_gt hnlt)
      exact hchine (hchi.2.2.2.2 _ harg)
    have hupper : (h : ℝ) ≤ 4 * H := by
      by_contra hnle
      have harg : (4 : ℝ) ≤ (h : ℝ) / H := by
        rw [le_div_iff₀ hH]
        exact le_of_not_ge hnle
      exact hchine (hchi.2.1 _ harg)
    rw [intRange, Finset.mem_coe, Finset.mem_Ioc]
    exact ⟨(Nat.floor_lt hH.le).2 hlower, (Nat.le_floor_iff (by positivity)).2 hupper⟩
  unfold psiH
  change finsum f = _
  exact finsum_eq_sum_of_support_subset _ hsupp

/-- On the support shell `(1,4]`, every dyadic partition has absolute value
at most one. -/
theorem chi_abs_le_one {chi : ℝ → ℝ} (hchi : IsDyadicPartition chi)
    {u : ℝ} (hu₁ : 1 < u) (hu₄ : u ≤ 4) : |chi u| ≤ 1 := by
  by_cases hu₂ : u < 2
  · have htwoLower : (2 : ℝ) ≤ 2 * u := by linarith
    have htwoUpper : 2 * u < (4 : ℝ) := by linarith
    have htwice := hchi.2.2.1 (2 * u) htwoLower htwoUpper
    have hrec := hchi.2.2.2.1 u hu₁ hu₂.le
    rw [hrec, abs_of_nonneg (by linarith [htwice.2])]
    linarith [htwice.1, htwice.2]
  · have hu₂' : (2 : ℝ) ≤ u := le_of_not_gt hu₂
    rcases lt_or_eq_of_le hu₄ with hu₄lt | rfl
    · have hu := hchi.2.2.1 u hu₂' hu₄lt
      rw [abs_of_pos hu.1]
      exact hu.2
    · rw [hchi.2.1 4 le_rfl]
      norm_num

/-- Every frequency in the literal Fourier shell satisfies `H < h <= 4H`. -/
theorem mem_intRange_four_mul {H : ℝ} (hH : 0 < H) {h : ℕ}
    (hh : h ∈ intRange H (4 * H)) : H < (h : ℝ) ∧ (h : ℝ) ≤ 4 * H := by
  simp only [intRange, Finset.mem_Ioc] at hh
  have hupper : (h : ℝ) ≤ (⌊4 * H⌋₊ : ℝ) := by exact_mod_cast hh.2
  exact ⟨(Nat.floor_lt hH.le).1 hh.1,
    hupper.trans (Nat.floor_le (by positivity))⟩

/-- The Fourier coefficient on the support shell is bounded by `1 / (pi H)`. -/
theorem psiH_coefficient_abs_le {chi : ℝ → ℝ} (hchi : IsDyadicPartition chi)
    {H : ℝ} (hH : 0 < H) {h : ℕ} (hh : h ∈ intRange H (4 * H)) :
    |chi (h / H) / (Real.pi * h)| ≤ 1 / (Real.pi * H) := by
  obtain ⟨hhLower, hhUpper⟩ := mem_intRange_four_mul hH hh
  have hh₀ : (0 : ℝ) < h := hH.trans hhLower
  have hu₁ : (1 : ℝ) < (h : ℝ) / H := by
    rw [lt_div_iff₀ hH]
    simpa using hhLower
  have hu₄ : (h : ℝ) / H ≤ 4 := by
    rw [div_le_iff₀ hH]
    simpa [mul_comm] using hhUpper
  rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hh₀]
  calc
    |chi ((h : ℝ) / H)| / (Real.pi * h) ≤ 1 / (Real.pi * h) :=
      div_le_div_of_nonneg_right (chi_abs_le_one hchi hu₁ hu₄) (by positivity)
    _ ≤ 1 / (Real.pi * H) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_left hhLower.le Real.pi_pos.le

/-! ## Averaging the congruence classes -/

/-- Frequencies `h` in the Fourier shell whose Poisson dual variable lies in
the required residue class. -/
noncomputable def frequencyFiber (a c : ℕ) (H : ℝ) (k : ℤ) : Finset ℕ :=
  (intRange H (4 * H)).filter fun h =>
    k ≡ -((a : ℤ) * (h : ℤ)) [ZMOD (c : ℤ)]

/-- If `a` and `c` are coprime, two frequencies in the same Poisson fiber
are congruent modulo `c`. -/
theorem frequencyFiber_modEq {a c : ℕ} {H : ℝ} {k : ℤ}
    (hac : Nat.Coprime a c) {h₁ h₂ : ℕ}
    (hh₁ : h₁ ∈ frequencyFiber a c H k)
    (hh₂ : h₂ ∈ frequencyFiber a c H k) :
    h₁ ≡ h₂ [MOD c] := by
  rw [frequencyFiber, Finset.mem_filter] at hh₁ hh₂
  have hk₁ : (k : ZMod c) = -((a : ZMod c) * (h₁ : ZMod c)) := by
    have hk₁' : (k : ZMod c) =
        ((-((a : ℤ) * (h₁ : ℤ)) : ℤ) : ZMod c) :=
      (ZMod.intCast_eq_intCast_iff k (-((a : ℤ) * (h₁ : ℤ))) c).2 hh₁.2
    simpa only [Int.cast_neg, Int.cast_mul, Int.cast_natCast] using hk₁'
  have hk₂ : (k : ZMod c) = -((a : ZMod c) * (h₂ : ZMod c)) := by
    have hk₂' : (k : ZMod c) =
        ((-((a : ℤ) * (h₂ : ℤ)) : ℤ) : ZMod c) :=
      (ZMod.intCast_eq_intCast_iff k (-((a : ℤ) * (h₂ : ℤ))) c).2 hh₂.2
    simpa only [Int.cast_neg, Int.cast_mul, Int.cast_natCast] using hk₂'
  have hmul : (a : ZMod c) * (h₁ : ZMod c) = (a : ZMod c) * (h₂ : ZMod c) := by
    exact neg_inj.mp (hk₁.symm.trans hk₂)
  have haUnit : IsUnit (a : ZMod c) := (ZMod.isUnit_iff_coprime a c).2 hac
  exact (ZMod.natCast_eq_natCast_iff h₁ h₂ c).1 (haUnit.mul_left_cancel hmul)

/-- A Poisson residue class meets the full shell `(H,4H]` at most `5H/c`
times.  The proof uses the quotient `h / c`: congruence fixes the remainder,
so that quotient is injective on the fiber.  The constant five is deliberately
slack; it avoids any dependence on integral endpoints. -/
theorem frequencyFiber_card_le {a c : ℕ} {H : ℝ} {k : ℤ}
    (hH : 0 < H) (hc : 1 ≤ c) (hcH : (c : ℝ) ≤ H)
    (hac : Nat.Coprime a c) :
    ((frequencyFiber a c H k).card : ℝ) ≤ 5 * H / c := by
  classical
  let Q : ℕ := ⌊4 * H / c⌋₊
  have hc₀ : 0 < c := lt_of_lt_of_le Nat.zero_lt_one hc
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc₀
  have hmaps : Set.MapsTo (fun h : ℕ => h / c)
      (frequencyFiber a c H k : Set ℕ) (Finset.range (Q + 1) : Set ℕ) := by
    intro h hh
    change h ∈ frequencyFiber a c H k at hh
    rw [frequencyFiber, Finset.mem_filter] at hh
    have hhShell : h ∈ intRange H (4 * H) := hh.1
    have hhUpper := (mem_intRange_four_mul hH hhShell).2
    have hquot : ((h / c : ℕ) : ℝ) ≤ 4 * H / c := by
      exact Nat.cast_div_le.trans (div_le_div_of_nonneg_right hhUpper hcR.le)
    rw [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le ((Nat.le_floor_iff (by positivity)).2 hquot)
  have hinj : Set.InjOn (fun h : ℕ => h / c)
      (frequencyFiber a c H k : Set ℕ) := by
    intro h₁ hh₁ h₂ hh₂ hquot
    change h₁ ∈ frequencyFiber a c H k at hh₁
    change h₂ ∈ frequencyFiber a c H k at hh₂
    have hmod := frequencyFiber_modEq hac hh₁ hh₂
    rw [Nat.ModEq] at hmod
    change h₁ / c = h₂ / c at hquot
    calc
      h₁ = h₁ / c * c + h₁ % c := (Nat.div_add_mod' h₁ c).symm
      _ = h₂ / c * c + h₂ % c := by rw [hquot, hmod]
      _ = h₂ := Nat.div_add_mod' h₂ c
  have hcard : (frequencyFiber a c H k).card ≤ (Finset.range (Q + 1)).card :=
    Finset.card_le_card_of_injOn (fun h : ℕ => h / c) hmaps hinj
  calc
    ((frequencyFiber a c H k).card : ℝ) ≤
        ((Finset.range (Q + 1)).card : ℝ) := by exact_mod_cast hcard
    _ = (Q : ℝ) + 1 := by simp
    _ ≤ 4 * H / c + 1 := by
      have hfloor : (Q : ℝ) ≤ 4 * H / c :=
        Nat.floor_le (by positivity : 0 ≤ 4 * H / (c : ℝ))
      linarith
    _ ≤ 5 * H / c := by
      calc
        4 * H / c + 1 = (4 * H + c) / c := by
          field_simp [hcR.ne']
        _ ≤ 5 * H / c := (div_le_div_iff_of_pos_right hcR).2 (by nlinarith)

/-!
After `frequencyFiber_card_le`, the remaining analytic kernel is independent
of the arithmetic parameters: show that the majorant from (7.3)/(7.4) is
summable and has total mass

`O(A + c^(6/5))`, where
`A = (x * H * M^(-3))^(-1/2)`.

The finite `h`-sum can then be commuted with that summable `k`-sum, and the
preceding cardinality estimate contributes the required factor `1/c`.
-/

/-! ## A summable replacement for the logarithmic tail -/

/-- The high-frequency kernel in (7.3), without its absolute constant. -/
noncomputable def poissonTailKernel (c : ℝ) (k : ℤ) : ℝ :=
  min (c / |(k : ℝ)|) (c ^ 2 / (k : ℝ) ^ 2)

/-- The high-frequency kernel is pointwise nonnegative when `c` is. -/
theorem poissonTailKernel_nonneg {c : ℝ} (hc : 0 ≤ c) (k : ℤ) :
    0 ≤ poissonTailKernel c k := by
  unfold poissonTailKernel
  exact le_min
    (div_nonneg hc (abs_nonneg _))
    (div_nonneg (sq_nonneg c) (sq_nonneg (k : ℝ)))

/-- A fixed convergent `p`-series used to dominate the logarithmic kernel.
Using exponent `6/5`, rather than evaluating the harmonic split sharply,
costs only `c^(1/5)` after congruence averaging.  The main-range inequality
`c < x^(2/11)` leaves enough power saving to absorb that factor. -/
noncomputable def poissonTailConstant : ℝ :=
  ∑' k : ℤ, |(k : ℝ)| ^ (-((6 : ℝ) / 5))

/-- Interpolation between `c/|k|` and `c²/k²` gives a summable
`6/5`-power majorant. -/
theorem poissonTailKernel_le {c : ℝ} (hc : 0 < c) (k : ℤ) :
    poissonTailKernel c k ≤
      c ^ ((6 : ℝ) / 5) * |(k : ℝ)| ^ (-((6 : ℝ) / 5)) := by
  by_cases hk : k = 0
  · subst k
    simp [poissonTailKernel]
  · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have habs : 0 < |(k : ℝ)| := abs_pos.mpr hkR
    let u : ℝ := c / |(k : ℝ)|
    have hu : 0 < u := div_pos hc habs
    have hsquare : c ^ 2 / (k : ℝ) ^ 2 = u ^ 2 := by
      dsimp [u]
      rw [div_pow, sq_abs]
    have hinterp : min u (u ^ 2) ≤ u ^ ((6 : ℝ) / 5) := by
      by_cases hu₁ : u ≤ 1
      · calc
          min u (u ^ 2) ≤ u ^ 2 := min_le_right _ _
          _ = u ^ (2 : ℝ) := (Real.rpow_two u).symm
          _ ≤ u ^ ((6 : ℝ) / 5) :=
            Real.rpow_le_rpow_of_exponent_ge hu hu₁ (by norm_num)
      · have hu₁' : 1 ≤ u := le_of_not_ge hu₁
        calc
          min u (u ^ 2) ≤ u := min_le_left _ _
          _ = u ^ (1 : ℝ) := (Real.rpow_one u).symm
          _ ≤ u ^ ((6 : ℝ) / 5) :=
            Real.rpow_le_rpow_of_exponent_le hu₁' (by norm_num)
    calc
      poissonTailKernel c k = min u (u ^ 2) := by
        rw [poissonTailKernel, hsquare]
      _ ≤ u ^ ((6 : ℝ) / 5) := hinterp
      _ = c ^ ((6 : ℝ) / 5) * |(k : ℝ)| ^ (-((6 : ℝ) / 5)) := by
        dsimp [u]
        rw [Real.div_rpow hc.le (abs_nonneg _) ((6 : ℝ) / 5),
          Real.rpow_neg (abs_nonneg _)]
        ring

/-- The high-frequency kernel is summable over all integers. -/
theorem summable_poissonTailKernel {c : ℝ} (hc : 0 < c) :
    Summable (poissonTailKernel c) := by
  have hp : (1 : ℝ) < (6 : ℝ) / 5 := by norm_num
  have henv : Summable fun k : ℤ =>
      c ^ ((6 : ℝ) / 5) * |(k : ℝ)| ^ (-((6 : ℝ) / 5)) :=
    (Real.summable_abs_int_rpow hp).mul_left _
  exact henv.of_nonneg_of_le
    (poissonTailKernel_nonneg hc.le)
    (poissonTailKernel_le hc)

/-- The total high-frequency mass is bounded by the fixed `6/5`-series. -/
theorem tsum_poissonTailKernel_le {c : ℝ} (hc : 0 < c) :
    ∑' k : ℤ, poissonTailKernel c k ≤
      c ^ ((6 : ℝ) / 5) * poissonTailConstant := by
  have hp : (1 : ℝ) < (6 : ℝ) / 5 := by norm_num
  have htail := summable_poissonTailKernel hc
  have henv : Summable fun k : ℤ =>
      c ^ ((6 : ℝ) / 5) * |(k : ℝ)| ^ (-((6 : ℝ) / 5)) :=
    (Real.summable_abs_int_rpow hp).mul_left _
  calc
    ∑' k : ℤ, poissonTailKernel c k ≤
        ∑' k : ℤ, c ^ ((6 : ℝ) / 5) *
          |(k : ℝ)| ^ (-((6 : ℝ) / 5)) :=
      htail.tsum_le_tsum (poissonTailKernel_le hc) henv
    _ = c ^ ((6 : ℝ) / 5) * poissonTailConstant := by
      rw [poissonTailConstant, tsum_mul_left]

/-- The finitely many indices below the (7.3)/(7.4) cutoff. -/
noncomputable def poissonLowIndexSet (k₀ : ℝ) : Finset ℤ :=
  Finset.Icc (-((⌈k₀⌉₊ : ℕ) : ℤ)) ((⌈k₀⌉₊ : ℕ) : ℤ)

/-- Every integer with `|k| < k₀` belongs to the finite low-frequency
index set. -/
theorem mem_poissonLowIndexSet {k₀ : ℝ} (_hk₀ : 0 < k₀) {k : ℤ}
    (hk : |(k : ℝ)| < k₀) : k ∈ poissonLowIndexSet k₀ := by
  have hkceil : k₀ ≤ (⌈k₀⌉₊ : ℝ) := Nat.le_ceil k₀
  have hlowerR : -((⌈k₀⌉₊ : ℕ) : ℝ) ≤ (k : ℝ) := by
    linarith [neg_abs_le (k : ℝ)]
  have hupperR : (k : ℝ) ≤ ((⌈k₀⌉₊ : ℕ) : ℝ) := by
    linarith [le_abs_self (k : ℝ)]
  rw [poissonLowIndexSet, Finset.mem_Icc]
  constructor
  · exact_mod_cast hlowerR
  · exact_mod_cast hupperR

/-- The pointwise majorant supplied by (7.3)/(7.4). -/
noncomputable def poissonIntegralMajorant
    (A c k₀ C : ℝ) (k : ℤ) : ℝ :=
  if |(k : ℝ)| < k₀ then C * A else C * poissonTailKernel c k

/-- The complete (7.3)/(7.4) majorant is summable. -/
theorem summable_poissonIntegralMajorant
    {A c k₀ C : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (hk₀ : 0 < k₀) (hC : 0 ≤ C) :
    Summable (poissonIntegralMajorant A c k₀ C) := by
  let low : ℤ → ℝ := fun k =>
    if k ∈ poissonLowIndexSet k₀ then C * A else 0
  have hlow : Summable low := by
    apply summable_of_hasFiniteSupport
    exact (poissonLowIndexSet k₀).finite_toSet.subset (by
      intro k hk
      change low k ≠ 0 at hk
      change k ∈ poissonLowIndexSet k₀
      by_contra hmem
      exact hk (by simp [low, hmem]))
  have htail : Summable fun k : ℤ => C * poissonTailKernel c k :=
    (summable_poissonTailKernel hc).mul_left C
  have henv := hlow.add htail
  apply henv.of_nonneg_of_le
  · intro k
    by_cases hk : |(k : ℝ)| < k₀
    · rw [poissonIntegralMajorant, if_pos hk]
      exact mul_nonneg hC hA
    · rw [poissonIntegralMajorant, if_neg hk]
      exact mul_nonneg hC (poissonTailKernel_nonneg hc.le k)
  · intro k
    by_cases hk : |(k : ℝ)| < k₀
    · rw [poissonIntegralMajorant, if_pos hk]
      have hmem := mem_poissonLowIndexSet hk₀ hk
      simp only [low, hmem, if_true]
      exact le_add_of_nonneg_right
        (mul_nonneg hC (poissonTailKernel_nonneg hc.le k))
    · rw [poissonIntegralMajorant, if_neg hk]
      have hlowNonneg : 0 ≤ low k := by simp [low]; positivity
      linarith

/-- Total mass of the (7.3)/(7.4) majorant.  The first coefficient depends
only on the absolute cutoff `k₀`; the second is the fixed convergent
`6/5`-series. -/
theorem tsum_poissonIntegralMajorant_le
    {A c k₀ C : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (hk₀ : 0 < k₀) (hC : 0 ≤ C) :
    ∑' k : ℤ, poissonIntegralMajorant A c k₀ C k ≤
      ((poissonLowIndexSet k₀).card : ℝ) * (C * A) +
        C * (c ^ ((6 : ℝ) / 5) * poissonTailConstant) := by
  let low : ℤ → ℝ := fun k =>
    if k ∈ poissonLowIndexSet k₀ then C * A else 0
  let env : ℤ → ℝ := fun k => low k + C * poissonTailKernel c k
  have hmajorant := summable_poissonIntegralMajorant hA hc hk₀ hC
  have hlow : Summable low := by
    apply summable_of_hasFiniteSupport
    exact (poissonLowIndexSet k₀).finite_toSet.subset (by
      intro k hk
      change low k ≠ 0 at hk
      change k ∈ poissonLowIndexSet k₀
      by_contra hmem
      exact hk (by simp [low, hmem]))
  have htail : Summable fun k : ℤ => C * poissonTailKernel c k :=
    (summable_poissonTailKernel hc).mul_left C
  have henv : Summable env := by simpa [env] using hlow.add htail
  have hpoint : ∀ k, poissonIntegralMajorant A c k₀ C k ≤ env k := by
    intro k
    by_cases hk : |(k : ℝ)| < k₀
    · rw [poissonIntegralMajorant, if_pos hk]
      have hmem := mem_poissonLowIndexSet hk₀ hk
      simp only [env, low, hmem, if_true]
      exact le_add_of_nonneg_right
        (mul_nonneg hC (poissonTailKernel_nonneg hc.le k))
    · rw [poissonIntegralMajorant, if_neg hk]
      have hlowNonneg : 0 ≤ low k := by simp [low]; positivity
      simp only [env]
      linarith
  calc
    ∑' k : ℤ, poissonIntegralMajorant A c k₀ C k ≤ ∑' k : ℤ, env k :=
      hmajorant.tsum_le_tsum hpoint henv
    _ = (∑' k : ℤ, low k) + C * (∑' k : ℤ, poissonTailKernel c k) := by
      rw [show env = fun k => low k + C * poissonTailKernel c k by rfl,
        hlow.tsum_add htail, tsum_mul_left]
    _ ≤ ((poissonLowIndexSet k₀).card : ℝ) * (C * A) +
        C * (c ^ ((6 : ℝ) / 5) * poissonTailConstant) := by
      have hlowMass : (∑' k : ℤ, low k) =
          ((poissonLowIndexSet k₀).card : ℝ) * (C * A) := by
        rw [tsum_eq_sum (s := poissonLowIndexSet k₀)]
        · simp [low]
        · intro k hk
          simp [low, hk]
      rw [hlowMass]
      have htailMass :=
        mul_le_mul_of_nonneg_left (tsum_poissonTailKernel_le hc) hC
      linarith

/-! ## Long-cell absorption -/

/-- The fixed tail constant is nonnegative. -/
theorem poissonTailConstant_nonneg : 0 ≤ poissonTailConstant := by
  unfold poissonTailConstant
  exact tsum_nonneg fun k => Real.rpow_nonneg (abs_nonneg _) _

/-- Abstract form of the long-cell absorption used after congruence
averaging.  The hypotheses are exactly the two scale facts extracted from the
main range:

* `c <= x^(2/11)`, and
* `x^(1/22) G <= A`.

Together with `c <= mu₀ G`, they absorb both the endpoint correction and the
`c^(1/5)` loss from `poissonTailKernel_le` into `A/c`. -/
theorem longCell_absorbs_one_add_fifthPower
    {x c mu₀ A G : ℝ}
    (hx : 1 ≤ x) (hc : 1 ≤ c) (hmu₀ : 0 < mu₀)
    (hcPower : c ≤ x ^ ((2 : ℝ) / 11))
    (hAG : x ^ ((1 : ℝ) / 22) * G ≤ A)
    (hcG : c ≤ mu₀ * G) :
    1 + c ^ ((1 : ℝ) / 5) ≤ 2 * mu₀ * (A / c) := by
  have hx₀ : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hc₀ : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hmuNonneg : 0 ≤ mu₀ := hmu₀.le
  have hxSmallLe : x ^ ((2 : ℝ) / 55) ≤ x ^ ((1 : ℝ) / 22) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hcFifth : c ^ ((1 : ℝ) / 5) ≤ x ^ ((1 : ℝ) / 22) := by
    calc
      c ^ ((1 : ℝ) / 5) ≤ (x ^ ((2 : ℝ) / 11)) ^ ((1 : ℝ) / 5) :=
        Real.rpow_le_rpow hc₀.le hcPower (by norm_num)
      _ = x ^ ((2 : ℝ) / 55) := by
        rw [← Real.rpow_mul hx₀.le]
        congr 1
        norm_num
      _ ≤ x ^ ((1 : ℝ) / 22) := hxSmallLe
  have hscaleMul : x ^ ((1 : ℝ) / 22) * c ≤ mu₀ * A := by
    calc
      x ^ ((1 : ℝ) / 22) * c ≤
          x ^ ((1 : ℝ) / 22) * (mu₀ * G) :=
        mul_le_mul_of_nonneg_left hcG (Real.rpow_nonneg hx₀.le _)
      _ = mu₀ * (x ^ ((1 : ℝ) / 22) * G) := by ring
      _ ≤ mu₀ * A := mul_le_mul_of_nonneg_left hAG hmuNonneg
  have hxScale : x ^ ((1 : ℝ) / 22) ≤ mu₀ * (A / c) := by
    rw [← mul_div_assoc, le_div_iff₀ hc₀]
    simpa [mul_assoc] using hscaleMul
  have hOne : 1 ≤ mu₀ * (A / c) := by
    exact (Real.one_le_rpow hx (by norm_num)).trans hxScale
  have hFifth : c ^ ((1 : ℝ) / 5) ≤ mu₀ * (A / c) :=
    hcFifth.trans hxScale
  linarith

/-- The main and Farey ranges put every denominator below `x^(2/11)`.
This is the first scale input to `longCell_absorbs_one_add_fifthPower`. -/
theorem farey_denominator_le_twoElevenths
    {x H M : ℝ} {a c : ℕ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c) :
    (c : ℝ) ≤ x ^ ((2 : ℝ) / 11) := by
  rcases hmain with ⟨hx, hxM, hMx, hH, hHupper, hshift₁, hshift₂, hMlower⟩
  rcases hfarey with ⟨hc, hcH, hac, haLower, haUpper⟩
  have hx₀ : 0 < x := lt_of_lt_of_le zero_lt_one hx
  calc
    (c : ℝ) ≤ H := hcH
    _ ≤ M * x ^ (-theta0) := hHupper
    _ ≤ x ^ ((1 : ℝ) / 2) * x ^ (-theta0) := by
      exact (mul_lt_mul_of_pos_right hMx (Real.rpow_pos_of_pos hx₀ _)).le
    _ = x ^ ((2 : ℝ) / 11) := by
      rw [← Real.rpow_add hx₀]
      unfold theta0
      congr 1
      norm_num

/-! ## Farey-point geometry -/

/-- The elementary geometry hidden in the definitions of `fareyPoint` and
`fareyFrac`.  In the main/Farey ranges the centre is positive, its fractional
part lies in `[0,1)`, and the rational coefficient in the reciprocal phase is
exactly `a/c`. -/
theorem fareyPoint_geometry
    {x H M : ℝ} {a c : ℕ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c) :
    0 < fareyPoint x a c ∧
      0 ≤ fareyFrac x a c ∧ fareyFrac x a c < 1 ∧
      (fareyPoint x a c : ℝ) + fareyFrac x a c =
        Real.sqrt ((c : ℝ) * x / a) ∧
      x / ((fareyPoint x a c : ℝ) + fareyFrac x a c) ^ 2 =
        (a : ℝ) / c ∧
      M ≤ Real.sqrt ((c : ℝ) * x / a) ∧
      Real.sqrt ((c : ℝ) * x / a) ≤ 2 * M := by
  rcases hmain with ⟨hx, hxM, hMx, hH, hHupper, hshift₁, hshift₂, hMlower⟩
  rcases hfarey with ⟨hc, hcH, hac, haLower, haUpper⟩
  have hx₀ : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hcNat₀ : 0 < c := lt_of_lt_of_le Nat.zero_lt_one hc
  have hc₀ : (0 : ℝ) < c := by exact_mod_cast hcNat₀
  have hxTheta : 1 ≤ x ^ theta0 := by
    exact Real.one_le_rpow hx (by norm_num [theta0])
  have hM₁ : 1 < M := hxTheta.trans_lt hxM
  have hM₀ : 0 < M := zero_lt_one.trans hM₁
  have htwoM₀ : 0 < 2 * M := mul_pos (by norm_num) hM₀
  have ha₀ : (0 : ℝ) < a := by
    have hleft : 0 < (c : ℝ) * x / (2 * M) ^ 2 := by positivity
    exact hleft.trans_le haLower
  have haNat₀ : 0 < a := by exact_mod_cast ha₀
  have hratio₀ : 0 < (c : ℝ) * x / a := by positivity
  have hratioLower : M ^ 2 ≤ (c : ℝ) * x / a := by
    apply (le_div_iff₀ ha₀).2
    simpa [mul_comm] using (le_div_iff₀ (sq_pos_of_pos hM₀)).1 haUpper
  have hratioUpper : (c : ℝ) * x / a ≤ (2 * M) ^ 2 := by
    apply (div_le_iff₀ ha₀).2
    simpa [mul_comm] using (div_le_iff₀ (sq_pos_of_pos htwoM₀)).1 haLower
  have hsqrtLower : M ≤ Real.sqrt ((c : ℝ) * x / a) := by
    rw [← Real.sqrt_sq hM₀.le]
    exact Real.sqrt_le_sqrt hratioLower
  have hsqrtUpper : Real.sqrt ((c : ℝ) * x / a) ≤ 2 * M := by
    rw [← Real.sqrt_sq htwoM₀.le]
    exact Real.sqrt_le_sqrt hratioUpper
  have hsqrtOne : 1 ≤ Real.sqrt ((c : ℝ) * x / a) :=
    hM₁.le.trans hsqrtLower
  have hmOne : 1 ≤ fareyPoint x a c := by
    unfold fareyPoint
    exact (Nat.one_le_floor_iff _).2 hsqrtOne
  have hmPos : 0 < fareyPoint x a c := lt_of_lt_of_le Nat.zero_lt_one hmOne
  have hfloorLe : (fareyPoint x a c : ℝ) ≤
      Real.sqrt ((c : ℝ) * x / a) := by
    unfold fareyPoint
    exact Nat.floor_le (Real.sqrt_nonneg _)
  have hsqrtLt : Real.sqrt ((c : ℝ) * x / a) <
      (fareyPoint x a c : ℝ) + 1 := by
    unfold fareyPoint
    exact Nat.lt_floor_add_one _
  have hvNonneg : 0 ≤ fareyFrac x a c := by
    unfold fareyFrac
    linarith
  have hvLt : fareyFrac x a c < 1 := by
    unfold fareyFrac
    linarith
  have hsum : (fareyPoint x a c : ℝ) + fareyFrac x a c =
      Real.sqrt ((c : ℝ) * x / a) := by
    unfold fareyFrac
    ring
  have hcoefficient :
      x / ((fareyPoint x a c : ℝ) + fareyFrac x a c) ^ 2 =
        (a : ℝ) / c := by
    rw [hsum, Real.sq_sqrt hratio₀.le]
    field_simp [ne_of_gt ha₀, ne_of_gt hc₀]
  exact ⟨hmPos, hvNonneg, hvLt, hsum, hcoefficient, hsqrtLower, hsqrtUpper⟩

/-! ## The low-frequency scale -/

/-- The low-frequency quantity in (7.4), in the multiplicative form used in
the conclusion of (7.5). -/
noncomputable def section7Amplitude (x H M : ℝ) : ℝ :=
  (x * H) ^ (-(1 : ℝ) / 2) * M ^ ((3 : ℝ) / 2)

/-- The two presentations of the (7.4) scale agree. -/
theorem section7Amplitude_eq {x H M : ℝ}
    (hx : 0 < x) (hH : 0 < H) (hM : 0 < M) :
    (x * H * M ^ (-(3 : ℝ))) ^ (-(1 : ℝ) / 2) =
      section7Amplitude x H M := by
  unfold section7Amplitude
  rw [Real.mul_rpow (mul_nonneg hx.le hH.le) (Real.rpow_nonneg hM.le _),
    ← Real.rpow_mul hM.le]
  congr 1
  norm_num

private theorem shiftLength_eq_section7 (x M : ℝ) :
    shiftLength x M = M * x ^ (-(3 : ℝ) / 11) := by
  unfold shiftLength
  congr 1
  norm_num [theta0]

/-- The amplitude is positive in the main range. -/
theorem section7Amplitude_pos {x H M : ℝ}
    (hx : 0 < x) (hH : 0 < H) (hM : 0 < M) :
    0 < section7Amplitude x H M := by
  unfold section7Amplitude
  positivity

/-- The exact scale identity `A² = N G`. -/
theorem section7Amplitude_sq_eq_shift_mul_Gscale
    {x H M : ℝ} (hx : 0 < x) (hH : 0 < H) (hM : 0 < M) :
    section7Amplitude x H M ^ 2 = shiftLength x M * Gscale x H M := by
  have hxH : 0 < x * H := mul_pos hx hH
  have hpowXH : ((x * H) ^ (-(1 : ℝ) / 2)) ^ 2 = (x * H)⁻¹ := by
    calc
      ((x * H) ^ (-(1 : ℝ) / 2)) ^ 2 =
          (x * H) ^ ((-(1 : ℝ) / 2) * (2 : ℕ)) :=
        (Real.rpow_mul_natCast hxH.le (-(1 : ℝ) / 2) 2).symm
      _ = (x * H) ^ (-(1 : ℝ)) := by norm_num
      _ = (x * H)⁻¹ := Real.rpow_neg_one _
  have hpowM : (M ^ ((3 : ℝ) / 2)) ^ 2 = M ^ 3 := by
    calc
      (M ^ ((3 : ℝ) / 2)) ^ 2 = M ^ (((3 : ℝ) / 2) * (2 : ℕ)) :=
        (Real.rpow_mul_natCast hM.le ((3 : ℝ) / 2) 2).symm
      _ = M ^ (3 : ℝ) := by norm_num
      _ = M ^ 3 := Real.rpow_natCast _ _
  have hAmplitudeSq : section7Amplitude x H M ^ 2 = M ^ 3 / (x * H) := by
    unfold section7Amplitude
    rw [mul_pow, hpowXH, hpowM]
    field_simp [hxH.ne']
  rw [hAmplitudeSq]
  unfold Gscale
  have hN : shiftLength x M ≠ 0 := by
    rw [shiftLength_eq_section7]
    positivity
  field_simp [hx.ne', hH.ne', hN]

/-- On the main range, `x^(1/11) G <= N`.  This is the squared form of the
power saving used to absorb the low-frequency and endpoint terms. -/
theorem mainRange_power_mul_Gscale_le_shiftLength
    {x H M : ℝ} (hmain : InMainRange x H M) :
    x ^ ((1 : ℝ) / 11) * Gscale x H M ≤ shiftLength x M := by
  rcases hmain with ⟨hx, hxM, hMx, hH, hHupper, hshift, hsecond, hMlower⟩
  have hx₀ : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hM₀ : 0 < M := (Real.rpow_pos_of_pos hx₀ theta0).trans hxM
  have hH₀ : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hshift' : M * x ^ (-(4 : ℝ) / 11) ≤ H := by
    rw [show (-(4 : ℝ) / 11) = 2 * theta0 - 1 by norm_num [theta0]]
    exact hshift.le
  have hxCombineLeft :
      x ^ ((5 : ℝ) / 11) * x ^ (-(4 : ℝ) / 11) =
        x ^ ((1 : ℝ) / 11) := by
    rw [← Real.rpow_add hx₀]
    congr 1
    norm_num
  have hxCombineRight :
      x ^ (-(3 : ℝ) / 11) * x * x ^ (-(3 : ℝ) / 11) =
        x ^ ((5 : ℝ) / 11) := by
    calc
      x ^ (-(3 : ℝ) / 11) * x * x ^ (-(3 : ℝ) / 11) =
          x ^ (-(3 : ℝ) / 11) * x ^ (1 : ℝ) *
            x ^ (-(3 : ℝ) / 11) := by rw [Real.rpow_one]
      _ = x ^ (-(3 : ℝ) / 11 + 1 + -(3 : ℝ) / 11) := by
        rw [← Real.rpow_add hx₀, ← Real.rpow_add hx₀]
      _ = x ^ ((5 : ℝ) / 11) := by norm_num
  have hscaled := mul_le_mul_of_nonneg_left hshift'
    (mul_nonneg (sq_nonneg M) (Real.rpow_nonneg hx₀.le ((5 : ℝ) / 11)))
  have hcore : x ^ ((1 : ℝ) / 11) * M ^ 3 ≤
      (M * x ^ (-(3 : ℝ) / 11)) *
        (x * (M * x ^ (-(3 : ℝ) / 11)) * H) := by
    calc
      x ^ ((1 : ℝ) / 11) * M ^ 3 =
          (M ^ 2 * x ^ ((5 : ℝ) / 11)) *
            (M * x ^ (-(4 : ℝ) / 11)) := by
        rw [← hxCombineLeft]
        ring
      _ ≤ (M ^ 2 * x ^ ((5 : ℝ) / 11)) * H := hscaled
      _ = (M * x ^ (-(3 : ℝ) / 11)) *
          (x * (M * x ^ (-(3 : ℝ) / 11)) * H) := by
        rw [← hxCombineRight]
        ring
  rw [shiftLength_eq_section7]
  unfold Gscale
  rw [shiftLength_eq_section7]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity :
    0 < x * (M * x ^ (-(3 : ℝ) / 11)) * H)).2
  simpa [mul_assoc] using hcore

/-- The scale inequality `x^(1/22) G <= A` needed by long-cell absorption. -/
theorem mainRange_power_mul_Gscale_le_amplitude
    {x H M : ℝ} (hmain : InMainRange x H M) :
    x ^ ((1 : ℝ) / 22) * Gscale x H M ≤ section7Amplitude x H M := by
  rcases hmain with ⟨hx, hxM, hMx, hH, hHupper, hshift, hsecond, hMlower⟩
  have hx₀ : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hM₀ : 0 < M := (Real.rpow_pos_of_pos hx₀ theta0).trans hxM
  have hH₀ : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hG₀ : 0 < Gscale x H M := by
    unfold Gscale
    rw [shiftLength_eq_section7]
    positivity
  have hleft₀ : 0 ≤ x ^ ((1 : ℝ) / 22) * Gscale x H M := by positivity
  have hAmp₀ : 0 ≤ section7Amplitude x H M :=
    (section7Amplitude_pos hx₀ hH₀ hM₀).le
  apply (sq_le_sq₀ hleft₀ hAmp₀).1
  have hxSquare : (x ^ ((1 : ℝ) / 22)) ^ 2 = x ^ ((1 : ℝ) / 11) := by
    calc
      (x ^ ((1 : ℝ) / 22)) ^ 2 = x ^ (((1 : ℝ) / 22) * (2 : ℕ)) :=
        (Real.rpow_mul_natCast hx₀.le ((1 : ℝ) / 22) 2).symm
      _ = x ^ ((1 : ℝ) / 11) := by norm_num
  rw [mul_pow, hxSquare,
    section7Amplitude_sq_eq_shift_mul_Gscale hx₀ hH₀ hM₀]
  have hNG := mainRange_power_mul_Gscale_le_shiftLength
    (show InMainRange x H M from ⟨hx, hxM, hMx, hH, hHupper, hshift, hsecond, hMlower⟩)
  calc
    x ^ ((1 : ℝ) / 11) * Gscale x H M ^ 2 =
        (x ^ ((1 : ℝ) / 11) * Gscale x H M) * Gscale x H M := by ring
    _ ≤ shiftLength x M * Gscale x H M :=
      mul_le_mul_of_nonneg_right hNG hG₀.le

/-! ## Summing the Poisson residue classes -/

/-- A generic nonnegative summable kernel gains the expected factor `1/c`
when averaged over the full frequency shell. -/
theorem sum_tsum_residueClass_le
    {a c : ℕ} {H : ℝ} {J : ℤ → ℝ}
    (hH : 0 < H) (hc : 1 ≤ c) (hcH : (c : ℝ) ≤ H)
    (hac : Nat.Coprime a c) (hJ₀ : ∀ k, 0 ≤ J k) (hJ : Summable J) :
    ∑ h ∈ intRange H (4 * H),
        ∑' k : ℤ, (if k ≡ -((a : ℤ) * (h : ℤ)) [ZMOD (c : ℤ)]
          then J k else (0 : ℝ)) ≤
      5 * H / c * ∑' k : ℤ, J k := by
  classical
  let F : ℕ → ℤ → ℝ := fun h k =>
    if k ≡ -((a : ℤ) * (h : ℤ)) [ZMOD (c : ℤ)] then J k else 0
  have hF (h : ℕ) : Summable (F h) := by
    apply hJ.of_nonneg_of_le
    · intro k
      simp only [F]
      split_ifs
      · exact hJ₀ k
      · exact le_rfl
    · intro k
      simp only [F]
      split_ifs
      · exact le_rfl
      · exact hJ₀ k
  have hcommute :
      ∑ h ∈ intRange H (4 * H), ∑' k : ℤ, F h k =
        ∑' k : ℤ, ∑ h ∈ intRange H (4 * H), F h k := by
    rw [Summable.tsum_finsetSum (fun h _ => hF h)]
  have hinner (k : ℤ) :
      ∑ h ∈ intRange H (4 * H), F h k =
        ((frequencyFiber a c H k).card : ℝ) * J k := by
    simp only [F, frequencyFiber]
    rw [← Finset.sum_filter]
    simp
  have hbound (k : ℤ) :
      ∑ h ∈ intRange H (4 * H), F h k ≤ (5 * H / c) * J k := by
    rw [hinner]
    exact mul_le_mul_of_nonneg_right
      (frequencyFiber_card_le hH hc hcH hac) (hJ₀ k)
  have henv : Summable fun k : ℤ => (5 * H / c) * J k := hJ.mul_left _
  have hsumInner : Summable fun k : ℤ =>
      ∑ h ∈ intRange H (4 * H), F h k := by
    apply henv.of_nonneg_of_le
    · intro k
      exact Finset.sum_nonneg fun h _ => by
        simp only [F]
        split_ifs
        · exact hJ₀ k
        · exact le_rfl
    · exact hbound
  change ∑ h ∈ intRange H (4 * H), ∑' k : ℤ, F h k ≤ _
  rw [hcommute]
  calc
    ∑' k : ℤ, ∑ h ∈ intRange H (4 * H), F h k ≤
        ∑' k : ℤ, (5 * H / c) * J k :=
      hsumInner.tsum_le_tsum hbound henv
    _ = 5 * H / c * ∑' k : ℤ, J k := by rw [tsum_mul_left]

/-- The shell contains at most `4H` frequencies. -/
theorem card_intRange_four_mul_le {H : ℝ} (hH : 0 < H) :
    ((intRange H (4 * H)).card : ℝ) ≤ 4 * H := by
  unfold intRange
  rw [Nat.card_Ioc]
  calc
    ((⌊4 * H⌋₊ - ⌊H⌋₊ : ℕ) : ℝ) ≤ (⌊4 * H⌋₊ : ℝ) := by
      exact_mod_cast (Nat.sub_le ⌊4 * H⌋₊ ⌊H⌋₊)
    _ ≤ 4 * H := Nat.floor_le (by positivity)

/-- The (7.3)/(7.4) hypotheses dominate the norm of each integral by
`poissonIntegralMajorant`. -/
theorem trapezoidIntegral_norm_le_majorant
    {x H M : ℝ} {a c h : ℕ} {L₁ L₂ : ℤ}
    {k₀ C : ℝ} (_hk₀ : 0 < k₀) (_hC : 0 ≤ C)
    (hbounds :
      (∀ k : ℤ, k₀ ≤ |(k : ℝ)| →
        ‖trapezoidIntegral x h (fareyPoint x a c) (fareyFrac x a c) L₁ L₂ c k‖ ≤
          C * min (c / |(k : ℝ)|) ((c : ℝ) ^ 2 / (k : ℝ) ^ 2)) ∧
      (∀ k : ℤ, |(k : ℝ)| < k₀ →
        ‖trapezoidIntegral x h (fareyPoint x a c) (fareyFrac x a c) L₁ L₂ c k‖ ≤
          C * (x * H * M ^ (-(3 : ℝ))) ^ (-(1 : ℝ) / 2)))
    (hx : 0 < x) (hH : 0 < H) (hM : 0 < M) (k : ℤ) :
    ‖trapezoidIntegral x h (fareyPoint x a c) (fareyFrac x a c) L₁ L₂ c k‖ ≤
      poissonIntegralMajorant (section7Amplitude x H M) c k₀ C k := by
  by_cases hk : |(k : ℝ)| < k₀
  · rw [poissonIntegralMajorant, if_pos hk, ← section7Amplitude_eq hx hH hM]
    exact hbounds.2 k hk
  · rw [poissonIntegralMajorant, if_neg hk, poissonTailKernel]
    exact hbounds.1 k (le_of_not_gt hk)

/-- The norm of one congruence-restricted Poisson dual sum is bounded by the
corresponding restricted majorant. -/
theorem norm_poissonDual_le
    {x H M : ℝ} {a c h : ℕ} {L₁ L₂ : ℤ}
    {k₀ C : ℝ} (hk₀ : 0 < k₀) (hC : 0 ≤ C)
    (hc : 1 ≤ c) (hx : 0 < x) (hH : 0 < H) (hM : 0 < M)
    (hbounds :
      (∀ k : ℤ, k₀ ≤ |(k : ℝ)| →
        ‖trapezoidIntegral x h (fareyPoint x a c) (fareyFrac x a c) L₁ L₂ c k‖ ≤
          C * min (c / |(k : ℝ)|) ((c : ℝ) ^ 2 / (k : ℝ) ^ 2)) ∧
      (∀ k : ℤ, |(k : ℝ)| < k₀ →
        ‖trapezoidIntegral x h (fareyPoint x a c) (fareyFrac x a c) L₁ L₂ c k‖ ≤
          C * (x * H * M ^ (-(3 : ℝ))) ^ (-(1 : ℝ) / 2))) :
    ‖∑' k : ℤ, if k ≡ -((a : ℤ) * (h : ℤ)) [ZMOD (c : ℤ)] then
        trapezoidIntegral x h (fareyPoint x a c) (fareyFrac x a c) L₁ L₂ c k else 0‖ ≤
      ∑' k : ℤ, if k ≡ -((a : ℤ) * (h : ℤ)) [ZMOD (c : ℤ)] then
        poissonIntegralMajorant (section7Amplitude x H M) c k₀ C k else 0 := by
  have hA₀ : 0 ≤ section7Amplitude x H M :=
    (section7Amplitude_pos hx hH hM).le
  have hcR : (0 : ℝ) < c := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hc)
  have hmajorant := summable_poissonIntegralMajorant hA₀ hcR hk₀ hC
  let f : ℤ → ℂ := fun k =>
    if k ≡ -((a : ℤ) * (h : ℤ)) [ZMOD (c : ℤ)] then
      trapezoidIntegral x h (fareyPoint x a c) (fareyFrac x a c) L₁ L₂ c k else 0
  let g : ℤ → ℝ := fun k =>
    if k ≡ -((a : ℤ) * (h : ℤ)) [ZMOD (c : ℤ)] then
      poissonIntegralMajorant (section7Amplitude x H M) c k₀ C k else 0
  have hg : Summable g := by
    apply hmajorant.of_nonneg_of_le
    · intro k
      simp only [g]
      split_ifs
      · unfold poissonIntegralMajorant
        split_ifs
        · exact mul_nonneg hC hA₀
        · exact mul_nonneg hC (poissonTailKernel_nonneg hcR.le k)
      · exact le_rfl
    · intro k
      simp only [g]
      split_ifs
      · exact le_rfl
      · unfold poissonIntegralMajorant
        split_ifs
        · exact mul_nonneg hC hA₀
        · exact mul_nonneg hC (poissonTailKernel_nonneg hcR.le k)
  have hfg (k : ℤ) : ‖f k‖ ≤ g k := by
    simp only [f, g]
    by_cases hk : k ≡ -((a : ℤ) * (h : ℤ)) [ZMOD (c : ℤ)]
    · rw [if_pos hk, if_pos hk]
      exact trapezoidIntegral_norm_le_majorant hk₀ hC hbounds hx hH hM k
    · simp [hk]
  have hfnorm : Summable fun k => ‖f k‖ := hg.of_nonneg_of_le (fun _ => norm_nonneg _) hfg
  change ‖∑' k : ℤ, f k‖ ≤ ∑' k : ℤ, g k
  exact (norm_tsum_le_tsum_norm hfnorm).trans (hfnorm.tsum_le_tsum hfg hg)

/-! ## Recovering the real sine block -/

/-- The imaginary part of the standard additive character. -/
theorem e_im (t : ℝ) : (e t).im = Real.sin (2 * Real.pi * t) := by
  simp [e, Complex.exp_im]

/-- The complex exponential block whose imaginary part is the sum in (7.5). -/
noncomputable def section7ComplexBlock
    (chi : ℝ → ℝ) (x H : ℝ) (m : ℕ) (L₁ L₂ : ℤ) : ℂ :=
  ∑ h ∈ intRange H (4 * H),
    ((chi (h / H) / (Real.pi * h) : ℝ) : ℂ) *
      ∑ l ∈ Finset.Ico L₁ L₂, e (x * h / (m + l))

/-- The interval sum of `psiH` is the imaginary part of the corresponding
weighted complex exponential block. -/
theorem sum_psiH_eq_im_complexBlock
    {chi : ℝ → ℝ} (hchi : IsDyadicPartition chi)
    {x H : ℝ} (hH : 0 < H) (m : ℕ) (L₁ L₂ : ℤ) :
    ∑ l ∈ Finset.Ico L₁ L₂, psiH chi H (x / (m + l)) =
      (section7ComplexBlock chi x H m L₁ L₂).im := by
  unfold section7ComplexBlock
  simp_rw [psiH_eq_intRange hchi hH]
  rw [Finset.sum_comm, Complex.im_sum]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Complex.mul_im, Complex.im_sum]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, e_im]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

end IMReductionEq75

open IMReductionEq75

/-- **Iwaniec--Mozzochi (7.5), conditional reduction.**  Poisson summation
(7.2), together with the integral estimates (7.3)/(7.4), implies the uniform
long-cell bound (7.5).  The proof includes the inclusive endpoint correction,
averaging over the coprime congruence classes, an absolutely summable
`6/5`-power replacement for the logarithmic tail, and its absorption on
`c <= mu₀ G`. -/
theorem iwaniecMozzochi_eq75_of_eq72_eq73_eq74
    (h72 : iwaniecMozzochi_eq72) (h734 : iwaniecMozzochi_eq73_eq74) :
    iwaniecMozzochi_eq75 := by
  rw [iwaniecMozzochi_eq75]
  intro chi mu₀ hchi hmu₀
  rcases h734 with ⟨k₀, C₀, hk₀, hC₀, h734⟩
  let C : ℝ :=
    5 * ((poissonLowIndexSet k₀).card : ℝ) * C₀ +
      10 * C₀ * poissonTailConstant * mu₀ + 8 * mu₀
  refine ⟨C, ?_⟩
  intro x H M a c L₁ L₂ hmain hfarey hcLong hL hpole hLlower hLupper
  have hmainData := hmain
  have hfareyData := hfarey
  obtain ⟨hx, hxM, hMx, hH, hHupper, hshift, hsecond, hMlower⟩ := hmainData
  obtain ⟨hc, hcH, hac, haLower, haUpper⟩ := hfareyData
  have hx₀ : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hH₀ : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hM₀ : 0 < M := (Real.rpow_pos_of_pos hx₀ theta0).trans hxM
  have hcNat₀ : 0 < c := lt_of_lt_of_le Nat.zero_lt_one hc
  have hcR₀ : (0 : ℝ) < c := by exact_mod_cast hcNat₀
  have hgeometry := fareyPoint_geometry hmain hfarey
  obtain ⟨hm₀, hv₀, hv₁, hmv, hcoefficient, hmLower, hmUpper⟩ := hgeometry
  let A : ℝ := section7Amplitude x H M
  let J : ℤ → ℝ := poissonIntegralMajorant A c k₀ C₀
  let R : ℕ → ℝ := fun h =>
    ∑' k : ℤ, if k ≡ -((a : ℤ) * (h : ℤ)) [ZMOD (c : ℤ)] then J k else 0
  have hA₀ : 0 ≤ A := by
    exact (section7Amplitude_pos hx₀ hH₀ hM₀).le
  have hJ₀ (k : ℤ) : 0 ≤ J k := by
    unfold J poissonIntegralMajorant
    split_ifs
    · exact mul_nonneg hC₀.le hA₀
    · exact mul_nonneg hC₀.le (poissonTailKernel_nonneg hcR₀.le k)
  have hJsum : Summable J := by
    exact summable_poissonIntegralMajorant hA₀ hcR₀ hk₀ hC₀.le
  have hR₀ (h : ℕ) : 0 ≤ R h := by
    unfold R
    exact tsum_nonneg fun k => by
      split_ifs
      · exact hJ₀ k
      · exact le_rfl
  have hfrequency (h : ℕ) (hhShell : h ∈ intRange H (4 * H)) :
      ‖∑ l ∈ Finset.Ico L₁ L₂,
          e (x * h / ((fareyPoint x a c : ℝ) + l))‖ ≤ R h + 1 := by
    have hhBounds := mem_intRange_four_mul hH₀ hhShell
    have hhNat₀ : 0 < h := by
      have : (0 : ℝ) < h := hH₀.trans hhBounds.1
      exact_mod_cast this
    have hb := h734 x H M a c h L₁ L₂ hmain hfarey hhShell hL hpole hLlower hLupper
    have hPoisson := eq72_halfOpen_sum h72 x (fareyPoint x a c) (fareyFrac x a c)
      a c h L₁ L₂ hx₀ hhNat₀ (by exact_mod_cast hm₀) hv₀ hv₁ hc hL hpole
      hcoefficient
    rw [hPoisson, norm_mul, norm_e, one_mul]
    calc
      ‖(∑' k : ℤ, if k ≡ -((a : ℤ) * (h : ℤ)) [ZMOD (c : ℤ)] then
          trapezoidIntegral x h (fareyPoint x a c) (fareyFrac x a c) L₁ L₂ c k else 0) -
          e (-((a : ℝ) * h * L₂ / c) +
            rPhase x h (fareyPoint x a c) (fareyFrac x a c) L₂)‖ ≤
          ‖∑' k : ℤ, if k ≡ -((a : ℤ) * (h : ℤ)) [ZMOD (c : ℤ)] then
            trapezoidIntegral x h (fareyPoint x a c) (fareyFrac x a c) L₁ L₂ c k else 0‖ +
            ‖e (-((a : ℝ) * h * L₂ / c) +
              rPhase x h (fareyPoint x a c) (fareyFrac x a c) L₂)‖ := norm_sub_le _ _
      _ ≤ R h + 1 := by
        apply add_le_add
        · simpa [R, J] using
            (norm_poissonDual_le hk₀ hC₀.le hc hx₀ hH₀ hM₀ hb)
        · rw [norm_e]
  have hcoefficientBound (h : ℕ) (hhShell : h ∈ intRange H (4 * H)) :
      ‖((chi (h / H) / (Real.pi * h) : ℝ) : ℂ)‖ ≤ 1 / H := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    calc
      |chi (h / H) / (Real.pi * h)| ≤ 1 / (Real.pi * H) :=
        psiH_coefficient_abs_le hchi hH₀ hhShell
      _ ≤ 1 / H := by
        apply one_div_le_one_div_of_le hH₀
        simpa using mul_le_mul_of_nonneg_right
          ((show (1 : ℝ) ≤ 2 by norm_num).trans Real.two_le_pi) hH₀.le
  have hblockRaw :
      ‖section7ComplexBlock chi x H (fareyPoint x a c) L₁ L₂‖ ≤
        (1 / H) *
          ((∑ h ∈ intRange H (4 * H), R h) +
            ((intRange H (4 * H)).card : ℝ)) := by
    unfold section7ComplexBlock
    calc
      ‖∑ h ∈ intRange H (4 * H),
          ((chi (h / H) / (Real.pi * h) : ℝ) : ℂ) *
            ∑ l ∈ Finset.Ico L₁ L₂,
              e (x * h / ((fareyPoint x a c : ℝ) + l))‖ ≤
          ∑ h ∈ intRange H (4 * H),
            ‖((chi (h / H) / (Real.pi * h) : ℝ) : ℂ) *
              ∑ l ∈ Finset.Ico L₁ L₂,
                e (x * h / ((fareyPoint x a c : ℝ) + l))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ h ∈ intRange H (4 * H), (1 / H) * (R h + 1) := by
        refine Finset.sum_le_sum fun h hh => ?_
        rw [norm_mul]
        exact mul_le_mul (hcoefficientBound h hh) (hfrequency h hh)
          (norm_nonneg _) (by positivity)
      _ = (1 / H) *
          ((∑ h ∈ intRange H (4 * H), R h) +
            ((intRange H (4 * H)).card : ℝ)) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        ring
  have hsumR :
      ∑ h ∈ intRange H (4 * H), R h ≤
        5 * H / c * ∑' k : ℤ, J k := by
    simpa [R] using sum_tsum_residueClass_le hH₀ hc hcH hac hJ₀ hJsum
  have hcard : ((intRange H (4 * H)).card : ℝ) ≤ 4 * H :=
    card_intRange_four_mul_le hH₀
  have hblockKernel :
      ‖section7ComplexBlock chi x H (fareyPoint x a c) L₁ L₂‖ ≤
        5 * (∑' k : ℤ, J k) / c + 4 := by
    calc
      ‖section7ComplexBlock chi x H (fareyPoint x a c) L₁ L₂‖ ≤
          (1 / H) *
            ((∑ h ∈ intRange H (4 * H), R h) +
              ((intRange H (4 * H)).card : ℝ)) := hblockRaw
      _ ≤ (1 / H) * (5 * H / c * (∑' k : ℤ, J k) + 4 * H) := by
        exact mul_le_mul_of_nonneg_left (add_le_add hsumR hcard) (by positivity)
      _ = 5 * (∑' k : ℤ, J k) / c + 4 := by
        field_simp [hH₀.ne', hcR₀.ne']
  have hmass :
      ∑' k : ℤ, J k ≤
        ((poissonLowIndexSet k₀).card : ℝ) * (C₀ * A) +
          C₀ * ((c : ℝ) ^ ((6 : ℝ) / 5) * poissonTailConstant) := by
    simpa [J] using tsum_poissonIntegralMajorant_le hA₀ hcR₀ hk₀ hC₀.le
  have hpowDiv : (c : ℝ) ^ ((6 : ℝ) / 5) / c = c ^ ((1 : ℝ) / 5) := by
    calc
      (c : ℝ) ^ ((6 : ℝ) / 5) / c = c ^ (((6 : ℝ) / 5) - 1) :=
        (Real.rpow_sub_one hcR₀.ne' ((6 : ℝ) / 5)).symm
      _ = c ^ ((1 : ℝ) / 5) := by norm_num
  have hcPower : (c : ℝ) ≤ x ^ ((2 : ℝ) / 11) :=
    farey_denominator_le_twoElevenths hmain hfarey
  have hAG : x ^ ((1 : ℝ) / 22) * Gscale x H M ≤ A := by
    simpa [A] using mainRange_power_mul_Gscale_le_amplitude hmain
  have habsorb : 1 + (c : ℝ) ^ ((1 : ℝ) / 5) ≤ 2 * mu₀ * (A / c) :=
    longCell_absorbs_one_add_fifthPower hx (by exact_mod_cast hc) hmu₀ hcPower hAG hcLong
  have hOneAbsorb : 1 ≤ 2 * mu₀ * (A / c) :=
    (le_add_of_nonneg_right (Real.rpow_nonneg hcR₀.le _)).trans habsorb
  have hPowAbsorb : (c : ℝ) ^ ((1 : ℝ) / 5) ≤ 2 * mu₀ * (A / c) :=
    (le_add_of_nonneg_left zero_le_one).trans habsorb
  have htail₀ : 0 ≤ poissonTailConstant := poissonTailConstant_nonneg
  have hblockFinal :
      ‖section7ComplexBlock chi x H (fareyPoint x a c) L₁ L₂‖ ≤ C * (A / c) := by
    calc
      ‖section7ComplexBlock chi x H (fareyPoint x a c) L₁ L₂‖ ≤
          5 * (∑' k : ℤ, J k) / c + 4 := hblockKernel
      _ ≤ 5 *
          (((poissonLowIndexSet k₀).card : ℝ) * (C₀ * A) +
            C₀ * ((c : ℝ) ^ ((6 : ℝ) / 5) * poissonTailConstant)) / c + 4 := by
        have hmassFive :
            5 * (∑' k : ℤ, J k) ≤
              5 * (((poissonLowIndexSet k₀).card : ℝ) * (C₀ * A) +
                C₀ * ((c : ℝ) ^ ((6 : ℝ) / 5) * poissonTailConstant)) :=
          mul_le_mul_of_nonneg_left (a := (5 : ℝ)) hmass (by norm_num)
        exact add_le_add_left
          (div_le_div_of_nonneg_right hmassFive hcR₀.le) 4
      _ = 5 * ((poissonLowIndexSet k₀).card : ℝ) * C₀ * (A / c) +
          5 * C₀ * poissonTailConstant * (c : ℝ) ^ ((1 : ℝ) / 5) + 4 := by
        calc
          5 *
                (((poissonLowIndexSet k₀).card : ℝ) * (C₀ * A) +
                  C₀ * ((c : ℝ) ^ ((6 : ℝ) / 5) * poissonTailConstant)) /
                c + 4 =
              5 * ((poissonLowIndexSet k₀).card : ℝ) * C₀ * (A / c) +
                5 * C₀ * poissonTailConstant *
                  ((c : ℝ) ^ ((6 : ℝ) / 5) / c) + 4 := by
            field_simp [hcR₀.ne']
          _ = 5 * ((poissonLowIndexSet k₀).card : ℝ) * C₀ * (A / c) +
              5 * C₀ * poissonTailConstant * (c : ℝ) ^ ((1 : ℝ) / 5) + 4 := by
            rw [hpowDiv]
      _ ≤ 5 * ((poissonLowIndexSet k₀).card : ℝ) * C₀ * (A / c) +
          5 * C₀ * poissonTailConstant * (2 * mu₀ * (A / c)) +
            4 * (2 * mu₀ * (A / c)) := by
        have htailAbs :
            5 * C₀ * poissonTailConstant * (c : ℝ) ^ ((1 : ℝ) / 5) ≤
              5 * C₀ * poissonTailConstant * (2 * mu₀ * (A / c)) :=
          mul_le_mul_of_nonneg_left hPowAbsorb
            (mul_nonneg (mul_nonneg (by positivity) hC₀.le) htail₀)
        have hfourAbs : (4 : ℝ) ≤ 4 * (2 * mu₀ * (A / c)) :=
          by simpa only [mul_one] using
            mul_le_mul_of_nonneg_left (a := (4 : ℝ)) hOneAbsorb (by norm_num)
        have htailWithBase :
            5 * ((poissonLowIndexSet k₀).card : ℝ) * C₀ * (A / c) +
                5 * C₀ * poissonTailConstant * (c : ℝ) ^ ((1 : ℝ) / 5) ≤
              5 * ((poissonLowIndexSet k₀).card : ℝ) * C₀ * (A / c) +
                5 * C₀ * poissonTailConstant * (2 * mu₀ * (A / c)) :=
          add_le_add (le_refl _) htailAbs
        exact add_le_add htailWithBase hfourAbs
      _ = C * (A / c) := by
        unfold C
        ring
  rw [sum_psiH_eq_im_complexBlock hchi hH₀]
  calc
    |(section7ComplexBlock chi x H (fareyPoint x a c) L₁ L₂).im| ≤
        ‖section7ComplexBlock chi x H (fareyPoint x a c) L₁ L₂‖ :=
      Complex.abs_im_le_norm _
    _ ≤ C * (A / c) := hblockFinal
    _ = C * ((c : ℝ)⁻¹ * (x * H) ^ (-(1 : ℝ) / 2) * M ^ ((3 : ℝ) / 2)) := by
      unfold A section7Amplitude
      ring

end LeanProofs.IntegerPoints
