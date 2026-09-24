import Diophantine.Paper1982.ShortExistence
import Diophantine.Paper1982.Master3
import Mathlib.Algebra.Polynomial.Div

/-!
# Positive witnesses for the shorter coding equations in Jones 1982, §5

For any fixed digits with a positive tail coordinate, sufficiently large
powers of two give positive natural witnesses for every equation in
`ShortEqs`. The two transfer quotients are positive because the digit
polynomials strictly increase between `2z` and the enlarged base `B`.
No polynomial solution hypothesis or carry condition is used here.
-/

namespace Jones1982

open Polynomial Finset

/-- A strictly increasing digit polynomial gives a positive value and a
positive quotient in its evaluation congruence. -/
theorem exists_positive_eval_witness (p : ℤ[X]) (hp : ∀ i, 0 ≤ p.coeff i)
    {n : ℕ} (hn : 1 ≤ n) (hpn : 0 < p.coeff n)
    {a : ℤ} {B y : ℕ} (ha : 0 ≤ a) (haB : a < B) (hy : (y : ℤ) = p.eval a) :
    ∃ e m : ℕ, 0 < e ∧ 0 < m ∧ (e : ℤ) = p.eval (B : ℤ) ∧
      (e : ℤ) = y + m * ((B : ℤ) - a) := by
  have hlt := eval_lt_eval_of_pos hp hn hpn ha haB
  rw [← hy] at hlt
  have hepos : 0 < p.eval (B : ℤ) := lt_of_le_of_lt (by positivity) hlt
  have hdiv := sub_dvd_eval_sub (B : ℤ) a p
  rw [← hy] at hdiv
  obtain ⟨q, hq⟩ := hdiv
  have hqpos : 0 < q := by
    by_contra hqnot
    have hqnonpos : q ≤ 0 := by omega
    have hmul := mul_nonpos_of_nonneg_of_nonpos (by omega : 0 ≤ (B : ℤ) - a) hqnonpos
    omega
  have hecast : ((p.eval (B : ℤ)).toNat : ℤ) = p.eval (B : ℤ) :=
    Int.toNat_of_nonneg hepos.le
  have hqcast : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hqpos.le
  refine ⟨(p.eval (B : ℤ)).toNat, q.toNat, ?_, ?_, hecast, ?_⟩
  · exact_mod_cast (show (0 : ℤ) < (p.eval (B : ℤ)).toNat by omega)
  · exact_mod_cast (show (0 : ℤ) < q.toNat by omega)
  · rw [hecast, hqcast]
    linear_combination hq

/-- Actual positive natural witnesses for the short coding equations, retaining
all code evaluation identities and a power-of-two base parameter. -/
theorem exists_shortEqs_of_digits {ν : ℕ} {P : MvPolynomial (Fin (ν + 1)) ℤ}
    {z u y : ℕ} (hν : 1 ≤ ν) (hI : Index ν P z u y)
    (zs : Fin (ν + 1) → ℕ) (_hx : 0 < zs 0)
    (htail : ∃ j : Fin (ν + 1), j ≠ 0 ∧ 0 < zs j) :
    ∃ b B c e g l m Q t lam ε w : ℕ,
      0 < b ∧ 0 < B ∧ 0 < c ∧ 0 < e ∧ 0 < g ∧ 0 < l ∧ 0 < m ∧ 0 < Q ∧
      0 < t ∧ 0 < lam ∧ 0 < ε ∧ 0 < w ∧ b = 2 ^ w ∧ (∀ j, zs j < b) ∧
      ShortEqs ν (zs 0) z u y b B c e g l m Q t lam ε ∧
      (c : ℤ) = (cpoly ν 4 zs).eval (B : ℤ) ∧
      (e : ℤ) = (epoly ν 4 P z).eval (B : ℤ) ∧
      (l : ℤ) = (lpoly ν 4).eval (B : ℤ) ∧
      (g : ℤ) = (gpoly ν zs).eval (B : ℤ) := by
  obtain ⟨cutoff, hcutoff⟩ := exists_short_D8_cutoff_nat hν hI zs
  let w : ℕ := cutoff + ∑ j, zs j + 1
  let b : ℕ := 2 ^ w
  have hw : 0 < w := by dsimp [w]; omega
  have hwb : w < b := Nat.lt_two_pow_self
  have hbcut : cutoff ≤ b := by dsimp [w] at hwb; omega
  have hzs : ∀ j, zs j < b := by
    intro j
    have hjsum : zs j ≤ ∑ i, zs i :=
      Finset.single_le_sum (f := fun i => zs i) (fun i _ => Nat.zero_le (zs i)) (mem_univ j)
    dsimp [w] at hwb
    omega
  have hb : 0 < b := by dsimp [b]; positivity
  let B : ℕ := shortBase ν z b
  obtain ⟨hbB, hzB, -⟩ := shortBase_bounds (ν := ν) hI.two_le hb
  change b < B at hbB
  change 4 * z < B at hzB
  have hB : 0 < B := by omega
  have haB : 2 * (z : ℤ) < B := by exact_mod_cast (show 2 * z < B by omega)
  have hL : 1 ≤ L4 ν := Nat.one_le_pow _ _ (by norm_num)
  -- Positive coefficients ensure strict increase for both transfer polynomials.
  obtain ⟨k₀, hk₀, hexp⟩ : ∃ k₀ ∈ star ν 4, expo ν 4 k₀ = 0 :=
    ⟨(fun _ => 0 : Fin (ν + 2) → ℕ) + Pi.single 0 4,
      by rw [mem_star]; simp, by simp [expo]⟩
  have hecoeff : 0 < (epoly ν 4 P z).coeff (L4 ν) := by
    have hc := coeff_epoly_of_mem ν 4 P z hk₀
    rw [hexp, Nat.sub_zero] at hc
    rw [hc]
    have hbig := hI.big k₀ hk₀
    have hneg := neg_abs_le (Pcoef ν P k₀)
    linarith
  obtain ⟨e, m, he, hm, heZ, hmZ⟩ := exists_positive_eval_witness (epoly ν 4 P z)
    (fun i => (hI.coeff_epoly_bounds i).1) hL hecoeff (by positivity) haB hI.hy
  obtain ⟨l, t, hl, ht, hlZ, htZ⟩ := exists_positive_eval_witness (lpoly ν 4)
    (fun i => (coeff_lpoly_bounds ν i).1) (by norm_num : 1 ≤ 5 ^ 1)
    (by rw [coeff_lpoly_of_mem ν (mem_Icc.2 ⟨le_rfl, hν⟩)]; norm_num)
    (by positivity) haB hI.hu
  -- A positive tail digit makes the tail code `g` positive.
  have hgval : 0 < (gpoly ν zs).eval (B : ℤ) := by
    unfold gpoly
    rw [eval_finsetSum]
    apply Finset.sum_pos'
    · intro j _
      split_ifs
      · simp
      · simp only [eval_mul, eval_C, eval_pow, eval_X]
        positivity
    · obtain ⟨j, hj, hzj⟩ := htail
      refine ⟨j, mem_univ j, ?_⟩
      rw [if_neg hj]
      simp only [eval_mul, eval_C, eval_pow, eval_X]
      have hzjZ : (0 : ℤ) < zs j := by exact_mod_cast hzj
      have hBZ : (0 : ℤ) < B := by exact_mod_cast hB
      positivity
  let g : ℕ := ((gpoly ν zs).eval (B : ℤ)).toNat
  have hgZ : (g : ℤ) = (gpoly ν zs).eval (B : ℤ) := Int.toNat_of_nonneg hgval.le
  have hg : 0 < g := by exact_mod_cast (show (0 : ℤ) < g by omega)
  let c : ℕ := 1 + zs 0 * B + g
  have hc : 0 < c := by dsimp [c]; omega
  have hcZ : (c : ℤ) = (cpoly ν 4 zs).eval (B : ℤ) := by
    rw [eval_cpoly_eq, ← hgZ]
    simp only [c, Nat.cast_add, Nat.cast_one, Nat.cast_mul]
  have hD8 := hcutoff b c e l hbcut hcZ heZ hlZ
  change e + 2 * z * b * l + 2 * z * B * c ^ 4 < 2 * z * B ^ (L4 ν) at hD8
  have hQ : 0 < B ^ (L4 ν) := pow_pos hB _
  have hlam : 0 < shortLam ν B := by
    have hterm : B ^ 0 ≤ ∑ i ∈ range (L4 ν), B ^ i :=
      Finset.single_le_sum (f := fun i => B ^ i) (fun i _ => Nat.zero_le (B ^ i)) (mem_range.2 hL)
    have h1 : 1 ≤ shortLam ν B := by simpa only [pow_zero, shortLam] using hterm
    exact Nat.succ_le_iff.mp h1
  have hgeom : B ^ (L4 ν) = 1 + shortLam ν B * (B - 1) := by
    have hh := geom_sum_mul_add (B - 1) (L4 ν)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ B)] at hh
    simpa only [shortLam, add_comm] using hh.symm
  have hε : 0 < b - zs 0 := Nat.sub_pos_of_lt (hzs 0)
  refine ⟨b, B, c, e, g, l, m, B ^ (L4 ν), t, shortLam ν B, b - zs 0, w,
    hb, hB, hc, he, hg, hl, hm, hQ, ht, hlam, hε, hw, rfl, hzs, ?_, hcZ, heZ, hlZ, hgZ⟩
  exact ⟨by omega, rfl, rfl, rfl, hgeom, hD8, htZ, hmZ⟩

end Jones1982
