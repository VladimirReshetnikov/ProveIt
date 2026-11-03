import DiophantineConsistency.ExecutableJonesCore
import DiophantineConsistency.WeightedExpressionDegree
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Jones's multinomial coding (§4) over an arbitrary commutative ring

Foundation-free counterpart of `Jones1982` `Coding.lean`, phrased with explicit finite
sums over the executable star `ExecutableJones.codingStar ν 4` instead of `ℤ[X]`, so that
it applies verbatim in the ring of differences of a model of `𝗜𝚺₁`.

* `expo_lt`, `expo_injOn`: the exponent map of the star is injective and below `L`;
* `ecoef seed z i`: the base-`B` digits of `e = Σ* (z + P_k) B^(L − e(k))`, with
  `sum_eq_ecoef` (regrouping) and `ecoef_bounds` (digits in `[0, 2z)`);
* `cval_pow`: `(1 + Σ_j zⱼ B^(5^j))⁴ = Σ* c_k z^k B^(e(k))` (multinomial theorem);
* `sum_mult_pCoefficient`: `Σ* c_k z^k P_k = 24 · P(z)` for `P` of total degree `≤ 4`;
* `hcoef`, `H_eq`, `hcoef_L`, `abs_hcoef_le`: `c⁴(e − zλ) = Σ_{i<8L} hᵢ Bⁱ`, `h_L = 24 P(z)`,
  `|hᵢ| ≤ z (1 + Σ zⱼ)⁴` (the article's (4.9)–(4.11));
* the index facts of `indexZ seed 0`, `indexY seed 0`: `|P_k| + 1 < z`, `4 ≤ z`,
  `y = Σ* (z + P_k)(2z)^(L − e(k))`, `2(2z)^L ≤ y`, `2z(ν+2)⁴ < y`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelCoding
open ExecutableJones

/-! ### The star and its exponent map -/

section Star
variable {ν : ℕ}

theorem mem_codingStar {k : Fin (ν + 2) → ℕ} : k ∈ codingStar ν 4 ↔ ∑ j, k j = 4 := by
  simp [codingStar, Finset.mem_piAntidiag]

theorem le_four_of_mem {k : Fin (ν + 2) → ℕ} (hk : k ∈ codingStar ν 4) (j : Fin (ν + 2)) :
    k j ≤ 4 := by
  have h := mem_codingStar.mp hk
  have := Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  omega

theorem sum_four_mul_pow (n : ℕ) : ∑ j ∈ Finset.range n, 4 * 5 ^ j + 1 = 5 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

theorem codingLexp_eq (ν : ℕ) : codingLexp ν 4 = 5 ^ (ν + 1) := rfl

theorem codingLexp_pos (ν : ℕ) : 0 < codingLexp ν 4 := pow_pos (by decide) _

theorem expo_lt {k : Fin (ν + 2) → ℕ} (hk : k ∈ codingStar ν 4) :
    codingExpo ν 4 k < codingLexp ν 4 := by
  have h1 : codingExpo ν 4 k ≤ ∑ j : Fin (ν + 1), 4 * 5 ^ (j : ℕ) := by
    unfold codingExpo
    apply Finset.sum_le_sum
    intro j _
    exact Nat.mul_le_mul (le_four_of_mem hk j.succ) (le_refl _)
  have h2 : ∑ j : Fin (ν + 1), 4 * 5 ^ (j : ℕ) = ∑ j ∈ Finset.range (ν + 1), 4 * 5 ^ j :=
    Fin.sum_univ_eq_sum_range (fun j => 4 * 5 ^ j) (ν + 1)
  have h3 := sum_four_mul_pow (ν + 1)
  have h4 := codingLexp_eq ν
  omega

/-- Uniqueness of base-5 digits. -/
theorem base5_inj : ∀ (n : ℕ) (a c : Fin n → ℕ), (∀ j, a j < 5) → (∀ j, c j < 5) →
    ∑ j, a j * 5 ^ (j : ℕ) = ∑ j, c j * 5 ^ (j : ℕ) → a = c
  | 0, _, _, _, _, _ => funext fun j => j.elim0
  | n + 1, a, c, ha, hc, h => by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at h
    have hs : ∀ f : Fin (n + 1) → ℕ, ∑ j : Fin n, f j.succ * 5 ^ ((j.succ : Fin (n + 1)) : ℕ) =
        5 * ∑ j : Fin n, f j.succ * 5 ^ (j : ℕ) := by
      intro f
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Fin.val_succ, pow_succ]
      ring
    rw [hs a, hs c] at h
    simp only [Fin.val_zero, pow_zero, mul_one] at h
    have ha0 := ha 0
    have hc0 := hc 0
    have h0 : a 0 = c 0 := by omega
    have ht : ∑ j : Fin n, a j.succ * 5 ^ (j : ℕ) = ∑ j : Fin n, c j.succ * 5 ^ (j : ℕ) := by
      omega
    have hrec := base5_inj n (fun j => a j.succ) (fun j => c j.succ) (fun j => ha _)
      (fun j => hc _) ht
    funext j
    refine Fin.cases h0 (fun i => ?_) j
    exact congrFun hrec i

theorem expo_injOn {k k' : Fin (ν + 2) → ℕ} (hk : k ∈ codingStar ν 4)
    (hk' : k' ∈ codingStar ν 4) (h : codingExpo ν 4 k = codingExpo ν 4 k') : k = k' := by
  have ht : (fun j : Fin (ν + 1) => k j.succ) = fun j => k' j.succ :=
    base5_inj (ν + 1) (fun j => k j.succ) (fun j => k' j.succ)
      (fun j => show k j.succ < 5 by have := le_four_of_mem hk j.succ; omega)
      (fun j => show k' j.succ < 5 by have := le_four_of_mem hk' j.succ; omega) h
  have hs := mem_codingStar.mp hk
  have hs' := mem_codingStar.mp hk'
  rw [Fin.sum_univ_succ] at hs hs'
  have htail : ∑ j : Fin (ν + 1), k j.succ = ∑ j : Fin (ν + 1), k' j.succ :=
    Finset.sum_congr rfl (fun j _ => congrFun ht j)
  funext j
  refine Fin.cases ?_ (fun i => congrFun ht i) j
  omega

end Star

/-! ### The digits of `e` -/

section Digits
variable {ν : ℕ} (seed : Expr (Fin (ν + 1)))

/-- The base-`B` digit of `e = Σ* (z + P_k) B^(L − e(k))` at position `i`. -/
def ecoef (z : ℕ) (i : ℕ) : ℤ :=
  ∑ k ∈ codingStar ν 4,
    if codingLexp ν 4 - codingExpo ν 4 k = i then (z : ℤ) + pCoefficient seed k else 0

theorem ecoef_of_mem (z : ℕ) {k : Fin (ν + 2) → ℕ} (hk : k ∈ codingStar ν 4) :
    ecoef seed z (codingLexp ν 4 - codingExpo ν 4 k) = (z : ℤ) + pCoefficient seed k := by
  unfold ecoef
  rw [Finset.sum_eq_single k]
  · rw [if_pos rfl]
  · intro k' hk' hne
    rw [if_neg]
    intro h
    apply hne
    have h1 := expo_lt hk
    have h2 := expo_lt hk'
    exact expo_injOn hk' hk (by omega)
  · intro h
    exact absurd hk h

theorem ecoef_of_not (z i : ℕ) (h : ∀ k ∈ codingStar ν 4, codingLexp ν 4 - codingExpo ν 4 k ≠ i) :
    ecoef seed z i = 0 :=
  Finset.sum_eq_zero (fun k hk => if_neg (h k hk))

/-- The digits lie in `[0, 2z)`, and `|z − dᵢ| ≤ z`. -/
theorem ecoef_bounds {z : ℕ} (hz : ∀ k ∈ codingStar ν 4, |pCoefficient seed k| + 1 < (z : ℤ))
    (hz2 : 2 ≤ z) (i : ℕ) :
    0 ≤ ecoef seed z i ∧ ecoef seed z i < 2 * (z : ℤ) ∧ |(z : ℤ) - ecoef seed z i| ≤ z := by
  by_cases h : ∃ k ∈ codingStar ν 4, codingLexp ν 4 - codingExpo ν 4 k = i
  · obtain ⟨k, hk, rfl⟩ := h
    rw [ecoef_of_mem seed z hk]
    have h1 := hz k hk
    have h2 := neg_abs_le (pCoefficient seed k)
    have h3 := le_abs_self (pCoefficient seed k)
    refine ⟨by linarith, by linarith, ?_⟩
    rw [show (z : ℤ) - ((z : ℤ) + pCoefficient seed k) = -pCoefficient seed k by ring, abs_neg]
    linarith
  · rw [ecoef_of_not seed z i (fun k hk he => h ⟨k, hk, he⟩)]
    have hz0 : (2 : ℤ) ≤ z := by exact_mod_cast hz2
    refine ⟨le_refl 0, by linarith, ?_⟩
    simp only [sub_zero]
    exact le_of_eq (abs_of_nonneg (by linarith))

variable {R : Type*} [CommRing R]

/-- Regrouping `Σ* (z + P_k) B^(L − e(k))` by positions (`L < n`). -/
theorem sum_eq_ecoef (z : ℕ) (B : R) (n : ℕ) (hn : codingLexp ν 4 < n) :
    ∑ k ∈ codingStar ν 4, ((z : R) + (pCoefficient seed k : R)) *
        B ^ (codingLexp ν 4 - codingExpo ν 4 k) =
      ∑ i ∈ Finset.range n, (ecoef seed z i : R) * B ^ i := by
  have h1 : ∀ i, (ecoef seed z i : R) * B ^ i = ∑ k ∈ codingStar ν 4,
      if codingLexp ν 4 - codingExpo ν 4 k = i then
        ((z : R) + (pCoefficient seed k : R)) * B ^ i else 0 := by
    intro i
    unfold ecoef
    rw [Int.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    split_ifs <;> simp
  calc ∑ k ∈ codingStar ν 4, ((z : R) + (pCoefficient seed k : R)) *
        B ^ (codingLexp ν 4 - codingExpo ν 4 k)
      = ∑ k ∈ codingStar ν 4, ∑ i ∈ Finset.range n,
          (if codingLexp ν 4 - codingExpo ν 4 k = i then
            ((z : R) + (pCoefficient seed k : R)) * B ^ i else 0) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (by omega))]
    _ = ∑ i ∈ Finset.range n, ∑ k ∈ codingStar ν 4,
          (if codingLexp ν 4 - codingExpo ν 4 k = i then
            ((z : R) + (pCoefficient seed k : R)) * B ^ i else 0) := Finset.sum_comm
    _ = ∑ i ∈ Finset.range n, (ecoef seed z i : R) * B ^ i :=
        Finset.sum_congr rfl (fun i _ => (h1 i).symm)

end Digits

/-! ### The multinomial expansion of the code -/

section Multinomial
variable {ν : ℕ} {R : Type*} [CommRing R]

/-- The multinomial coefficient `c_k`. -/
def mult (k : Fin (ν + 2) → ℕ) : ℕ := Nat.multinomial Finset.univ k

/-- `z^k = Π_j zⱼ^(k (j+1))`. -/
def zpow (zs : Fin (ν + 1) → R) (k : Fin (ν + 2) → ℕ) : R := ∏ j : Fin (ν + 1), zs j ^ k j.succ

/-- The code `c = 1 + Σ_j zⱼ B^(5^j)` (with `z₀ = x`). -/
def cval (zs : Fin (ν + 1) → R) (B : R) : R := 1 + ∑ j : Fin (ν + 1), zs j * B ^ (5 ^ (j : ℕ))

/-- The terms of the code. -/
def cterm (zs : Fin (ν + 1) → R) (B : R) : Fin (ν + 2) → R :=
  Fin.cons (α := fun _ => R) 1 (fun j => zs j * B ^ (5 ^ (j : ℕ)))

theorem cterm_zero (zs : Fin (ν + 1) → R) (B : R) : cterm zs B 0 = 1 := Fin.cons_zero _ _

theorem cterm_succ (zs : Fin (ν + 1) → R) (B : R) (j : Fin (ν + 1)) :
    cterm zs B j.succ = zs j * B ^ (5 ^ (j : ℕ)) := Fin.cons_succ _ _ _

theorem zpow_nonneg [LinearOrder R] [IsStrictOrderedRing R] {zs : Fin (ν + 1) → R}
    (hzs : ∀ j, 0 ≤ zs j) (k : Fin (ν + 2) → ℕ) : 0 ≤ zpow zs k :=
  Finset.prod_nonneg (fun j _ => pow_nonneg (hzs j) _)

/-- **The multinomial theorem for the code**: `c⁴ = Σ* c_k z^k B^(e(k))`. -/
theorem cval_pow (zs : Fin (ν + 1) → R) (B : R) :
    cval zs B ^ 4 = ∑ k ∈ codingStar ν 4, (mult k : R) * zpow zs k * B ^ codingExpo ν 4 k := by
  have hc : cval zs B = ∑ j : Fin (ν + 2), cterm zs B j := by
    rw [Fin.sum_univ_succ, cterm_zero]
    simp only [cterm_succ]
    rfl
  rw [hc, Finset.sum_pow_eq_sum_piAntidiag]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have e1 : ∏ i : Fin (ν + 2), cterm zs B i ^ k i = zpow zs k * B ^ codingExpo ν 4 k := by
    rw [Fin.prod_univ_succ, cterm_zero, one_pow, one_mul]
    have e2 : ∀ j : Fin (ν + 1), cterm zs B j.succ ^ k j.succ =
        zs j ^ k j.succ * B ^ (k j.succ * 5 ^ (j : ℕ)) := by
      intro j
      rw [cterm_succ, mul_pow, ← pow_mul, mul_comm (5 ^ (j : ℕ))]
    rw [Finset.prod_congr rfl (fun j _ => e2 j), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
    rfl
  rw [e1]
  unfold mult
  ring

/-- `Σ* c_k z^k = (1 + Σ_j zⱼ)⁴` (`cval_pow` at `B = 1`). -/
theorem sum_mult_zpow (zs : Fin (ν + 1) → R) :
    ∑ k ∈ codingStar ν 4, (mult k : R) * zpow zs k = cval zs 1 ^ 4 := by
  rw [cval_pow]
  exact Finset.sum_congr rfl (fun k _ => by rw [one_pow, mul_one])

end Multinomial

/-! ### The coefficient identity `Σ* c_k z^k P_k = 24 P(z)` -/

section Coefficients
variable {ν : ℕ} {R : Type*} [CommRing R]

theorem evalRing_eq_eval₂ {σ : Type*} (e : Expr σ) (v : σ → R) :
    e.evalRing v = MvPolynomial.eval₂ (Int.castRingHom R) v e.toPolynomial := by
  induction e with
  | constant a =>
      show (a : R) = MvPolynomial.eval₂ (Int.castRingHom R) v (MvPolynomial.C a)
      rw [MvPolynomial.eval₂_C]
      rfl
  | var i => simp only [Expr.evalRing, Expr.toPolynomial, MvPolynomial.eval₂_X]
  | add p q hp hq => simp only [Expr.evalRing, Expr.toPolynomial, MvPolynomial.eval₂_add, hp, hq]
  | sub p q hp hq => simp only [Expr.evalRing, Expr.toPolynomial, MvPolynomial.eval₂_sub, hp, hq]
  | mul p q hp hq => simp only [Expr.evalRing, Expr.toPolynomial, MvPolynomial.eval₂_mul, hp, hq]

/-- A tail of exponents completed to a degree-four vector. -/
def extend (d : Fin (ν + 1) →₀ ℕ) : Fin (ν + 2) → ℕ :=
  Fin.cons (α := fun _ => ℕ) (4 - ∑ j, d j) (fun j => d j)

theorem extend_zero (d : Fin (ν + 1) →₀ ℕ) : extend d 0 = 4 - ∑ j, d j := Fin.cons_zero _ _

theorem extend_succ (d : Fin (ν + 1) →₀ ℕ) (j : Fin (ν + 1)) : extend d j.succ = d j :=
  Fin.cons_succ _ _ _

/-- **(3.10)/(M5).** `Σ* c_k z^k P_k = 4! · P(z)` for a seed of total degree `≤ 4`. -/
theorem sum_mult_pCoefficient (seed : Expr (Fin (ν + 1)))
    (hP : seed.toPolynomial.totalDegree ≤ 4) (zs : Fin (ν + 1) → R) :
    ∑ k ∈ codingStar ν 4, (mult k : R) * zpow zs k * (pCoefficient seed k : R) =
      24 * seed.evalRing zs := by
  have hcoef : ∀ k ∈ codingStar ν 4, (mult k : R) * (pCoefficient seed k : R) =
      24 * ((MvPolynomial.coeff (SyntaxCoefficients.exponent fun j => k j.succ)
        seed.toPolynomial : ℤ) : R) := by
    intro k hk
    have hspec := Nat.multinomial_spec (Finset.univ : Finset (Fin (ν + 2))) k
    rw [mem_codingStar.mp hk] at hspec
    have h24 : (∏ i, (k i).factorial) * Nat.multinomial Finset.univ k = 24 := by
      rw [hspec]; rfl
    have hZ : (mult k : ℤ) * pCoefficient seed k =
        24 * MvPolynomial.coeff (SyntaxCoefficients.exponent fun j => k j.succ)
          seed.toPolynomial := by
      unfold pCoefficient mult
      rw [SyntaxCoefficients.coefficient_expand, ← mul_assoc]
      congr 1
      rw [mul_comm]
      exact_mod_cast h24
    have h := congrArg (fun t : ℤ => (t : R)) hZ
    push_cast at h
    exact h
  have hL : ∑ k ∈ codingStar ν 4, (mult k : R) * zpow zs k * (pCoefficient seed k : R) =
      24 * ∑ k ∈ codingStar ν 4,
        ((MvPolynomial.coeff (SyntaxCoefficients.exponent fun j => k j.succ)
          seed.toPolynomial : ℤ) : R) * zpow zs k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    calc (mult k : R) * zpow zs k * (pCoefficient seed k : R)
        = ((mult k : R) * (pCoefficient seed k : R)) * zpow zs k := by ring
      _ = _ := by rw [hcoef k hk]; ring
  have hfg : ∀ d : Fin (ν + 1) →₀ ℕ,
      (Int.castRingHom R) (MvPolynomial.coeff d seed.toPolynomial) * ∏ i, zs i ^ d i =
        ((MvPolynomial.coeff (SyntaxCoefficients.exponent fun j => extend d j.succ)
          seed.toPolynomial : ℤ) : R) * zpow zs (extend d) := by
    intro d
    have htail : SyntaxCoefficients.exponent (fun j => extend d j.succ) = d := by
      ext j
      simp [extend_succ]
    rw [htail]
    unfold zpow
    simp only [extend_succ, eq_intCast]
  rw [hL, evalRing_eq_eval₂, MvPolynomial.eval₂_eq']
  congr 1
  symm
  refine Finset.sum_bij_ne_zero (fun d _ _ => extend d) ?_ ?_ ?_ ?_
  · intro d hd _
    rw [mem_codingStar, Fin.sum_univ_succ, extend_zero]
    simp only [extend_succ]
    have h1 : ∑ i, d i ≤ 4 := by
      have h := MvPolynomial.le_totalDegree hd
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h
      exact le_trans h hP
    omega
  · intro d₁ _ _ d₂ _ _ h
    exact Finsupp.ext fun j => by rw [← extend_succ d₁ j, ← extend_succ d₂ j, h]
  · intro k hk hne
    have hk0 : extend (SyntaxCoefficients.exponent fun j => k j.succ) = k := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · rw [extend_zero]
        have hs : ∑ j, (SyntaxCoefficients.exponent fun j => k j.succ) j =
            ∑ j : Fin (ν + 1), k j.succ :=
          Finset.sum_congr rfl (fun j _ => by simp)
        have h4 := mem_codingStar.mp hk
        rw [Fin.sum_univ_succ] at h4
        omega
      · rw [extend_succ]
        simp
    refine ⟨SyntaxCoefficients.exponent fun j => k j.succ, ?_, ?_, hk0⟩
    · rw [MvPolynomial.mem_support_iff]
      intro h0
      apply hne
      simp [h0]
    · rw [hfg, hk0]
      exact hne
  · intro d _ _
    exact hfg d

end Coefficients

/-! ### The coefficients `hᵢ` of `c⁴ (e − zλ)` -/

section Hcoef
variable {ν : ℕ} {R : Type*} [CommRing R] (seed : Expr (Fin (ν + 1)))

theorem sum_ite_add_eq (e i n : ℕ) (Y : ℕ → R) :
    ∑ a ∈ Finset.range n, (if e + a = i then Y a else 0) =
      if e ≤ i ∧ i - e < n then Y (i - e) else 0 := by
  by_cases h : e ≤ i ∧ i - e < n
  · rw [if_pos h]
    rw [Finset.sum_eq_single (i - e)]
    · rw [if_pos (by omega)]
    · intro a _ ha
      rw [if_neg (by omega)]
    · intro hne
      exact absurd (Finset.mem_range.mpr h.2) hne
  · rw [if_neg h]
    refine Finset.sum_eq_zero (fun a ha => if_neg ?_)
    intro he
    have := Finset.mem_range.mp ha
    exact h ⟨by omega, by omega⟩

/-- The coefficient of `Bⁱ` in `c⁴ (e − zλ)` (`i < 8L`). -/
def hcoef (z : ℕ) (zs : Fin (ν + 1) → R) (i : ℕ) : R :=
  ∑ k ∈ codingStar ν 4, ∑ a ∈ Finset.range (4 * codingLexp ν 4),
    if codingExpo ν 4 k + a = i then
      (mult k : R) * zpow zs k * ((ecoef seed z a : R) - z) else 0

theorem hcoef_eq (z : ℕ) (zs : Fin (ν + 1) → R) (i : ℕ) :
    hcoef seed z zs i = ∑ k ∈ codingStar ν 4,
      if codingExpo ν 4 k ≤ i ∧ i - codingExpo ν 4 k < 4 * codingLexp ν 4 then
        (mult k : R) * zpow zs k * ((ecoef seed z (i - codingExpo ν 4 k) : R) - z) else 0 := by
  unfold hcoef
  exact Finset.sum_congr rfl (fun k _ => sum_ite_add_eq _ _ _ _)

/-- **(4.9)**: `c⁴ (e − zλ) = Σ_{i<8L} hᵢ Bⁱ`, with `e`, `λ` as sums over `4L` positions. -/
theorem H_eq (z : ℕ) (zs : Fin (ν + 1) → R) (B : R) :
    cval zs B ^ 4 * (∑ a ∈ Finset.range (4 * codingLexp ν 4), (ecoef seed z a : R) * B ^ a -
        (z : R) * ∑ a ∈ Finset.range (4 * codingLexp ν 4), B ^ a) =
      ∑ i ∈ Finset.range (8 * codingLexp ν 4), hcoef seed z zs i * B ^ i := by
  have hD : ∑ a ∈ Finset.range (4 * codingLexp ν 4), (ecoef seed z a : R) * B ^ a -
      (z : R) * ∑ a ∈ Finset.range (4 * codingLexp ν 4), B ^ a =
      ∑ a ∈ Finset.range (4 * codingLexp ν 4), ((ecoef seed z a : R) - z) * B ^ a := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  rw [hD, cval_pow, Finset.sum_mul_sum]
  symm
  calc ∑ i ∈ Finset.range (8 * codingLexp ν 4), hcoef seed z zs i * B ^ i
      = ∑ i ∈ Finset.range (8 * codingLexp ν 4), ∑ k ∈ codingStar ν 4,
          ∑ a ∈ Finset.range (4 * codingLexp ν 4),
            (if codingExpo ν 4 k + a = i then
              (mult k : R) * zpow zs k * ((ecoef seed z a : R) - z) * B ^ i else 0) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        unfold hcoef
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        split_ifs <;> simp
    _ = ∑ k ∈ codingStar ν 4, ∑ i ∈ Finset.range (8 * codingLexp ν 4),
          ∑ a ∈ Finset.range (4 * codingLexp ν 4),
            (if codingExpo ν 4 k + a = i then
              (mult k : R) * zpow zs k * ((ecoef seed z a : R) - z) * B ^ i else 0) :=
        Finset.sum_comm
    _ = ∑ k ∈ codingStar ν 4, ∑ a ∈ Finset.range (4 * codingLexp ν 4),
          ∑ i ∈ Finset.range (8 * codingLexp ν 4),
            (if codingExpo ν 4 k + a = i then
              (mult k : R) * zpow zs k * ((ecoef seed z a : R) - z) * B ^ i else 0) :=
        Finset.sum_congr rfl (fun k _ => Finset.sum_comm)
    _ = ∑ k ∈ codingStar ν 4, ∑ a ∈ Finset.range (4 * codingLexp ν 4),
          (mult k : R) * zpow zs k * ((ecoef seed z a : R) - z) *
            B ^ (codingExpo ν 4 k + a) := by
        refine Finset.sum_congr rfl (fun k hk => Finset.sum_congr rfl (fun a ha => ?_))
        have h1 := expo_lt hk
        have h2 := Finset.mem_range.mp ha
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (by omega))]
    _ = ∑ k ∈ codingStar ν 4, ∑ a ∈ Finset.range (4 * codingLexp ν 4),
          (mult k : R) * zpow zs k * B ^ codingExpo ν 4 k *
            (((ecoef seed z a : R) - z) * B ^ a) := by
        refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun a _ => ?_))
        rw [pow_add]
        ring

/-- **(4.10)/(M5)**: the coefficient of `B^L` is `24 · P(z)`. -/
theorem hcoef_L (hP : seed.toPolynomial.totalDegree ≤ 4) (z : ℕ) (zs : Fin (ν + 1) → R) :
    hcoef seed z zs (codingLexp ν 4) = 24 * seed.evalRing zs := by
  rw [hcoef_eq, ← sum_mult_pCoefficient seed hP zs]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have h1 := expo_lt hk
  have h4 := codingLexp_pos ν
  rw [if_pos ⟨le_of_lt h1, by omega⟩, ecoef_of_mem seed z hk]
  push_cast
  ring

/-- The bound `|hᵢ| ≤ z (1 + Σ zⱼ)⁴`. -/
theorem abs_hcoef_le [LinearOrder R] [IsStrictOrderedRing R] {z : ℕ}
    (hz : ∀ k ∈ codingStar ν 4, |pCoefficient seed k| + 1 < (z : ℤ)) (hz2 : 2 ≤ z)
    {zs : Fin (ν + 1) → R} (hzs : ∀ j, 0 ≤ zs j) (i : ℕ) :
    |hcoef seed z zs i| ≤ (z : R) * cval zs 1 ^ 4 := by
  have habs : ∀ a, |(ecoef seed z a : R) - z| ≤ (z : R) := by
    intro a
    have h := (ecoef_bounds seed hz hz2 a).2.2
    have h' : ((|(z : ℤ) - ecoef seed z a| : ℤ) : R) ≤ ((z : ℤ) : R) := Int.cast_le.mpr h
    push_cast at h'
    rw [abs_sub_comm]
    exact h'
  have hnn : ∀ k, 0 ≤ (mult k : R) * zpow zs k :=
    fun k => mul_nonneg (Nat.cast_nonneg _) (zpow_nonneg hzs k)
  have hk : ∀ k ∈ codingStar ν 4,
      |(if codingExpo ν 4 k ≤ i ∧ i - codingExpo ν 4 k < 4 * codingLexp ν 4 then
        (mult k : R) * zpow zs k * ((ecoef seed z (i - codingExpo ν 4 k) : R) - z) else 0)| ≤
      (mult k : R) * zpow zs k * z := by
    intro k _
    split_ifs
    · rw [abs_mul, abs_of_nonneg (hnn k)]
      exact mul_le_mul_of_nonneg_left (habs _) (hnn k)
    · rw [abs_zero]
      exact mul_nonneg (hnn k) (Nat.cast_nonneg z)
  rw [hcoef_eq]
  calc |∑ k ∈ codingStar ν 4,
        (if codingExpo ν 4 k ≤ i ∧ i - codingExpo ν 4 k < 4 * codingLexp ν 4 then
          (mult k : R) * zpow zs k * ((ecoef seed z (i - codingExpo ν 4 k) : R) - z) else 0)|
      ≤ ∑ k ∈ codingStar ν 4,
        |(if codingExpo ν 4 k ≤ i ∧ i - codingExpo ν 4 k < 4 * codingLexp ν 4 then
          (mult k : R) * zpow zs k * ((ecoef seed z (i - codingExpo ν 4 k) : R) - z) else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ codingStar ν 4, (mult k : R) * zpow zs k * z := Finset.sum_le_sum hk
    _ = (z : R) * ∑ k ∈ codingStar ν 4, (mult k : R) * zpow zs k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by ring)
    _ = (z : R) * cval zs 1 ^ 4 := by rw [sum_mult_zpow]

/-- `λ (1 + q⁴) = Σ_{i<8L} Bⁱ` for `λ = Σ_{i<4L} Bⁱ`, `q = B^L`. -/
theorem lam_mul_one_add (B : R) (L : ℕ) :
    (∑ i ∈ Finset.range (4 * L), B ^ i) * (1 + (B ^ L) ^ 4) =
      ∑ i ∈ Finset.range (8 * L), B ^ i := by
  rw [show 8 * L = 4 * L + 4 * L by omega, Finset.sum_range_add, mul_add, mul_one, ← pow_mul,
    Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_add]
  ring

/-- `(B − 1) Σ_{i<n} Bⁱ + 1 = Bⁿ`. -/
theorem geom_identity (B : R) (n : ℕ) : (B - 1) * ∑ i ∈ Finset.range n, B ^ i + 1 = B ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ, ← ih]
    ring

/-- **(4.9)–(4.11)**: with `B = 2E`,
`S₃ = 2(e − zλ)c⁴ + λB + λBq⁴ = 2 Σ_{i<8L} (hᵢ + E) Bⁱ`. -/
theorem third_eq (z : ℕ) (zs : Fin (ν + 1) → R) (B E : R) (hBE : B = 2 * E) :
    2 * (∑ k ∈ codingStar ν 4, ((z : R) + (pCoefficient seed k : R)) *
          B ^ (codingLexp ν 4 - codingExpo ν 4 k) -
        (z : R) * ∑ i ∈ Finset.range (4 * codingLexp ν 4), B ^ i) * cval zs B ^ 4 +
      (∑ i ∈ Finset.range (4 * codingLexp ν 4), B ^ i) * B +
      (∑ i ∈ Finset.range (4 * codingLexp ν 4), B ^ i) * B * (B ^ codingLexp ν 4) ^ 4 =
    2 * ∑ i ∈ Finset.range (8 * codingLexp ν 4), (hcoef seed z zs i + E) * B ^ i := by
  have hL := codingLexp_pos ν
  rw [sum_eq_ecoef seed z B (4 * codingLexp ν 4) (by omega)]
  have h1 := H_eq seed z zs B
  have h2 := lam_mul_one_add B (codingLexp ν 4)
  calc 2 * (∑ i ∈ Finset.range (4 * codingLexp ν 4), (ecoef seed z i : R) * B ^ i -
          (z : R) * ∑ i ∈ Finset.range (4 * codingLexp ν 4), B ^ i) * cval zs B ^ 4 +
        (∑ i ∈ Finset.range (4 * codingLexp ν 4), B ^ i) * B +
        (∑ i ∈ Finset.range (4 * codingLexp ν 4), B ^ i) * B * (B ^ codingLexp ν 4) ^ 4
      = 2 * (cval zs B ^ 4 * (∑ a ∈ Finset.range (4 * codingLexp ν 4),
            (ecoef seed z a : R) * B ^ a -
          (z : R) * ∑ a ∈ Finset.range (4 * codingLexp ν 4), B ^ a)) +
        B * ((∑ i ∈ Finset.range (4 * codingLexp ν 4), B ^ i) *
          (1 + (B ^ codingLexp ν 4) ^ 4)) := by ring
    _ = 2 * ∑ i ∈ Finset.range (8 * codingLexp ν 4), hcoef seed z zs i * B ^ i +
        B * ∑ i ∈ Finset.range (8 * codingLexp ν 4), B ^ i := by rw [h1, h2]
    _ = 2 * ∑ i ∈ Finset.range (8 * codingLexp ν 4), (hcoef seed z zs i + E) * B ^ i := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hBE]
        ring

end Hcoef

/-! ### Two estimates in an ordered ring -/

section Estimates
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The size of `S₃`: `0 ≤ S₃ < q⁹`, from `0 ≤ e < q² ≤ λ`, `1 ≤ z`, `0 ≤ c ≤ q`, `2z ≤ B`,
`(B − 1)λ + 1 = q⁴`, `2 ≤ B`, `5 ≤ q`. -/
theorem third_bounds (e z lam B q c : R) (he : 0 ≤ e) (heq : e < q ^ 2) (hq2 : q ^ 2 ≤ lam)
    (hz : 1 ≤ z) (hc0 : 0 ≤ c) (hcq : c ≤ q) (hzB : 2 * z ≤ B)
    (hgeom : (B - 1) * lam + 1 = q ^ 4) (hB2 : 2 ≤ B) (hq5 : 5 ≤ q) :
    0 ≤ 2 * (e - z * lam) * c ^ 4 + lam * B + lam * B * q ^ 4 ∧
      2 * (e - z * lam) * c ^ 4 + lam * B + lam * B * q ^ 4 < q ^ 9 := by
  have hlam0 : 0 ≤ lam := le_trans (sq_nonneg q) hq2
  have hq0 : 0 ≤ q := le_trans hc0 hcq
  have hc4 : c ^ 4 ≤ q ^ 4 := pow_le_pow_left₀ hc0 hcq 4
  have hq4 : 0 ≤ q ^ 4 := pow_nonneg hq0 4
  have hc40 : 0 ≤ c ^ 4 := pow_nonneg hc0 4
  constructor
  · have h1 : z * lam * c ^ 4 ≤ z * lam * q ^ 4 :=
      mul_le_mul_of_nonneg_left hc4 (mul_nonneg (by linarith) hlam0)
    have h2 : 0 ≤ e * c ^ 4 := mul_nonneg he hc40
    have h3 : 2 * z * (lam * q ^ 4) ≤ B * (lam * q ^ 4) :=
      mul_le_mul_of_nonneg_right hzB (mul_nonneg hlam0 hq4)
    have h4 : 0 ≤ lam * B := mul_nonneg hlam0 (by linarith)
    linarith
  · have h5 : e ≤ z * lam := by
      have : lam ≤ z * lam := le_mul_of_one_le_left hlam0 hz
      linarith
    have h6 : (e - z * lam) * c ^ 4 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hc40
    have h7a : 1 * lam ≤ (B - 1) * lam := mul_le_mul_of_nonneg_right (by linarith) hlam0
    have h7 : lam * B ≤ 2 * q ^ 4 := by linarith
    have h8 : lam * B * q ^ 4 ≤ 2 * q ^ 4 * q ^ 4 := mul_le_mul_of_nonneg_right h7 hq4
    have hq8 : 0 < q ^ 8 := pow_pos (by linarith) 8
    have h9 : 4 * q ^ 8 < q * q ^ 8 := mul_lt_mul_of_pos_right (by linarith) hq8
    have h10 : q ^ 4 ≤ q ^ 8 := pow_le_pow_right₀ (by linarith) (by omega)
    have e1 : q * q ^ 8 = q ^ 9 := by ring
    have e2 : 2 * q ^ 4 * q ^ 4 = 2 * q ^ 8 := by ring
    linarith

/-- `2 z (1 + Σ zⱼ)⁴ < b⁵` for digits `0 ≤ zⱼ ≤ b − 1` and `2z(ν+2)⁴ < b`. -/
theorem code_bound {ν : ℕ} (z b : R) (zs : Fin (ν + 1) → R) (hzs0 : ∀ j, 0 ≤ zs j)
    (hzsb : ∀ j, zs j + 1 ≤ b) (hz : 0 < z) (hzb : 2 * z * ((ν : R) + 2) ^ 4 < b) (hb : 0 < b) :
    2 * (z * cval zs 1 ^ 4) < b ^ 5 := by
  have hc : cval zs 1 = 1 + ∑ j, zs j := by
    unfold cval
    simp only [one_pow, mul_one]
  have hsum : ∑ j, zs j ≤ ∑ _j : Fin (ν + 1), (b - 1) :=
    Finset.sum_le_sum (fun j _ => by have := hzsb j; linarith)
  have hconst : ∑ _j : Fin (ν + 1), (b - 1) = ((ν : R) + 1) * (b - 1) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one]
  have hν0 : (0 : R) ≤ ν := Nat.cast_nonneg ν
  have hs0 : 0 ≤ 1 + ∑ j, zs j := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hzs0 j)
    linarith
  have hlt : 1 + ∑ j, zs j < ((ν : R) + 2) * b := by
    have e : ((ν : R) + 2) * b - (1 + ((ν : R) + 1) * (b - 1)) = b + ν := by ring
    linarith
  have h4 : (1 + ∑ j, zs j) ^ 4 < (((ν : R) + 2) * b) ^ 4 :=
    pow_lt_pow_left₀ hlt hs0 (by decide)
  have h5 : z * (1 + ∑ j, zs j) ^ 4 < z * (((ν : R) + 2) * b) ^ 4 :=
    mul_lt_mul_of_pos_left h4 hz
  have hb4 : 0 < b ^ 4 := pow_pos hb 4
  have h6 : 2 * z * ((ν : R) + 2) ^ 4 * b ^ 4 < b * b ^ 4 := mul_lt_mul_of_pos_right hzb hb4
  have e3 : z * (((ν : R) + 2) * b) ^ 4 = z * ((ν : R) + 2) ^ 4 * b ^ 4 := by ring
  have e4 : b * b ^ 4 = b ^ 5 := by ring
  rw [hc]
  linarith

end Estimates

/-- Evaluation at an integer point commutes with the cast. -/
theorem evalRing_intCast {R : Type*} [CommRing R] {σ : Type*} (e : Expr σ) (v : σ → ℤ) :
    e.evalRing (fun i => (v i : R)) = (e.eval v : R) := by
  induction e <;> simp_all [Expr.evalRing, Expr.eval]

/-! ### The index of the seed -/

section Index
variable {ν : ℕ} (seed : Expr (Fin (ν + 1)))

theorem indexZ_eq : indexZ seed 0 = 2 ^ indexExponent seed 0 := rfl

theorem indexExponent_eq :
    indexExponent seed 0 = 0 + (∑ k ∈ codingStar ν 4, (pCoefficient seed k).natAbs) + 2 := rfl

theorem two_le_indexExponent : 2 ≤ indexExponent seed 0 := by
  rw [indexExponent_eq]; omega

theorem four_le_indexZ : 4 ≤ indexZ seed 0 := by
  rw [indexZ_eq]
  calc 4 = 2 ^ 2 := rfl
    _ ≤ 2 ^ indexExponent seed 0 := Nat.pow_le_pow_right (by omega) (two_le_indexExponent seed)

theorem natAbs_add_one_lt {k : Fin (ν + 2) → ℕ} (hk : k ∈ codingStar ν 4) :
    (pCoefficient seed k).natAbs + 1 < indexZ seed 0 := by
  have h1 : (pCoefficient seed k).natAbs ≤ ∑ k ∈ codingStar ν 4, (pCoefficient seed k).natAbs :=
    Finset.single_le_sum (f := fun k => (pCoefficient seed k).natAbs)
      (fun _ _ => Nat.zero_le _) hk
  have h2 : indexExponent seed 0 < 2 ^ indexExponent seed 0 := Nat.lt_two_pow_self
  have h3 := indexExponent_eq seed
  have h4 := indexZ_eq seed
  omega

/-- `z > 1 + max* |P_k|`. -/
theorem index_big {k : Fin (ν + 2) → ℕ} (hk : k ∈ codingStar ν 4) :
    |pCoefficient seed k| + 1 < (indexZ seed 0 : ℤ) := by
  have h := natAbs_add_one_lt seed hk
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h

theorem index_big' : ∀ k ∈ codingStar ν 4, |pCoefficient seed k| + 1 < (indexZ seed 0 : ℤ) :=
  fun _ hk => index_big seed hk

theorem indexY_eq : (indexY seed 0 : ℤ) = ∑ k ∈ codingStar ν 4,
    ((indexZ seed 0 : ℤ) + pCoefficient seed k) *
      (2 * (indexZ seed 0 : ℤ)) ^ (codingLexp ν 4 - codingExpo ν 4 k) := by
  unfold indexY
  apply Int.toNat_of_nonneg
  apply Finset.sum_nonneg
  intro k hk
  have h1 := index_big seed hk
  have h2 := neg_abs_le (pCoefficient seed k)
  have h3 : (0 : ℤ) ≤ 2 * (indexZ seed 0 : ℤ) := by
    have := Nat.cast_nonneg (α := ℤ) (indexZ seed 0); linarith
  exact mul_nonneg (by linarith) (pow_nonneg h3 _)

/-- `y = Σ_{i<n} dᵢ (2z)ⁱ` for the digits `dᵢ = ecoef`. -/
theorem indexY_ecoef (n : ℕ) (hn : codingLexp ν 4 < n) :
    (indexY seed 0 : ℤ) = ∑ i ∈ Finset.range n,
      ecoef seed (indexZ seed 0) i * (2 * (indexZ seed 0 : ℤ)) ^ i := by
  have h := sum_eq_ecoef (R := ℤ) seed (indexZ seed 0) (2 * (indexZ seed 0 : ℤ)) n hn
  simp only [Int.cast_id] at h
  rw [indexY_eq, h]

/-- The digit at `L` of `y` (the term `k = (4, 0, …, 0)`) gives `y ≥ 2(2z)^L`. -/
theorem y_ge : 2 * (2 * indexZ seed 0) ^ codingLexp ν 4 ≤ indexY seed 0 := by
  have hk₀ : (Pi.single (0 : Fin (ν + 2)) 4 : Fin (ν + 2) → ℕ) ∈ codingStar ν 4 := by
    rw [mem_codingStar]; simp
  have he : codingExpo ν 4 (Pi.single (0 : Fin (ν + 2)) 4 : Fin (ν + 2) → ℕ) = 0 := by
    simp [codingExpo, Pi.single_apply, Fin.succ_ne_zero]
  have hz0 : (0 : ℤ) ≤ 2 * (indexZ seed 0 : ℤ) := by
    have := Nat.cast_nonneg (α := ℤ) (indexZ seed 0); linarith
  have h1 : ((indexZ seed 0 : ℤ) + pCoefficient seed (Pi.single (0 : Fin (ν + 2)) 4)) *
      (2 * (indexZ seed 0 : ℤ)) ^ (codingLexp ν 4 -
        codingExpo ν 4 (Pi.single (0 : Fin (ν + 2)) 4 : Fin (ν + 2) → ℕ)) ≤
      ∑ k ∈ codingStar ν 4, ((indexZ seed 0 : ℤ) + pCoefficient seed k) *
        (2 * (indexZ seed 0 : ℤ)) ^ (codingLexp ν 4 - codingExpo ν 4 k) := by
    apply Finset.single_le_sum (f := fun k => ((indexZ seed 0 : ℤ) + pCoefficient seed k) *
        (2 * (indexZ seed 0 : ℤ)) ^ (codingLexp ν 4 - codingExpo ν 4 k)) _ hk₀
    intro k hk
    have := index_big seed hk
    have := neg_abs_le (pCoefficient seed k)
    exact mul_nonneg (by linarith) (pow_nonneg hz0 _)
  rw [he, Nat.sub_zero] at h1
  have h2 : (2 : ℤ) ≤ (indexZ seed 0 : ℤ) + pCoefficient seed (Pi.single (0 : Fin (ν + 2)) 4) := by
    have := index_big seed hk₀
    have := neg_abs_le (pCoefficient seed (Pi.single (0 : Fin (ν + 2)) 4))
    linarith
  have h3 : (2 : ℤ) * (2 * (indexZ seed 0 : ℤ)) ^ codingLexp ν 4 ≤
      ((indexZ seed 0 : ℤ) + pCoefficient seed (Pi.single (0 : Fin (ν + 2)) 4)) *
        (2 * (indexZ seed 0 : ℤ)) ^ codingLexp ν 4 :=
    mul_le_mul_of_nonneg_right h2 (pow_nonneg hz0 _)
  have h4 : (2 : ℤ) * (2 * (indexZ seed 0 : ℤ)) ^ codingLexp ν 4 ≤ (indexY seed 0 : ℤ) := by
    rw [indexY_eq]; linarith
  exact_mod_cast h4

theorem two_z_le_y : 2 * indexZ seed 0 ≤ indexY seed 0 := by
  have h := y_ge seed
  have h2 : 2 * indexZ seed 0 ≤ (2 * indexZ seed 0) ^ codingLexp ν 4 :=
    Nat.le_self_pow (Nat.pos_iff_ne_zero.mp (codingLexp_pos ν)) _
  omega

/-- `2z(ν+2)⁴ < y` (for the bound `|hᵢ| < B/2`). -/
theorem y_big : 2 * indexZ seed 0 * (ν + 2) ^ 4 < indexY seed 0 := by
  have hz := four_le_indexZ seed
  have hL := codingLexp_eq ν
  have hL1 := codingLexp_pos ν
  have hpow : ∀ m : ℕ, 4 * (m + 1) + 7 ≤ 3 * 5 ^ (m + 1) := by
    intro m
    induction m with
    | zero => decide
    | succ m ih =>
      rw [pow_succ]
      omega
  have hA : 4 * ν + 4 ≤ 3 * (codingLexp ν 4 - 1) := by
    have := hpow ν
    omega
  have hB : ν + 2 ≤ 2 ^ (ν + 1) := by
    have : ν + 1 < 2 ^ (ν + 1) := Nat.lt_two_pow_self
    omega
  have hC : (ν + 2) ^ 4 ≤ 2 ^ (4 * ν + 4) := by
    calc (ν + 2) ^ 4 ≤ (2 ^ (ν + 1)) ^ 4 := Nat.pow_le_pow_left hB 4
      _ = 2 ^ (4 * ν + 4) := by
          rw [← pow_mul]
          congr 1
          omega
  have hD : 2 ^ (4 * ν + 4) ≤ 2 ^ (3 * (codingLexp ν 4 - 1)) := Nat.pow_le_pow_right (by omega) hA
  have hE : 2 ^ (3 * (codingLexp ν 4 - 1)) ≤ (2 * indexZ seed 0) ^ (codingLexp ν 4 - 1) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (show 2 ^ 3 ≤ 2 * indexZ seed 0 by
      have : (2 : ℕ) ^ 3 = 8 := rfl
      omega) _
  have hF : (2 * indexZ seed 0) ^ codingLexp ν 4 =
      (2 * indexZ seed 0) ^ (codingLexp ν 4 - 1) * (2 * indexZ seed 0) := by
    rw [← pow_succ]
    congr 1
    omega
  have hG : 0 < (2 * indexZ seed 0) ^ codingLexp ν 4 := pow_pos (by omega) _
  have hy := y_ge seed
  calc 2 * indexZ seed 0 * (ν + 2) ^ 4 ≤ 2 * indexZ seed 0 * 2 ^ (4 * ν + 4) :=
        Nat.mul_le_mul_left _ hC
    _ ≤ 2 * indexZ seed 0 * (2 * indexZ seed 0) ^ (codingLexp ν 4 - 1) :=
        Nat.mul_le_mul_left _ (hD.trans hE)
    _ = (2 * indexZ seed 0) ^ codingLexp ν 4 := by rw [hF]; ring
    _ < 2 * (2 * indexZ seed 0) ^ codingLexp ν 4 := by omega
    _ ≤ indexY seed 0 := hy

end Index

end DiophantineConsistency.ModelCoding
