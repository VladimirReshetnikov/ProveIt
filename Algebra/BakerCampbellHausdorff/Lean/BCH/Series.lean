/-
# The homogeneous BCH series and its convergence (Theorem 7.3 (i), (ii))

This file formalizes the analytic Baker–Campbell–Hausdorff theorem of the
accompanying article (`docs/combined`, Theorem 7.3 (i) and the remainder
estimate (7.4) of part (ii)): in a real or complex unital Banach algebra, if
`s = ‖X‖ + ‖Y‖ < log 2`, the homogeneous BCH series `∑ₙ Zₙ(X, Y)` converges
absolutely, `∑ₙ ρⁿ ‖Zₙ(X, Y)‖ ≤ -log(2 - e^{ρ s})` whenever `ρ > 0` and
`ρ s < log 2`, its sum `Z` is the Mercator logarithm of `e^X e^Y`, and
`e^Z = e^X e^Y`.

## The homogeneous components

The article (Section 2.2, equation (2.2)) defines `Z(X, Y) = log(e^X e^Y)`
in the completed free algebra by expanding the two exponentials and then the
logarithm, and `Zₙ` is the degree-`n` part of that expansion. Here the
homogeneous components are defined directly by the article's degree-by-degree
rules (the Cauchy product of Section 2.1), for `X, Y` in any normed algebra:

* `expBlock 𝕂 X Y d = ∑_{r + s = d} X^r Y^s / (r! s!)` is the degree-`d` part
  of `e^X e^Y`;
* `uBlock 𝕂 X Y d` is the degree-`d` part of `U = e^X e^Y - 1`, namely
  `expBlock` for `d ≥ 1` and `0` for `d = 0`;
* `powBlock 𝕂 X Y k n` is the degree-`n` part of `U^k`, defined by the Cauchy
  product recursion `powBlock (k+1) n = ∑_{d + m = n} uBlock d * powBlock k m`;
* `bchHom 𝕂 X Y n = ∑_{k=1}^{n} (-1)^{k-1}/k · powBlock k n` is `Zₙ(X, Y)`,
  the degree-`n` part of `∑ₖ (-1)^{k-1} U^k / k` (equation (2.6) of the
  article, grouped by the degrees of the blocks, which is the recursion (2.7)).

Expanding the products `uBlock d₁ ⋯ uBlock d_k` into monomials recovers the
article's sum over `k`-tuples of blocks `X^{r_i} Y^{s_i}` with `r_i + s_i > 0`,
so `bchHom 𝕂 X Y n` is the article's `Zₙ(X, Y)` (equations (2.6), (2.7); Remark 2.3).

## Method

The scalar majorant is obtained by applying the same definitions to the
real numbers `‖X‖`, `‖Y‖` (with `𝕂 = 𝔸 = ℝ`): termwise,
`‖powBlock 𝕂 X Y k n‖ ≤ powBlock ℝ ‖X‖ ‖Y‖ k n`. The generic lemma
`hasSum_powBlock` (the degree-`n` parts of `U^k` sum to `U^k`, absolutely)
applied over `ℝ` gives `∑ₙ powBlock ℝ a b k n = (e^{a+b} - 1)^k`, and the
double series `∑ₖ ∑ₙ (1/k) powBlock ℝ a b k n = -log(2 - e^{a+b})` can be
summed in either order because its terms are nonnegative. The same
rearrangement, now justified by absolute convergence, identifies
`∑ₙ Zₙ(X, Y)` with the Mercator logarithm `mlog 𝕂 (e^X e^Y - 1)` of
`BCH.Log`, and `exp_mlog` gives `e^Z = e^X e^Y`.
-/
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import BCH.Log

open NormedSpace Finset Finset.Nat

namespace BCH

section Defs

variable (𝕂 : Type*) {𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

/-- The degree-`d` part `∑_{r + s = d} X^r Y^s / (r! s!)` of `e^X e^Y`. -/
noncomputable def expBlock (X Y : 𝔸) (d : ℕ) : 𝔸 :=
  ∑ p ∈ antidiagonal d, ((Nat.factorial p.1 * Nat.factorial p.2 : ℕ) : 𝕂)⁻¹ • (X ^ p.1 * Y ^ p.2)

/-- The degree-`d` part of `U = e^X e^Y - 1`. -/
noncomputable def uBlock (X Y : 𝔸) (d : ℕ) : 𝔸 :=
  if d = 0 then 0 else expBlock 𝕂 X Y d

/-- The degree-`n` part of `U^k`, `U = e^X e^Y - 1`, by the Cauchy product rule
`(U^{k+1})_n = ∑_{d + m = n} U_d (U^k)_m`. -/
noncomputable def powBlock (X Y : 𝔸) : ℕ → ℕ → 𝔸
  | 0, n => if n = 0 then 1 else 0
  | k + 1, n => ∑ p ∈ antidiagonal n, uBlock 𝕂 X Y p.1 * powBlock X Y k p.2

/-- The homogeneous component `Zₙ(X, Y) = ∑_{k=1}^{n} (-1)^{k-1}/k · (U^k)_n` of the
BCH series (article, equations (2.6) and (2.7)); `Z₀ = 0`. -/
noncomputable def bchHom (X Y : 𝔸) (n : ℕ) : 𝔸 :=
  ∑ k ∈ range n, ((-1 : 𝕂) ^ k * ((k + 1 : ℕ) : 𝕂)⁻¹) • powBlock 𝕂 X Y (k + 1) n

variable {𝕂}

lemma expBlock_zero (X Y : 𝔸) : expBlock 𝕂 X Y 0 = 1 := by
  simp [expBlock]

lemma uBlock_zero (X Y : 𝔸) : uBlock 𝕂 X Y 0 = 0 := by simp [uBlock]

lemma powBlock_zero (X Y : 𝔸) (n : ℕ) :
    powBlock 𝕂 X Y 0 n = if n = 0 then 1 else 0 := rfl

lemma powBlock_succ (X Y : 𝔸) (k n : ℕ) :
    powBlock 𝕂 X Y (k + 1) n =
      ∑ p ∈ antidiagonal n, uBlock 𝕂 X Y p.1 * powBlock 𝕂 X Y k p.2 := rfl

lemma powBlock_one (X Y : 𝔸) (n : ℕ) : powBlock 𝕂 X Y 1 n = uBlock 𝕂 X Y n := by
  rw [powBlock_succ, Finset.sum_eq_single (n, 0)]
  · simp [powBlock_zero]
  · intro p hp hne
    rw [mem_antidiagonal] at hp
    have h2 : p.2 ≠ 0 := by
      intro h0
      apply hne
      ext <;> simp [h0]
      omega
    simp [powBlock_zero, h2]
  · intro h
    exact absurd (mem_antidiagonal.mpr (by simp)) h

/-- `(U^k)_n = 0` for `n < k`: every block has positive degree. -/
lemma powBlock_eq_zero_of_lt (X Y : 𝔸) : ∀ k n : ℕ, n < k → powBlock 𝕂 X Y k n = 0
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, n, h => by
    rw [powBlock_succ]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [mem_antidiagonal] at hp
    by_cases h1 : p.1 = 0
    · simp [uBlock, h1]
    · rw [powBlock_eq_zero_of_lt X Y k p.2 (by omega), mul_zero]

lemma bchHom_zero (X Y : 𝔸) : bchHom 𝕂 X Y 0 = 0 := by simp [bchHom]

/-! ### Homogeneity -/

lemma expBlock_smul (c : 𝕂) (X Y : 𝔸) (d : ℕ) :
    expBlock 𝕂 (c • X) (c • Y) d = c ^ d • expBlock 𝕂 X Y d := by
  unfold expBlock
  rw [Finset.smul_sum]
  refine sum_congr rfl fun p hp => ?_
  rw [mem_antidiagonal] at hp
  rw [smul_pow, smul_pow, smul_mul_smul_comm, smul_smul, smul_smul, ← pow_add, hp, mul_comm]

lemma uBlock_smul (c : 𝕂) (X Y : 𝔸) (d : ℕ) :
    uBlock 𝕂 (c • X) (c • Y) d = c ^ d • uBlock 𝕂 X Y d := by
  unfold uBlock
  split_ifs with h
  · simp
  · exact expBlock_smul c X Y d

lemma powBlock_smul (c : 𝕂) (X Y : 𝔸) :
    ∀ k n : ℕ, powBlock 𝕂 (c • X) (c • Y) k n = c ^ n • powBlock 𝕂 X Y k n
  | 0, n => by
    rw [powBlock_zero, powBlock_zero]
    split_ifs with h
    · subst h; simp
    · simp
  | k + 1, n => by
    rw [powBlock_succ, powBlock_succ, Finset.smul_sum]
    refine sum_congr rfl fun p hp => ?_
    rw [mem_antidiagonal] at hp
    rw [uBlock_smul, powBlock_smul c X Y k, smul_mul_smul_comm, ← pow_add, hp]

lemma bchHom_smul (c : 𝕂) (X Y : 𝔸) (n : ℕ) :
    bchHom 𝕂 (c • X) (c • Y) n = c ^ n • bchHom 𝕂 X Y n := by
  unfold bchHom
  rw [Finset.smul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [powBlock_smul, smul_comm]

end Defs

/-! ### The real majorant -/

section Majorant

variable {𝕂 : Type*} {𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

lemma expBlock_real_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (d : ℕ) :
    0 ≤ expBlock ℝ a b d :=
  Finset.sum_nonneg fun p _ => by
    rw [smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
      (mul_nonneg (pow_nonneg ha _) (pow_nonneg hb _))

lemma uBlock_real_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (d : ℕ) :
    0 ≤ uBlock ℝ a b d := by
  unfold uBlock
  split_ifs
  · exact le_rfl
  · exact expBlock_real_nonneg ha hb d

lemma powBlock_real_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ k n : ℕ, 0 ≤ powBlock ℝ a b k n
  | 0, n => by
    rw [powBlock_zero]
    split_ifs <;> norm_num
  | k + 1, n => by
    rw [powBlock_succ]
    exact Finset.sum_nonneg fun p _ =>
      mul_nonneg (uBlock_real_nonneg ha hb _) (powBlock_real_nonneg ha hb k _)

lemma norm_pow_mul_pow_le (X Y : 𝔸) {r s : ℕ} (h : 0 < r + s) :
    ‖X ^ r * Y ^ s‖ ≤ ‖X‖ ^ r * ‖Y‖ ^ s := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    simp only [pow_zero, one_mul]
    exact norm_pow_le' Y (by simpa using h)
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    simp only [pow_zero, mul_one]
    exact norm_pow_le' X hr
  exact (norm_mul_le _ _).trans
    (mul_le_mul (norm_pow_le' X hr) (norm_pow_le' Y hs) (norm_nonneg _)
      (pow_nonneg (norm_nonneg _) _))

lemma norm_expBlock_le (X Y : 𝔸) {d : ℕ} (hd : 0 < d) :
    ‖expBlock 𝕂 X Y d‖ ≤ expBlock ℝ ‖X‖ ‖Y‖ d := by
  unfold expBlock
  refine (norm_sum_le _ _).trans (sum_le_sum fun p hp => ?_)
  rw [mem_antidiagonal] at hp
  rw [norm_smul, norm_inv, RCLike.norm_natCast, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (norm_pow_mul_pow_le X Y (hp ▸ hd))
    (inv_nonneg.2 (Nat.cast_nonneg _))

lemma norm_uBlock_le (X Y : 𝔸) (d : ℕ) : ‖uBlock 𝕂 X Y d‖ ≤ uBlock ℝ ‖X‖ ‖Y‖ d := by
  unfold uBlock
  split_ifs with h
  · simp
  · exact norm_expBlock_le X Y (Nat.pos_of_ne_zero h)

lemma norm_powBlock_succ_le (X Y : 𝔸) :
    ∀ k n : ℕ, ‖powBlock 𝕂 X Y (k + 1) n‖ ≤ powBlock ℝ ‖X‖ ‖Y‖ (k + 1) n
  | 0, n => by
    rw [powBlock_one, powBlock_one]
    exact norm_uBlock_le X Y n
  | k + 1, n => by
    rw [powBlock_succ, powBlock_succ (𝕂 := ℝ)]
    refine (norm_sum_le _ _).trans (sum_le_sum fun p _ => ?_)
    exact (norm_mul_le _ _).trans
      (mul_le_mul (norm_uBlock_le X Y _) (norm_powBlock_succ_le X Y k _) (norm_nonneg _)
        (uBlock_real_nonneg (norm_nonneg _) (norm_nonneg _) _))

/-- The majorant term `(1/k) (U^k)_n` computed for the real numbers `a, b`. -/
noncomputable def majTerm (a b : ℝ) (p : ℕ × ℕ) : ℝ :=
  ((p.1 + 1 : ℕ) : ℝ)⁻¹ * powBlock ℝ a b (p.1 + 1) p.2

/-- The majorant `∑_{k=1}^{n} (1/k) (U^k)_n` of `‖Zₙ‖`, computed for the real numbers
`a, b`. -/
noncomputable def bchMaj (a b : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, majTerm a b (k, n)

lemma majTerm_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (p : ℕ × ℕ) : 0 ≤ majTerm a b p :=
  mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (powBlock_real_nonneg ha hb _ _)

lemma majTerm_eq_zero_of_le (a b : ℝ) {k n : ℕ} (h : n ≤ k) : majTerm a b (k, n) = 0 := by
  unfold majTerm
  rw [powBlock_eq_zero_of_lt a b (k + 1) n (by omega), mul_zero]

lemma bchMaj_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) : 0 ≤ bchMaj a b n :=
  Finset.sum_nonneg fun _ _ => majTerm_nonneg ha hb _

lemma bchMaj_mul (c a b : ℝ) (n : ℕ) : bchMaj (c * a) (c * b) n = c ^ n * bchMaj a b n := by
  unfold bchMaj majTerm
  rw [Finset.mul_sum]
  refine sum_congr rfl fun k _ => ?_
  have h := powBlock_smul (𝕂 := ℝ) c a b (k + 1) n
  simp only [smul_eq_mul] at h
  rw [h]; ring

lemma norm_bchHom_le (X Y : 𝔸) (n : ℕ) : ‖bchHom 𝕂 X Y n‖ ≤ bchMaj ‖X‖ ‖Y‖ n := by
  unfold bchHom bchMaj majTerm
  refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
  rw [norm_smul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_inv,
    RCLike.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_powBlock_succ_le X Y k n)
    (inv_nonneg.2 (Nat.cast_nonneg _))

end Majorant

/-! ### Summation of the block expansion -/

section Sums

variable {𝕂 : Type*} {𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸]

omit [CompleteSpace 𝔸] in
lemma expBlock_eq_sum_antidiagonal (X Y : 𝔸) (n : ℕ) :
    ∑ p ∈ antidiagonal n,
      (((Nat.factorial p.1 : ℕ) : 𝕂)⁻¹ • X ^ p.1) * (((Nat.factorial p.2 : ℕ) : 𝕂)⁻¹ • Y ^ p.2) =
      expBlock 𝕂 X Y n := by
  unfold expBlock
  refine sum_congr rfl fun p _ => ?_
  rw [smul_mul_smul_comm, Nat.cast_mul, mul_inv]

omit [CompleteSpace 𝔸] in
lemma summable_norm_expBlock (X Y : 𝔸) : Summable fun d => ‖expBlock 𝕂 X Y d‖ := by
  have h := summable_norm_sum_mul_antidiagonal_of_summable_norm
    (norm_expSeries_summable' (𝕂 := 𝕂) X) (norm_expSeries_summable' (𝕂 := 𝕂) Y)
  exact h.congr fun n => congrArg norm (expBlock_eq_sum_antidiagonal X Y n)

/-- `e^X e^Y = ∑_d (e^X e^Y)_d`. -/
theorem hasSum_expBlock (X Y : 𝔸) : HasSum (expBlock 𝕂 X Y) (exp X * exp Y) := by
  have h := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (norm_expSeries_summable' (𝕂 := 𝕂) X) (norm_expSeries_summable' (𝕂 := 𝕂) Y)
  rw [(exp_series_hasSum_exp' (𝕂 := 𝕂) X).tsum_eq, (exp_series_hasSum_exp' (𝕂 := 𝕂) Y).tsum_eq] at h
  have h3 : exp X * exp Y = ∑' n, expBlock 𝕂 X Y n :=
    h.trans (tsum_congr (expBlock_eq_sum_antidiagonal X Y))
  rw [h3]
  exact (summable_norm_expBlock (𝕂 := 𝕂) X Y).of_norm.hasSum

omit [CompleteSpace 𝔸] in
lemma summable_norm_uBlock (X Y : 𝔸) : Summable fun d => ‖uBlock 𝕂 X Y d‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun d => ?_)
    (summable_norm_expBlock (𝕂 := 𝕂) X Y)
  unfold uBlock
  split_ifs <;> simp

/-- `e^X e^Y - 1 = ∑_d U_d`. -/
theorem hasSum_uBlock (X Y : 𝔸) : HasSum (uBlock 𝕂 X Y) (exp X * exp Y - 1) := by
  have h := (hasSum_expBlock (𝕂 := 𝕂) X Y).sub (hasSum_ite_eq (0 : ℕ) (1 : 𝔸))
  have heq : uBlock 𝕂 X Y = fun d => expBlock 𝕂 X Y d - if d = 0 then 1 else 0 := by
    funext d
    unfold uBlock
    split_ifs with hd
    · subst hd; rw [expBlock_zero, sub_self]
    · rw [sub_zero]
  rw [heq]
  exact h

/-- The degree-`n` parts of `U^k` are absolutely summable, with sum `U^k`. -/
theorem hasSum_powBlock (X Y : 𝔸) :
    ∀ k : ℕ, (Summable fun n => ‖powBlock 𝕂 X Y k n‖) ∧
      HasSum (powBlock 𝕂 X Y k) ((exp X * exp Y - 1) ^ k)
  | 0 => by
    refine ⟨?_, ?_⟩
    · have h := (hasSum_ite_eq (0 : ℕ) ‖(1 : 𝔸)‖).summable
      convert h using 1
      funext n
      rw [powBlock_zero]
      split_ifs <;> simp
    · rw [pow_zero]
      exact hasSum_ite_eq (0 : ℕ) (1 : 𝔸)
  | k + 1 => by
    obtain ⟨hPn, hP⟩ := hasSum_powBlock X Y k
    have hUn := summable_norm_uBlock (𝕂 := 𝕂) X Y
    have hU := hasSum_uBlock (𝕂 := 𝕂) X Y
    have hsum : Summable fun n => ‖powBlock 𝕂 X Y (k + 1) n‖ :=
      summable_norm_sum_mul_antidiagonal_of_summable_norm hUn hPn
    refine ⟨hsum, ?_⟩
    have h := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hUn hPn
    rw [hU.tsum_eq, hP.tsum_eq] at h
    rw [pow_succ', h]
    exact hsum.of_norm.hasSum

end Sums

/-! ### The real computation -/

section RealSums

lemma hasSum_powBlock_real (a b : ℝ) (k : ℕ) :
    HasSum (powBlock ℝ a b k) ((Real.exp (a + b) - 1) ^ k) := by
  have h := (hasSum_powBlock (𝕂 := ℝ) a b k).2
  rwa [← Real.exp_eq_exp_ℝ, ← Real.exp_add] at h

lemma hasSum_majTerm_row (a b : ℝ) (k : ℕ) :
    HasSum (fun n => majTerm a b (k, n)) (((k + 1 : ℕ) : ℝ)⁻¹ * (Real.exp (a + b) - 1) ^ (k + 1)) :=
  (hasSum_powBlock_real a b (k + 1)).mul_left _

lemma hasSum_inv_mul_pow_log {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun k : ℕ => ((k + 1 : ℕ) : ℝ)⁻¹ * q ^ (k + 1)) (-Real.log (1 - q)) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := q) (by rw [abs_of_nonneg hq0]; exact hq1)
  convert h using 1
  funext k
  rw [Nat.cast_succ, div_eq_inv_mul]

lemma exp_sub_one_lt_one {a b : ℝ} (hab : a + b < Real.log 2) : Real.exp (a + b) - 1 < 1 := by
  have : Real.exp (a + b) < 2 := by
    calc Real.exp (a + b) < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr hab
      _ = 2 := Real.exp_log two_pos
  linarith

lemma exp_sub_one_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ Real.exp (a + b) - 1 := by
  linarith [Real.add_one_le_exp (a + b)]

lemma summable_majTerm {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b < Real.log 2) :
    Summable (majTerm a b) := by
  refine (summable_prod_of_nonneg (majTerm_nonneg ha hb)).2
    ⟨fun k => (hasSum_majTerm_row a b k).summable, ?_⟩
  have h : (fun k => ∑' n, majTerm a b (k, n)) =
      fun k => ((k + 1 : ℕ) : ℝ)⁻¹ * (Real.exp (a + b) - 1) ^ (k + 1) :=
    funext fun k => (hasSum_majTerm_row a b k).tsum_eq
  rw [h]
  exact (hasSum_inv_mul_pow_log (exp_sub_one_nonneg ha hb) (exp_sub_one_lt_one hab)).summable

/-- The majorant sums to `-log(2 - e^{a+b})` (equation (7.3) of the article, for the
scalar majorant). -/
theorem hasSum_bchMaj {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b < Real.log 2) :
    HasSum (bchMaj a b) (-Real.log (2 - Real.exp (a + b))) := by
  have hsum := summable_majTerm ha hb hab
  have hswap : Summable fun p : ℕ × ℕ => majTerm a b p.swap := hsum.prod_symm
  have hcol := (summable_prod_of_nonneg (fun p => majTerm_nonneg ha hb _)).1 hswap
  simp only [Prod.swap_prod_mk] at hcol
  have hrows : (fun k => ∑' n, majTerm a b (k, n)) =
      fun k => ((k + 1 : ℕ) : ℝ)⁻¹ * (Real.exp (a + b) - 1) ^ (k + 1) :=
    funext fun k => (hasSum_majTerm_row a b k).tsum_eq
  have hcomm : ∑' n, ∑' k, majTerm a b (k, n) = ∑' k, ∑' n, majTerm a b (k, n) :=
    Summable.tsum_comm' (f := fun k n => majTerm a b (k, n)) hsum
      (fun k => (hasSum_majTerm_row a b k).summable) hcol.1
  have hval : ∑' n, ∑' k, majTerm a b (k, n) = -Real.log (2 - Real.exp (a + b)) := by
    rw [hcomm, hrows,
      (hasSum_inv_mul_pow_log (exp_sub_one_nonneg ha hb) (exp_sub_one_lt_one hab)).tsum_eq]
    congr 1
    ring_nf
  have hbch : bchMaj a b = fun n => ∑' k, majTerm a b (k, n) := by
    funext n
    unfold bchMaj
    exact (tsum_eq_sum fun k hk => majTerm_eq_zero_of_le a b (by simpa using hk)).symm
  rw [hbch, ← hval]
  exact hcol.2.hasSum

end RealSums

/-! ### The theorem -/

section Main

variable {𝕂 : Type*} {𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸]

omit [CompleteSpace 𝔸] in
/-- **Absolute convergence of the homogeneous BCH series** (Theorem 7.3 (i)): if
`‖X‖ + ‖Y‖ < log 2` then `∑ₙ ‖Zₙ(X, Y)‖ < ∞`. -/
theorem summable_norm_bchHom {X Y : 𝔸} (hs : ‖X‖ + ‖Y‖ < Real.log 2) :
    Summable fun n => ‖bchHom 𝕂 X Y n‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_bchHom_le X Y)
    (hasSum_bchMaj (norm_nonneg X) (norm_nonneg Y) hs).summable

omit [CompleteSpace 𝔸] in
/-- **The majorant** (Theorem 7.3 (i), second line of (7.3)): for `ρ > 0` with
`ρ (‖X‖ + ‖Y‖) < log 2`, `∑ₙ ρⁿ ‖Zₙ(X, Y)‖ ≤ -log(2 - e^{ρ (‖X‖ + ‖Y‖)})`. -/
theorem tsum_pow_mul_norm_bchHom_le (X Y : 𝔸) {ρ : ℝ} (hρ : 0 < ρ)
    (hs : ρ * (‖X‖ + ‖Y‖) < Real.log 2) :
    ∑' n, ρ ^ n * ‖bchHom 𝕂 X Y n‖ ≤ -Real.log (2 - Real.exp (ρ * (‖X‖ + ‖Y‖))) := by
  have hM := hasSum_bchMaj (mul_nonneg hρ.le (norm_nonneg X)) (mul_nonneg hρ.le (norm_nonneg Y))
    (by rw [← mul_add]; exact hs)
  have hle : ∀ n, ρ ^ n * ‖bchHom 𝕂 X Y n‖ ≤ bchMaj (ρ * ‖X‖) (ρ * ‖Y‖) n := fun n => by
    rw [bchMaj_mul]
    exact mul_le_mul_of_nonneg_left (norm_bchHom_le X Y n) (pow_nonneg hρ.le n)
  rw [mul_add, ← hM.tsum_eq]
  exact Summable.tsum_le_tsum hle
    (Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg hρ.le n) (norm_nonneg _)) hle
      hM.summable) hM.summable

variable (𝕂) in
/-- The summands `(-1)^{k-1}/k · (U^k)_n` of the double series. -/
noncomputable def bchTerm (X Y : 𝔸) (p : ℕ × ℕ) : 𝔸 :=
  ((-1 : 𝕂) ^ p.1 * ((p.1 + 1 : ℕ) : 𝕂)⁻¹) • powBlock 𝕂 X Y (p.1 + 1) p.2

omit [CompleteSpace 𝔸] in
lemma norm_bchTerm_le (X Y : 𝔸) (p : ℕ × ℕ) : ‖bchTerm 𝕂 X Y p‖ ≤ majTerm ‖X‖ ‖Y‖ p := by
  unfold bchTerm majTerm
  rw [norm_smul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_inv,
    RCLike.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_powBlock_succ_le X Y _ _)
    (inv_nonneg.2 (Nat.cast_nonneg _))

lemma hasSum_bchTerm_row (X Y : 𝔸) (k : ℕ) :
    HasSum (fun n => bchTerm 𝕂 X Y (k, n)) (mlogTerm 𝕂 (exp X * exp Y - 1) k) := by
  have h := (hasSum_powBlock (𝕂 := 𝕂) X Y (k + 1)).2.const_smul
    ((-1 : 𝕂) ^ k * ((k + 1 : ℕ) : 𝕂)⁻¹)
  simpa only [mlogTerm, bchTerm] using h

omit [CompleteSpace 𝔸] in
lemma hasSum_bchTerm_col (X Y : 𝔸) (n : ℕ) :
    HasSum (fun k => bchTerm 𝕂 X Y (k, n)) (bchHom 𝕂 X Y n) := by
  have h : HasSum (fun k => bchTerm 𝕂 X Y (k, n)) (∑ k ∈ range n, bchTerm 𝕂 X Y (k, n)) :=
    hasSum_sum_of_ne_finset_zero fun k hk => by
      simp only [bchTerm]
      rw [powBlock_eq_zero_of_lt X Y (k + 1) n (by simpa using hk), smul_zero]
  exact h

/-- **The BCH series is the Mercator logarithm** (Theorem 7.3 (i)): for
`‖X‖ + ‖Y‖ < log 2`, `∑ₙ Zₙ(X, Y) = log(e^X e^Y)`, the Mercator logarithm of
`1 + (e^X e^Y - 1)`. -/
theorem tsum_bchHom_eq_mlog {X Y : 𝔸} (hs : ‖X‖ + ‖Y‖ < Real.log 2) :
    ∑' n, bchHom 𝕂 X Y n = mlog 𝕂 (exp X * exp Y - 1) := by
  have hsum : Summable (bchTerm 𝕂 X Y) :=
    Summable.of_norm_bounded (summable_majTerm (norm_nonneg X) (norm_nonneg Y) hs)
      (norm_bchTerm_le X Y)
  have hcol : (fun n => bchHom 𝕂 X Y n) = fun n => ∑' k, bchTerm 𝕂 X Y (k, n) :=
    funext fun n => (hasSum_bchTerm_col X Y n).tsum_eq.symm
  have hrow : (fun k => ∑' n, bchTerm 𝕂 X Y (k, n)) = mlogTerm 𝕂 (exp X * exp Y - 1) :=
    funext fun k => (hasSum_bchTerm_row X Y k).tsum_eq
  rw [hcol, Summable.tsum_comm' (f := fun k n => bchTerm 𝕂 X Y (k, n)) hsum
    (fun k => (hasSum_bchTerm_row X Y k).summable) (fun n => (hasSum_bchTerm_col X Y n).summable),
    hrow]
  rfl

/-- **The Baker–Campbell–Hausdorff theorem** (Theorem 7.3 (i)): if `‖X‖ + ‖Y‖ < log 2`, the
homogeneous BCH series converges absolutely and its sum `Z = ∑ₙ Zₙ(X, Y)` satisfies
`e^Z = e^X e^Y`. -/
theorem exp_tsum_bchHom {X Y : 𝔸} (hs : ‖X‖ + ‖Y‖ < Real.log 2) :
    exp (∑' n, bchHom 𝕂 X Y n) = exp X * exp Y := by
  rw [tsum_bchHom_eq_mlog hs, exp_mlog (exp_mlog_exp_mul_exp 𝕂 hs).1, add_sub_cancel]

/-- **Theorem 7.3 (i)** in one statement: for `s = ‖X‖ + ‖Y‖ < log 2` the homogeneous BCH
series converges absolutely, `∑ₙ ρⁿ ‖Zₙ‖ ≤ -log(2 - e^{ρ s})` whenever `ρ > 0` and
`ρ s < log 2`, and the sum `Z` satisfies `e^Z = e^X e^Y`. -/
theorem bch_convergence {X Y : 𝔸} (hs : ‖X‖ + ‖Y‖ < Real.log 2) :
    (Summable fun n => ‖bchHom 𝕂 X Y n‖) ∧
    (∀ ρ : ℝ, 0 < ρ → ρ * (‖X‖ + ‖Y‖) < Real.log 2 →
      ∑' n, ρ ^ n * ‖bchHom 𝕂 X Y n‖ ≤ -Real.log (2 - Real.exp (ρ * (‖X‖ + ‖Y‖)))) ∧
    exp (∑' n, bchHom 𝕂 X Y n) = exp X * exp Y :=
  ⟨summable_norm_bchHom hs, fun _ hρ hρs => tsum_pow_mul_norm_bchHom_le X Y hρ hρs,
    exp_tsum_bchHom hs⟩

omit [CompleteSpace 𝔸] in
/-- **Tail estimate, sum-of-norms form** (Theorem 7.3 (ii)): if `1 < ρ` and
`ρ (‖X‖ + ‖Y‖) < log 2`, then `∑_{n > N} ‖Zₙ(X, Y)‖ ≤ ρ^{-(N+1)} · (-log(2 - e^{ρ (‖X‖ + ‖Y‖)}))`. -/
theorem tsum_norm_bchHom_tail_le (X Y : 𝔸) {ρ : ℝ} (hρ : 1 < ρ)
    (hs : ρ * (‖X‖ + ‖Y‖) < Real.log 2) (N : ℕ) :
    ∑' i, ‖bchHom 𝕂 X Y (i + (N + 1))‖ ≤
      (ρ ^ (N + 1))⁻¹ * -Real.log (2 - Real.exp (ρ * (‖X‖ + ‖Y‖))) := by
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ
  have hs1 : ‖X‖ + ‖Y‖ < Real.log 2 := by
    have h0 : 0 ≤ ‖X‖ + ‖Y‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have h1 : ‖X‖ + ‖Y‖ ≤ ρ * (‖X‖ + ‖Y‖) := le_mul_of_one_le_left h0 hρ.le
    linarith
  have hZn := summable_norm_bchHom (𝕂 := 𝕂) hs1
  -- the weighted series
  have hM := hasSum_bchMaj (mul_nonneg hρ0.le (norm_nonneg X)) (mul_nonneg hρ0.le (norm_nonneg Y))
    (by rw [← mul_add]; exact hs)
  have hw : ∀ n, ρ ^ n * ‖bchHom 𝕂 X Y n‖ ≤ bchMaj (ρ * ‖X‖) (ρ * ‖Y‖) n := fun n => by
    rw [bchMaj_mul]
    exact mul_le_mul_of_nonneg_left (norm_bchHom_le X Y n) (pow_nonneg hρ0.le n)
  have hwn : Summable fun n => ρ ^ n * ‖bchHom 𝕂 X Y n‖ :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg hρ0.le n) (norm_nonneg _)) hw
      hM.summable
  have hbound := tsum_pow_mul_norm_bchHom_le (𝕂 := 𝕂) X Y hρ0 hs
  have htail : Summable fun i => ‖bchHom 𝕂 X Y (i + (N + 1))‖ :=
    (summable_nat_add_iff (N + 1) (f := fun n => ‖bchHom 𝕂 X Y n‖)).2 hZn
  -- `‖Z_{n}‖ ≤ ρ^{-(N+1)} ρ^n ‖Z_n‖` for `n ≥ N + 1`
  have hshift : ∀ i, ‖bchHom 𝕂 X Y (i + (N + 1))‖ ≤
      (ρ ^ (N + 1))⁻¹ * (ρ ^ (i + (N + 1)) * ‖bchHom 𝕂 X Y (i + (N + 1))‖) := fun i => by
    have hpos : 0 < ρ ^ (N + 1) := pow_pos hρ0 _
    calc ‖bchHom 𝕂 X Y (i + (N + 1))‖
        = (ρ ^ (N + 1))⁻¹ * (ρ ^ (N + 1) * ‖bchHom 𝕂 X Y (i + (N + 1))‖) := by
          rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
      _ ≤ (ρ ^ (N + 1))⁻¹ * (ρ ^ (i + (N + 1)) * ‖bchHom 𝕂 X Y (i + (N + 1))‖) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hρ.le (Nat.le_add_left _ _))
              (norm_nonneg _)) (inv_nonneg.2 hpos.le)
  have hwn' : Summable fun i => ρ ^ (i + (N + 1)) * ‖bchHom 𝕂 X Y (i + (N + 1))‖ :=
    (summable_nat_add_iff (N + 1) (f := fun n => ρ ^ n * ‖bchHom 𝕂 X Y n‖)).2 hwn
  refine (Summable.tsum_le_tsum hshift htail (hwn'.mul_left _)).trans ?_
  rw [hwn'.tsum_mul_left]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (pow_pos hρ0 _).le)
  refine le_trans ?_ hbound
  rw [← hwn.sum_add_tsum_nat_add (N + 1)]
  exact le_add_of_nonneg_left
    (Finset.sum_nonneg fun n _ => mul_nonneg (pow_pos hρ0 n).le (norm_nonneg _))

/-- **Remainder estimate** (Theorem 7.3 (ii), equation (7.4)): if `1 < ρ` and
`ρ (‖X‖ + ‖Y‖) < log 2`, then the tail after degree `N` of the BCH series has norm at most
`ρ^{-(N+1)} · (-log(2 - e^{ρ (‖X‖ + ‖Y‖)}))`. -/
theorem norm_tsum_bchHom_sub_sum_le (X Y : 𝔸) {ρ : ℝ} (hρ : 1 < ρ)
    (hs : ρ * (‖X‖ + ‖Y‖) < Real.log 2) (N : ℕ) :
    ‖∑' n, bchHom 𝕂 X Y n - ∑ n ∈ range (N + 1), bchHom 𝕂 X Y n‖ ≤
      (ρ ^ (N + 1))⁻¹ * -Real.log (2 - Real.exp (ρ * (‖X‖ + ‖Y‖))) := by
  have hs1 : ‖X‖ + ‖Y‖ < Real.log 2 := by
    have h0 : 0 ≤ ‖X‖ + ‖Y‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have h1 : ‖X‖ + ‖Y‖ ≤ ρ * (‖X‖ + ‖Y‖) := le_mul_of_one_le_left h0 hρ.le
    linarith
  have hZn := summable_norm_bchHom (𝕂 := 𝕂) hs1
  have hZ := hZn.of_norm
  have htail : Summable fun i => ‖bchHom 𝕂 X Y (i + (N + 1))‖ :=
    (summable_nat_add_iff (N + 1) (f := fun n => ‖bchHom 𝕂 X Y n‖)).2 hZn
  rw [← hZ.sum_add_tsum_nat_add (N + 1), add_sub_cancel_left]
  exact (norm_tsum_le_tsum_norm htail).trans (tsum_norm_bchHom_tail_le X Y hρ hs N)

end Main

end BCH
