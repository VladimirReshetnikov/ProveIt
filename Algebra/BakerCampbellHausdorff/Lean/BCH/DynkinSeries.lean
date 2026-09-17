/-
# Absolute convergence of Dynkin's Lie series (Theorem 7.3 (iii), (iv))

Dynkin's formula (Theorem 4.1, `BCH.Formal.Dynkin`) writes every homogeneous
component as a linear combination of right-nested commutators of the letters,

`Zₙ = (1/n) ∑_{k=1}^{n} (-1)^{k-1}/k ∑_{(rᵢ,sᵢ)} R(X^{r₁}Y^{s₁}⋯X^{r_k}Y^{s_k}) / ∏ rᵢ!sᵢ!`.

This file evaluates these summands in a normed space `L` with a bracket
satisfying `‖⁅u, v⁆‖ ≤ κ ‖u‖ ‖v‖` (a normed Lie algebra; the associative case
is `κ = 2`) and proves parts (iii) and (iv) of Theorem 7.3 of the accompanying
article (`docs/combined`):

* `dynkinTerm x n` is the degree-`n` part of Dynkin's series evaluated at
  `x 0, x 1`, `dynkinNormSum x n` the sum of the norms of its individual
  summands;
* `rbEval` is the right-nested bracket of a list of letters, and
  `norm_rbEval_le` the bound `‖[x₁,[x₂,…,xₙ]]‖ ≤ κ^{n-1} ∏ ‖xᵢ‖`;
* `summable_dynkinNormSum` and `tsum_dynkinNormSum_le`: for
  `κ (‖x 0‖ + ‖x 1‖) < log 2` the summands are absolutely summable, with
  `∑ ‖summand‖ ≤ κ⁻¹ [-log (2 - e^{κ s})]` (part (iv)); `tsum_dynkinNormSum_tail_le`
  is the tail bound `ρ^{-(N+1)} κ⁻¹ [-log (2 - e^{κ ρ s})]`; `summable_dynkinTerm`
  is the convergence of the series itself in a complete space;
* in an associative normed algebra (`κ = 2`): `evalHom_rbList` identifies
  the evaluated summands with those of `bchHom_eq_dynkin_blocks`,
  `bchHom_eq_dynkinTerm` gives `Zₙ = dynkinTerm ![X, Y] n`, and
  `tsum_dynkinNormSum_le_of_lt`, `tsum_dynkinNormSum_tail_le_of_lt` are the
  bounds `M_D(s) = -½ log (2 - e^{2s})` of equation (7.dynkinradius) for
  `s < ½ log 2` (part (iii)).
-/
import BCH.Formal.Dynkin
import BCH.Trace

open Finset

namespace BCH

section Eval

variable {𝕂 : Type*} [RCLike 𝕂] {L : Type*} [NormedAddCommGroup L] [NormedSpace 𝕂 L]
  [Bracket L L]

/-- The right-nested bracket `[x_{a₁}, [x_{a₂}, …, [x_{a_{n-1}}, x_{aₙ}]]]` of a list of letters,
evaluated at `x : Fin 2 → L`. -/
def rbEval (x : Fin 2 → L) : List (Fin 2) → L
  | [] => 0
  | [i] => x i
  | i :: j :: rest => ⁅x i, rbEval x (j :: rest)⁆

/-- The degree-`n` part of Dynkin's series, evaluated at `x 0, x 1`:
`(1/n) ∑_{k<n} (-1)^k/(k+1) ∑_{rs ∈ blockTuples (k+1) n} (∏ rᵢ!sᵢ!)⁻¹ R(word rs)`. -/
noncomputable def dynkinTerm (x : Fin 2 → L) (n : ℕ) : L :=
  (n : 𝕂)⁻¹ • ∑ k ∈ range n, ((-1 : 𝕂) ^ k * ((k + 1 : ℕ) : 𝕂)⁻¹) •
    ∑ rs ∈ blockTuples (k + 1) n,
      blockWeight 𝕂 rs • rbEval x (FreeMonoid.toList (blockMonoid rs))

/-- The sum of the norms of the individual summands of `dynkinTerm x n`. -/
noncomputable def dynkinNormSum (x : Fin 2 → L) (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k ∈ range n, ((k + 1 : ℕ) : ℝ)⁻¹ *
    ∑ rs ∈ blockTuples (k + 1) n,
      blockWeight ℝ rs * ‖rbEval x (FreeMonoid.toList (blockMonoid rs))‖

lemma blockWeight_real_nonneg {k : ℕ} (rs : Fin k → ℕ × ℕ) : 0 ≤ blockWeight ℝ rs :=
  Finset.prod_nonneg fun _ _ => inv_nonneg.2 (Nat.cast_nonneg _)

lemma norm_blockWeight {k : ℕ} (rs : Fin k → ℕ × ℕ) : ‖blockWeight 𝕂 rs‖ = blockWeight ℝ rs := by
  unfold blockWeight
  rw [norm_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [norm_inv, RCLike.norm_natCast]

lemma dynkinNormSum_nonneg (x : Fin 2 → L) (n : ℕ) : 0 ≤ dynkinNormSum x n := by
  unfold dynkinNormSum
  refine mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (sum_nonneg fun k _ => ?_)
  refine mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (sum_nonneg fun rs _ => ?_)
  exact mul_nonneg (blockWeight_real_nonneg rs) (norm_nonneg _)

/-- The norm of the degree-`n` part is at most the sum of the norms of its summands. -/
lemma norm_dynkinTerm_le (x : Fin 2 → L) (n : ℕ) :
    ‖dynkinTerm (𝕂 := 𝕂) x n‖ ≤ dynkinNormSum x n := by
  unfold dynkinTerm dynkinNormSum
  rw [norm_smul, norm_inv, RCLike.norm_natCast]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_))
    (inv_nonneg.2 (Nat.cast_nonneg _))
  rw [norm_smul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_inv,
    RCLike.norm_natCast]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun rs _ => ?_))
    (inv_nonneg.2 (Nat.cast_nonneg _))
  rw [norm_smul, norm_blockWeight]

/-- The product of the norms of the letters of a list. -/
def letterProd (x : Fin 2 → L) (l : List (Fin 2)) : ℝ := (l.map fun i => ‖x i‖).prod

/-- `‖[x_{a₁}, [x_{a₂}, …, x_{aₙ}]]‖ ≤ κ^{n-1} ∏ᵢ ‖x_{aᵢ}‖` for a nonempty list. -/
lemma norm_rbEval_le (x : Fin 2 → L) {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : ∀ u v : L, ‖⁅u, v⁆‖ ≤ κ * ‖u‖ * ‖v‖) :
    ∀ l : List (Fin 2), l ≠ [] → ‖rbEval x l‖ ≤ κ ^ (l.length - 1) * letterProd x l
  | [], h => absurd rfl h
  | [i], _ => by simp [rbEval, letterProd]
  | i :: j :: rest, _ => by
    have ih := norm_rbEval_le x hκ0 hκ (j :: rest) (List.cons_ne_nil _ _)
    simp only [rbEval, letterProd, List.map_cons, List.prod_cons, List.length_cons,
      Nat.add_sub_cancel] at ih ⊢
    calc ‖⁅x i, rbEval x (j :: rest)⁆‖ ≤ κ * ‖x i‖ * ‖rbEval x (j :: rest)‖ := hκ _ _
      _ ≤ κ * ‖x i‖ * (κ ^ rest.length * (‖x j‖ * (rest.map fun i => ‖x i‖).prod)) := by
          gcongr
      _ = κ ^ (rest.length + 1) * (‖x i‖ * (‖x j‖ * (rest.map fun i => ‖x i‖).prod)) := by
          rw [pow_succ]; ring

omit [Bracket L L] in
/-- The letter product of a block word is `∏ᵢ ‖x 0‖^{rᵢ} ‖x 1‖^{sᵢ}`. -/
lemma letterProd_blockMonoid (x : Fin 2 → L) {k : ℕ} (rs : Fin k → ℕ × ℕ) :
    letterProd x (FreeMonoid.toList (blockMonoid rs)) = blockWord ‖x 0‖ ‖x 1‖ rs := by
  have h := map_blockWord (FreeMonoid.lift fun i => ‖x i‖) (FreeMonoid.of 0) (FreeMonoid.of 1) rs
  rw [FreeMonoid.lift_apply, FreeMonoid.lift_eval_of, FreeMonoid.lift_eval_of] at h
  exact h

lemma FreeMonoid.length_pow (a : FreeMonoid (Fin 2)) (r : ℕ) :
    FreeMonoid.length (a ^ r) = r * FreeMonoid.length a := by
  induction r with
  | zero => simp [FreeMonoid.length_one]
  | succ r ih => rw [pow_succ, FreeMonoid.length_mul, ih]; ring

/-- The length of a block word is the total degree. -/
lemma length_blockMonoid : ∀ {k : ℕ} (rs : Fin k → ℕ × ℕ),
    FreeMonoid.length (blockMonoid rs) = ∑ i, ((rs i).1 + (rs i).2)
  | 0, rs => by simp [blockMonoid, blockWord_zero, FreeMonoid.length_one]
  | k + 1, rs => by
    rw [← Fin.cons_self_tail rs, blockMonoid, blockWord_cons, FreeMonoid.length_mul,
      FreeMonoid.length_mul, FreeMonoid.length_pow, FreeMonoid.length_pow, FreeMonoid.length_of,
      FreeMonoid.length_of, Fin.sum_univ_succ, Fin.cons_zero]
    have := length_blockMonoid (Fin.tail rs)
    rw [blockMonoid] at this
    rw [this]
    simp only [Fin.cons_succ, Fin.tail, mul_one]

/-- The basic estimate: the sum of the norms of the degree-`n` Dynkin summands is at most
`κ⁻¹ ∑_{k=1}^{n} (1/k) (U^k)_n(κ‖x 0‖, κ‖x 1‖)`, the majorant of `BCH.Series` evaluated at
the scaled norms. -/
theorem dynkinNormSum_le (x : Fin 2 → L) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ : ∀ u v : L, ‖⁅u, v⁆‖ ≤ κ * ‖u‖ * ‖v‖) (n : ℕ) :
    dynkinNormSum x n ≤ κ⁻¹ * bchMaj (κ * ‖x 0‖) (κ * ‖x 1‖) n := by
  have ha : 0 ≤ κ * ‖x 0‖ := mul_nonneg hκ0.le (norm_nonneg _)
  have hb : 0 ≤ κ * ‖x 1‖ := mul_nonneg hκ0.le (norm_nonneg _)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [dynkinNormSum, Nat.cast_zero, inv_zero, zero_mul]
    exact mul_nonneg (inv_nonneg.2 hκ0.le) (bchMaj_nonneg ha hb 0)
  -- the inner sums
  have hinner : ∀ k, ∑ rs ∈ blockTuples (k + 1) n,
      blockWeight ℝ rs * ‖rbEval x (FreeMonoid.toList (blockMonoid rs))‖ ≤
      κ⁻¹ * powBlock ℝ (κ * ‖x 0‖) (κ * ‖x 1‖) (k + 1) n := by
    intro k
    have h1 : ∀ rs ∈ blockTuples (k + 1) n,
        blockWeight ℝ rs * ‖rbEval x (FreeMonoid.toList (blockMonoid rs))‖ ≤
        blockWeight ℝ rs * (κ ^ (n - 1) * blockWord ‖x 0‖ ‖x 1‖ rs) := by
      intro rs hrs
      refine mul_le_mul_of_nonneg_left ?_ (blockWeight_real_nonneg rs)
      have hlen : (FreeMonoid.toList (blockMonoid rs)).length = n := by
        have := length_blockMonoid rs
        rw [(mem_blockTuples.mp hrs).2] at this
        exact this
      have hne : FreeMonoid.toList (blockMonoid rs) ≠ [] := by
        intro h
        rw [h] at hlen
        simp at hlen
        omega
      have := norm_rbEval_le x hκ0.le hκ _ hne
      rwa [hlen, letterProd_blockMonoid] at this
    refine (sum_le_sum h1).trans (le_of_eq ?_)
    have hpow := powBlock_eq_sum_blockTuples (𝕂 := ℝ) ‖x 0‖ ‖x 1‖ (k + 1) n
    have hsmul := powBlock_smul (𝕂 := ℝ) κ ‖x 0‖ ‖x 1‖ (k + 1) n
    simp only [smul_eq_mul] at hpow hsmul
    rw [hsmul, hpow, Finset.mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun rs _ => ?_
    have hκn : κ ^ (n - 1) = κ⁻¹ * κ ^ n := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ', ← mul_assoc, inv_mul_cancel₀ hκ0.ne', one_mul]
    rw [hκn]
    ring
  unfold dynkinNormSum bchMaj majTerm
  calc (n : ℝ)⁻¹ * ∑ k ∈ range n, ((k + 1 : ℕ) : ℝ)⁻¹ * ∑ rs ∈ blockTuples (k + 1) n,
        blockWeight ℝ rs * ‖rbEval x (FreeMonoid.toList (blockMonoid rs))‖
      ≤ (n : ℝ)⁻¹ * ∑ k ∈ range n, ((k + 1 : ℕ) : ℝ)⁻¹ *
          (κ⁻¹ * powBlock ℝ (κ * ‖x 0‖) (κ * ‖x 1‖) (k + 1) n) := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun k _ => ?_)
          (inv_nonneg.2 (Nat.cast_nonneg _))
        exact mul_le_mul_of_nonneg_left (hinner k) (inv_nonneg.2 (Nat.cast_nonneg _))
    _ = (n : ℝ)⁻¹ * (κ⁻¹ * ∑ k ∈ range n, ((k + 1 : ℕ) : ℝ)⁻¹ *
          powBlock ℝ (κ * ‖x 0‖) (κ * ‖x 1‖) (k + 1) n) := by
        simp only [Finset.mul_sum]
        refine sum_congr rfl fun k _ => ?_
        ring
    _ ≤ 1 * (κ⁻¹ * ∑ k ∈ range n, ((k + 1 : ℕ) : ℝ)⁻¹ *
          powBlock ℝ (κ * ‖x 0‖) (κ * ‖x 1‖) (k + 1) n) := by
        refine mul_le_mul_of_nonneg_right ?_ ?_
        · exact inv_le_one_of_one_le₀ (by exact_mod_cast hn)
        · exact mul_nonneg (inv_nonneg.2 hκ0.le) (bchMaj_nonneg ha hb n)
    _ = _ := one_mul _

/-- **Theorem 7.3 (iv), summability**: if `‖⁅u, v⁆‖ ≤ κ ‖u‖ ‖v‖` and
`κ (‖x 0‖ + ‖x 1‖) < log 2`, the Dynkin summands are absolutely summable. -/
theorem summable_dynkinNormSum (x : Fin 2 → L) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ : ∀ u v : L, ‖⁅u, v⁆‖ ≤ κ * ‖u‖ * ‖v‖) (hs : κ * (‖x 0‖ + ‖x 1‖) < Real.log 2) :
    Summable (dynkinNormSum x) := by
  have hM := hasSum_bchMaj (mul_nonneg hκ0.le (norm_nonneg (x 0)))
    (mul_nonneg hκ0.le (norm_nonneg (x 1))) (by rw [← mul_add]; exact hs)
  exact Summable.of_nonneg_of_le (dynkinNormSum_nonneg x) (dynkinNormSum_le x hκ0 hκ)
    (hM.summable.mul_left _)

/-- **Theorem 7.3 (iv), the bound**: the absolute sum of Dynkin's Lie series is at most
`κ⁻¹ [-log (2 - e^{κ (‖x 0‖ + ‖x 1‖)})]`. -/
theorem tsum_dynkinNormSum_le (x : Fin 2 → L) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ : ∀ u v : L, ‖⁅u, v⁆‖ ≤ κ * ‖u‖ * ‖v‖) (hs : κ * (‖x 0‖ + ‖x 1‖) < Real.log 2) :
    ∑' n, dynkinNormSum x n ≤ κ⁻¹ * -Real.log (2 - Real.exp (κ * (‖x 0‖ + ‖x 1‖))) := by
  have hM := hasSum_bchMaj (mul_nonneg hκ0.le (norm_nonneg (x 0)))
    (mul_nonneg hκ0.le (norm_nonneg (x 1))) (by rw [← mul_add]; exact hs)
  refine (Summable.tsum_le_tsum (dynkinNormSum_le x hκ0 hκ)
    (summable_dynkinNormSum x hκ0 hκ hs) (hM.summable.mul_left _)).trans ?_
  rw [tsum_mul_left, hM.tsum_eq, mul_add]

/-- **Theorem 7.3 (iv), tail bound**: for `1 < ρ` with `κ ρ (‖x 0‖ + ‖x 1‖) < log 2`, the
absolute sum of the Dynkin summands of degree `> N` is at most
`ρ^{-(N+1)} κ⁻¹ [-log (2 - e^{κ ρ (‖x 0‖ + ‖x 1‖)})]`. -/
theorem tsum_dynkinNormSum_tail_le (x : Fin 2 → L) {κ ρ : ℝ} (hκ0 : 0 < κ)
    (hκ : ∀ u v : L, ‖⁅u, v⁆‖ ≤ κ * ‖u‖ * ‖v‖) (hρ : 1 < ρ)
    (hs : κ * ρ * (‖x 0‖ + ‖x 1‖) < Real.log 2) (N : ℕ) :
    ∑' i, dynkinNormSum x (i + (N + 1)) ≤
      (ρ ^ (N + 1))⁻¹ * (κ⁻¹ * -Real.log (2 - Real.exp (κ * ρ * (‖x 0‖ + ‖x 1‖)))) := by
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ
  have hs1 : κ * (‖x 0‖ + ‖x 1‖) < Real.log 2 := by
    have h0 : 0 ≤ κ * (‖x 0‖ + ‖x 1‖) :=
      mul_nonneg hκ0.le (add_nonneg (norm_nonneg _) (norm_nonneg _))
    have h1 : κ * (‖x 0‖ + ‖x 1‖) ≤ κ * ρ * (‖x 0‖ + ‖x 1‖) :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hκ0.le hρ.le)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
    linarith
  have hD := summable_dynkinNormSum x hκ0 hκ hs1
  have hM := hasSum_bchMaj (mul_nonneg (mul_nonneg hκ0.le hρ0.le) (norm_nonneg (x 0)))
    (mul_nonneg (mul_nonneg hκ0.le hρ0.le) (norm_nonneg (x 1))) (by rw [← mul_add]; exact hs)
  -- `dynkinNormSum x n ≤ κ⁻¹ ρ^{-n} bchMaj (κ ρ a) (κ ρ b) n`
  have hw : ∀ n, dynkinNormSum x n ≤
      κ⁻¹ * ((ρ ^ n)⁻¹ * bchMaj (κ * ρ * ‖x 0‖) (κ * ρ * ‖x 1‖) n) := fun n => by
    have h := dynkinNormSum_le x hκ0 hκ n
    have hmul := bchMaj_mul ρ (κ * ‖x 0‖) (κ * ‖x 1‖) n
    have hpos : 0 < ρ ^ n := pow_pos hρ0 n
    calc dynkinNormSum x n ≤ κ⁻¹ * bchMaj (κ * ‖x 0‖) (κ * ‖x 1‖) n := h
      _ = κ⁻¹ * ((ρ ^ n)⁻¹ * (ρ ^ n * bchMaj (κ * ‖x 0‖) (κ * ‖x 1‖) n)) := by
          rw [← mul_assoc (ρ ^ n)⁻¹, inv_mul_cancel₀ hpos.ne', one_mul]
      _ = κ⁻¹ * ((ρ ^ n)⁻¹ * bchMaj (κ * ρ * ‖x 0‖) (κ * ρ * ‖x 1‖) n) := by
          rw [← hmul]
          congr 3 <;> ring
  have htail : Summable fun i => dynkinNormSum x (i + (N + 1)) :=
    (summable_nat_add_iff (N + 1) (f := dynkinNormSum x)).2 hD
  have hMt : Summable fun i => bchMaj (κ * ρ * ‖x 0‖) (κ * ρ * ‖x 1‖) (i + (N + 1)) :=
    (summable_nat_add_iff (N + 1) (f := bchMaj (κ * ρ * ‖x 0‖) (κ * ρ * ‖x 1‖))).2 hM.summable
  have hshift : ∀ i, dynkinNormSum x (i + (N + 1)) ≤
      (ρ ^ (N + 1))⁻¹ * (κ⁻¹ * bchMaj (κ * ρ * ‖x 0‖) (κ * ρ * ‖x 1‖) (i + (N + 1))) := by
    intro i
    refine (hw _).trans ?_
    have hb : 0 ≤ bchMaj (κ * ρ * ‖x 0‖) (κ * ρ * ‖x 1‖) (i + (N + 1)) :=
      bchMaj_nonneg (mul_nonneg (mul_nonneg hκ0.le hρ0.le) (norm_nonneg _))
        (mul_nonneg (mul_nonneg hκ0.le hρ0.le) (norm_nonneg _)) _
    have hle : (ρ ^ (i + (N + 1)))⁻¹ ≤ (ρ ^ (N + 1))⁻¹ :=
      inv_anti₀ (pow_pos hρ0 _) (pow_le_pow_right₀ hρ.le (Nat.le_add_left _ _))
    calc κ⁻¹ * ((ρ ^ (i + (N + 1)))⁻¹ * bchMaj (κ * ρ * ‖x 0‖) (κ * ρ * ‖x 1‖) (i + (N + 1)))
        ≤ κ⁻¹ * ((ρ ^ (N + 1))⁻¹ * bchMaj (κ * ρ * ‖x 0‖) (κ * ρ * ‖x 1‖) (i + (N + 1))) := by
          gcongr
      _ = _ := by ring
  refine (Summable.tsum_le_tsum hshift htail ((hMt.mul_left _).mul_left _)).trans ?_
  rw [tsum_mul_left, tsum_mul_left]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hκ0.le))
    (inv_nonneg.2 (pow_pos hρ0 _).le)
  rw [mul_add, ← hM.tsum_eq, ← hM.summable.sum_add_tsum_nat_add (N + 1)]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun n _ =>
    bchMaj_nonneg (mul_nonneg (mul_nonneg hκ0.le hρ0.le) (norm_nonneg _))
      (mul_nonneg (mul_nonneg hκ0.le hρ0.le) (norm_nonneg _)) n)

/-- **Theorem 7.3 (iv)**: in a complete space, Dynkin's Lie series converges. -/
theorem summable_dynkinTerm [CompleteSpace L] (x : Fin 2 → L) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ : ∀ u v : L, ‖⁅u, v⁆‖ ≤ κ * ‖u‖ * ‖v‖) (hs : κ * (‖x 0‖ + ‖x 1‖) < Real.log 2) :
    Summable (dynkinTerm (𝕂 := 𝕂) x) :=
  Summable.of_norm_bounded (summable_dynkinNormSum x hκ0 hκ hs) (norm_dynkinTerm_le x)

end Eval

section Associative

variable {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

/-- In a normed ring the commutator satisfies `‖⁅u, v⁆‖ ≤ 2 ‖u‖ ‖v‖`. -/
lemma norm_lie_le_two_mul (u v : 𝔸) : ‖⁅u, v⁆‖ ≤ 2 * ‖u‖ * ‖v‖ := by
  rw [Ring.lie_def]
  calc ‖u * v - v * u‖ ≤ ‖u * v‖ + ‖v * u‖ := norm_sub_le _ _
    _ ≤ ‖u‖ * ‖v‖ + ‖v‖ * ‖u‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖u‖ * ‖v‖ := by ring

/-- **Theorem 7.3 (iii)**: for `‖X‖ + ‖Y‖ < ½ log 2` the right-nested commutator summands of
Dynkin's formula are absolutely summable, with absolute sum at most
`M_D(s) = -½ log (2 - e^{2s})`, `s = ‖X‖ + ‖Y‖`. -/
theorem tsum_dynkinNormSum_le_of_lt (X Y : 𝔸) (hs : ‖X‖ + ‖Y‖ < Real.log 2 / 2) :
    Summable (dynkinNormSum ![X, Y]) ∧
    ∑' n, dynkinNormSum ![X, Y] n ≤ -(2⁻¹ * Real.log (2 - Real.exp (2 * (‖X‖ + ‖Y‖)))) := by
  have h2 : (2 : ℝ) * (‖![X, Y] 0‖ + ‖![X, Y] 1‖) < Real.log 2 := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linarith
  refine ⟨summable_dynkinNormSum ![X, Y] two_pos norm_lie_le_two_mul h2, ?_⟩
  have := tsum_dynkinNormSum_le ![X, Y] two_pos norm_lie_le_two_mul h2
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_neg]
    using this

/-- **Theorem 7.3 (iii), tail**: for `1 < ρ` with `ρ (‖X‖ + ‖Y‖) < ½ log 2`, the absolute sum
of the Dynkin summands of degree `> N` is at most `ρ^{-(N+1)} M_D(ρ s)`. -/
theorem tsum_dynkinNormSum_tail_le_of_lt (X Y : 𝔸) {ρ : ℝ} (hρ : 1 < ρ)
    (hs : ρ * (‖X‖ + ‖Y‖) < Real.log 2 / 2) (N : ℕ) :
    ∑' i, dynkinNormSum ![X, Y] (i + (N + 1)) ≤
      (ρ ^ (N + 1))⁻¹ * -(2⁻¹ * Real.log (2 - Real.exp (2 * (ρ * (‖X‖ + ‖Y‖))))) := by
  have h2 : (2 : ℝ) * ρ * (‖![X, Y] 0‖ + ‖![X, Y] 1‖) < Real.log 2 := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linarith
  have := tsum_dynkinNormSum_tail_le ![X, Y] two_pos norm_lie_le_two_mul hρ h2 N
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_neg,
    mul_assoc] using this

attribute [local instance 100] LieRing.ofAssociativeRing in
/-- The evaluated right-nested bracket of a list is the evaluation of the formal one. -/
lemma evalHom_rbList (X Y : 𝔸) : ∀ l : List (Fin 2),
    evalHom X Y (rbList 𝕂 l) = rbEval ![X, Y] l
  | [] => by simp [rbList, rbEval]
  | [i] => by
    simp only [rbList, rbEval, gen, evalHom, MonoidAlgebra.lift_single, one_smul,
      FreeMonoid.lift_eval_of]
  | i :: j :: rest => by
    have ih := evalHom_rbList X Y (j :: rest)
    simp only [rbList, rbEval]
    rw [Ring.lie_def, map_sub, map_mul, map_mul, ih, Ring.lie_def]
    have hg : evalHom X Y (gen 𝕂 i) = ![X, Y] i := by
      simp only [gen, evalHom, MonoidAlgebra.lift_single, one_smul, FreeMonoid.lift_eval_of]
    rw [hg]

/-- **Dynkin's formula, evaluated** (Theorem 4.1 in a normed algebra): for `n ≥ 1`,
`Zₙ(X, Y)` is the degree-`n` part of Dynkin's series `dynkinTerm ![X, Y] n`. -/
theorem bchHom_eq_dynkinTerm (X Y : 𝔸) {n : ℕ} (hn : 0 < n) :
    bchHom 𝕂 X Y n = dynkinTerm (𝕂 := 𝕂) ![X, Y] n := by
  rw [bchHom_eq_evalHom, bchHom_eq_dynkin_blocks hn, dynkinTerm, map_smul, map_sum]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [map_smul, map_sum]
  congr 1
  refine sum_congr rfl fun rs _ => ?_
  rw [map_smul, blockWord_gen, R_single, one_smul, rb, evalHom_rbList]

end Associative

end BCH
