import GowersSzemeredi.Definitions

/-! The weak-transitivity ladder: the engine of Milićević's abstract
Balog–Szemerédi–Gowers theorem (arXiv:2601.01682, Theorem 4.1, Claims 4.3
and 4.4).

Let `R : ℕ → V → V → Prop` be a family of relations on a finite vertex set
`S`, with *weak transitivity* against the first level: whenever at least
`c·|S|` vertices `z ∈ S` satisfy `R i x z` and `R 1 z y`, then
`R (i+1) x y`. Then many short `R 1`-chains force a relation:
* `chainCount r S m x y` counts the sequences `z₁, …, z_m ∈ S` with
  `r x z₁, r z₁ z₂, …, r z_m y`;
* `chainCount_le`: there are at most `|S|^m`;
* `rel_of_chainCount`: weak transitivity is needed only up to level `M`.
  If `m + 1 ≤ M`, `2^m·c ≤ η`, `0 < η` and
  `η·|S|^m ≤ chainCount (R 1) S m x y`, then `R (m+1) x y`.

The proof is Milićević's induction: average over the last intermediate
vertex, losing a factor `2` per step, and apply weak transitivity once. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The number of `r`-chains `x = z₀, z₁, …, z_m, z_{m+1} = y` with all
intermediate vertices in `S`. -/
def chainCount {V : Type*} (r : V → V → Prop) (S : Finset V) : Nat → V → V → Nat
  | 0, x, y => if r x y then 1 else 0
  | m + 1, x, y => ∑ z ∈ S, chainCount r S m x z * (if r z y then 1 else 0)

theorem chainCount_le {V : Type*} (r : V → V → Prop) (S : Finset V) (m : Nat) (x y : V) :
    chainCount r S m x y ≤ S.card ^ m := by
  induction m generalizing y with
  | zero => simp only [chainCount, pow_zero]; split_ifs <;> omega
  | succ m ih =>
    simp only [chainCount]
    calc ∑ z ∈ S, chainCount r S m x z * (if r z y then 1 else 0)
        ≤ ∑ _z ∈ S, S.card ^ m := Finset.sum_le_sum fun z _ => by
          split_ifs <;> simp [ih z]
      _ = S.card ^ (m + 1) := by rw [Finset.sum_const, smul_eq_mul, pow_succ, mul_comm]

/-- **Averaging over the last intermediate vertex.** If the chains of
length `m+1` number at least `η·|S|^(m+1)`, then at least `(η/2)·|S|`
vertices `z` close the chain (`r z y`) and carry at least `(η/2)·|S|^m`
shorter chains. -/
theorem many_good_last_vertices {V : Type*} (r : V → V → Prop) (S : Finset V) (m : Nat)
    (x y : V) {η : Real}
    (h : η * (S.card : Real) ^ (m + 1) ≤ chainCount r S (m + 1) x y) :
    η / 2 * S.card ≤ ((S.filter fun z => r z y ∧
      η / 2 * (S.card : Real) ^ m ≤ chainCount r S m x z).card : Real) := by
  rcases le_or_gt η 0 with hη | hη
  · have : η / 2 * (S.card : Real) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    exact this.trans (by positivity)
  let p : V → Prop := fun z => r z y ∧ η / 2 * (S.card : Real) ^ m ≤ chainCount r S m x z
  let Z := S.filter p
  let t : V → Real := fun z => (chainCount r S m x z : Real) * (if r z y then 1 else 0)
  have hsum : (chainCount r S (m + 1) x y : Real) = ∑ z ∈ S, t z := by
    simp only [chainCount, t]; push_cast; rfl
  have hin : ∑ z ∈ Z, t z ≤ Z.card * (S.card : Real) ^ m := by
    calc ∑ z ∈ Z, t z ≤ ∑ _z ∈ Z, (S.card : Real) ^ m := Finset.sum_le_sum fun z _ => by
          have hle : (chainCount r S m x z : Real) ≤ (S.card : Real) ^ m := by
            exact_mod_cast chainCount_le r S m x z
          simp only [t]
          split_ifs
          · rw [mul_one]; exact hle
          · rw [mul_zero]; positivity
      _ = Z.card * (S.card : Real) ^ m := by rw [Finset.sum_const, nsmul_eq_mul]
  have hout : ∑ z ∈ S.filter (fun z => ¬ p z), t z ≤ S.card * (η / 2 * (S.card : Real) ^ m) := by
    calc ∑ z ∈ S.filter (fun z => ¬ p z), t z
        ≤ ∑ _z ∈ S.filter (fun z => ¬ p z), η / 2 * (S.card : Real) ^ m :=
          Finset.sum_le_sum fun z hz => by
            have hnp : ¬ p z := (Finset.mem_filter.mp hz).2
            simp only [t]
            by_cases hr : r z y
            · rw [if_pos hr, mul_one]
              exact (not_le.mp fun h' => hnp ⟨hr, h'⟩).le
            · rw [if_neg hr, mul_zero]; positivity
      _ = ((S.filter fun z => ¬ p z).card : Real) * (η / 2 * (S.card : Real) ^ m) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ S.card * (η / 2 * (S.card : Real) ^ m) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast Finset.card_filter_le _ _
  have hsplit : (chainCount r S (m + 1) x y : Real) ≤
      Z.card * (S.card : Real) ^ m + S.card * (η / 2 * (S.card : Real) ^ m) := by
    rw [hsum, ← Finset.sum_filter_add_sum_filter_not S p]
    exact add_le_add hin hout
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · simp [h0]
  have hSm : (0 : Real) < (S.card : Real) ^ m := by positivity
  have h2 : η * (S.card * (S.card : Real) ^ m) ≤
      Z.card * (S.card : Real) ^ m + S.card * (η / 2 * (S.card : Real) ^ m) := by
    have hpow : (S.card : Real) ^ (m + 1) = S.card * (S.card : Real) ^ m := by ring
    rw [← hpow]; exact h.trans hsplit
  have h3 : η / 2 * S.card * (S.card : Real) ^ m ≤ Z.card * (S.card : Real) ^ m := by
    nlinarith
  exact le_of_mul_le_mul_right h3 hSm

/-- **The weak-transitivity ladder.** -/
theorem rel_of_chainCount {V : Type*} (R : Nat → V → V → Prop) (S : Finset V) {c : Real}
    {M : Nat}
    (hWT : ∀ i, i + 1 ≤ M → ∀ x y,
      c * S.card ≤ ((S.filter fun z => R i x z ∧ R 1 z y).card : Real) → R (i + 1) x y) :
    ∀ (m : Nat) (x y : V) {η : Real}, m + 1 ≤ M → 0 < η → 2 ^ m * c ≤ η →
      η * (S.card : Real) ^ m ≤ chainCount (R 1) S m x y → R (m + 1) x y := by
  intro m
  induction m with
  | zero =>
    intro x y η _ hη _ h
    simp only [chainCount, pow_zero, mul_one] at h
    by_contra hr
    simp only [hr, if_false, Nat.cast_zero] at h
    linarith
  | succ m ih =>
    intro x y η hM hη hc h
    apply hWT (m + 1) hM x y
    have hgood := many_good_last_vertices (R 1) S m x y h
    have hsub : (S.filter fun z => R 1 z y ∧
        η / 2 * (S.card : Real) ^ m ≤ chainCount (R 1) S m x z) ⊆
        S.filter fun z => R (m + 1) x z ∧ R 1 z y := by
      intro z hz
      obtain ⟨hzS, hzy, hcount⟩ := Finset.mem_filter.mp hz
      refine Finset.mem_filter.mpr ⟨hzS, ih x z (by omega) (by positivity) ?_ hcount, hzy⟩
      rw [pow_succ] at hc
      linarith
    have hc2 : c ≤ η / 2 := by
      have h1 : (1 : Real) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
      rw [pow_succ] at hc
      by_cases hc0 : c ≤ 0
      · linarith
      · have hc0 := not_le.mp hc0; nlinarith
    calc c * S.card ≤ η / 2 * S.card := mul_le_mul_of_nonneg_right hc2 (by positivity)
      _ ≤ _ := hgood
      _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub

end LeanProofs.GowersSzemeredi
