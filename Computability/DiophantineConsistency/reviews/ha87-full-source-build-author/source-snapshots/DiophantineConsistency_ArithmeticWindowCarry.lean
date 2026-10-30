import DiophantineConsistency.ArithmeticCyclicWord

/-! Explicit end-around carries, in every model of IΣ1, replacing the external
least-fixed-point construction. A finite (standard) family of words `X i < 2^{wn}`
with Boolean digits and coefficients `a i` has column values
`raw k = Σ_i a_i·dig(X_i,k)`. If `Σ a_i X_i ≡ F (mod 2^{wn}-1)` with `F < 2^{wn}-1`
and the coefficient mass is below `(b+1)(2^w-1)`, then with `E = ⌊Σ a_i X_i/M⌋`,
`Q k = E + Σ_i a_i (X_i mod 2^{wk})` and `κ k = ⌊Q(k+1)/2^{w(k+1)}⌋`, every carry is
at most `b`, the incoming carry of position 0 is `κ (n-1) = E`, and the cyclic
carry equation holds with the digits of `F`. Every step is a ring/division
identity at one position; the only induction is the remainder bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticWindowCarry
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {ι : Type*} [Fintype ι]

/-- The column value at position `k`. -/
noncomputable def raw (w : V) (a X : ι → V) (k : V) : V := ∑ i, a i * dig w (X i) k

/-- The quotient of the total word by `2^{wn}-1`; it is the end-around carry. -/
noncomputable def excess (w n : V) (a X : ι → V) : V :=
  (∑ i, a i * X i) / (Exp.exp (w*n) - 1)

/-- The value entering position `k`: the excess plus the first `k` columns. -/
noncomputable def prefixValue (w n : V) (a X : ι → V) (k : V) : V :=
  excess w n a X + ∑ i, a i * (X i % Exp.exp (w*k))

/-- The carry out of position `k`. -/
noncomputable def carry (w n : V) (a X : ι → V) (k : V) : V :=
  prefixValue w n a X (k+1) / Exp.exp (w*(k+1))

/-- Hypotheses of the end-around carry. -/
structure CarryInput (w n F b : V) (a X : ι → V) : Prop where
  n_pos : 0 < n
  M_pos : 0 < Exp.exp (w*n) - 1
  word_lt : ∀ i, X i < Exp.exp (w*n)
  boolean : ∀ i, ∀ k < n, dig w (X i) k ≤ 1
  F_lt : F < Exp.exp (w*n) - 1
  congr : (∑ i, a i * X i) % (Exp.exp (w*n) - 1) = F % (Exp.exp (w*n) - 1)
  mass : (∑ i, a i) + 1 ≤ (b+1) * (Exp.exp w - 1)

section
variable {w n F b : V} {a X : ι → V}

private theorem sum_mod_le (h : CarryInput w n F b a X) {k : V} (hk : k ≤ n) :
    ∑ i, a i * (X i % Exp.exp (w*k)) ≤ (∑ i, a i) * rep w k := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left
    (mod_le_rep w (X i) k fun j hj => h.boolean i j (lt_of_lt_of_le hj hk)) (by simp)

private theorem key_bound (h : CarryInput w n F b a X) (k : V) :
    (∑ i, a i) * rep w k + rep w k + (b+1) ≤ (b+1) * Exp.exp (w*k) := by
  have hu := repunit_identity w k
  have hm := mul_le_mul_of_nonneg_right h.mass (by simp : (0:V) ≤ rep w k)
  calc (∑ i, a i) * rep w k + rep w k + (b+1) = ((∑ i, a i) + 1) * rep w k + (b+1) := by ring
    _ ≤ (b+1) * (Exp.exp w - 1) * rep w k + (b+1) := (add_le_add_iff_right _).mpr hm
    _ = (b+1) * ((Exp.exp w - 1) * rep w k + 1) := by ring
    _ = (b+1) * Exp.exp (w*k) := by rw [hu]

private theorem total_eq (h : CarryInput w n F b a X) :
    ∑ i, a i * X i = (Exp.exp (w*n) - 1) * excess w n a X + F := by
  have hd := div_add_mod (∑ i, a i * X i) (Exp.exp (w*n) - 1)
  rw [h.congr, mod_eq_self_of_lt h.F_lt] at hd
  exact hd.symm

private theorem one_le_rep {n : V} (hn : 0 < n) (w : V) : 1 ≤ rep w n := by
  have hn1 : n - 1 + 1 = n := tsub_add_cancel_of_le (pos_iff_one_le.mp hn)
  rw [← hn1, rep_succ_add]
  exact le_trans (one_le_exp _) (le_add_of_nonneg_left (by simp))

theorem excess_le (h : CarryInput w n F b a X) : excess w n a X ≤ b := by
  set M := Exp.exp (w*n) - 1
  set E := excess w n a X
  set U := rep w n
  have hPM : Exp.exp (w*n) = M + 1 := (tsub_add_cancel_of_le (one_le_exp _)).symm
  have hT : ∑ i, a i * X i ≤ (∑ i, a i) * U := by
    have := sum_mod_le h (le_refl n)
    have hw : ∀ i, X i % Exp.exp (w*n) = X i := fun i => mod_eq_self_of_lt (h.word_lt i)
    simpa only [hw] using this
  have hk := key_bound h n
  rw [hPM] at hk
  have hU : 1 ≤ U := one_le_rep h.n_pos w
  have hlt : (∑ i, a i) * U < (b+1) * M := by
    have h2 : (∑ i, a i) * U + U ≤ (b+1) * M := by
      have : (∑ i, a i) * U + U + (b+1) ≤ (b+1) * M + (b+1) := by
        calc _ ≤ (b+1) * (M+1) := hk
          _ = _ := by ring
      exact (add_le_add_iff_right _).mp this
    exact lt_of_lt_of_le (lt_of_lt_of_le (lt_add_one _) ((add_le_add_iff_left _).mpr hU)) h2
  have hME : M * E < M * (b+1) := by
    calc M * E ≤ M * E + F := le_add_of_nonneg_right (by simp)
      _ = ∑ i, a i * X i := (total_eq h).symm
      _ ≤ (∑ i, a i) * U := hT
      _ < (b+1) * M := hlt
      _ = M * (b+1) := mul_comm _ _
  exact le_iff_lt_succ.mpr (lt_of_mul_lt_mul_left hME (by simp))

theorem prefix_zero : prefixValue w n a X 0 = excess w n a X := by
  simp [prefixValue]

theorem prefix_succ (k : V) :
    prefixValue w n a X (k+1) = prefixValue w n a X k + raw w a X k * Exp.exp (w*k) := by
  have hi : ∀ i, a i * (X i % Exp.exp (w*(k+1))) =
      a i * (X i % Exp.exp (w*k)) + a i * dig w (X i) k * Exp.exp (w*k) := fun i => by
    rw [mod_exp_succ]; ring
  unfold prefixValue raw
  rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_add_distrib, Finset.sum_mul]
  ring

theorem prefix_length (h : CarryInput w n F b a X) :
    prefixValue w n a X n = F + excess w n a X * Exp.exp (w*n) := by
  unfold prefixValue
  have hw : ∀ i, X i % Exp.exp (w*n) = X i := fun i => mod_eq_self_of_lt (h.word_lt i)
  simp only [hw]
  rw [total_eq h]
  have hPM : Exp.exp (w*n) = (Exp.exp (w*n) - 1) + 1 :=
    (tsub_add_cancel_of_le (one_le_exp _)).symm
  conv_rhs => rw [hPM]
  ring

theorem carry_last (h : CarryInput w n F b a X) : carry w n a X (n-1) = excess w n a X := by
  have hn1 : n - 1 + 1 = n := tsub_add_cancel_of_le (pos_iff_one_le.mp h.n_pos)
  unfold carry
  rw [hn1, prefix_length h, add_comm, div_mul_add _ _
    (lt_of_lt_of_le h.F_lt tsub_le_self)]

theorem carry_le (h : CarryInput w n F b a X) {k : V} (hk : k < n) : carry w n a X k ≤ b := by
  have hk1 : k + 1 ≤ n := lt_iff_succ_le.mp hk
  have hQ : prefixValue w n a X (k+1) < (b+1) * Exp.exp (w*(k+1)) := by
    unfold prefixValue
    have h1 := sum_mod_le h hk1
    have h2 := key_bound h (k+1)
    have hE := excess_le h
    calc excess w n a X + ∑ i, a i * (X i % Exp.exp (w*(k+1)))
        ≤ b + (∑ i, a i) * rep w (k+1) := add_le_add hE h1
      _ < b + (∑ i, a i) * rep w (k+1) + 1 := lt_add_one _
      _ ≤ (∑ i, a i) * rep w (k+1) + rep w (k+1) + (b+1) := by
          have : b + (∑ i, a i) * rep w (k+1) + 1 = (∑ i, a i) * rep w (k+1) + (b+1) := by ring
          rw [this]
          exact (add_le_add_iff_right _).mpr (le_add_of_nonneg_right (by simp))
      _ ≤ _ := h2
  have := div_lt_of_lt_mul hQ
  exact (add_le_add_iff_right 1).mp (lt_iff_succ_le.mp this)

/-- The incoming carry of position `k`. -/
theorem incoming (h : CarryInput w n F b a X) {k : V} (hk : k < n) :
    prefixValue w n a X k / Exp.exp (w*k) = carry w n a X (cyc n k 1) := by
  rcases zero_or_succ k with rfl | ⟨j, rfl⟩
  · rw [(cyc_one hk).1 rfl, carry_last h, prefix_zero]
    simp
  · have hpos : 0 < j + 1 := by simp
    rw [(cyc_one hk).2 hpos, add_tsub_cancel_right]
    rfl

private theorem prefix_tail (h : CarryInput w n F b a X) {k : V} (hk : k < n) :
    ∃ Z, prefixValue w n a X n = prefixValue w n a X (k+1) + Z * Exp.exp (w*(k+1)) := by
  have hk1 : k + 1 ≤ n := lt_iff_succ_le.mp hk
  refine ⟨∑ i, a i * (X i % Exp.exp (w*n) / Exp.exp (w*(k+1))), ?_⟩
  unfold prefixValue
  have : ∀ i, a i * (X i % Exp.exp (w*n)) =
      a i * (X i % Exp.exp (w*(k+1))) +
        a i * (X i % Exp.exp (w*n) / Exp.exp (w*(k+1))) * Exp.exp (w*(k+1)) := by
    intro i
    conv_lhs => rw [mod_eq_mod_add w (X i) (k+1) n hk1]
    ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_mul]
  ring

/-- **The local carry identity** at every position. -/
theorem carry_column (h : CarryInput w n F b a X) {k : V} (hk : k < n) :
    carry w n a X k = (raw w a X k + carry w n a X (cyc n k 1)) / Exp.exp w ∧
      dig w F k = (raw w a X k + carry w n a X (cyc n k 1)) % Exp.exp w := by
  have hP : (0:V) < Exp.exp (w*k) := exp_pos _
  have hY : prefixValue w n a X (k+1) / Exp.exp (w*k) =
      raw w a X k + carry w n a X (cyc n k 1) := by
    rw [← incoming h hk, prefix_succ]
    have hd := div_add_mod (prefixValue w n a X k) (Exp.exp (w*k))
    have e : prefixValue w n a X k + raw w a X k * Exp.exp (w*k) =
        (raw w a X k + prefixValue w n a X k / Exp.exp (w*k)) * Exp.exp (w*k) +
          prefixValue w n a X k % Exp.exp (w*k) := by
      conv_lhs => rw [← hd]
      ring
    rw [e, div_mul_add _ _ (mod_lt _ hP)]
  constructor
  · show prefixValue w n a X (k+1) / Exp.exp (w*(k+1)) = _
    rw [div_exp_succ, ← hY]
  · obtain ⟨Z, hZ⟩ := prefix_tail h hk
    have h1 : dig w F k = dig w (prefixValue w n a X n) k := by
      rw [prefix_length h]
      exact (dig_add_mul_high w F _ k n hk).symm
    rw [h1, hZ, dig_add_mul_high w _ Z k (k+1) (lt_add_one k)]
    unfold dig
    rw [← hY]

/-- **End-around carries**: bounded carries, digits, and the cyclic carry equation. -/
theorem end_around_carry (h : CarryInput w n F b a X) :
    ∀ k < n, carry w n a X k ≤ b ∧ dig w F k < Exp.exp w ∧
      raw w a X k + carry w n a X (cyc n k 1) = dig w F k + Exp.exp w * carry w n a X k ∧
      carry w n a X k = (raw w a X k + carry w n a X (cyc n k 1)) / Exp.exp w := by
  intro k hk
  obtain ⟨hc, hd⟩ := carry_column h hk
  refine ⟨carry_le h hk, dig_lt w F k, ?_, hc⟩
  rw [hc, hd, add_comm (_ % _)]
  exact (div_add_mod _ _).symm

end

end DiophantineConsistency.ArithmeticWindowCarry
