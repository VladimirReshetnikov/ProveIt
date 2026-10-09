import GowersSzemeredi.Proofs05SimultaneousMultiaffinePartition

/-! The Schmidt recurrence and the multilinear partition with named constants.

`Proofs05SchmidtRecurrence` and `Proofs05SimultaneousMultiaffinePartition`
state their constants existentially. A comparison with a printed budget
needs an upper bound on them, which a bare `∃` cannot give (research notes,
J.5b). The upstream constants are concrete. The Weyl budget is the value of
the explicit polynomial `OAI.Erdos3.weylBudgetPolynomial j`, and every later
constant is a closed formula in it. This module restates the existential
steps with these witnesses:
* `schmidtWeylA`, `schmidtWeylD`, `schmidtWeylC`: the Weyl inverse-theorem
  constants, and `polynomial_weyl_inverse_power_interval_explicit`;
* `schmidtMonomialK`, `schmidtMonomialP`:
  `simultaneous_modular_monomial_recurrence_explicit`;
* `uniformSchmidtK`, `uniformSchmidtP`:
  `uniform_modular_monomial_recurrence_explicit`;
* `multiaffinePartitionK`, `multiaffinePartitionP`:
  `simultaneous_multiaffine_partition_bound_explicit` and
  `simultaneous_multilinear_partition_bound_explicit`.

The proofs follow the existential versions step by step. No numerical size
of the constants is asserted here. The module imports the OAI port, so it is
checked on the full-verification host. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

section Weyl

open Polynomial

/-- The coefficient sum of the upstream Weyl budget polynomial. -/
def schmidtWeylA (j : Nat) : Nat := (OAI.Erdos3.weylBudgetPolynomial j).eval 1

/-- One more than the degree of the upstream Weyl budget polynomial. -/
def schmidtWeylD (j : Nat) : Nat := (OAI.Erdos3.weylBudgetPolynomial j).natDegree + 1

/-- The Weyl inverse-theorem constant in degree `j + 1`. -/
def schmidtWeylC (j : Nat) : Nat := schmidtWeylA j * 3 ^ schmidtWeylD j

theorem schmidtWeylA_pos (j : Nat) : 0 < schmidtWeylA j := by
  unfold schmidtWeylA
  rw [OAI.Erdos3.weylBudgetPolynomial_eval]
  exact OAI.Erdos3.weylBudget_pos j (by decide)

theorem schmidtWeylD_pos (j : Nat) : 0 < schmidtWeylD j := Nat.succ_pos _

theorem schmidtWeylC_pos (j : Nat) : 0 < schmidtWeylC j :=
  Nat.mul_pos (schmidtWeylA_pos j) (by positivity)

/-- The Weyl budget is at most `A * B^d` with the named constants. -/
theorem weylBudget_le_explicit (j : Nat) {B : Nat} (hB : 1 ≤ B) :
    OAI.Erdos3.weylBudget j B ≤ schmidtWeylA j * B ^ schmidtWeylD j := by
  rw [← OAI.Erdos3.weylBudgetPolynomial_eval]
  exact (OAI.Erdos3.natPolynomial_eval_le_one_mul_pow _ hB).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hB (Nat.le_succ _)))

/-- **Weyl's inverse theorem with named constants.** -/
theorem polynomial_weyl_inverse_power_bound_explicit (j : Nat) :
    ∀ (P : Polynomial Real) (N : Nat) (δ : Real),
      P.natDegree ≤ j + 1 → 0 < N → 0 < δ → δ ≤ 1 →
      (schmidtWeylC j : Real) ≤ δ ^ schmidtWeylD j * N →
      δ * N ≤ ‖OAI.Erdos3.polynomialExponentialSum P N‖ →
      ∃ q : Nat, 0 < q ∧ (q : Real) ≤ schmidtWeylC j / δ ^ schmidtWeylD j ∧ ∃ p : Int,
        |(q : Real) * P.coeff (j + 1) - p| ≤
          schmidtWeylC j / (δ ^ schmidtWeylD j * (N : Real) ^ (j + 1)) := by
  intro P N δ hP hN hδ hδone hsize hscore
  obtain ⟨B, hB, hBupper, hBlower⟩ := OAI.Erdos3.exists_reciprocal_bias_integer hδ hδone
  have hBR : (0 : Real) < B := by exact_mod_cast (show 0 < B by omega)
  have hNR : (0 : Real) < N := Nat.cast_pos.mpr hN
  have hδd : 0 < δ ^ schmidtWeylD j := pow_pos hδ _
  have hbudgetR : (OAI.Erdos3.weylBudget j B : Real) ≤
      (schmidtWeylC j : Real) / δ ^ schmidtWeylD j := by
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg B : (0 : Real) ≤ B) hBupper (schmidtWeylD j)
    have hbp : (OAI.Erdos3.weylBudget j B : Real) ≤
        (schmidtWeylA j : Real) * (B : Real) ^ schmidtWeylD j := by
      exact_mod_cast weylBudget_le_explicit j (B := B) (by omega)
    apply hbp.trans
    have hm := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (α := Real) (schmidtWeylA j))
    simpa only [schmidtWeylC, div_pow, mul_div_assoc, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat] using hm
  have hsizeB : OAI.Erdos3.weylBudget j B ≤ N := by
    have hs : (schmidtWeylC j : Real) / δ ^ schmidtWeylD j ≤ N :=
      (div_le_iff₀ hδd).mpr (by nlinarith only [hsize])
    exact_mod_cast hbudgetR.trans hs
  have hscoreB : (N : Real) / B ≤ ‖OAI.Erdos3.polynomialExponentialSum P N‖ := by
    apply le_trans _ hscore
    apply (div_le_iff₀ hBR).mpr
    have hm := mul_le_mul_of_nonneg_right hBlower hNR.le
    nlinarith only [hm]
  obtain ⟨q, hq, hqbound, p, hp⟩ :=
    OAI.Erdos3.polynomial_weyl_inverse j P hB hP hN hsizeB hscoreB
  refine ⟨q, hq, (Nat.cast_le.mpr hqbound).trans hbudgetR, p, hp.trans ?_⟩
  calc
    (OAI.Erdos3.weylBudget j B : Real) / (N : Real) ^ (j + 1) ≤
        ((schmidtWeylC j : Real) / δ ^ schmidtWeylD j) / (N : Real) ^ (j + 1) :=
      div_le_div_of_nonneg_right hbudgetR (by positivity)
    _ = _ := by rw [div_div]

/-- **Weyl's inverse theorem on intervals, with named constants.** -/
theorem polynomial_weyl_inverse_power_interval_explicit (j : Nat) :
    OAI.Erdos3.PolynomialIntervalPowerBound (j + 1) (schmidtWeylC j) (schmidtWeylD j) := by
  intro P u v δ hP hN hδ hδone hsize hscore
  rw [OAI.Erdos3.polynomial_interval_sum_translate] at hscore
  obtain ⟨q, hq, hqbound, p, hp⟩ := polynomial_weyl_inverse_power_bound_explicit j
    (P.comp (Polynomial.X + Polynomial.C (u : Real))) (v - u).toNat δ
    (by rwa [OAI.Erdos3.polynomial_translate_degree]) hN hδ hδone hsize hscore
  rw [OAI.Erdos3.polynomial_translate_top_coeff P hP] at hp
  exact ⟨q, hq, hqbound, p, hp⟩

end Weyl

/-- The Schmidt base constant in degree `j + 1`. -/
def schmidtMonomialK (j : Nat) : Real :=
  OAI.Erdos3.schmidtRecurrenceBase (schmidtWeylC j) (schmidtWeylD j)

/-- The Schmidt exponent constant in degree `j + 1`. -/
def schmidtMonomialP (j : Nat) : Nat :=
  OAI.Erdos3.schmidtRecurrenceExponent (schmidtWeylD j)

theorem one_le_schmidtMonomialK (j : Nat) : 1 ≤ schmidtMonomialK j := by
  have h := (OAI.Erdos3.schmidtRecurrenceBase_bounds (schmidtWeylC j) (schmidtWeylD j)).1
  unfold schmidtMonomialK
  linarith

theorem schmidtMonomialP_pos (j : Nat) : 0 < schmidtMonomialP j := by
  unfold schmidtMonomialP OAI.Erdos3.schmidtRecurrenceExponent
  omega

/-- **Schmidt's monomial recurrence on `ZMod N`, with named constants.** -/
theorem simultaneous_modular_monomial_recurrence_explicit (j : Nat) :
    ∀ (N : Nat) [NeZero N] (ι : Type) [Fintype ι]
      (a : ι → ZMod N) (M : Nat) (R : Real), 0 < R → R ≤ 1 →
      (schmidtMonomialK j * ((Fintype.card ι : Real) + 1) / R) ^
        (schmidtMonomialP j * (Fintype.card ι + 1) ^ 2) ≤ M →
      ∃ q : Nat, 0 < q ∧ q ≤ M ∧ ∀ i,
        (centeredAbs ((q : ZMod N) ^ (j + 1) * a i) : Real) < R * N := by
  intro N _ ι _ a M R hR hR1 hM
  obtain ⟨q, hq, hqM, b, hb⟩ :=
    (polynomial_weyl_inverse_power_interval_explicit j).simultaneous_monomial_recurrence
      (fun i => (a i).valMinAbs / (N : Real)) M hR hR1 hM
  exact ⟨q, hq, hqM, fun i => centered_monomial_of_integer_approximation (a i) (b i) (hb i)⟩

/-- One base constant for the degrees `1, …, k`. -/
def uniformSchmidtK (k : Nat) : Real := 1 + ∑ j : Fin k, schmidtMonomialK j

/-- One exponent constant for the degrees `1, …, k`. -/
def uniformSchmidtP (k : Nat) : Nat := 1 + ∑ j : Fin k, schmidtMonomialP j

theorem one_le_uniformSchmidtK (k : Nat) : 1 ≤ uniformSchmidtK k := by
  unfold uniformSchmidtK
  have : 0 ≤ ∑ j : Fin k, schmidtMonomialK j :=
    Finset.sum_nonneg fun j _ => zero_le_one.trans (one_le_schmidtMonomialK j)
  linarith

theorem uniformSchmidtP_pos (k : Nat) : 0 < uniformSchmidtP k := by
  unfold uniformSchmidtP
  omega

/-- **The uniform recurrence with named constants.** -/
theorem uniform_modular_monomial_recurrence_explicit (k : Nat) :
    UniformModularMonomialRecurrence k (uniformSchmidtK k) (uniformSchmidtP k) := by
  have hK0 (j : Fin k) : 0 ≤ schmidtMonomialK j :=
    zero_le_one.trans (one_le_schmidtMonomialK j)
  have hKC (j : Fin k) : schmidtMonomialK j ≤ uniformSchmidtK k := by
    have h := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hK0 i)
      (Finset.mem_univ j)
    unfold uniformSchmidtK
    linarith
  have hpe (j : Fin k) : schmidtMonomialP j ≤ uniformSchmidtP k := by
    have h := Finset.single_le_sum
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => Nat.zero_le (schmidtMonomialP i))
      (Finset.mem_univ j)
    unfold uniformSchmidtP
    omega
  have hC := one_le_uniformSchmidtK k
  intro N _ ι _ a M R hR hR1 hM j
  apply simultaneous_modular_monomial_recurrence_explicit j N ι a M R hR hR1
  have hc : (1 : Real) ≤ (Fintype.card ι : Real) + 1 := by norm_num
  have hbase : 1 ≤ uniformSchmidtK k * ((Fintype.card ι : Real) + 1) / R := by
    rw [le_div_iff₀ hR, one_mul]
    exact hR1.trans (by simpa using mul_le_mul hC hc (by norm_num) (by linarith))
  calc
    _ ≤ (uniformSchmidtK k * ((Fintype.card ι : Real) + 1) / R) ^
          (schmidtMonomialP j * (Fintype.card ι + 1) ^ 2) :=
      pow_le_pow_left₀ (by have := hK0 j; positivity)
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hKC j) (by positivity)) hR.le) _
    _ ≤ (uniformSchmidtK k * ((Fintype.card ι : Real) + 1) / R) ^
          (uniformSchmidtP k * (Fintype.card ι + 1) ^ 2) :=
      pow_le_pow_right₀ hbase (Nat.mul_le_mul_right _ (hpe j))
    _ ≤ M := hM

/-- The partition base constant after `h` monomial-family steps. -/
def multiaffinePartitionK (k : Nat) : Nat → Real
  | 0 => 2
  | h + 1 => max (multiaffinePartitionK k h) (uniformSchmidtK k)

/-- The partition exponent constant after `h` monomial-family steps. -/
def multiaffinePartitionP (k : Nat) : Nat → Nat
  | 0 => 1
  | h + 1 => multiaffinePartitionP k h * (2 * (k + 1) * uniformSchmidtP k + 4)

theorem two_le_multiaffinePartitionK (k h : Nat) : 2 ≤ multiaffinePartitionK k h := by
  induction h with
  | zero => exact le_rfl
  | succ h ih => exact ih.trans (le_max_left _ _)

theorem multiaffinePartitionP_pos (k h : Nat) : 0 < multiaffinePartitionP k h := by
  induction h with
  | zero => exact Nat.one_pos
  | succ h ih => exact Nat.mul_pos ih (by omega)

/-- **The multiaffine partition with named constants.** -/
theorem simultaneous_multiaffine_partition_bound_explicit (k : Nat) (hk : 0 < k) (h : Nat) :
    SimultaneousMultiaffinePartitionBound k h (multiaffinePartitionK k h)
      (multiaffinePartitionP k h) := by
  induction h with
  | zero => exact simultaneousMultiaffinePartitionBound_zero k
  | succ h ih =>
    exact ih.step hk (two_le_multiaffinePartitionK k h) (multiaffinePartitionP_pos k h)
      (one_le_uniformSchmidtK k) (uniform_modular_monomial_recurrence_explicit k)

/-- **The multilinear partition with named constants.** The constants are
`multiaffinePartitionK k (2^k)` and `multiaffinePartitionP k (2^k)`. -/
theorem simultaneous_multilinear_partition_bound_explicit (k : Nat) (hk : 0 < k) :
    ∀ (N : Nat) [NeZero N] (q : Nat) (P : Box N k), P.IsProper →
      ∀ mu : Fin q → Point N k → ZMod N, (∀ i, MultilinearOn P.carrier (mu i)) →
      ∀ H : Nat, 0 < H → multiaffinePartitionK k (2 ^ k) * ((q : Real) + 1) ≤ H →
        H ^ (multiaffinePartitionP k (2 ^ k) * (q + 1) ^ (2 * (2 ^ k))) ≤ P.width →
        ∃ M : Nat, ∃ Q : Fin M → Box N k,
          IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
          (∀ j, (H : Real) ≤ (Q j).width) ∧
          ∀ i j, diameterAtMostReal ((Q j).carrier.image (mu i)) ((2 ^ k : Real) / H * N) := by
  intro N _ q P hP mu hmu H hH hscale hsize
  choose psi hpsi heq using hmu
  choose c hc using (fun i => (isMultilinear_iff_multiaffineEval (psi i)).mp (hpsi i))
  obtain ⟨M, Q, hQpart, hQproper, hQwidth, hQdiam⟩ :=
    simultaneous_multiaffine_partition_bound_explicit k hk (2 ^ k) N q Finset.univ
      (fun _ _ _ _ => Finset.mem_univ _) (by simp) c P hP H hH hscale hsize
  refine ⟨M, Q, hQpart, hQproper, hQwidth, ?_⟩
  intro i j
  have himage : (Q j).carrier.image (mu i) =
      (Q j).carrier.image (multiaffineEval Finset.univ (c i)) := by
    apply Finset.image_congr
    intro x hx
    exact (heq i x (IsPartition.cell_subset hQpart j hx)).trans (hc i x)
  rw [himage]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hQdiam i j

end LeanProofs.GowersSzemeredi
