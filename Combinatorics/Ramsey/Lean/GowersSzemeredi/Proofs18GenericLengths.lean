import GowersSzemeredi.Proofs18GenericSzemeredi
import GowersSzemeredi.Proofs18GenericEnvelopeStep

/-! Theorem 18.2 and Corollary 18.7 at lengths `6 ≤ L ≤ 10`, from the
recurrence profiles (Notes L.7a, F4).

The single-piece step runs in every dimension `k = 2, …, L − 4`, starting
from the Fejér cubic bound (`envBound_three`). Dimension `k` uses
* the uniform covers of the split classes, at `V = classV Kc pc k`,
  `D = uDeg k = 2^(76·2^k)`;
* the recurrence profile in dimension `k`, with `Kc k, pc k ≤ 2^(2^(2^(k+5)))`.
`genMu k` is the envelope of the degree-`(k+2)` bound (`envBound_all`). The
lengths up to ten satisfy `genMu (L−4) + 2L + 14 ≤ 2^(L+9)`, which is checked
by evaluation; length eleven does not (Notes L.7a).
* `theorem_18_2_upto_ten_of_profiles`, `corollary_18_7_upto_ten_of_profiles`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-! ### The degrees -/

/-- The log-log-degree of the class base `V` in dimension `k`. -/
def genMuV (k : Nat) : Nat := 2 ^ (k + 6)
/-- The fixed-parameter exponent in dimension `k`. -/
def genMu0 (k : Nat) : Nat := max (genMuV k) (fixDeg k) + 2
/-- The log-degree of the cover control in dimension `k`. -/
def genMuD (k : Nat) : Nat := 76 * 2 ^ k

/-- The envelope of the degree-`(k+2)` bound after the steps in dimensions
`2, …, k`. -/
def genMu : Nat → Nat
  | 0 => 62
  | 1 => 62
  | k + 2 => envStep (k + 2) (genMuD (k + 2)) (genMu0 (k + 2)) (genMuK (k + 2)) (genMu (k + 1))

theorem genMu_succ {k : Nat} (hk : 1 ≤ k) :
    genMu (k + 1) = envStep (k + 1) (genMuD (k + 1)) (genMu0 (k + 1)) (genMuK (k + 1)) (genMu k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rfl

/-! ### Every degree -/

/-- The common hypotheses in dimension `k ≥ 2`. -/
theorem stdHyp_of_profiles (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5)))) {k : Nat}
    (hk : 2 ≤ k) :
    GenParams.StdHyp (classV Kc pc k) (uDeg k) k (Kc k) (pc k) (genMuV k) (genMuD k) (genMu0 k)
      (genMuK k) := by
  have hV1 := one_le_classV Kc pc k
  have hVb := classV_bound Kc pc hconst hk
  have hKr : (Kc k : Real) ≤ 2 ^ (2 ^ genMuK k) := by
    have := hconst k; unfold genMuK; push_cast at this ⊢
    linarith [Nat.cast_nonneg (α := Real) (pc k)]
  have hpr : (pc k : Real) ≤ 2 ^ (2 ^ genMuK k) := by
    have := hconst k; unfold genMuK; push_cast at this ⊢
    linarith [Nat.cast_nonneg (α := Real) (Kc k)]
  refine ⟨hV1, ?_, le_rfl, le_rfl, ?_, ?_, hK k, ?_, hp k, ?_⟩
  · -- `V ≤ 2·V ≤ 2^(2^(2^(k+6)) − 1) ≤ 2^(2^(2^(k+6)))`
    unfold genMuV
    have h1 : classV Kc pc k ≤ 2 * classV Kc pc k := by linarith
    refine h1.trans (hVb.trans (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)))
  · unfold uDeg
    calc k + 1 ≤ 2 ^ (k + 1) := Nat.lt_two_pow_self.le
      _ ≤ 2 ^ (76 * 2 ^ k) := Nat.pow_le_pow_right (by norm_num) (by
          have := Nat.lt_two_pow_self (n := k); omega)
  · unfold genMu0
    calc k ≤ 2 ^ k := Nat.lt_two_pow_self.le
      _ ≤ 2 ^ (max (genMuV k) (fixDeg k) + 2) := Nat.pow_le_pow_right (by norm_num) (by
          unfold fixDeg; have := Nat.lt_two_pow_self (n := k + 5)
          have := le_max_right (genMuV k) (2 ^ (k + 5) + 7); omega)
  · have : ((Kc k : Nat) : Real) ≤ ((2 ^ 2 ^ genMuK k : Nat) : Real) := by push_cast; exact hKr
    exact_mod_cast this
  · have : ((pc k : Nat) : Real) ≤ ((2 ^ 2 ^ genMuK k : Nat) : Real) := by push_cast; exact hpr
    exact_mod_cast this

/-- **Discrepancy bounds in every degree `k + 2 ≥ 4`**, from the recurrence
profiles. -/
theorem envBound_all (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5)))) :
    ∀ k, 2 ≤ k → EnvBound (k + 2) (genMu k) := by
  have hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))) :=
    fun k hk => abstractFamilyLemma166At_of k (hK k) (hp k) (hrec k hk)
  have hK1 : ∀ k, 1 ≤ Kc k := fun k => le_trans (by norm_num) (hK k)
  have hstep : ∀ k, 2 ≤ k → ∀ μ, EnvBound (k + 1) μ →
      EnvBound (k + 2) (envStep k (genMuD k) (genMu0 k) (genMuK k) μ) := by
    intro k hk μ hlow
    exact envBound_step (stdHyp_of_profiles Kc pc hK hp hconst hk) (by omega)
      (uniformCovers_of_classes Kc pc hK1 hp hlem k) (hrec k (by omega)) hlow
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact hstep 2 le_rfl 62 envBound_three
  | succ k hk ih =>
    rw [genMu_succ (by omega)]
    exact hstep (k + 1) (by omega) (genMu k) ih

/-! ### The lengths -/

/-- The envelopes at `L = 6, …, 10` fit the printed threshold. -/
theorem genMu_fits :
    (42 ≤ genMu 2 ∧ genMu 2 + 2 * 6 + 14 ≤ 2 ^ (6 + 9)) ∧
    (42 ≤ genMu 3 ∧ genMu 3 + 2 * 7 + 14 ≤ 2 ^ (7 + 9)) ∧
    (42 ≤ genMu 4 ∧ genMu 4 + 2 * 8 + 14 ≤ 2 ^ (8 + 9)) ∧
    (42 ≤ genMu 5 ∧ genMu 5 + 2 * 9 + 14 ≤ 2 ^ (9 + 9)) ∧
    (42 ≤ genMu 6 ∧ genMu 6 + 2 * 10 + 14 ≤ 2 ^ (10 + 9)) := by
  decide

/-- **Theorem 18.2 at every length `6 ≤ L ≤ 10`**, from the recurrence profiles. -/
theorem theorem_18_2_upto_ten_of_profiles (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {L : Nat} (hL6 : 6 ≤ L) (hL10 : L ≤ 10) : Theorem182At L := by
  have henv := envBound_all Kc pc hK hp hrec hconst (L - 4) (by omega)
  rw [show L - 4 + 2 = L - 2 by omega] at henv
  have hfit := genMu_fits
  have h42 : ∀ μ : Nat, 42 ≤ μ → 4 * L + 20 ≤ 2 ^ μ := by
    intro μ hμ
    calc 4 * L + 20 ≤ 2 ^ 42 := by omega
      _ ≤ 2 ^ μ := Nat.pow_le_pow_right (by norm_num) hμ
  interval_cases L
  · exact theorem182At_of_envBound (by norm_num) henv hfit.1.1 (h42 _ hfit.1.1) hfit.1.2
  · exact theorem182At_of_envBound (by norm_num) henv hfit.2.1.1 (h42 _ hfit.2.1.1) hfit.2.1.2
  · exact theorem182At_of_envBound (by norm_num) henv hfit.2.2.1.1 (h42 _ hfit.2.2.1.1)
      hfit.2.2.1.2
  · exact theorem182At_of_envBound (by norm_num) henv hfit.2.2.2.1.1 (h42 _ hfit.2.2.2.1.1)
      hfit.2.2.2.1.2
  · exact theorem182At_of_envBound (by norm_num) henv hfit.2.2.2.2.1 (h42 _ hfit.2.2.2.2.1)
      hfit.2.2.2.2.2

/-- **Corollary 18.7 at every length `6 ≤ L ≤ 10`**, from the recurrence profiles. -/
theorem corollary_18_7_upto_ten_of_profiles (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {L : Nat} (hL6 : 6 ≤ L) (hL10 : L ≤ 10) : Corollary187At L :=
  (theorem_18_2_upto_ten_of_profiles Kc pc hK hp hrec hconst hL6 hL10).corollary_18_7

end LeanProofs.GowersSzemeredi
