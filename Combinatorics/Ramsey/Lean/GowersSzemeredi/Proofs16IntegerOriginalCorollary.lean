import GowersSzemeredi.Proofs16IntegerPolynomialCorollary
import GowersSzemeredi.Proofs16IntegerCorollaryBounds

/-! The original common exponent of Corollary 16.11, with ascending
integer boxes. In fact the innermost shift improves from k+9 to k+8,
and the conclusion holds over every prime without an extra size threshold. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Corollary 16.11 strengthened from shift `k+9` to `k+8`, with genuine
ascending integer boxes and no additional lower bound on the prime. -/
theorem corollary_16_11_integer_shift_eight (k : Nat) (hk : 1 ≤ k)
    (alpha : Real) (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2)
    (N : Nat) [NeZero N] [Fact N.Prime]
    (f : ZMod N → Complex) (hf : DiscValued f) (hnot : ¬ UniformOfDegree f alpha (k + 1)) :
    ∃ P : Box N k, ∃ mu : Point N k → ZMod N,
      P.IsAscendingInteger ∧ IsMultilinear mu ∧
      (N : Real) ^ ((alpha / 2) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 8)))) ≤ P.width ∧
      (alpha / 2) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 8))) * P.carrier.card ≤
        section16LargeMultilinearFrequencyCount f P mu alpha := by
  let Kc (k : Nat) := Nat.ceil (multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
  let pc (k : Nat) := (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1))
  have hK : ∀ k, 1 ≤ Kc k := fun k =>
    le_trans (by norm_num) (two_le_ceil_multiaffinePartitionK _ _)
  have hp : ∀ k, 0 < pc k := fun k =>
    Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _)
  have hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))) := by
    intro k _
    exact abstractFamilyLemma166At_of k (two_le_ceil_multiaffinePartitionK _ _) (hp k)
      (section16RecurrenceProfileWith_explicit k)
  have hIntegerLemma : ∀ k, 1 ≤ k → IntegerAbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))) :=
    fun k _ => integerAbstractFamilyLemma166At_explicit k
  have hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))) :=
    fun k => explicit_family_constants_le k
  have hcov := integerPolyCoverAt_class68 Kc pc hK hp hlem hIntegerLemma hk
  obtain ⟨P, mu, hP, hmu, hwidth, hmass⟩ :=
    corollary_16_11_integer_of_polyCover hk _ _ hcov alpha ha haHalf N f hf hnot
  have hV := one_le_classV Kc pc k
  have hVb : classV Kc pc k ≤ (2 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6))) := by
    have h := classV_bound_all Kc pc hconst k
    have he : (2 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6)) - 1) ≤
        (2 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6))) :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    linarith
  obtain ⟨hd, hw⟩ := corollary_16_11_polynomial_bounds hV ha haHalf k hVb
  have hN : (1 : Real) ≤ N := by exact_mod_cast NeZero.pos N
  exact ⟨P, mu, hP, hmu,
    (Real.rpow_le_rpow_of_exponent_le hN hw).trans hwidth,
    (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg _)).trans hmass⟩

/-- The paper's exact common exponent, now combined with ordinary integer geometry. -/
theorem corollary_16_11_printed_integer (k : Nat) (hk : 1 ≤ k)
    (alpha : Real) (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2)
    (N : Nat) [NeZero N] [Fact N.Prime]
    (f : ZMod N → Complex) (hf : DiscValued f) (hnot : ¬ UniformOfDegree f alpha (k + 1)) :
    ∃ P : Box N k, ∃ mu : Point N k → ZMod N,
      P.IsAscendingInteger ∧ IsMultilinear mu ∧
      (N : Real) ^ ((alpha / 2) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 9)))) ≤ P.width ∧
      (alpha / 2) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 9))) * P.carrier.card ≤
        section16LargeMultilinearFrequencyCount f P mu alpha := by
  obtain ⟨P, mu, hP, hmu, hwidth, hmass⟩ :=
    corollary_16_11_integer_shift_eight k hk alpha ha haHalf N f hf hnot
  have he : (alpha / 2) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 9))) ≤
      (alpha / 2) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 8))) := by
    apply pow_le_pow_of_le_one (by positivity) (by linarith)
    exact Nat.pow_le_pow_right (by norm_num)
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hN : (1 : Real) ≤ N := by exact_mod_cast NeZero.pos N
  exact ⟨P, mu, hP, hmu, (Real.rpow_le_rpow_of_exponent_le hN he).trans hwidth,
    (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _)).trans hmass⟩

end LeanProofs.GowersSzemeredi
