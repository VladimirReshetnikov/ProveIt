import ExponentialIdentities.TwoBaseIntegerExponent.RadicalDegree
import ExponentialIdentities.TwoBaseIntegerExponent.RadicalReformulation
import Mathlib.RingTheory.Trace.Basic

/-!
# Field invariants and the swapped-radical rank obstruction

This module records what norms and conjugates genuinely add to the canonical
localized-radical reduction.  The exact pure-radical minpoly gives the field norm
and trace of its generator.  The simultaneous base-swapped normalization also
produces a third algebraic input/output pair for six exponentials, but its new
base satisfies an explicit monomial relation with the first two.

These results diagnose why field norms and the generic algebraic six-exponentials
theorem do not by themselves settle the remaining Alaoglu--Erdős obstruction.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set Polynomial IntermediateField

noncomputable section

/-- The relation supplied by the base-swapped radical normalization is already
a collision among the three prospective six-exponentials bases.  Thus those
bases can never satisfy the monomial-injectivity hypothesis. -/
theorem swappedRadical_relation_blocks_monomial_injectivity
    {w F : ℝ} {a b d e : ℕ} (he : 0 < e)
    (hrel : (2 : ℝ) ^ b * F ^ e = (2 : ℝ) ^ a * w ^ d) :
    ¬ Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦
        (2 : ℝ) ^ u.1 * w ^ u.2.1 * F ^ u.2.2) := by
  intro hinj
  have hcollision := hinj
    (a₁ := ((b, 0, e) : ℕ × ℕ × ℕ))
    (a₂ := ((a, d, 0) : ℕ × ℕ × ℕ)) (by simpa using hrel)
  have he0 : e = 0 := congrArg (fun u : ℕ × ℕ × ℕ ↦ u.2.2) hcollision
  omega

/-- The simultaneous primitive output normalization supplies exactly the
collision used above.  Thus adjoining the base-swapped radical produces six
algebraic exponentials, but never the required third independent base. -/
theorem simultaneousNormalization_blocks_swapped_monomial_injectivity
    {β : ℝ} {a b w v d e : ℕ} (hv : 0 < v) (he : 0 < e)
    (hM : ((2 ^ a * w ^ d : ℕ) : ℝ) = (2 : ℝ) ^ β)
    (hB : ((3 ^ b * v ^ e : ℕ) : ℝ) = (3 : ℝ) ^ β) :
    ¬ Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦
        (2 : ℝ) ^ u.1 * (w : ℝ) ^ u.2.1 *
          ((v : ℝ) ^ logTwoDivLogThree) ^ u.2.2) := by
  have hlog3 : Real.log (3 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 3))
  have hthreeSwap : (3 : ℝ) ^ logTwoDivLogThree = 2 := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
      logTwoDivLogThree]
    have hmul : Real.log (3 : ℝ) *
        (Real.log (2 : ℝ) / Real.log (3 : ℝ)) = Real.log (2 : ℝ) := by
      field_simp
    rw [hmul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have htransport :
      ((3 : ℝ) ^ β) ^ logTwoDivLogThree = (2 : ℝ) ^ β := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      logTwoDivLogThree]
    congr 1
    field_simp
  have hsplit :
      (((3 ^ b * v ^ e : ℕ) : ℝ) ^ logTwoDivLogThree) =
        (2 : ℝ) ^ b * ((v : ℝ) ^ logTwoDivLogThree) ^ e := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
      Real.mul_rpow (by positivity) (by positivity)]
    norm_num only [Nat.cast_ofNat]
    rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3)
        logTwoDivLogThree b,
      ← Real.rpow_pow_comm (by exact_mod_cast hv.le)
        logTwoDivLogThree e,
      hthreeSwap]
  have hrel :
      (2 : ℝ) ^ b * ((v : ℝ) ^ logTwoDivLogThree) ^ e =
        (2 : ℝ) ^ a * (w : ℝ) ^ d := by
    calc
      (2 : ℝ) ^ b * ((v : ℝ) ^ logTwoDivLogThree) ^ e =
          (((3 ^ b * v ^ e : ℕ) : ℝ) ^ logTwoDivLogThree) := hsplit.symm
      _ = ((3 : ℝ) ^ β) ^ logTwoDivLogThree := by rw [hB]
      _ = (2 : ℝ) ^ β := htransport
      _ = ((2 ^ a * w ^ d : ℕ) : ℝ) := hM.symm
      _ = (2 : ℝ) ^ a * (w : ℝ) ^ d := by
        norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  exact swappedRadical_relation_blocks_monomial_injectivity he hrel

/-- The field norm of the generator of an exact positive radical field. -/
theorem exactRadical_adjoin_norm_gen
    {E : ℝ} {d : ℕ} (hd : 0 < d) {q : ℚ}
    (hq : E ^ d = (q : ℝ))
    (hmin : minpoly ℚ E = X ^ d - C q) :
    @Algebra.norm ℚ ℚ⟮E⟯ _ _ (IntermediateField.algebra' ℚ⟮E⟯)
        (AdjoinSimple.gen ℚ E) = (-1 : ℚ) ^ d * (-q) := by
  have hpMonic : (X ^ d - C q : ℚ[X]).Monic :=
    monic_X_pow_sub_C q hd.ne'
  have hpEval : Polynomial.aeval E (X ^ d - C q : ℚ[X]) = 0 := by
    simp [hq]
  have hEint : IsIntegral ℚ E := ⟨X ^ d - C q, hpMonic, hpEval⟩
  rw [← adjoin.powerBasis_gen hEint]
  rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
  rw [adjoin.powerBasis_dim]
  rw [adjoin.powerBasis_gen]
  rw [minpoly_gen, hmin]
  simp [Ne.symm hd.ne']

/-- In degree at least two, the field trace of the generator of an exact radical
field vanishes. -/
theorem exactRadical_adjoin_trace_gen_eq_zero
    {E : ℝ} {d : ℕ} (hd : 1 < d) {q : ℚ}
    (hq : E ^ d = (q : ℝ))
    (hmin : minpoly ℚ E = X ^ d - C q) :
    @Algebra.trace ℚ ℚ⟮E⟯ _ _ (IntermediateField.algebra' ℚ⟮E⟯)
        (AdjoinSimple.gen ℚ E) = 0 := by
  have hd0 : 0 < d := by omega
  have hpMonic : (X ^ d - C q : ℚ[X]).Monic :=
    monic_X_pow_sub_C q hd0.ne'
  have hpEval : Polynomial.aeval E (X ^ d - C q : ℚ[X]) = 0 := by
    simp [hq]
  have hEint : IsIntegral ℚ E := ⟨X ^ d - C q, hpMonic, hpEval⟩
  rw [trace_adjoinSimpleGen hEint, hmin]
  rw [Polynomial.nextCoeff, coeff_sub, coeff_X_pow, coeff_C]
  simp [show d - 1 ≠ d by omega, show d - 1 ≠ 0 by omega]

/-- Specialized conjugate product/sum restriction for the normalized odd-core
radical.  Its generator has the displayed exact norm, and in nontrivial degree
its trace is zero. -/
theorem oddCoreRpow_exact_field_norm_and_trace
    {w d a c : ℕ} (hw : 0 < w) (hd : 0 < d)
    (hleast : ∀ j : ℤ, oddCoreRpow w ^ j ∈ Set.range ((↑) : ℚ → ℝ) →
      0 < j → (d : ℤ) ≤ j)
    (hnorm : oddCoreRpow w ^ d = (c : ℝ) / (3 : ℝ) ^ a) :
    @Algebra.norm ℚ ℚ⟮oddCoreRpow w⟯ _ _
        (IntermediateField.algebra' ℚ⟮oddCoreRpow w⟯)
        (AdjoinSimple.gen ℚ (oddCoreRpow w)) =
          (-1 : ℚ) ^ d * (-((c : ℚ) / (3 : ℚ) ^ a)) ∧
      (1 < d →
        @Algebra.trace ℚ ℚ⟮oddCoreRpow w⟯ _ _
            (IntermediateField.algebra' ℚ⟮oddCoreRpow w⟯)
            (AdjoinSimple.gen ℚ (oddCoreRpow w)) = 0) := by
  obtain ⟨_hirr, hmin, _hdeg⟩ :=
    oddCoreRpow_exact_radical_degree hw hd hleast hnorm
  have hq : oddCoreRpow w ^ d =
      (((c : ℚ) / (3 : ℚ) ^ a : ℚ) : ℝ) := by
    rw [hnorm]
    push_cast
    rfl
  refine ⟨exactRadical_adjoin_norm_gen hd hq hmin, ?_⟩
  intro hdTwo
  exact exactRadical_adjoin_trace_gen_eq_zero hdTwo hq hmin

end

end LeanProofs.TwoBaseIntegerExponent
