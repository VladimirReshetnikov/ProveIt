import GowersSzemeredi.Proofs07ModularBudgetSpan
import GowersSzemeredi.Proofs07AllScalesStepSpan

/-! The affine partition's numerical reserve absorbs localization to a parent
of at least one third the reference length, without reducing the target. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The ceiling of the original power target remains within the direct
partition budget after a factor-three loss in the parent length. -/
theorem cor711_short_parent_ceiling_budget {L S : Nat} {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1)
    (hparent : S ≤ 3 * L)
    (hlarge : 8 ≤ (S : Real) ^ cor711Exponent alpha 1) :
    34 * (Nat.ceil ((S : Real) ^ cor711Exponent alpha 1) : Real) ^ 2 ≤
      (L : Real) ^ ((23 / 6) * cor711Exponent alpha 1) := by
  let e := cor711Exponent alpha 1
  let X : Real := (S : Real) ^ e
  have he := cor711_single_exponent_bounds hα hαone
  have hX : 0 < X := by dsimp only [X, e]; linarith only [hlarge]
  have hm : (Nat.ceil X : Real) ≤ (9 / 8) * X := by
    have hceil := Nat.ceil_lt_add_one hX.le
    dsimp only [X, e] at hceil ⊢
    linarith
  have hpower : (45 : Real) ≤ (8 : Real) ^ (11 / 6 : Real) := by
    apply (Real.rpow_le_rpow_iff (by norm_num)
      (Real.rpow_nonneg (by norm_num) _) (by norm_num : (0 : Real) < 6)).mp
    rw [← Real.rpow_mul (by norm_num)]
    norm_num
  have hXpower : 45 ≤ X ^ (11 / 6 : Real) := hpower.trans
    (Real.rpow_le_rpow (by norm_num) hlarge (by norm_num))
  have hthree : (3 : Real) ^ ((23 / 6) * e) ≤ 33 / 32 := by
    calc
      _ ≤ (3 : Real) ^ (1 / 64 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by dsimp [e]; linarith [he.2])
      _ ≤ 33 / 32 := by
        apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg (by norm_num) _)
          (by norm_num) (by norm_num : (0 : Real) < 64)).mp
        rw [← Real.rpow_mul (by norm_num)]
        norm_num
  have hloss : (S : Real) ^ ((23 / 6) * e) ≤
      (33 / 32) * (L : Real) ^ ((23 / 6) * e) := by
    calc
      _ ≤ (3 * (L : Real)) ^ ((23 / 6) * e) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hparent) (mul_nonneg (by norm_num) he.1.le)
      _ = (3 : Real) ^ ((23 / 6) * e) * (L : Real) ^ ((23 / 6) * e) :=
        Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right hthree (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hbudget : 34 * (Nat.ceil X : Real) ^ 2 * (33 / 32) ≤
      (S : Real) ^ ((23 / 6) * e) := by
    calc
      _ ≤ 34 * ((9 / 8) * X) ^ 2 * (33 / 32) := by
        gcongr
      _ ≤ 45 * X ^ 2 := by nlinarith only [sq_nonneg X]
      _ ≤ X ^ (11 / 6 : Real) * X ^ 2 :=
        mul_le_mul_of_nonneg_right hXpower (sq_nonneg _)
      _ = X ^ (23 / 6 : Real) := by
        rw [← Real.rpow_two, ← Real.rpow_add hX]
        norm_num
      _ = (S : Real) ^ ((23 / 6) * e) := by
        dsimp only [X]
        rw [← Real.rpow_mul (Nat.cast_nonneg _)]
        congr 1
        ring
  change 34 * (Nat.ceil X : Real) ^ 2 ≤ (L : Real) ^ ((23 / 6) * e)
  nlinarith only [hbudget, hloss]

/-- A shorter parent retains the reference progression's full affine length
target. The parent needs only four points and at least one third of the
reference length; the integer step and span are preserved at every scale. -/
theorem corollary_7_11_short_parent_with_step_span (N : Nat) [Fact N.Prime]
    (R : ModAP N) (A : Finset (ZMod N)) (alpha : Real) (S : Nat)
    (hR : R.IsProper) (hstep : R.step != 0) (hl : 4 ≤ R.length)
    (hα : 0 < alpha) (hαone : alpha ≤ 1) (hparent : S ≤ 3 * R.length)
    (hA : A ⊆ R.carrier) (hdensity : alpha * R.length ≤ A.card) :
    ∃ M : Nat, ∃ Q : Fin M → ModAP N,
      IsPartition (fun j ↦ (Q j).carrier) R.carrier ∧
      (∀ j, (Q j).step != 0 ∧ (Q j).IsProper ∧
        (S : Real) ^ cor711Exponent alpha 1 ≤ (Q j).length ∧
        ∀ phi : ZMod N → ZMod N, FreimanHom 8 A phi →
          LinearOn ((Q j).carrier.filter fun x ↦ x ∈ A) phi) ∧
      ∃ d : Nat, 0 < d ∧ ∀ j,
        (Q j).step = (d : ZMod N) * R.step ∧ d * ((Q j).length - 1) < R.length := by
  have he := cor711_single_exponent_bounds hα hαone
  by_cases hlarge : 8 ≤ (S : Real) ^ cor711Exponent alpha 1
  · have hm : 2 ≤ Nat.ceil ((S : Real) ^ cor711Exponent alpha 1) := by
      have h := Nat.le_ceil ((S : Real) ^ cor711Exponent alpha 1)
      have htwo : (2 : Real) ≤ Nat.ceil ((S : Real) ^ cor711Exponent alpha 1) := by linarith
      exact_mod_cast htwo
    obtain ⟨M, Q, hpart, hcell, hspan⟩ := corollary_7_11_modular_budget_with_step_span
      N R A alpha _ hm hR (by omega) hα hA hdensity
      (cor711_short_parent_ceiling_budget hα hαone hparent hlarge)
    refine ⟨M, Q, hpart, fun j ↦ ⟨(hcell j).1, (hcell j).2.1, ?_, (hcell j).2.2.2.2⟩, hspan⟩
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr (hcell j).2.2.1)
  by_cases hlen : 64 ≤ R.length
  · exact short_universal_modular_partition_with_step_span R A 8 hR hstep
      (by norm_num) (by norm_num) hlen (le_of_not_ge hlarge)
  have hsmall : (S : Real) ^ cor711Exponent alpha 1 ≤ 2 := by
    calc
      _ ≤ (256 : Real) ^ cor711Exponent alpha 1 :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (show S ≤ 256 by omega)) he.1.le
      _ = (2 : Real) ^ (8 * cor711Exponent alpha 1) := by
        rw [Real.rpow_mul (by norm_num)]
        norm_num
      _ ≤ (2 : Real) ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [he.2])
      _ = 2 := Real.rpow_one _
  exact short_universal_modular_partition_with_step_span R A 2 hR hstep
    (by norm_num) (by norm_num) hl hsmall

end LeanProofs.GowersSzemeredi
