import GowersSzemeredi.Proofs13QuadraticRecurrence

/-! Declarations of `Proofs13QuadraticRecurrence` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ### Audited numerical gap in the printed case split -/

set_option exponentiation.threshold 400 in
/-- At `q = 1`, the cutoff used for the "small" case in the printed proof is
strictly below the threshold required by the repaired Lemma 5.9. -/
theorem lemma135_small_cutoff_lt_lemma59_threshold :
    2 ^ (2 ^ 12) < simultaneousPolynomialThreshold 2 1 := by
  have hsmallExponent : 12 < 40 * 2 ^ 3 := by norm_num
  have hinner : 2 ^ 12 < 2 ^ (40 * 2 ^ 3) :=
    Nat.pow_lt_pow_right (by norm_num) hsmallExponent
  have hsmallW : 2 ^ (2 ^ 12) < weylThreshold 2 := by
    unfold weylThreshold
    exact Nat.pow_lt_pow_right (by norm_num) hinner
  exact hsmallW.trans_le <|
    (weylThreshold_le_polynomialPartitionThreshold 2).trans
      (polynomialPartitionThreshold_le_simultaneousPolynomialThreshold 2 1)

/-! ### Transporting a progression of indices -/

theorem stage135Transport_step_ne_zero {N : Nat} [NeZero N]
    (P : ModAP N) (R : NatAP) (hP : P.IsProper)
    (hR : R.IsProper) (hRtwo : 2 ≤ R.length)
    (hsub : R.carrier ⊆ Finset.range P.length) :
    (section5Transport P R).step != 0 := by
  apply bne_iff_ne.mpr
  intro hzero
  have hproper := section5Transport_isProper P R hP hR hsub
  have hcard : (section5Transport P R).carrier.card = R.length := by
    simpa only [ModAP.IsProper, section5Transport_length] using hproper
  have hcollapse : (section5Transport P R).carrier.card ≤ 1 := by
    rw [ModAP.carrier]
    apply Finset.card_le_one_iff.mpr
    intro x y hx hy
    rw [Finset.mem_image] at hx hy
    obtain ⟨i, _, rfl⟩ := hx
    obtain ⟨j, _, rfl⟩ := hy
    simp [hzero]
  omega

/-- The quadratic identity used in the paper is genuinely unavailable at an
even composite modulus: division by two and four collapses in `ZMod 4`. -/
theorem stage135Quadratic_identity_mod_four_counterexample :
    stage135Quadratic
        ({ start := 0, step := 1, length := 4 } : ModAP 4) 1 0 (1 + 1) -
      stage135Quadratic
        ({ start := 0, step := 1, length := 4 } : ModAP 4) 1 0 (1 - 1) ≠
      ((1 : ZMod 4) *
          stage135ModPoint
            ({ start := 0, step := 1, length := 4 } : ModAP 4) 1 + 0) *
        ((1 : ZMod 4) * 1) := by
  norm_num [stage135Quadratic, stage135ModPoint]
  have h4 : (4 : ZMod 4) = 0 := ZMod.natCast_self 4
  rw [h4]
  intro h
  have hone : (1 : ZMod 4) = 0 := h.symm
  have hmod : (4 : Nat) = 1 := ZMod.one_eq_zero_iff.mp hone
  omega

/-- The weighted-selection part of Lemma 13.5.  Any recurrence argument which
produces `Stage135CandidateFamily` immediately yields the exact live output. -/
theorem lemma_13_5_of_candidate_family {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N)
    (F : Stage135CandidateFamily S D) :
    ∃ E : Stage135Data N, IsStage135Data S D E := by
  have hnonempty : (Finset.univ : Finset (Fin F.count)).Nonempty := by
    let j : Fin F.count := ⟨0, F.count_pos⟩
    exact ⟨j, Finset.mem_univ j⟩
  obtain ⟨j, _, hj⟩ := Finset.exists_le_of_sum_le hnonempty F.weighted_average
  let E : Stage135Data N := ⟨F.Q j⟩
  refine ⟨E, F.step_ne_zero j, F.proper j, F.subset j,
    F.length_lower j, F.small_affine j, ?_⟩
  have hcount := stage135_critical_count_of_weight S D (F.Q j) (F.proper j) hj
  have hnonneg : 0 ≤ S.alpha ^ 32 * ((F.Q j).length : Real) :=
    mul_nonneg (pow_nonneg S.alpha_pos.le _) (Nat.cast_nonneg _)
  change S.alpha ^ 32 * ((F.Q j).length : Real) / 20 ≤ _
  linarith only [hcount, hnonneg]

/-- A recurrence construction producing the certified family for every live
input immediately discharges the exact proposition `lemma_13_5`. -/
theorem lemma_13_5_holds_of_candidate_families
    (hcert : ∀ (N : Nat) [NeZero N] (S : Section13Context N)
        (theta : Real) (D : Stage134Data N),
      IsStage134Data S theta D → Nonempty (Stage135CandidateFamily S D)) :
    lemma_13_5 := by
  intro N _ S theta D _hprime hD
  obtain ⟨F⟩ := hcert N S theta D hD
  exact lemma_13_5_of_candidate_family S D F

end LeanProofs.GowersSzemeredi
