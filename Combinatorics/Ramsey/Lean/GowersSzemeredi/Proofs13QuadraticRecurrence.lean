import GowersSzemeredi.Proofs13InitialProgression
import GowersSzemeredi.Section05
import GowersSzemeredi.Proofs05Downstream

/-!
# Quadratic-recurrence infrastructure for Gowers's Lemma 13.5

This module isolates the parts of Lemma 13.5 which do not depend on the
simultaneous polynomial-partition theorem.  In particular, it provides the
transport from progressions of natural indices to a modular progression and
the weighted selection argument used after a family of suitable candidate
progressions has been constructed.

The printed proof has two currently unresolved interface gaps: its small-case
cutoff does not imply the threshold of the repaired Lemma 5.9 for every
positive `q`, and its endpoint deletion is not justified by the hypotheses of
the live statement.  Consequently this file deliberately does not assert a
theorem `lemma_5_9 -> lemma_13_5`.
-/

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

/-! ### The quadratic identity behind the recurrence step -/

/-- The quadratic phase from the printed proof, expressed on the ambient
modular progression. -/
def stage135Quadratic {N : Nat} (P : ModAP N) (a b : ZMod N)
    (t : ZMod N) : ZMod N :=
  a * (4 : ZMod N)⁻¹ * (P.start + t * P.step) ^ 2 +
    b * (2 : ZMod N)⁻¹ * (P.start + t * P.step)

/-- The modular parametrization of `P`, used when the parameter is already in
`ZMod N`. -/
def stage135ModPoint {N : Nat} (P : ModAP N) (t : ZMod N) : ZMod N :=
  P.start + t * P.step

theorem stage135Quadratic_polynomial {N : Nat} [NeZero N]
    (P : ModAP N) (a b : ZMod N) :
    PolynomialOn 2 Finset.univ (stage135Quadratic P a b) := by
  refine ⟨![a * (4 : ZMod N)⁻¹ * P.start ^ 2 +
        b * (2 : ZMod N)⁻¹ * P.start,
      2 * (a * (4 : ZMod N)⁻¹) * P.start * P.step +
        b * (2 : ZMod N)⁻¹ * P.step,
      a * (4 : ZMod N)⁻¹ * P.step ^ 2], ?_⟩
  intro t _
  simp [stage135Quadratic, Fin.sum_univ_succ]
  ring

/-- For an odd prime modulus, the symmetric difference of the quadratic
phase is the desired affine value times the progression step. -/
theorem stage135Quadratic_symmetric_difference {N : Nat} [NeZero N]
    (hprime : Nat.Prime N) (hNtwo : N != 2) (P : ModAP N)
    (a b : ZMod N) (t u : ZMod N) :
    stage135Quadratic P a b (t + u) -
        stage135Quadratic P a b (t - u) =
      (a * stage135ModPoint P t + b) * (u * P.step) := by
  letI : Fact N.Prime := ⟨hprime⟩
  have hNtwo' : N ≠ 2 := bne_iff_ne.mp hNtwo
  have htwo : (2 : ZMod N) ≠ 0 := by
    intro hz
    have hdvd : N ∣ 2 := (ZMod.natCast_eq_zero_iff 2 N).mp hz
    have hNle : N ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have htwole : 2 ≤ N := hprime.two_le
    exact hNtwo' (Nat.le_antisymm hNle htwole)
  have hfour : (4 : ZMod N) ≠ 0 := by
    rw [show (4 : ZMod N) = 2 * 2 by norm_num]
    exact mul_ne_zero htwo htwo
  unfold stage135Quadratic stage135ModPoint
  field_simp [htwo, hfour]
  ring

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

/-! ### Weighted selection from certified candidate progressions -/

/-- A family of candidate progressions carrying all geometric conclusions of
Lemma 13.5 together with the precise weighted-average inequality needed for
the final selection.  This is the clean interface that a repaired recurrence
argument must produce. -/
structure Stage135CandidateFamily {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) where
  count : Nat
  Q : Fin count → ModAP N
  count_pos : 0 < count
  step_ne_zero : ∀ j, (Q j).step != 0
  proper : ∀ j, (Q j).IsProper
  subset : ∀ j, (Q j).carrier ⊆ D.P.carrier
  length_lower : ∀ j,
    (D.P.length : Real) ^
        ((1 : Real) / (2 : Real) ^ (12 * D.q)) / 2 ≤ (Q j).length
  small_affine : ∀ j i h, h ∈ (Q j).carrier →
    (centeredAbs ((D.a i * h + D.b i) * (Q j).step) : Real) ≤
      (D.P.length : Real) ^
        (-((1 : Real) / (2 : Real) ^ (11 * D.q))) * N
  weighted_average :
    ∑ j, S.alpha ^ 32 * (N : Real) ^ 31 * (Q j).length / 8 ≤
      ∑ j, (goodHeightWeight S ((Q j).carrier ∩ D.H) : Real)

alias stage135_additive_ext := lemma134_additive_ext

alias stage135_sectionC_upper := lemma134_sectionC_upper

/-- Weighted height mass supplies the stronger pre-trimming density 1/16. -/
theorem stage135_critical_count_of_weight {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (Q : ModAP N)
    (hQproper : Q.IsProper)
    (hweight : S.alpha ^ 32 * (N : Real) ^ 31 * Q.length / 8 ≤
      (goodHeightWeight S (Q.carrier ∩ D.H) : Real)) :
    S.alpha ^ 32 * Q.length / 16 ≤
      (criticalHeights S D ⟨Q⟩).card := by
  classical
  change S.alpha ^ 32 * Q.length / 16 ≤
    (((Q.carrier ∩ D.H).filter (IsStrongHeight S)).card : Real)
  let G := (Q.carrier ∩ D.H).filter (IsGoodHeight S)
  let K := G.filter fun h =>
    S.alpha ^ 32 * (N : Real) ^ 31 / 16 ≤ section13C S h
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hNpow : (0 : Real) < (N : Real) ^ 31 := pow_pos hNpos 31
  have hthresholdNonneg :
      0 ≤ S.alpha ^ 32 * (N : Real) ^ 31 / 16 := by positivity
  have hsumUpper : (goodHeightWeight S (Q.carrier ∩ D.H) : Real) ≤
      (K.card : Real) * (N : Real) ^ 31 +
        S.alpha ^ 32 * (N : Real) ^ 31 / 16 * Q.length := by
    unfold goodHeightWeight
    change ((G.sum (section13C S) : Nat) : Real) ≤ _
    rw [Nat.cast_sum]
    calc
      ∑ h ∈ G, (section13C S h : Real) ≤
          ∑ h ∈ G, if h ∈ K then (N : Real) ^ 31
            else S.alpha ^ 32 * (N : Real) ^ 31 / 16 := by
        apply Finset.sum_le_sum
        intro h hh
        by_cases hk : h ∈ K
        · rw [if_pos hk]
          have hc : ((section13C S h : Nat) : Real) ≤
              ((N ^ 31 : Nat) : Real) := by
            exact_mod_cast stage135_sectionC_upper S h
          simpa only [Nat.cast_pow] using hc
        · rw [if_neg hk]
          have hnot : ¬ S.alpha ^ 32 * (N : Real) ^ 31 / 16 ≤
              section13C S h := by
            intro hs
            exact hk (Finset.mem_filter.mpr ⟨hh, hs⟩)
          exact le_of_lt (lt_of_not_ge hnot)
      _ ≤ (K.card : Real) * (N : Real) ^ 31 +
          (G.card : Real) *
            (S.alpha ^ 32 * (N : Real) ^ 31 / 16) := by
        calc
          (∑ h ∈ G, if h ∈ K then (N : Real) ^ 31
              else S.alpha ^ 32 * (N : Real) ^ 31 / 16) ≤
              (∑ h ∈ G, if h ∈ K then (N : Real) ^ 31 else 0) +
                ∑ _h ∈ G, S.alpha ^ 32 * (N : Real) ^ 31 / 16 := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_le_sum
            intro h _
            by_cases hk : h ∈ K <;> simp [hk, hthresholdNonneg]
          _ = _ := by
            have hKG : K ⊆ G := Finset.filter_subset _ _
            rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hKG]
            simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (K.card : Real) * (N : Real) ^ 31 +
          S.alpha ^ 32 * (N : Real) ^ 31 / 16 * Q.length := by
        have hGQ : G.card ≤ Q.length := by
          calc
            G.card ≤ (Q.carrier ∩ D.H).card := Finset.card_filter_le _ _
            _ ≤ Q.carrier.card := Finset.card_le_card (Finset.inter_subset_left)
            _ = Q.length := hQproper
        have hGQreal : (G.card : Real) ≤ Q.length := by exact_mod_cast hGQ
        calc
          (K.card : Real) * (N : Real) ^ 31 +
              (G.card : Real) *
                (S.alpha ^ 32 * (N : Real) ^ 31 / 16) ≤
              (K.card : Real) * (N : Real) ^ 31 +
                Q.length *
                  (S.alpha ^ 32 * (N : Real) ^ 31 / 16) := by
            gcongr
          _ = _ := by ring
  have hKlower : S.alpha ^ 32 * Q.length / 16 ≤ (K.card : Real) := by
    have hmul :
        (S.alpha ^ 32 * Q.length / 16) * (N : Real) ^ 31 ≤
          (K.card : Real) * (N : Real) ^ 31 := by
      nlinarith
    exact le_of_mul_le_mul_right hmul hNpow
  have hKcritical : K =
      (Q.carrier ∩ D.H).filter (IsStrongHeight S) := by
    ext h
    simp only [K, G, Finset.mem_filter, IsStrongHeight]
    tauto
  rw [← hKcritical]
  exact hKlower

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
