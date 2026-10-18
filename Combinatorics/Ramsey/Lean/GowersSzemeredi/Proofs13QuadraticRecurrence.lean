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

`lemma135_small_cutoff_lt_lemma59_threshold`,
`lemma_13_5_holds_of_candidate_families`, `lemma_13_5_of_candidate_family`,
`stage135Quadratic_identity_mod_four_counterexample` and
`stage135Transport_step_ne_zero` are in `Proofs13QuadraticRecurrenceSide`,
outside the final route. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

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
  let G := (Q.carrier ∩ D.H).filter (IsGoodHeight S)
  let p := fun h => S.alpha ^ 32 * (N : Real) ^ 31 / 16 ≤ section13C S h
  have hK : criticalHeights S D ⟨Q⟩ = G.filter p := by
    ext h
    simp only [criticalHeights, G, p, Finset.mem_filter, IsStrongHeight]
    tauto
  have hw : (goodHeightWeight S (Q.carrier ∩ D.H) : Real) =
      ∑ h ∈ G.filter p, (section13C S h : Real) +
        ∑ h ∈ G.filter (¬p ·), (section13C S h : Real) := by
    rw [Finset.sum_filter_add_sum_filter_not]
    exact Nat.cast_sum _ _
  have h1 := Finset.sum_le_card_nsmul (G.filter p) (fun h => (section13C S h : Real))
    ((N : Real) ^ 31) fun h _ => by exact_mod_cast stage135_sectionC_upper S h
  have h2 := Finset.sum_le_card_nsmul (G.filter (¬p ·)) (fun h => (section13C S h : Real))
    (S.alpha ^ 32 * (N : Real) ^ 31 / 16) fun h hh => (not_le.mp (Finset.mem_filter.mp hh).2).le
  have hG : ((G.filter (¬p ·)).card : Real) ≤ Q.length := by
    exact_mod_cast ((Finset.card_filter_le _ _).trans (Finset.card_filter_le _ _)).trans
      ((Finset.card_le_card Finset.inter_subset_left).trans (le_of_eq hQproper))
  rw [nsmul_eq_mul] at h1 h2
  rw [hK]
  refine le_of_mul_le_mul_right ?_ (pow_pos (Nat.cast_pos.mpr (NeZero.pos N)) 31)
  linarith [mul_le_mul_of_nonneg_right hG
    (by positivity : (0 : Real) ≤ S.alpha ^ 32 * (N : Real) ^ 31 / 16)]

end LeanProofs.GowersSzemeredi
