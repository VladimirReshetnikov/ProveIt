import IntegerPoints.IwaniecMozzochi
import IntegerPoints.GKProcessWords
import IntegerPoints.GKSec33LGeHalf

/-!
# Iwaniec--Mozzochi Section 4: exponent-pair bounds

This module specializes the proved Graham--Kolesnik exponent-pair estimates to
the reciprocal phase `t / m`.  The smooth phase `L9.ftest (-t)` belongs to the
class `F(M, P, 2, t, epsilon)` and agrees with `-t / m` on the dyadic interval;
complex conjugation removes that harmless sign.
-/

open scoped BigOperators
open Real Finset

namespace LeanProofs.IntegerPoints

namespace IMSection4

/-- The reciprocal phase belongs to every finite-order Graham--Kolesnik class
on a real dyadic interval whose lower endpoint is at least one. -/
theorem inversePhase_mem_gkClass (M : ℝ) (P : ℕ) (epsilon t : ℝ)
    (hM : 1 ≤ M) (hepsilon : 0 < epsilon) (ht : 0 < t) :
    InGKClass M P 2 t epsilon M (2 * M) (L9.ftest (-t)) := by
  refine ⟨le_rfl, ?_, le_rfl, L9.ftest_contDiff_nat (-t) P, ?_⟩
  · linarith
  · intro p _hp u hu
    have huhalf : 1 / 2 < u := lt_of_lt_of_le (by norm_num) (hM.trans hu.1)
    rw [GKSec33.iteratedDeriv_ftest_neg t u p huhalf,
      GKSec33.two_poch_eq_factorial]
    have hfac : (0 : ℝ) < ((p + 1).factorial : ℝ) := by positivity
    have hrpow : 0 < u ^ (-(2 : ℝ) - p) := by positivity
    norm_num
    positivity

/-- On `(M, 2M]`, the smooth negative reciprocal phase has the same sum norm
as the positive reciprocal phase. -/
theorem norm_inversePhase_eq_ftest_neg (t M : ℝ) :
    ‖∑ m ∈ dyadic M, e (t / m)‖ =
      ‖∑ m ∈ intRange M (2 * M), e (L9.ftest (-t) m)‖ := by
  have hphase : ∀ m ∈ intRange M (2 * M),
      L9.ftest (-t) m = -(t / (m : ℝ)) := by
    intro m hm
    have hm' := hm
    simp only [intRange, Finset.mem_Ioc] at hm'
    have hmoneNat : 1 ≤ m := by omega
    have hmone : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmoneNat
    have hmhalf : (1 / 2 : ℝ) ≤ (m : ℝ) := by linarith
    unfold L9.ftest
    rw [L9.hfun_eq hmhalf]
    ring
  rw [dyadic]
  calc
    ‖∑ m ∈ intRange M (2 * M), e (t / m)‖ =
        ‖∑ m ∈ intRange M (2 * M), e (-(t / m))‖ :=
      (GKB.norm_sum_e_neg (intRange M (2 * M)) (fun u : ℕ => t / u)).symm
    _ = ‖∑ m ∈ intRange M (2 * M), e (L9.ftest (-t) m)‖ := by
      congr 1
      exact Finset.sum_congr rfl fun m hm => by rw [hphase m hm]

/-- An exponent-pair estimate specialized to `e(t/m)`, with a nonnegative
constant. -/
theorem exists_inversePhase_exponentPair_bound {k l : ℝ}
    (hpair : IsExponentPair k l) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t M : ℝ, 1 ≤ M → M ^ 2 ≤ t →
      ‖∑ m ∈ dyadic M, e (t / m)‖ ≤
        C * ((t * M ^ (-(2 : ℝ))) ^ k * M ^ l + t⁻¹ * M ^ (2 : ℝ)) := by
  obtain ⟨P, epsilon, C, hepsilon, _hepsilonHalf, hbound⟩ :=
    hpair.2.2.2.2 2 (by norm_num)
  let C₀ : ℝ := max C 0
  have hC₀ : 0 ≤ C₀ := le_max_right _ _
  refine ⟨C₀, hC₀, ?_⟩
  intro t M hM htM
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hM2 : 0 < M ^ 2 := sq_pos_of_pos hM0
  have ht : 0 < t := hM2.trans_le htM
  have hclass := inversePhase_mem_gkClass M P epsilon t hM hepsilon ht
  have hraw := hbound M t M (2 * M) (L9.ftest (-t)) hM0 ht hclass
  have hraw' :
      ‖∑ m ∈ dyadic M, e (t / m)‖ ≤
        C * ((t * M ^ (-(2 : ℝ))) ^ k * M ^ l + t⁻¹ * M ^ (2 : ℝ)) := by
    rw [norm_inversePhase_eq_ftest_neg t M]
    simpa only [Real.rpow_two] using hraw
  have hinside :
      0 ≤ (t * M ^ (-(2 : ℝ))) ^ k * M ^ l + t⁻¹ * M ^ (2 : ℝ) := by
    positivity
  calc
    ‖∑ m ∈ dyadic M, e (t / m)‖ ≤
        C * ((t * M ^ (-(2 : ℝ))) ^ k * M ^ l + t⁻¹ * M ^ (2 : ℝ)) := hraw'
    _ ≤ C₀ * ((t * M ^ (-(2 : ℝ))) ^ k * M ^ l +
          t⁻¹ * M ^ (2 : ℝ)) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hinside

/-- The classical pair `(2/7, 4/7) = B A A B (0,1)`. -/
theorem isExponentPair_two_sevenths_four_sevenths :
    IsExponentPair (2 / 7) (4 / 7) := by
  have hA : IsExponentPair (1 / 14) (11 / 14) := by
    have h := AP.isExponentPair_A AP.isExponentPair_sixth_two_thirds
    norm_num at h ⊢
    exact h
  have hB := gk_theorem310_holds (1 / 14) (11 / 14) hA
  norm_num at hB ⊢
  exact hB

end IMSection4

/-- **Iwaniec--Mozzochi, Section 4.**  The exponent pairs `(1/2, 1/2)` and
`(2/7, 4/7)` give the two reciprocal-phase estimates used in the paper. -/
theorem iwaniecMozzochi_section4_exponentPairBounds_holds :
    iwaniecMozzochi_section4_exponentPairBounds := by
  obtain ⟨C₁, hC₁, hhalf⟩ :=
    IMSection4.exists_inversePhase_exponentPair_bound isExponentPair_half_half
  obtain ⟨C₂, hC₂, htwoSevenths⟩ :=
    IMSection4.exists_inversePhase_exponentPair_bound
      IMSection4.isExponentPair_two_sevenths_four_sevenths
  let C : ℝ := 2 * max C₁ C₂
  refine ⟨C, ?_⟩
  intro x h M hM hxh
  let t : ℝ := x * h
  have htM : M ^ 2 ≤ t := by simpa only [t] using hxh
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hM2 : 0 < M ^ 2 := sq_pos_of_pos hM0
  have ht : 0 < t := hM2.trans_le htM
  have hMnegTwo : M ^ (-(2 : ℝ)) = 1 / M ^ 2 := by
    rw [Real.rpow_neg hM0.le, Real.rpow_two, inv_eq_one_div]
  let q : ℝ := t * M ^ (-(2 : ℝ))
  have hqeq : q = t / M ^ 2 := by
    simp only [q, hMnegTwo]
    ring
  have hq : 1 ≤ q := by
    rw [hqeq, le_div_iff₀ hM2]
    simpa only [one_mul] using htM
  have herr : t⁻¹ * M ^ (2 : ℝ) ≤ 1 := by
    rw [Real.rpow_two, inv_mul_eq_div, div_le_iff₀ ht]
    simpa only [one_mul] using htM
  constructor
  · have hraw := hhalf t M hM htM
    change ‖∑ m ∈ dyadic M, e (t / m)‖ ≤
      C₁ * (q ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) +
        t⁻¹ * M ^ (2 : ℝ)) at hraw
    have hmainOne : 1 ≤ q ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) :=
      one_le_mul_of_one_le_of_one_le
        (Real.one_le_rpow hq (by norm_num))
        (Real.one_le_rpow hM (by norm_num))
    have hinside :
        q ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) +
            t⁻¹ * M ^ (2 : ℝ) ≤
          2 * (q ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2)) := by
      nlinarith
    have hmain :
        q ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) =
          t ^ ((1 : ℝ) / 2) * M ^ (-(1 : ℝ) / 2) := by
      dsimp [q]
      rw [Real.mul_rpow ht.le (Real.rpow_nonneg hM0.le _),
        ← Real.rpow_mul hM0.le, mul_assoc, ← Real.rpow_add hM0]
      congr 1
      ring_nf
    calc
      ‖∑ m ∈ dyadic M, e (t / m)‖ ≤
          C₁ * (q ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) +
            t⁻¹ * M ^ (2 : ℝ)) := hraw
      _ ≤ C₁ * (2 * (q ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left hinside hC₁
      _ = 2 * C₁ * (q ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2)) := by ring
      _ ≤ 2 * max C₁ C₂ *
          (q ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_max_left C₁ C₂) (by norm_num))
          (by positivity)
      _ = C * (t ^ ((1 : ℝ) / 2) * M ^ (-(1 : ℝ) / 2)) := by
        rw [hmain]
  · have hraw := htwoSevenths t M hM htM
    change ‖∑ m ∈ dyadic M, e (t / m)‖ ≤
      C₂ * (q ^ ((2 : ℝ) / 7) * M ^ ((4 : ℝ) / 7) +
        t⁻¹ * M ^ (2 : ℝ)) at hraw
    have hmainOne : 1 ≤ q ^ ((2 : ℝ) / 7) * M ^ ((4 : ℝ) / 7) :=
      one_le_mul_of_one_le_of_one_le
        (Real.one_le_rpow hq (by norm_num))
        (Real.one_le_rpow hM (by norm_num))
    have hinside :
        q ^ ((2 : ℝ) / 7) * M ^ ((4 : ℝ) / 7) +
            t⁻¹ * M ^ (2 : ℝ) ≤
          2 * (q ^ ((2 : ℝ) / 7) * M ^ ((4 : ℝ) / 7)) := by
      nlinarith
    have hmain :
        q ^ ((2 : ℝ) / 7) * M ^ ((4 : ℝ) / 7) = t ^ ((2 : ℝ) / 7) := by
      dsimp [q]
      rw [Real.mul_rpow ht.le (Real.rpow_nonneg hM0.le _),
        ← Real.rpow_mul hM0.le, mul_assoc, ← Real.rpow_add hM0]
      norm_num
    calc
      ‖∑ m ∈ dyadic M, e (t / m)‖ ≤
          C₂ * (q ^ ((2 : ℝ) / 7) * M ^ ((4 : ℝ) / 7) +
            t⁻¹ * M ^ (2 : ℝ)) := hraw
      _ ≤ C₂ * (2 * (q ^ ((2 : ℝ) / 7) * M ^ ((4 : ℝ) / 7))) :=
        mul_le_mul_of_nonneg_left hinside hC₂
      _ = 2 * C₂ * (q ^ ((2 : ℝ) / 7) * M ^ ((4 : ℝ) / 7)) := by ring
      _ ≤ 2 * max C₁ C₂ *
          (q ^ ((2 : ℝ) / 7) * M ^ ((4 : ℝ) / 7)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_max_right C₁ C₂) (by norm_num))
          (by positivity)
      _ = C * t ^ ((2 : ℝ) / 7) := by rw [hmain]

end LeanProofs.IntegerPoints
