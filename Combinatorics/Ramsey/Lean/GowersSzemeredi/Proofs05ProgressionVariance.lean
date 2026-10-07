import GowersSzemeredi.Proofs05ProgressionMoments

/-! The variance lower bound for sampling all starts and directions of a
fixed-length modular progression. Repeated positions count with multiplicity;
proper directions will be selected separately. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def realSetIndicator {N : Nat} (A : Finset (ZMod N)) (x : ZMod N) : Real :=
  if x ∈ A then 1 else 0

def realSetBalanced {N : Nat} (A : Finset (ZMod N)) (x : ZMod N) : Real :=
  realSetIndicator A x - density A

def progressionSampleDensity {N : Nat} (A : Finset (ZMod N)) (L : Nat)
    (a d : ZMod N) : Real :=
  (∑ i : Fin L, realSetIndicator A (a + (i.val : ZMod N) * d)) / L

theorem sum_realSetIndicator {N : Nat} [NeZero N] (A : Finset (ZMod N)) :
    (∑ x, realSetIndicator A x) = (A.card : Real) := by
  classical
  simp [realSetIndicator]

theorem sum_sq_realSetBalanced {N : Nat} [NeZero N] (A : Finset (ZMod N)) :
    (∑ x, realSetBalanced A x ^ 2) = (N : Real) * density A * (1 - density A) := by
  classical
  have hpoint (x : ZMod N) : realSetBalanced A x ^ 2 =
      (1 - 2 * density A) * realSetIndicator A x + density A ^ 2 := by
    dsimp [realSetBalanced, realSetIndicator]
    split_ifs <;> ring
  have hcard : density A * (N : Real) = A.card := by
    exact div_mul_cancel₀ _ (by exact_mod_cast NeZero.ne N)
  simp only [hpoint, Finset.sum_add_distrib, ← Finset.mul_sum, sum_realSetIndicator,
    Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  rw [← hcard]
  ring

theorem progressionSampleDensity_range {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) {L : Nat} (hL : 0 < L) (a d : ZMod N) :
    0 ≤ progressionSampleDensity A L a d ∧ progressionSampleDensity A L a d ≤ 1 := by
  have hLr : (0 : Real) < L := by exact_mod_cast hL
  have hpoint (x : ZMod N) : 0 ≤ realSetIndicator A x ∧ realSetIndicator A x ≤ 1 := by
    dsimp [realSetIndicator]
    split_ifs <;> norm_num
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i _ => (hpoint _).1) hLr.le
  · apply (div_le_one hLr).mpr
    calc
      _ ≤ ∑ _i : Fin L, (1 : Real) := Finset.sum_le_sum fun i _ => (hpoint _).2
      _ = (L : Real) := by simp

theorem progressionSampleDensity_mean {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) {L : Nat} (hL : 0 < L) (d : ZMod N) :
    (∑ a, progressionSampleDensity A L a d) = (A.card : Real) := by
  have hLr : (L : Real) ≠ 0 := by exact_mod_cast hL.ne'
  unfold progressionSampleDensity
  rw [← Finset.sum_div, Finset.sum_comm]
  have ht (i : Fin L) : (∑ a, realSetIndicator A (a + (i.val : ZMod N) * d)) =
      A.card := (sum_translate_real (realSetIndicator A) _).trans (sum_realSetIndicator A)
  simp only [ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ hLr

theorem progressionSampleDensity_variance_lower {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) {L : Nat} (hL : 0 < L) :
    (N : Real) ^ 2 * density A * (1 - density A) ≤
      L * ∑ d, ∑ a, (progressionSampleDensity A L a d - density A) ^ 2 := by
  have hLr : (0 : Real) < L := by exact_mod_cast hL
  have hraw (a d : ZMod N) :
      (∑ i : Fin L, realSetBalanced A (a + (i.val : ZMod N) * d)) =
        L * (progressionSampleDensity A L a d - density A) := by
    simp only [realSetBalanced, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, progressionSampleDensity]
    field_simp
  have h := cyclic_progression_second_moment_lower (realSetBalanced A) L
  simp only [sum_sq_realSetBalanced, hraw, mul_pow, ← Finset.mul_sum] at h
  apply (mul_le_mul_iff_right₀ hLr).mp
  nlinarith [h]

/-- A uniform bound on the samples for one direction bounds its conditional
variance, since the mean is the density for every direction separately. -/
theorem progressionSampleDensity_variance_upper {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) {L : Nat} (hL : 0 < L) (d : ZMod N) (c : Real)
    (hc : ∀ a, progressionSampleDensity A L a d ≤ c) :
    (∑ a, (progressionSampleDensity A L a d - density A) ^ 2) ≤
      (c - density A) * density A * N := by
  have hpoint (a : ZMod N) : (progressionSampleDensity A L a d - density A) ^ 2 ≤
      (c - 2 * density A) * progressionSampleDensity A L a d + density A ^ 2 := by
    have hx := (progressionSampleDensity_range A hL a d).1
    have hmul := mul_le_mul_of_nonneg_right (hc a) hx
    nlinarith [hmul]
  have hcard : density A * (N : Real) = A.card := by
    exact div_mul_cancel₀ _ (by exact_mod_cast NeZero.ne N)
  calc
    _ ≤ ∑ a, ((c - 2 * density A) * progressionSampleDensity A L a d + density A ^ 2) :=
      Finset.sum_le_sum fun a _ => hpoint a
    _ = (c - density A) * density A * N := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, progressionSampleDensity_mean A hL,
        Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      rw [← hcard]
      ring

end LeanProofs.GowersSzemeredi
