import Mathlib.Data.Finset.Union
import OAI.Combinatorics.Progressions.Estimates.TriangularCorrectionRows
import OAI.Combinatorics.Progressions.Sampling.BoundedKernelGridEnumerationBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators

private theorem exists_finite_triangular_correction_of_windows
    (B : ℝ) (hB : 0 ≤ B) (q W : ℕ)
    (hwindow : ∀ c : ℝ, ∃ S : Finset ℚ, S.card ≤ W ∧ ∀ r : ℚ,
      r ∈ S ↔ (∃ z : ℤ, r = (z : ℚ) / q) ∧ |(r : ℝ) - c| ≤ B) :
    ∀ n (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ),
      (∀ i j, i < j → A i j = 0) →
      (∀ i, A i i ≠ 0 ∧ |A i i| ≤ 1) →
      ∃ S : Finset ((Fin n → ℝ) × (Fin n → ℚ)), S.card ≤ W ^ n ∧
        ∀ sr, sr ∈ S ↔ sr ∈ triangularCorrectionSolutions A c B q := by
  classical
  choose window hcard hmem using hwindow
  intro n
  induction n with
  | zero =>
    intro A c htri hdiag
    let z : (Fin 0 → ℝ) × (Fin 0 → ℚ) := (0, 0)
    refine ⟨{z}, by simp, ?_⟩
    intro sr
    have he : sr = z := Subsingleton.elim _ _
    subst sr
    simp [triangularCorrectionSolutions]
  | succ n ih =>
    intro A c htri hdiag
    let A' : Matrix (Fin n) (Fin n) ℝ := fun i j => A i.castSucc j.castSucc
    let c' : Fin n → ℝ := fun i => c i.castSucc
    obtain ⟨S, hS, hSiff⟩ := ih A' c'
      (fun i j hij => htri i.castSucc j.castSucc hij) (fun i => hdiag i.castSucc)
    let center : ((Fin n → ℝ) × (Fin n → ℚ)) → ℝ :=
      fun u => c (Fin.last n) - ∑ j, A (Fin.last n) j.castSucc * u.1 j
    let extend : ((Fin n → ℝ) × (Fin n → ℚ)) → ℚ →
        ((Fin (n + 1) → ℝ) × (Fin (n + 1) → ℚ)) := fun u r =>
      (Fin.snoc u.1 ((center u - (r : ℝ)) / A (Fin.last n) (Fin.last n)), Fin.snoc u.2 r)
    let all := S.biUnion (fun u => (window (center u)).image (extend u))
    let out := all.filter (fun sr => sr ∈ triangularCorrectionSolutions A c B q)
    have hallcard : all.card ≤ W ^ (n + 1) := by
      calc
        all.card ≤ ∑ u ∈ S, ((window (center u)).image (extend u)).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _u ∈ S, W := Finset.sum_le_sum
          (fun u _ => Finset.card_image_le.trans (hcard (center u)))
        _ = S.card * W := by simp
        _ ≤ W ^ n * W := Nat.mul_le_mul_right W hS
        _ = W ^ (n + 1) := (pow_succ W n).symm
    refine ⟨out, (Finset.card_filter_le _ _).trans hallcard, ?_⟩
    intro sr
    constructor
    · intro hs
      exact (Finset.mem_filter.mp hs).2
    · intro hsr
      apply Finset.mem_filter.mpr
      refine ⟨?_, hsr⟩
      let u : (Fin n → ℝ) × (Fin n → ℚ) :=
        (fun i => sr.1 i.castSucc, fun i => sr.2 i.castSucc)
      have hu : u ∈ S := (hSiff u).mpr
        (triangularCorrectionSolutions_prefix htri hsr)
      have hr : sr.2 (Fin.last n) ∈ window (center u) := by
        apply (hmem _ _).mpr
        refine ⟨hsr.2.1 (Fin.last n), ?_⟩
        exact triangularCorrectionSolutions_last_window hsr hB
          (hdiag (Fin.last n)).2
      apply Finset.mem_biUnion.mpr
      refine ⟨u, hu, Finset.mem_image.mpr ⟨sr.2 (Fin.last n), hr, ?_⟩⟩
      have hlast := triangularCorrectionSolutions_last_eq hsr
        (hdiag (Fin.last n)).1
      apply Prod.ext
      · funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [extend, Fin.snoc_last, center, u] using hlast.symm
        · simp only [extend, Fin.snoc_castSucc, u]
      · funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [extend, Fin.snoc_last]
        · simp only [extend, Fin.snoc_castSucc, u]

theorem exists_finite_triangular_rational_correction
    (q : ℕ) (hq : 0 < q) (B : ℝ) (hB : 0 ≤ B)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ)
    (htri : ∀ i j, i < j → A i j = 0)
    (hdiag : ∀ i, A i i ≠ 0) (hdiagBound : ∀ i, |A i i| ≤ 1) :
    ∃ S : Finset ((Fin n → ℝ) × (Fin n → ℚ)),
      S.card ≤ (2 * ⌈(q : ℝ) * B⌉₊ + 3) ^ n ∧
      ∀ sr, sr ∈ S ↔ sr ∈ triangularCorrectionSolutions A c B q := by
  apply exists_finite_triangular_correction_of_windows B hB q
    (2 * ⌈(q : ℝ) * B⌉₊ + 3) ?_ n A c htri (fun i => ⟨hdiag i, hdiagBound i⟩)
  intro center
  obtain ⟨S, hS, hmem⟩ := exists_scalar_rational_grid_window q hq center B
  refine ⟨S, hS, ?_⟩
  intro r
  rw [hmem]
  apply and_congr_left
  intro _
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, by exact_mod_cast hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by exact_mod_cast hz⟩

theorem exists_triangular_rational_correction_enumeration
    (q : ℕ) (hq : 0 < q) (B : ℝ) (hB : 0 ≤ B)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ)
    (htri : ∀ i j, i < j → A i j = 0)
    (hdiag : ∀ i, A i i ≠ 0) (hdiagBound : ∀ i, |A i i| ≤ 1) :
    ∃ m : ℕ, m ≤ (2 * ⌈(q : ℝ) * B⌉₊ + 3) ^ n ∧
      ∃ candidate : Fin m → ((Fin n → ℝ) × (Fin n → ℚ)),
        (∀ j, candidate j ∈ triangularCorrectionSolutions A c B q) ∧
        ∀ sr, sr ∈ triangularCorrectionSolutions A c B q → ∃ j, candidate j = sr := by
  classical
  obtain ⟨S, hS, hmem⟩ := exists_finite_triangular_rational_correction q hq B hB
    n A c htri hdiag hdiagBound
  let e := Fintype.equivFin S
  refine ⟨Fintype.card S, ?_, fun j => (e.symm j).val, ?_, ?_⟩
  · simpa only [Fintype.card_coe] using hS
  · intro j
    exact (hmem _).mp (e.symm j).property
  · intro sr hsr
    let v : S := ⟨sr, (hmem sr).mpr hsr⟩
    exact ⟨e v, congrArg Subtype.val (e.symm_apply_apply v)⟩

theorem exists_triangular_rational_correction_enumeration_exp
    (q : ℕ) (hq : 0 < q) {B p : ℝ} (hp : 0 ≤ p) (hB : 0 ≤ B)
    (n : ℕ) (hn : (n : ℝ) ≤ p) (hqCap : (q : ℝ) ≤ Real.exp p)
    (hBCap : B ≤ Real.exp p)
    (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ)
    (htri : ∀ i j, i < j → A i j = 0)
    (hdiag : ∀ i, A i i ≠ 0) (hdiagBound : ∀ i, |A i i| ≤ 1) :
    ∃ m : ℕ, (m : ℝ) ≤ Real.exp ((p + 3) ^ 3) ∧
      ∃ candidate : Fin m → ((Fin n → ℝ) × (Fin n → ℚ)),
        (∀ j, candidate j ∈ triangularCorrectionSolutions A c B q) ∧
        ∀ sr, sr ∈ triangularCorrectionSolutions A c B q → ∃ j, candidate j = sr := by
  obtain ⟨m, hm, candidate, hmem, hcover⟩ :=
    exists_triangular_rational_correction_enumeration q hq B hB n A c htri hdiag hdiagBound
  exact ⟨m, (Nat.cast_le.mpr hm).trans
    (real_grid_window_count_le_exp n q hp hB hn hqCap hBCap), candidate, hmem, hcover⟩

theorem exists_uniform_triangular_rational_correction_enumeration (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (q : ℕ), 0 < q → ∀ (B p : ℝ), 0 ≤ p → 0 ≤ B →
      ∀ (n : ℕ), (n : ℝ) ≤ p →
      (q : ℝ) ≤ Real.exp ((p + a) ^ a) → B ≤ Real.exp ((p + a) ^ a) →
      ∀ (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ),
      (∀ i j, i < j → A i j = 0) → (∀ i, A i i ≠ 0) → (∀ i, |A i i| ≤ 1) →
      ∃ m : ℕ, (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ candidate : Fin m → ((Fin n → ℝ) × (Fin n → ℚ)),
          (∀ j, candidate j ∈ triangularCorrectionSolutions A c B q) ∧
          ∀ sr, sr ∈ triangularCorrectionSolutions A c B q → ∃ j, candidate j = sr := by
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + (Polynomial.X + Polynomial.C a) ^ a + 3) ^ 3)
  refine ⟨C, hC, ?_⟩
  intro q hq B p hp hB n hn hqCap hBCap A c htri hdiag hdiagBound
  let p' := p + (p + a) ^ a
  have hp' : 0 ≤ p' := by dsimp [p']; positivity
  have hpp : p ≤ p' := le_add_of_nonneg_right (by positivity)
  have hap : (p + a) ^ a ≤ p' := le_add_of_nonneg_left hp
  obtain ⟨m, hm, candidate, hmem, hcover⟩ :=
    exists_triangular_rational_correction_enumeration_exp q hq hp' hB n (hn.trans hpp)
      (hqCap.trans (Real.exp_le_exp.mpr hap)) (hBCap.trans (Real.exp_le_exp.mpr hap))
      A c htri hdiag hdiagBound
  refine ⟨m, hm.trans (Real.exp_le_exp.mpr ?_), candidate, hmem, hcover⟩
  simpa [p', Polynomial.eval₂_pow] using hbudget p hp

end Erdos3

end

end OAI
