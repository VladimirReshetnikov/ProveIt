import OAI.Combinatorics.Progressions.Estimates.FiniteTriangularRationalCorrection
import OAI.Combinatorics.Progressions.Linear.FiniteDescendingRankOrder

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def finiteRankCorrectionSolutions {I : Type*} [Fintype I]
    (A : Matrix I I ℝ) (c : I → ℝ) (B : ℝ) (q : ℕ) :
    Set ((I → ℝ) × (I → ℚ)) :=
  {sr | (∀ i, |sr.1 i| ≤ B) ∧
    (∀ i, ∃ z : ℤ, sr.2 i = (z : ℚ) / q) ∧
    ∀ i, c i = ∑ j, A i j * sr.1 j + (sr.2 i : ℝ)}

theorem finiteRankCorrectionSolutions_reindex
    {I J : Type*} [Fintype I] [Fintype J] (e : J ≃ I)
    (A : Matrix I I ℝ) (c : I → ℝ) (B : ℝ) (q : ℕ)
    (sr : (I → ℝ) × (I → ℚ)) :
    sr ∈ finiteRankCorrectionSolutions A c B q ↔
      ((fun i => sr.1 (e i)), (fun i => sr.2 (e i))) ∈
        finiteRankCorrectionSolutions (fun i j => A (e i) (e j)) (fun i => c (e i)) B q := by
  constructor
  · intro hs
    refine ⟨fun i => hs.1 (e i), fun i => hs.2.1 (e i), ?_⟩
    intro i
    dsimp only
    have hsum : (∑ j, A (e i) (e j) * sr.1 (e j)) =
        ∑ j : I, A (e i) j * sr.1 j := e.sum_comp (fun j : I => A (e i) j * sr.1 j)
    rw [hsum]
    exact hs.2.2 (e i)
  · intro hs
    refine ⟨?_, ?_, ?_⟩
    · intro i
      simpa only [e.apply_symm_apply] using hs.1 (e.symm i)
    · intro i
      simpa only [e.apply_symm_apply] using hs.2.1 (e.symm i)
    · intro i
      have hi := hs.2.2 (e.symm i)
      dsimp only at hi
      have hsum : (∑ j, A i (e j) * sr.1 (e j)) =
          ∑ j : I, A i j * sr.1 j := e.sum_comp (fun j : I => A i j * sr.1 j)
      simpa only [e.apply_symm_apply, hsum] using hi

theorem exists_rank_triangular_equiv {I : Type*} [Fintype I]
    (rank : I → ℕ) (A : Matrix I I ℝ)
    (htri : ∀ i j, rank j ≤ rank i → j ≠ i → A i j = 0) :
    ∃ e : Fin (Fintype.card I) ≃ I,
      (∀ i j, i ≤ j → rank (e j) ≤ rank (e i)) ∧
      ∀ i j, i < j → A (e i) (e j) = 0 := by
  obtain ⟨e, he⟩ := exists_finite_descending_rank_equiv rank
  refine ⟨e, he, ?_⟩
  intro i j hij
  exact htri (e i) (e j) (he i j hij.le)
    (fun h => hij.ne (e.injective h).symm)

theorem exists_finite_rank_triangular_correction_enumeration
    {I : Type*} [Fintype I] (q : ℕ) (hq : 0 < q) (B : ℝ) (hB : 0 ≤ B)
    (rank : I → ℕ) (A : Matrix I I ℝ) (c : I → ℝ)
    (htri : ∀ i j, rank j ≤ rank i → j ≠ i → A i j = 0)
    (hdiag : ∀ i, A i i ≠ 0) (hdiagBound : ∀ i, |A i i| ≤ 1) :
    ∃ m : ℕ, m ≤ (2 * ⌈(q : ℝ) * B⌉₊ + 3) ^ Fintype.card I ∧
      ∃ candidate : Fin m → ((I → ℝ) × (I → ℚ)),
        (∀ j, candidate j ∈ finiteRankCorrectionSolutions A c B q) ∧
        ∀ sr, sr ∈ finiteRankCorrectionSolutions A c B q → ∃ j, candidate j = sr := by
  obtain ⟨e, _, he⟩ := exists_rank_triangular_equiv rank A htri
  let A' : Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℝ :=
    fun i j => A (e i) (e j)
  let c' : Fin (Fintype.card I) → ℝ := fun i => c (e i)
  obtain ⟨m, hm, candidate, hmem, hcover⟩ :=
    exists_triangular_rational_correction_enumeration q hq B hB (Fintype.card I) A' c'
      he (fun i => hdiag (e i)) (fun i => hdiagBound (e i))
  let candidate' : Fin m → ((I → ℝ) × (I → ℚ)) :=
    fun j => (fun i => (candidate j).1 (e.symm i), fun i => (candidate j).2 (e.symm i))
  refine ⟨m, hm, candidate', ?_, ?_⟩
  · intro j
    apply (finiteRankCorrectionSolutions_reindex e A c B q (candidate' j)).mpr
    simpa only [candidate', e.symm_apply_apply, finiteRankCorrectionSolutions,
      triangularCorrectionSolutions, A', c'] using hmem j
  · intro sr hsr
    have hsr' := (finiteRankCorrectionSolutions_reindex e A c B q sr).mp hsr
    obtain ⟨j, hj⟩ := hcover (fun i => sr.1 (e i), fun i => sr.2 (e i)) hsr'
    refine ⟨j, ?_⟩
    dsimp only [candidate']
    rw [hj]
    simp only [e.apply_symm_apply]

theorem exists_finite_rank_triangular_correction_enumeration_exp
    {I : Type*} [Fintype I] (q : ℕ) (hq : 0 < q) {B p : ℝ}
    (hp : 0 ≤ p) (hB : 0 ≤ B) (hI : (Fintype.card I : ℝ) ≤ p)
    (hqCap : (q : ℝ) ≤ Real.exp p) (hBCap : B ≤ Real.exp p)
    (rank : I → ℕ) (A : Matrix I I ℝ) (c : I → ℝ)
    (htri : ∀ i j, rank j ≤ rank i → j ≠ i → A i j = 0)
    (hdiag : ∀ i, A i i ≠ 0) (hdiagBound : ∀ i, |A i i| ≤ 1) :
    ∃ m : ℕ, (m : ℝ) ≤ Real.exp ((p + 3) ^ 3) ∧
      ∃ candidate : Fin m → ((I → ℝ) × (I → ℚ)),
        (∀ j, candidate j ∈ finiteRankCorrectionSolutions A c B q) ∧
        ∀ sr, sr ∈ finiteRankCorrectionSolutions A c B q → ∃ j, candidate j = sr := by
  obtain ⟨m, hm, candidate, hmem, hcover⟩ :=
    exists_finite_rank_triangular_correction_enumeration q hq B hB rank A c htri hdiag hdiagBound
  exact ⟨m, (Nat.cast_le.mpr hm).trans
    (real_grid_window_count_le_exp (Fintype.card I) q hp hB hI hqCap hBCap),
    candidate, hmem, hcover⟩

theorem exists_uniform_finite_rank_triangular_correction_enumeration (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type*} [Fintype I] (q : ℕ), 0 < q →
      ∀ (B p : ℝ), 0 ≤ p → 0 ≤ B → (Fintype.card I : ℝ) ≤ p →
      (q : ℝ) ≤ Real.exp ((p + a) ^ a) → B ≤ Real.exp ((p + a) ^ a) →
      ∀ (rank : I → ℕ) (A : Matrix I I ℝ) (c : I → ℝ),
      (∀ i j, rank j ≤ rank i → j ≠ i → A i j = 0) →
      (∀ i, A i i ≠ 0) → (∀ i, |A i i| ≤ 1) →
      ∃ m : ℕ, (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ candidate : Fin m → ((I → ℝ) × (I → ℚ)),
          (∀ j, candidate j ∈ finiteRankCorrectionSolutions A c B q) ∧
          ∀ sr, sr ∈ finiteRankCorrectionSolutions A c B q → ∃ j, candidate j = sr := by
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + (Polynomial.X + Polynomial.C a) ^ a + 3) ^ 3)
  refine ⟨C, hC, ?_⟩
  intro I _ q hq B p hp hB hI hqCap hBCap rank A c htri hdiag hdiagBound
  let p' := p + (p + a) ^ a
  have hp' : 0 ≤ p' := by dsimp [p']; positivity
  have hpp : p ≤ p' := le_add_of_nonneg_right (by positivity)
  have hap : (p + a) ^ a ≤ p' := le_add_of_nonneg_left hp
  obtain ⟨m, hm, candidate, hmem, hcover⟩ :=
    exists_finite_rank_triangular_correction_enumeration_exp q hq hp' hB (hI.trans hpp)
      (hqCap.trans (Real.exp_le_exp.mpr hap)) (hBCap.trans (Real.exp_le_exp.mpr hap))
      rank A c htri hdiag hdiagBound
  refine ⟨m, hm.trans (Real.exp_le_exp.mpr ?_), candidate, hmem, hcover⟩
  simpa [p', Polynomial.eval₂_pow] using hbudget p hp

end Erdos3

end

section

namespace Erdos3

private theorem correction_finset_of_enumeration
    {I : Type*} [Fintype I] {A : Matrix I I ℝ} {c : I → ℝ} {B : ℝ} {q m : ℕ}
    (candidate : Fin m → ((I → ℝ) × (I → ℚ)))
    (hmem : ∀ j, candidate j ∈ finiteRankCorrectionSolutions A c B q)
    (hcover : ∀ sr, sr ∈ finiteRankCorrectionSolutions A c B q →
      ∃ j, candidate j = sr) :
    ∃ H : Finset ((I → ℝ) × (I → ℚ)), H.card ≤ m ∧
      ∀ sr, sr ∈ H ↔ sr ∈ finiteRankCorrectionSolutions A c B q := by
  classical
  refine ⟨Finset.univ.image candidate, ?_, ?_⟩
  · exact (Finset.card_image_le).trans (by simp)
  · intro sr
    constructor
    · intro hs
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hs
      exact hmem j
    · intro hs
      obtain ⟨j, hj⟩ := hcover sr hs
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩

theorem exists_finite_rank_triangular_correction_finset
    {I : Type*} [Fintype I] (q : ℕ) (hq : 0 < q) (B : ℝ) (hB : 0 ≤ B)
    (rank : I → ℕ) (A : Matrix I I ℝ) (c : I → ℝ)
    (htri : ∀ i j, rank j ≤ rank i → j ≠ i → A i j = 0)
    (hdiag : ∀ i, A i i ≠ 0) (hdiagBound : ∀ i, |A i i| ≤ 1) :
    ∃ H : Finset ((I → ℝ) × (I → ℚ)),
      H.card ≤ (2 * ⌈(q : ℝ) * B⌉₊ + 3) ^ Fintype.card I ∧
      ∀ sr, sr ∈ H ↔ sr ∈ finiteRankCorrectionSolutions A c B q := by
  obtain ⟨m, hm, candidate, hmem, hcover⟩ :=
    exists_finite_rank_triangular_correction_enumeration q hq B hB rank A c htri hdiag hdiagBound
  obtain ⟨H, hH, heq⟩ := correction_finset_of_enumeration candidate hmem hcover
  exact ⟨H, hH.trans hm, heq⟩

theorem exists_finite_rank_triangular_correction_finset_exp
    {I : Type*} [Fintype I] (q : ℕ) (hq : 0 < q) {B p : ℝ}
    (hp : 0 ≤ p) (hB : 0 ≤ B) (hI : (Fintype.card I : ℝ) ≤ p)
    (hqCap : (q : ℝ) ≤ Real.exp p) (hBCap : B ≤ Real.exp p)
    (rank : I → ℕ) (A : Matrix I I ℝ) (c : I → ℝ)
    (htri : ∀ i j, rank j ≤ rank i → j ≠ i → A i j = 0)
    (hdiag : ∀ i, A i i ≠ 0) (hdiagBound : ∀ i, |A i i| ≤ 1) :
    ∃ H : Finset ((I → ℝ) × (I → ℚ)),
      (H.card : ℝ) ≤ Real.exp ((p + 3) ^ 3) ∧
      ∀ sr, sr ∈ H ↔ sr ∈ finiteRankCorrectionSolutions A c B q := by
  obtain ⟨m, hm, candidate, hmem, hcover⟩ :=
    exists_finite_rank_triangular_correction_enumeration_exp q hq hp hB hI hqCap hBCap
      rank A c htri hdiag hdiagBound
  obtain ⟨H, hH, heq⟩ := correction_finset_of_enumeration candidate hmem hcover
  exact ⟨H, (Nat.cast_le.mpr hH).trans hm, heq⟩

theorem exists_uniform_finite_rank_triangular_correction_finset (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type*} [Fintype I] (q : ℕ), 0 < q →
      ∀ (B p : ℝ), 0 ≤ p → 0 ≤ B → (Fintype.card I : ℝ) ≤ p →
      (q : ℝ) ≤ Real.exp ((p + a) ^ a) → B ≤ Real.exp ((p + a) ^ a) →
      ∀ (rank : I → ℕ) (A : Matrix I I ℝ) (c : I → ℝ),
      (∀ i j, rank j ≤ rank i → j ≠ i → A i j = 0) →
      (∀ i, A i i ≠ 0) → (∀ i, |A i i| ≤ 1) →
      ∃ H : Finset ((I → ℝ) × (I → ℚ)),
        (H.card : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ sr, sr ∈ H ↔ sr ∈ finiteRankCorrectionSolutions A c B q := by
  obtain ⟨C, hC, h⟩ := exists_uniform_finite_rank_triangular_correction_enumeration a
  refine ⟨C, hC, ?_⟩
  intro I _ q hq B p hp hB hI hqCap hBCap rank A c htri hdiag hdiagBound
  obtain ⟨m, hm, candidate, hmem, hcover⟩ :=
    h q hq B p hp hB hI hqCap hBCap rank A c htri hdiag hdiagBound
  obtain ⟨H, hH, heq⟩ := correction_finset_of_enumeration candidate hmem hcover
  exact ⟨H, (Nat.cast_le.mpr hH).trans hm, heq⟩

end Erdos3

end

end OAI
