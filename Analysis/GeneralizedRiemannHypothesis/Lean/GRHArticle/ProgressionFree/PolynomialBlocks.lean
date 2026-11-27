import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Gluing progression-free polynomial degree blocks

The cutoffs grow fast enough that degrees in two different blocks cannot mix
in an arithmetic progression. The individual blocks may use different sets.
-/

namespace GRHArticle.ProgressionFree

open Polynomial

/-- Upper degree limits for the blocks in the proof of `gpp:lem:replacement`. -/
def polynomialBlockCutoff (start : ℕ) : ℕ → ℕ
  | 0 => start
  | j + 1 => 2 * polynomialBlockCutoff start j + 2 * (j + 1) + 1

theorem polynomialBlockCutoff_strictMono (start : ℕ) :
    StrictMono (polynomialBlockCutoff start) := by
  apply strictMono_nat_of_lt_succ
  intro j
  simp only [polynomialBlockCutoff]
  omega

theorem polynomialBlockCutoff_gap (start : ℕ) {i j : ℕ} (hij : i < j) :
    2 * polynomialBlockCutoff start i + 2 * j < polynomialBlockCutoff start j := by
  cases j with
  | zero => omega
  | succ k =>
    have h := (polynomialBlockCutoff_strictMono start).monotone (Nat.le_of_lt_succ hij)
    rw [polynomialBlockCutoff]
    omega

/-- Keep the top `j + 1` degree layers of the set at cutoff `N j` and take their union. -/
def polynomialBlockUnion {F : Type*} [Semiring F] (N : ℕ → ℕ)
    (E : ℕ → Set (Polynomial F)) : Set (Polynomial F) :=
  {f | ∃ j, f ∈ E j ∧ N j ≤ f.natDegree + j ∧ f.natDegree ≤ N j}

/-- Under the separation inequalities of the article, progression-freeness
within each degree ball implies progression-freeness of the single union. -/
theorem polynomialBlockUnion_no_ratio_progression {F : Type*} [CommRing F] [IsDomain F]
    {N : ℕ → ℕ} (hgap : ∀ ⦃i j⦄, i < j → 2 * N i + 2 * j < N j)
    (E : ℕ → Set (Polynomial F)) (hne : ∀ i, (0 : Polynomial F) ∉ E i)
    (hfree : ∀ i (f r : Polynomial F), 0 < r.natDegree →
      ¬ (f ∈ E i ∧ f * r ∈ E i ∧ f * r * r ∈ E i))
    (f r : Polynomial F) (hr : 0 < r.natDegree) :
    ¬ (f ∈ polynomialBlockUnion N E ∧ f * r ∈ polynomialBlockUnion N E ∧
      f * r * r ∈ polynomialBlockUnion N E) := by
  rintro ⟨⟨i, hi, hi₀, hi₁⟩, ⟨j, hj, hj₀, hj₁⟩, ⟨k, hk, hk₀, hk₁⟩⟩
  have hf : f ≠ 0 := fun h ↦ hne i (h ▸ hi)
  have hr' : r ≠ 0 := by rintro rfl; simp at hr
  have h₁ := natDegree_mul hf hr'
  have h₂ := natDegree_mul (mul_ne_zero hf hr') hr'
  have hjk : j = k := by
    rcases lt_trichotomy j k with h | h | h
    · have := hgap h
      omega
    · exact h
    · have := hgap h
      omega
  subst k
  have hij : i = j := by
    rcases lt_trichotomy i j with h | h | h
    · have := hgap h
      omega
    · exact h
    · have := hgap h
      omega
  subst j
  exact hfree i f r hr ⟨hi, hj, hk⟩

open Filter Topology

variable {F : Type*} [Field F] [Fintype F]

/-- All polynomials of degree below `k`, including the zero polynomial. -/
noncomputable def polynomialDegreeLTFinset (F : Type*) [Field F] [Fintype F] (k : ℕ) :
    Finset (Polynomial F) :=
  Finset.univ.map ((degreeLTEquiv F k).symm.toEquiv.toEmbedding.trans
    (Function.Embedding.subtype fun f ↦ f ∈ degreeLT F k))

theorem mem_polynomialDegreeLTFinset {k : ℕ} {f : Polynomial F} :
    f ∈ polynomialDegreeLTFinset F k ↔ f.degree < k := by
  simp only [polynomialDegreeLTFinset, Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.trans_apply, Function.Embedding.subtype_apply]
  constructor
  · rintro ⟨a, rfl⟩
    exact mem_degreeLT.mp ((degreeLTEquiv F k).symm a).property
  · intro h
    let g : degreeLT F k := ⟨f, mem_degreeLT.mpr h⟩
    exact ⟨degreeLTEquiv F k g, congrArg Subtype.val ((degreeLTEquiv F k).symm_apply_apply g)⟩

theorem card_polynomialDegreeLTFinset (k : ℕ) :
    (polynomialDegreeLTFinset F k).card = Fintype.card F ^ k := by
  simp [polynomialDegreeLTFinset]

/-- Proportion of a set in the degree-at-most-`n` ball of size `q^(n+1)`. -/
noncomputable def polynomialBallProportion (E : Set (Polynomial F)) (n : ℕ) : ℝ := by
  classical
  exact (((polynomialDegreeLTFinset F (n+1)).filter (· ∈ E)).card : ℝ) /
    (Fintype.card F : ℝ) ^ (n+1)

theorem polynomialBallProportion_le_one (E : Set (Polynomial F)) (n : ℕ) :
    polynomialBallProportion E n ≤ 1 := by
  classical
  have h := ((polynomialDegreeLTFinset F (n+1)).card_filter_le (· ∈ E)).trans_eq
    (card_polynomialDegreeLTFinset (n+1))
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  unfold polynomialBallProportion
  rw [div_le_one (pow_pos hq _)]
  exact_mod_cast h

/-- At the selected cutoff the union can lose only the polynomials below
degree `N j - j`. Their fraction is at most `q^(-(j+1))`. -/
theorem polynomialBlockUnion_proportion (N : ℕ → ℕ) (E : ℕ → Set (Polynomial F))
    (j : ℕ) (hj : j ≤ N j) :
    polynomialBallProportion (E j) (N j) - (Fintype.card F : ℝ)⁻¹ ^ (j+1) ≤
      polynomialBallProportion (polynomialBlockUnion N E) (N j) := by
  classical
  let B := polynomialDegreeLTFinset F (N j + 1)
  let U := polynomialBlockUnion N E
  let low := polynomialDegreeLTFinset F (N j - j)
  have hsub : B.filter (· ∈ E j) ⊆ B.filter (· ∈ U) ∪ low := by
    intro f hf
    obtain ⟨hb, he⟩ := Finset.mem_filter.mp hf
    apply Finset.mem_union.mpr
    by_cases h : f.natDegree + j < N j
    · right
      apply mem_polynomialDegreeLTFinset.mpr
      exact (degree_le_natDegree.trans_lt (Nat.cast_lt.mpr (by omega : f.natDegree < N j - j)))
    · left
      refine Finset.mem_filter.mpr ⟨hb, j, he, by omega, ?_⟩
      by_cases hf₀ : f = 0
      · simp [hf₀]
      · have hd := mem_polynomialDegreeLTFinset.mp hb
        rw [degree_eq_natDegree hf₀, Nat.cast_lt] at hd
        omega
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hlow : low.card = Fintype.card F ^ (N j - j) := card_polynomialDegreeLTFinset _
  rw [hlow] at h
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsplit : (Fintype.card F : ℝ) ^ (N j + 1) =
      (Fintype.card F : ℝ) ^ (N j-j) * (Fintype.card F : ℝ) ^ (j+1) := by
    rw [← pow_add, show N j - j + (j + 1) = N j + 1 by omega]
  have herr : (Fintype.card F : ℝ)⁻¹ ^ (j+1) =
      (Fintype.card F : ℝ) ^ (N j-j) / (Fintype.card F : ℝ) ^ (N j+1) := by
    rw [hsplit, inv_pow]
    field_simp
  unfold polynomialBallProportion
  rw [herr, ← sub_div, div_le_div_iff_of_pos_right (pow_pos hq _), sub_le_iff_le_add]
  exact_mod_cast h

/-- If the proportions of the original sets tend to `d`, the one glued set
has upper ball density at least `d`. -/
theorem polynomialBlockUnion_le_limsup {N : ℕ → ℕ} (hN : StrictMono N)
    (E : ℕ → Set (Polynomial F)) {d : ℝ}
    (hd : Tendsto (fun j ↦ polynomialBallProportion (E j) (N j)) atTop (𝓝 d)) :
    d ≤ limsup (polynomialBallProportion (polynomialBlockUnion N E)) atTop := by
  let U := polynomialBlockUnion N E
  have hq : 1 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.one_lt_card
  have hz := (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr (by positivity))
    (inv_lt_one_of_one_lt₀ hq)).comp (tendsto_add_atTop_nat 1)
  have hlow : Tendsto (fun j ↦ polynomialBallProportion (E j) (N j) -
      (Fintype.card F : ℝ)⁻¹ ^ (j+1)) atTop (𝓝 d) := by
    simpa using hd.sub hz
  apply le_limsup_of_le ⟨1, eventually_map.mpr (Eventually.of_forall (polynomialBallProportion_le_one U))⟩
  intro b hb
  exact le_of_tendsto hlow ((hN.tendsto_atTop.eventually hb).mono fun j hj ↦
    (polynomialBlockUnion_proportion N E j (hN.id_le j)).trans hj)

end GRHArticle.ProgressionFree
