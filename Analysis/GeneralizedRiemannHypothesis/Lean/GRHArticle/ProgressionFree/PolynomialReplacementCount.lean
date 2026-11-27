import GRHArticle.ProgressionFree.PolynomialSmoothCount
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# Counting the modified polynomial degree balls

At each selected rough part the scalar and smooth polynomial can be chosen
independently. Counting these fibers gives the signed change from the baseline.
-/

namespace GRHArticle.ProgressionFree

open Polynomial UniqueFactorizationMonoid
open scoped Classical BigOperators

variable {F : Type*} [Field F]

/-- The squarefree monic rough polynomials of a prescribed degree. -/
noncomputable def polynomialSquarefreeRoughLayer (F : Type*) [Field F] [Fintype F]
    (L n : ℕ) : Finset (Polynomial F) :=
  (polynomialDegreeLayer F n).filter fun g ↦
    g.Monic ∧ Squarefree g ∧ ∀ p ∈ normalizedFactors g, L < p.natDegree

@[simp] theorem mem_polynomialSquarefreeRoughLayer [Fintype F] {L n : ℕ} {g : Polynomial F} :
    g ∈ polynomialSquarefreeRoughLayer F L n ↔
      g.Monic ∧ g.natDegree = n ∧ Squarefree g ∧
        ∀ p ∈ normalizedFactors g, L < p.natDegree := by
  simp only [polynomialSquarefreeRoughLayer, Finset.mem_filter, mem_polynomialDegreeLayer]
  exact ⟨fun ⟨⟨_, hdeg⟩, hm, hs, hp⟩ ↦ ⟨hm, hdeg, hs, hp⟩,
    fun ⟨hm, hdeg, hs, hp⟩ ↦ ⟨⟨hm.ne_zero, hdeg⟩, hm, hs, hp⟩⟩

private theorem monic_polynomialSmoothPart (L : ℕ) (f : Polynomial F) :
    (polynomialSmoothPart L f).Monic := by
  rw [polynomialSmoothPart]
  simpa only [Multiset.map_id] using
    (Polynomial.monic_multiset_prod_of_monic
      ((normalizedFactors f).filter fun p ↦ p.natDegree ≤ L) id
      (fun p hp ↦ by
        have hp' := (Multiset.mem_filter.mp hp).1
        exact (Polynomial.normalize_eq_self_iff_monic
          (irreducible_of_normalized_factor p hp').ne_zero).mp (normalize_normalized_factor p hp')))

private theorem normalizedFactors_polynomialSmoothPart (L : ℕ) (f : Polynomial F) :
    normalizedFactors (polynomialSmoothPart L f) =
      (normalizedFactors f).filter fun p ↦ p.natDegree ≤ L := by
  rw [polynomialSmoothPart, normalizedFactors_prod_eq _ (fun p hp ↦
    irreducible_of_normalized_factor p (Multiset.mem_filter.mp hp).1)]
  rw [Multiset.map_congr rfl (f := normalize) (g := id) (fun p hp ↦
    normalize_normalized_factor p (Multiset.mem_filter.mp hp).1), Multiset.map_id]

private theorem natDegree_roughPart_add_smoothPart (L : ℕ) {f : Polynomial F} (hf : f ≠ 0) :
    (polynomialRoughPart L f).natDegree + (polynomialSmoothPart L f).natDegree = f.natDegree := by
  have h := congrArg Polynomial.natDegree (polynomial_eq_leadingCoeff_mul_roughPart_mul_smoothPart L f)
  rwa [natDegree_mul (mul_ne_zero (C_ne_zero.mpr (leadingCoeff_ne_zero.mpr hf))
    (monic_polynomialRoughPart L f).ne_zero) (monic_polynomialSmoothPart L f).ne_zero,
    natDegree_C_mul (leadingCoeff_ne_zero.mpr hf)] at h

private theorem parts_of_scalar_mul (L : ℕ) (c : Fˣ) {g h : Polynomial F}
    (hg : g.Monic) (hh : h.Monic)
    (hrough : ∀ p ∈ normalizedFactors g, L < p.natDegree)
    (hsmooth : ∀ p ∈ normalizedFactors h, p.natDegree ≤ L) :
    polynomialRoughPart L (C (c : F) * g * h) = g ∧
      polynomialSmoothPart L (C (c : F) * g * h) = h := by
  have hC := C_ne_zero.mpr c.ne_zero
  have hfac : normalizedFactors (C (c : F) * g * h) = normalizedFactors g + normalizedFactors h := by
    rw [normalizedFactors_mul (mul_ne_zero hC hg.ne_zero) hh.ne_zero,
      normalizedFactors_mul hC hg.ne_zero, normalizedFactors_of_isUnit (isUnit_C.mpr c.isUnit),
      zero_add]
  have hprod {p : Polynomial F} (hp : p.Monic) : (normalizedFactors p).prod = p := by
    simpa only [hp, Monic.leadingCoeff, C_1, one_mul] using leadingCoeff_mul_prod_normalizedFactors p
  constructor
  · rw [polynomialRoughPart, polynomialRoughFactors, hfac, Multiset.filter_add,
      Multiset.filter_eq_self.mpr hrough,
      Multiset.filter_eq_nil.mpr (fun p hp ↦ Nat.not_lt.mpr (hsmooth p hp)), add_zero, hprod hg]
  · rw [polynomialSmoothPart, hfac, Multiset.filter_add,
      Multiset.filter_eq_nil.mpr (fun p hp ↦ Nat.not_le.mpr (hrough p hp)),
      Multiset.filter_eq_self.mpr hsmooth, zero_add, hprod hh]

private def marked (N R : ℕ) (f : Polynomial F) : Prop :=
  Squarefree (polynomialRoughPart 480 f) ∧ (polynomialRoughPart 480 f).natDegree = N - R

private noncomputable def markedFiber (F : Type*) [Field F] [Fintype F] (N R k : ℕ) :
    Finset (Polynomial F) :=
  (polynomialDegreeLayer F (N - R + k)).filter (marked N R)

variable [Fintype F]

private theorem mem_markedFiber {N R k : ℕ} {f : Polynomial F} :
    f ∈ markedFiber F N R k ↔ (f ≠ 0 ∧ f.natDegree = N - R + k) ∧ marked N R f := by
  simp only [markedFiber, Finset.mem_filter, mem_polynomialDegreeLayer]

private noncomputable def markedFiberEquiv (N R k : ℕ) :
    (Fˣ × polynomialSquarefreeRoughLayer F 480 (N - R) × polynomialSmoothLayer F 480 k) ≃
      markedFiber F N R k := by
  let toFiber (x : Fˣ × polynomialSquarefreeRoughLayer F 480 (N - R) ×
      polynomialSmoothLayer F 480 k) : markedFiber F N R k := by
    refine ⟨C (x.1 : F) * x.2.1.1 * x.2.2.1, ?_⟩
    rcases x with ⟨c, ⟨g, hg⟩, ⟨h, hh⟩⟩
    obtain ⟨hgm, hgd, hgs, hgr⟩ := mem_polynomialSquarefreeRoughLayer.mp hg
    obtain ⟨hhm, hhd, hhr⟩ := mem_polynomialSmoothLayer.mp hh
    have hC := C_ne_zero.mpr c.ne_zero
    rw [markedFiber, Finset.mem_filter, mem_polynomialDegreeLayer, marked,
      (parts_of_scalar_mul 480 c hgm hhm hgr hhr).1,
      natDegree_mul (mul_ne_zero hC hgm.ne_zero) hhm.ne_zero, natDegree_C_mul c.ne_zero, hgd, hhd]
    exact ⟨⟨mul_ne_zero (mul_ne_zero hC hgm.ne_zero) hhm.ne_zero, rfl⟩, hgs, rfl⟩
  let fromFiber (x : markedFiber F N R k) :
      Fˣ × polynomialSquarefreeRoughLayer F 480 (N - R) × polynomialSmoothLayer F 480 k := by
    have hx := mem_markedFiber.mp x.2
    let f := x.1
    refine ⟨Units.mk0 f.leadingCoeff (leadingCoeff_ne_zero.mpr hx.1.1),
      ⟨polynomialRoughPart 480 f, ?_⟩, ⟨polynomialSmoothPart 480 f, ?_⟩⟩
    · refine mem_polynomialSquarefreeRoughLayer.mpr ⟨monic_polynomialRoughPart 480 f, hx.2.2, hx.2.1, ?_⟩
      rw [normalizedFactors_polynomialRoughPart, polynomialRoughFactors]
      exact fun p hp ↦ (Multiset.mem_filter.mp hp).2
    · have hdeg := natDegree_roughPart_add_smoothPart 480 hx.1.1
      refine mem_polynomialSmoothLayer.mpr ⟨monic_polynomialSmoothPart 480 f, ?_, ?_⟩
      · have hdF := hx.1.2
        have hdR := hx.2.2
        change (polynomialSmoothPart 480 x.1).natDegree = k
        omega
      · rw [normalizedFactors_polynomialSmoothPart]
        exact fun p hp ↦ (Multiset.mem_filter.mp hp).2
  refine ⟨toFiber, fromFiber, ?_, ?_⟩
  · rintro ⟨c, ⟨g, hg⟩, ⟨h, hh⟩⟩
    obtain ⟨hgm, _, _, hgr⟩ := mem_polynomialSquarefreeRoughLayer.mp hg
    obtain ⟨hhm, _, hhr⟩ := mem_polynomialSmoothLayer.mp hh
    have ⟨hrough, hsmooth⟩ := parts_of_scalar_mul 480 c hgm hhm hgr hhr
    refine Prod.ext (Units.ext ?_) (Prod.ext (Subtype.ext hrough) (Subtype.ext hsmooth))
    change (C (c : F) * g * h).leadingCoeff = (c : F)
    rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, hgm.leadingCoeff, hhm.leadingCoeff,
      mul_one, mul_one]
  · intro f
    apply Subtype.ext
    exact polynomial_eq_leadingCoeff_mul_roughPart_mul_smoothPart 480 f.1

private theorem card_markedFiber (N R k : ℕ) :
    (markedFiber F N R k).card = (Fintype.card F - 1) *
      (polynomialSquarefreeRoughLayer F 480 (N - R)).card * (polynomialSmoothLayer F 480 k).card := by
  simpa only [Fintype.card_prod, Fintype.card_units, Fintype.card_coe, mul_assoc] using
    (Fintype.card_congr (markedFiberEquiv (F := F) N R k)).symm

private noncomputable def markedSelection (F : Type*) [Field F] [Fintype F]
    (A : Set ℕ) (N R : ℕ) : Finset (Polynomial F) :=
  (polynomialDegreeLTFinset F (N + 1)).filter fun f ↦ f ∈ polynomialDeficitSet A N ∧ marked N R f

omit [Fintype F] in
private theorem degree_ge_of_marked {N R : ℕ} {f : Polynomial F}
    (hf : f ≠ 0) (hm : marked N R f) : N - R ≤ f.natDegree := by
  rw [← hm.2, ← natDegree_roughPart_add_smoothPart 480 hf]
  exact Nat.le_add_right ..

private theorem card_markedSelection (A : Set ℕ) {N R : ℕ} (hRN : R ≤ N) :
    (markedSelection F A N R).card =
      ∑ k ∈ Finset.range (R + 1), if R - k ∈ A then (markedFiber F N R k).card else 0 := by
  have hmaps : Set.MapsTo (fun f : Polynomial F ↦ f.natDegree - (N - R))
      (markedSelection F A N R : Set (Polynomial F)) (Finset.range (R + 1)) := by
    intro f hf
    have hN := (Finset.mem_filter.mp hf).2.1.2.1
    change f.natDegree - (N - R) ∈ Finset.range (R + 1)
    exact Finset.mem_range.mpr (by omega)
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro k hk
  have hkR := Finset.mem_range.mp hk
  have hmem (f : Polynomial F) :
      f ∈ markedSelection F A N R ∧ f.natDegree - (N - R) = k ↔
      f ∈ markedFiber F N R k ∧ R - k ∈ A := by
    simp only [markedSelection, Finset.mem_filter, mem_polynomialDegreeLTFinset,
      polynomialDeficitSet, Set.mem_setOf_eq, markedFiber, mem_polynomialDegreeLayer]
    constructor
    · rintro ⟨⟨_, ⟨hf, _, hA⟩, hm⟩, hkf⟩
      have hlow := degree_ge_of_marked hf hm
      exact ⟨⟨⟨hf, by omega⟩, hm⟩, (show N - f.natDegree = R - k by omega) ▸ hA⟩
    · rintro ⟨⟨⟨hf, hd⟩, hm⟩, hA⟩
      refine ⟨⟨?_, ⟨hf, by omega, ?_⟩, hm⟩, by omega⟩
      · rw [degree_eq_natDegree hf, Nat.cast_lt]
        omega
      · exact (show R - k = N - f.natDegree by omega) ▸ hA
  have heq : ((markedSelection F A N R).filter fun f ↦ f.natDegree - (N - R) = k) =
      if R - k ∈ A then markedFiber F N R k else ∅ := by
    ext f
    by_cases hA : R - k ∈ A <;> simp [Finset.mem_filter, hmem, hA]
  rw [heq]
  split <;> simp

private theorem card_replacement_sub_baseline_eq_marked_sub (N R : ℕ) :
    (((polynomialDegreeLTFinset F (N + 1)).filter
        (· ∈ polynomialDeficitReplacement N R)).card : ℤ) -
      (((polynomialDegreeLTFinset F (N + 1)).filter
        (· ∈ polynomialDeficitSet greedyExponents N)).card : ℤ) =
      ((markedSelection F (polynomialDeficitWitness : Set ℕ) N R).card : ℤ) -
      (markedSelection F greedyExponents N R).card := by
  let B := polynomialDegreeLTFinset F (N + 1)
  let X := B.filter (· ∈ polynomialDeficitReplacement N R)
  let Y := B.filter (· ∈ polynomialDeficitSet greedyExponents N)
  change (X.card : ℤ) - Y.card = _
  have hx : X.filter (marked N R) = markedSelection F (polynomialDeficitWitness : Set ℕ) N R := by
    ext f
    simp only [X, B, Finset.mem_filter, mem_polynomialDeficitReplacement_iff, marked,
      markedSelection, polynomialDeficitSet, Set.mem_setOf_eq, Finset.mem_coe]
    tauto
  have hy : Y.filter (marked N R) = markedSelection F greedyExponents N R := by
    simp only [Y, B, Finset.filter_filter, markedSelection]
  have hcommon : (X.filter fun f ↦ ¬ marked N R f) = Y.filter fun f ↦ ¬ marked N R f := by
    ext f
    simp only [X, Y, Finset.mem_filter, mem_polynomialDeficitReplacement_iff, marked,
      polynomialDeficitSet, Set.mem_setOf_eq]
    tauto
  have hcX : ((X.filter (marked N R)).card : ℤ) +
      ((X.filter fun f ↦ ¬ marked N R f).card : ℤ) = X.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := X) (marked N R)
  have hcY : ((Y.filter (marked N R)).card : ℤ) +
      ((Y.filter fun f ↦ ¬ marked N R f).card : ℤ) = Y.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := Y) (marked N R)
  rw [hx, hcommon] at hcX
  rw [hy] at hcY
  omega

/-- The exact count change in the article's modified degree ball. The signed
convolution is taken over the actual smooth-polynomial degree layers. -/
theorem card_polynomialDeficitReplacement_sub {N R : ℕ} (hRN : R ≤ N) :
    (((polynomialDegreeLTFinset F (N + 1)).filter
        (· ∈ polynomialDeficitReplacement N R)).card : ℤ) -
      (((polynomialDegreeLTFinset F (N + 1)).filter
        (· ∈ polynomialDeficitSet greedyExponents N)).card : ℤ) =
      ((Fintype.card F - 1 : ℕ) : ℤ) *
        ((polynomialSquarefreeRoughLayer F 480 (N - R)).card : ℤ) *
        (∑ k ∈ Finset.range (R + 1),
          ((polynomialSmoothLayer F 480 k).card : ℤ) * polynomialDeficitDifference (R - k)) := by
  rw [card_replacement_sub_baseline_eq_marked_sub, card_markedSelection _ hRN,
    card_markedSelection _ hRN, Nat.cast_sum, Nat.cast_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [card_markedFiber (F := F) N R k]
  by_cases hD : R - k ∈ polynomialDeficitWitness <;> by_cases hA : R - k ∈ greedyExponents <;>
    simp [polynomialDeficitDifference, hD, hA]

/-- The replacement gain after division by the full degree-ball size. -/
theorem polynomialBallProportion_replacement_sub {N R : ℕ} (hRN : R ≤ N) :
    polynomialBallProportion (polynomialDeficitReplacement (F := F) N R) N -
      polynomialBallProportion (polynomialDeficitSet (F := F) greedyExponents N) N =
      ((Fintype.card F : ℝ) - 1) *
        ((polynomialSquarefreeRoughLayer F 480 (N - R)).card / (Fintype.card F : ℝ) ^ (N - R)) *
        ((↑(∑ k ∈ Finset.range (R + 1),
          ((polynomialSmoothLayer F 480 k).card : ℤ) * polynomialDeficitDifference (R - k)) : ℝ) /
          (Fintype.card F : ℝ) ^ (R + 1)) := by
  have hcount := congrArg (fun d : ℤ ↦ (d : ℝ)) (card_polynomialDeficitReplacement_sub (F := F) hRN)
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_mul] at hcount
  have hsplit : (Fintype.card F : ℝ) ^ (N + 1) =
      (Fintype.card F : ℝ) ^ (N - R) * (Fintype.card F : ℝ) ^ (R + 1) := by
    rw [← pow_add, show N - R + (R + 1) = N + 1 by omega]
  unfold polynomialBallProportion
  rw [← sub_div, hcount, hsplit, div_mul_eq_div_div,
    Nat.cast_sub (by exact Fintype.card_pos), Nat.cast_one]
  ring

end GRHArticle.ProgressionFree
