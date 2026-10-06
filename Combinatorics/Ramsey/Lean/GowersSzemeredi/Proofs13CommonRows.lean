import GowersSzemeredi.Proofs13RowSelection

/-!
# Interpreting the common-row count as a set cardinality

This connects the moment calculation to the actual translated subset of the
paper and to its row coefficients. Original-domain containment remains an
explicit hypothesis, rather than an implicit consequence of Stage 13.7.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset

namespace LeanProofs.GowersSzemeredi

/-- The columns of `B` on the row indexed by the displacement `h`. -/
def translatedRow {N : Nat} (S : Finset (ZMod N)) (B : Finset (Pair N))
    (y h : ZMod N) : Finset (ZMod N) :=
  S.filter fun x ↦ (x, y + h) ∈ B

/-- A translated row is in bijection with the corresponding fibre of `B`. -/
theorem translatedRow_card {N : Nat} (S : Finset (ZMod N))
    (B : Finset (Pair N)) (y h : ZMod N)
    (hB : ∀ z ∈ B, z.1 ∈ S) :
    (translatedRow S B y h).card = (B.filter fun z ↦ z.2 - y = h).card := by
  classical
  apply Finset.card_bij (fun x _ ↦ (x, y + h))
  · intro x hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).2, by simp⟩
  · intro x hx z hz heq
    exact congrArg Prod.fst heq
  · intro z hz
    obtain ⟨hzB, hzy⟩ := Finset.mem_filter.mp hz
    have heq : y + h = z.2 := by rw [← hzy]; abel
    refine ⟨z.1, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨hB z hzB, by simpa only [heq, Prod.mk.eta] using hzB⟩
    · exact Prod.ext rfl heq

/-- Sum the row sizes over any set of displacements. -/
theorem translatedRow_sum {N : Nat} (S : Finset (ZMod N))
    (B : Finset (Pair N)) (y : ZMod N) (J : Finset (ZMod N))
    (hB : ∀ z ∈ B, z.1 ∈ S) :
    ∑ h ∈ J, (translatedRow S B y h).card =
      (B.filter fun z ↦ z.2 - y ∈ J).card := by
  classical
  simp_rw [translatedRow_card S B y _ hB]
  rw [Finset.sum_card_fiberwise_eq_card_filter]

/-- The common rows of two columns, within the available displacement set. -/
def commonTranslatedRows {N : Nat} (B : Finset (Pair N))
    (I : Finset (ZMod N)) (y x₁ x₂ : ZMod N) : Finset (ZMod N) :=
  I.filter fun h ↦ (x₁, y + h) ∈ B ∧ (x₂, y + h) ∈ B

/-- The abstract pair mass is exactly the size of the retained subset `C`. -/
theorem rowPairMass_eq_common_card {N : Nat} (S I : Finset (ZMod N))
    (B : Finset (Pair N)) (y x₁ x₂ : ZMod N)
    (hB : ∀ z ∈ B, z.1 ∈ S) (h₁ : x₁ ∈ S) (h₂ : x₂ ∈ S) :
    rowPairMass I (translatedRow S B y) x₁ x₂ =
      ((B.filter fun z ↦ z.2 - y ∈ commonTranslatedRows B I y x₁ x₂).card : Real) := by
  classical
  rw [← translatedRow_sum S B y _ hB, Nat.cast_sum]
  unfold rowPairMass commonTranslatedRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro h hh
  simp only [translatedRow, Finset.mem_filter, h₁, h₂, true_and]

/-- Coefficients may be chosen on every affine row, even on rows with zero
or one point where the paper's assertion of uniqueness does not apply. -/
theorem exists_translated_row_coefficients {N : Nat}
    (S I : Finset (ZMod N)) (B : Finset (Pair N)) (y : ZMod N)
    (phi : Pair N → ZMod N) (hB : ∀ z ∈ B, z.1 ∈ S)
    (hlinear : ∀ h ∈ I, LinearOn (translatedRow S B y h) (fun x ↦ phi (x, y + h))) :
    ∃ a c : ZMod N → ZMod N, ∀ h ∈ I, ∀ x, (x, y + h) ∈ B →
      phi (x, y + h) = a h + c h * x := by
  classical
  have hchoice : ∀ h, ∃ a c : ZMod N, ∀ x, h ∈ I → (x, y + h) ∈ B →
      phi (x, y + h) = a + c * x := by
    intro h
    by_cases hh : h ∈ I
    · obtain ⟨c, a, heq⟩ := hlinear h hh
      refine ⟨a, c, ?_⟩
      intro x _ hx
      simpa only [add_comm] using heq x (Finset.mem_filter.mpr ⟨hB _ hx, hx⟩)
    · exact ⟨0, 0, fun _ hi _ ↦ (hh hi).elim⟩
  choose a c heq using hchoice
  exact ⟨a, c, fun h hh x hx ↦ heq h x hh hx⟩

/-- Assemble the combinatorial and algebraic parts of Lemma 13.8 from a
moment bound. This form keeps the exact quadratic diagonal loss. -/
theorem exists_freiman_common_rows_of_moments {N : Nat} [Fact N.Prime]
    (ctx : Section13Context N) (S I : Finset (ZMod N))
    (B : Finset (Pair N)) (y : ZMod N) (hS : S.Nonempty)
    (hBA : B ⊆ ctx.A) (hB : ∀ z ∈ B, z.1 ∈ S)
    (hlinear : ∀ h ∈ I, LinearOn (translatedRow S B y h)
      (fun x ↦ ctx.phi (x, y + h)))
    {t : Real} (ht : 0 < t)
    (hmoment : t * (S.card : Real) ^ 2 ≤
      (∑ h ∈ I, ((translatedRow S B y h).card : Real) ^ 3) -
      ∑ h ∈ I, ((translatedRow S B y h).card : Real) ^ 2) :
    ∃ a c : ZMod N → ZMod N, ∃ J : Finset (ZMod N),
      (∀ h ∈ I, ∀ x, (x, y + h) ∈ B → ctx.phi (x, y + h) = a h + c h * x) ∧
      J ⊆ I ∧ FreimanHom 8 J (fun h ↦ (a h, c h)) ∧
      t ≤ (B.filter fun z ↦ z.2 - y ∈ J).card := by
  classical
  obtain ⟨a, c, hrow⟩ := exists_translated_row_coefficients S I B y ctx.phi hB hlinear
  obtain ⟨x₁, hx₁, x₂, hx₂, hne, hmass⟩ :=
    exists_distinct_rowPairMass_of_moments S I (translatedRow S B y) hS
      (fun _ _ ↦ Finset.filter_subset _ _) ht hmoment
  let J := commonTranslatedRows B I y x₁ x₂
  have hJI : J ⊆ I := Finset.filter_subset _ _
  refine ⟨a, c, J, hrow, hJI, ?_, ?_⟩
  · exact lemma138_coefficients_freiman ctx hBA hne
      (fun h hh ↦ (Finset.mem_filter.mp hh).2.1)
      (fun h hh ↦ (Finset.mem_filter.mp hh).2.2)
      (fun h hh x hx ↦ hrow h (hJI hh) x hx)
  · simpa only [rowPairMass_eq_common_card S I B y x₁ x₂ hB hx₁ hx₂] using hmass

/-- The total translated-row mass equals the original set size when all
points are supported on the given columns and displacements. -/
theorem translatedRow_total {N : Nat} (S I : Finset (ZMod N))
    (B : Finset (Pair N)) (y : ZMod N)
    (hB : B ⊆ S.product (translateFinset I y)) :
    ∑ h ∈ I, (translatedRow S B y h).card = B.card := by
  classical
  rw [translatedRow_sum S B y I (fun z hz ↦ (Finset.mem_product.mp (hB hz)).1)]
  congr 1
  apply Finset.filter_eq_self.mpr
  intro z hz
  obtain ⟨h, hh, heq⟩ := Finset.mem_image.mp (Finset.mem_product.mp (hB hz)).2
  simpa only [← heq, add_sub_cancel_left] using hh

/-- A quantitative form of common-row extraction. It retains the additive
 diagonal loss `m`, rather than rounding the output down to half the cubic
 contribution. This is an auxiliary improvement, not a final Szemeredi bound. -/
theorem exists_freiman_common_rows_of_two_densities {N : Nat} [Fact N.Prime]
    (ctx : Section13Context N) (S I : Finset (ZMod N))
    (B : Finset (Pair N)) (y : ZMod N) (hS : S.Nonempty)
    (hBA : B ⊆ ctx.A) (hB : B ⊆ S.product (translateFinset I y))
    (hlinear : ∀ h ∈ I, LinearOn (translatedRow S B y h)
      (fun x ↦ ctx.phi (x, y + h)))
    {δ β m : Real} (hδ : 0 < δ) (hβ : 0 < β) (hm : 0 < m)
    (hIm : (I.card : Real) ≤ m)
    (hrel : δ * S.card * I.card ≤ B.card)
    (habs : β * m * S.card ≤ B.card)
    (hwidth : 1 < δ ^ 2 * β * S.card) :
    ∃ a c : ZMod N → ZMod N, ∃ J : Finset (ZMod N),
      (∀ h ∈ I, ∀ x, (x, y + h) ∈ B → ctx.phi (x, y + h) = a h + c h * x) ∧
      J ⊆ I ∧ FreimanHom 8 J (fun h ↦ (a h, c h)) ∧
      m * (δ ^ 2 * β * S.card - 1) ≤ (B.filter fun z ↦ z.2 - y ∈ J).card := by
  classical
  have hn : (0 : Real) < S.card := by exact_mod_cast hS.card_pos
  have htotal : (∑ h ∈ I, ((translatedRow S B y h).card : Real)) = B.card := by
    exact_mod_cast translatedRow_total S I B y hB
  have hI : I.Nonempty := by
    by_contra hi
    have hi0 : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hi
    have hz : (B.card : Real) = 0 := by simpa [hi0] using htotal.symm
    have hp : 0 < β * m * S.card := by positivity
    rw [hz] at habs
    linarith
  have hcube := cubic_row_moment_of_two_bounds I
    (fun h ↦ ((translatedRow S B y h).card : Real)) (fun _ _ ↦ Nat.cast_nonneg _) hI
    (mul_nonneg hδ.le hn.le) (show 0 ≤ β * m * S.card by positivity)
    (by simpa only [htotal] using hrel) (by simpa only [htotal] using habs)
  have hdiag := quadratic_row_moment_le S I (translatedRow S B y)
    (fun _ _ ↦ Finset.filter_subset _ _) hIm
  apply exists_freiman_common_rows_of_moments ctx S I B y hS hBA
    (fun z hz ↦ (Finset.mem_product.mp (hB hz)).1) hlinear
    (mul_pos hm (sub_pos.mpr hwidth))
  nlinarith [hcube, hdiag]

end LeanProofs.GowersSzemeredi
