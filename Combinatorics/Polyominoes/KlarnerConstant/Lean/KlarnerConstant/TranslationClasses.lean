import KlarnerConstant.Counting

/-!
# Translation classes of fixed polyominoes

This module identifies the finite counting type `NormalizedPolyomino n` with
the quotient of all `n`-cell polyominoes by integer translation.

The relation used in the quotient is the geometric one: `P` and `Q` are
related when `Q` is literally `P.translate v` for some lattice vector `v`.
The main technical fact is that this relation is exactly equality of the two
canonical southwest normalizations.  Consequently every translation class
has a normalized representative and that representative is unique.
-/

namespace LeanProofs.KlarnerConstant

namespace Polyomino

/-- Translation by the zero lattice vector does nothing. -/
@[simp]
theorem translate_zero (P : Polyomino) : P.translate (0 : Cell) = P := by
  apply Polyomino.ext
  simp [Polyomino.cells_translate]

/-- Successive translations compose in the order in which the translation
vectors act on cells. -/
theorem translate_translate (P : Polyomino) (v w : Cell) :
    (P.translate v).translate w = P.translate (w + v) := by
  apply Polyomino.ext
  simp only [Polyomino.cells_translate, Finset.image_image]
  apply Finset.image_congr
  intro c _
  simp [Function.comp_apply, add_assoc]

/-- Translation preserves the number of cells. -/
@[simp]
theorem card_cells_translate (P : Polyomino) (v : Cell) :
    (P.translate v).cells.card = P.cells.card := by
  simp only [Polyomino.cells_translate]
  exact Finset.card_image_of_injective P.cells (add_right_injective v)

/-- Southwest normalization is invariant under every lattice translation. -/
theorem normalize_translate (P : Polyomino) (v : Cell) :
    (P.translate v).normalize = P.normalize := by
  unfold Polyomino.normalize
  rw [Polyomino.southwestAnchor_translate, Polyomino.translate_translate]
  have hv : -(v + P.southwestAnchor) + v = -P.southwestAnchor := by
    apply Prod.ext <;> simp
  rw [hv]

/-- Normalization is idempotent. -/
@[simp]
theorem normalize_normalize (P : Polyomino) :
    P.normalize.normalize = P.normalize := by
  change (P.translate (-P.southwestAnchor)).normalize = P.normalize
  exact P.normalize_translate (-P.southwestAnchor)

end Polyomino

/-- A polyomino with a specified number of cells, before quotienting by
translation. -/
structure FixedSizePolyomino (n : ℕ) where
  toPolyomino : Polyomino
  card_cells : toPolyomino.cells.card = n

namespace FixedSizePolyomino

@[ext]
theorem ext {n : ℕ} {P Q : FixedSizePolyomino n}
    (h : P.toPolyomino = Q.toPolyomino) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

/-- Translate an `n`-cell polyomino without changing its size index. -/
def translate {n : ℕ} (P : FixedSizePolyomino n) (v : Cell) :
    FixedSizePolyomino n where
  toPolyomino := P.toPolyomino.translate v
  card_cells := by
    calc
      (P.toPolyomino.translate v).cells.card = P.toPolyomino.cells.card :=
        Polyomino.card_cells_translate P.toPolyomino v
      _ = n := P.card_cells

@[simp]
theorem toPolyomino_translate {n : ℕ} (P : FixedSizePolyomino n) (v : Cell) :
    (P.translate v).toPolyomino = P.toPolyomino.translate v :=
  rfl

@[simp]
theorem translate_zero {n : ℕ} (P : FixedSizePolyomino n) :
    P.translate (0 : Cell) = P := by
  apply FixedSizePolyomino.ext
  exact P.toPolyomino.translate_zero

theorem translate_translate {n : ℕ} (P : FixedSizePolyomino n) (v w : Cell) :
    (P.translate v).translate w = P.translate (w + v) := by
  apply FixedSizePolyomino.ext
  exact P.toPolyomino.translate_translate v w

/-- The canonical normalized representative of a fixed-size polyomino. -/
noncomputable def normalize {n : ℕ} (P : FixedSizePolyomino n) :
    NormalizedPolyomino n where
  toPolyomino := P.toPolyomino.normalize
  southwestAnchor_eq := P.toPolyomino.southwestAnchor_normalize
  card_cells := by
    calc
      P.toPolyomino.normalize.cells.card = P.toPolyomino.cells.card := by
        unfold Polyomino.normalize
        exact Polyomino.card_cells_translate _ _
      _ = n := P.card_cells

@[simp]
theorem toPolyomino_normalize {n : ℕ} (P : FixedSizePolyomino n) :
    P.normalize.toPolyomino = P.toPolyomino.normalize :=
  rfl

end FixedSizePolyomino

namespace NormalizedPolyomino

/-- Forget that the southwest anchor is the origin. -/
def toFixedSize {n : ℕ} (P : NormalizedPolyomino n) :
    FixedSizePolyomino n where
  toPolyomino := P.toPolyomino
  card_cells := P.card_cells

@[simp]
theorem toPolyomino_toFixedSize {n : ℕ} (P : NormalizedPolyomino n) :
    P.toFixedSize.toPolyomino = P.toPolyomino :=
  rfl

/-- A polyomino whose southwest anchor is already the origin is fixed by
normalization. -/
theorem normalize_toPolyomino {n : ℕ} (P : NormalizedPolyomino n) :
    P.toPolyomino.normalize = P.toPolyomino := by
  unfold Polyomino.normalize
  rw [P.southwestAnchor_eq]
  change P.toPolyomino.translate (0 : Cell) = P.toPolyomino
  exact P.toPolyomino.translate_zero

end NormalizedPolyomino

/-- `Q` is translation-equivalent to `P` when it is obtained from `P` by one
integer lattice translation. -/
def TranslationEquivalent {n : ℕ}
    (P Q : FixedSizePolyomino n) : Prop :=
  ∃ v : Cell, Q.toPolyomino = P.toPolyomino.translate v

namespace TranslationEquivalent

theorem refl {n : ℕ} (P : FixedSizePolyomino n) :
    TranslationEquivalent P P :=
  ⟨0, P.toPolyomino.translate_zero.symm⟩

theorem symm {n : ℕ} {P Q : FixedSizePolyomino n}
    (h : TranslationEquivalent P Q) : TranslationEquivalent Q P := by
  rcases h with ⟨v, hv⟩
  refine ⟨-v, ?_⟩
  rw [hv, Polyomino.translate_translate]
  simpa using P.toPolyomino.translate_zero.symm

theorem trans {n : ℕ} {P Q R : FixedSizePolyomino n}
    (hPQ : TranslationEquivalent P Q)
    (hQR : TranslationEquivalent Q R) : TranslationEquivalent P R := by
  rcases hPQ with ⟨v, hv⟩
  rcases hQR with ⟨w, hw⟩
  refine ⟨w + v, ?_⟩
  calc
    R.toPolyomino = Q.toPolyomino.translate w := hw
    _ = (P.toPolyomino.translate v).translate w := by rw [hv]
    _ = P.toPolyomino.translate (w + v) :=
      P.toPolyomino.translate_translate v w

end TranslationEquivalent

/-- Translation equivalence as a setoid on all fixed-size representatives. -/
def translationSetoid (n : ℕ) : Setoid (FixedSizePolyomino n) where
  r := TranslationEquivalent
  iseqv := ⟨TranslationEquivalent.refl, TranslationEquivalent.symm,
    TranslationEquivalent.trans⟩

/-- Translation classes of fixed `n`-cell polyominoes. -/
abbrev PolyominoTranslationClass (n : ℕ) :=
  Quotient (translationSetoid n)

namespace FixedSizePolyomino

/-- Translation-equivalent polyominoes have the same canonical normalized
representative. -/
theorem normalize_eq_of_translationEquivalent {n : ℕ}
    {P Q : FixedSizePolyomino n} (h : TranslationEquivalent P Q) :
    P.normalize = Q.normalize := by
  apply NormalizedPolyomino.ext
  rcases h with ⟨v, hv⟩
  change P.toPolyomino.normalize = Q.toPolyomino.normalize
  rw [hv, Polyomino.normalize_translate]

/-- Equality of canonical normal forms implies literal translation
equivalence. -/
theorem translationEquivalent_of_normalize_eq {n : ℕ}
    {P Q : FixedSizePolyomino n} (h : P.normalize = Q.normalize) :
    TranslationEquivalent P Q := by
  have hpoly : P.toPolyomino.normalize = Q.toPolyomino.normalize :=
    congrArg NormalizedPolyomino.toPolyomino h
  have htranslated := congrArg
    (fun R : Polyomino ↦ R.translate Q.toPolyomino.southwestAnchor) hpoly
  have hpq :
      P.toPolyomino.translate
          (Q.toPolyomino.southwestAnchor - P.toPolyomino.southwestAnchor) =
        Q.toPolyomino := by
    simpa [Polyomino.normalize, Polyomino.translate_translate,
      sub_eq_add_neg] using htranslated
  exact ⟨Q.toPolyomino.southwestAnchor - P.toPolyomino.southwestAnchor,
    hpq.symm⟩

/-- Translation equivalence is exactly equality of southwest-normalized
representatives. -/
theorem translationEquivalent_iff_normalize_eq {n : ℕ}
    {P Q : FixedSizePolyomino n} :
    TranslationEquivalent P Q ↔ P.normalize = Q.normalize :=
  ⟨normalize_eq_of_translationEquivalent,
    translationEquivalent_of_normalize_eq⟩

/-- Every fixed-size polyomino is translation-equivalent to its canonical
normalization. -/
theorem translationEquivalent_normalize {n : ℕ}
    (P : FixedSizePolyomino n) :
    TranslationEquivalent P P.normalize.toFixedSize := by
  refine ⟨-P.toPolyomino.southwestAnchor, ?_⟩
  rfl

/-- Every translation class has a normalized representative. -/
theorem exists_normalized_representative {n : ℕ}
    (P : FixedSizePolyomino n) :
    ∃ N : NormalizedPolyomino n,
      TranslationEquivalent P N.toFixedSize :=
  ⟨P.normalize, P.translationEquivalent_normalize⟩

end FixedSizePolyomino

namespace NormalizedPolyomino

/-- Two normalized fixed-size polyominoes which are translates are equal. -/
theorem eq_of_translationEquivalent {n : ℕ}
    {P Q : NormalizedPolyomino n}
    (h : TranslationEquivalent P.toFixedSize Q.toFixedSize) : P = Q := by
  have hnorm : P.toFixedSize.normalize = Q.toFixedSize.normalize :=
    FixedSizePolyomino.normalize_eq_of_translationEquivalent h
  apply NormalizedPolyomino.ext
  have hpoly := congrArg NormalizedPolyomino.toPolyomino hnorm
  change P.toPolyomino.normalize = Q.toPolyomino.normalize at hpoly
  rw [P.normalize_toPolyomino, Q.normalize_toPolyomino] at hpoly
  exact hpoly

end NormalizedPolyomino

/-- Canonically normalize a translation class. -/
noncomputable def translationClassNormalizer (n : ℕ) :
    PolyominoTranslationClass n → NormalizedPolyomino n :=
  Quotient.lift FixedSizePolyomino.normalize fun _P _Q h ↦
    FixedSizePolyomino.normalize_eq_of_translationEquivalent h

/-- Put a normalized polyomino into its translation class. -/
def NormalizedPolyomino.toTranslationClass {n : ℕ}
    (P : NormalizedPolyomino n) : PolyominoTranslationClass n :=
  Quotient.mk (translationSetoid n) P.toFixedSize

/-- Translation classes of `n`-cell polyominoes are canonically equivalent to
normalized `n`-cell polyominoes. -/
noncomputable def translationClassEquivNormalizedPolyomino (n : ℕ) :
    PolyominoTranslationClass n ≃ NormalizedPolyomino n where
  toFun := translationClassNormalizer n
  invFun := NormalizedPolyomino.toTranslationClass
  left_inv := by
    intro C
    refine Quotient.inductionOn C ?_
    intro P
    change Quotient.mk (translationSetoid n) P.normalize.toFixedSize =
      Quotient.mk (translationSetoid n) P
    exact (Quotient.sound P.translationEquivalent_normalize).symm
  right_inv := by
    intro P
    apply NormalizedPolyomino.ext
    change P.toPolyomino.normalize = P.toPolyomino
    exact P.normalize_toPolyomino

/-- The quotient of fixed-size polyominoes by translation is finite. -/
noncomputable instance polyominoTranslationClassFintype (n : ℕ) :
    Fintype (PolyominoTranslationClass n) :=
  Fintype.ofEquiv (NormalizedPolyomino n)
    (translationClassEquivNormalizedPolyomino n).symm

/-- `fixedPolyominoCount` is literally the number of translation classes of
fixed-size polyominoes. -/
theorem fixedPolyominoCount_eq_card_translationClasses (n : ℕ) :
    fixedPolyominoCount n = Fintype.card (PolyominoTranslationClass n) := by
  exact (Fintype.card_congr
    (translationClassEquivNormalizedPolyomino n)).symm

end LeanProofs.KlarnerConstant
