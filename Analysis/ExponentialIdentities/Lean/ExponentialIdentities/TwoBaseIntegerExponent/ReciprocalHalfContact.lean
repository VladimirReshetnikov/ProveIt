import Mathlib.Tactic

/-!
# Reciprocal half-contact for finite coefficient vectors

This module isolates the finite coefficient argument behind the half-degree ceiling for two
equal-degree reciprocal polynomials.  The coefficient vector below is intended to be the
difference of the two polynomials.  Reciprocity makes the vector invariant under reversal,
and contact order `K` at infinity says that its first nonzero entry from the top occurs in
degree `D - K`.

The main theorem gives `2 * K ≤ D`.  In the sharp even case the vector is supported only at
the middle coefficient.  The companion odd-degree theorem records the corrected floor-sharp
case: the two adjacent middle coefficients are both present and equal.
-/

namespace LeanProofs.TwoBaseIntegerExponent.ReciprocalHalfContact

variable {R : Type*} [Zero R]

/-- Reversal of an index in a coefficient vector of length `D + 1`. -/
def reverseIndex (D : ℕ) (i : Fin (D + 1)) : Fin (D + 1) :=
  ⟨D - i, by omega⟩

@[simp] theorem reverseIndex_val (D : ℕ) (i : Fin (D + 1)) :
    (reverseIndex D i : ℕ) = D - i := rfl

@[simp] theorem reverseIndex_reverseIndex (D : ℕ) (i : Fin (D + 1)) :
    reverseIndex D (reverseIndex D i) = i := by
  apply Fin.ext
  simp only [reverseIndex_val]
  omega

/-- A finite coefficient vector is reciprocal when reversal preserves every coefficient. -/
def IsReciprocal (D : ℕ) (a : Fin (D + 1) → R) : Prop :=
  ∀ i, a i = a (reverseIndex D i)

/-- The coefficient index corresponding to contact order `K` at infinity. -/
def contactIndex (D K : ℕ) : Fin (D + 1) :=
  ⟨D - K, by omega⟩

@[simp] theorem contactIndex_val (D K : ℕ) :
    (contactIndex D K : ℕ) = D - K := rfl

/-- `HasContactAtInfinity D a K` means that `K ≤ D`, the coefficient in degree `D - K`
is nonzero, and every coefficient of larger degree vanishes. -/
def HasContactAtInfinity (D : ℕ) (a : Fin (D + 1) → R) (K : ℕ) : Prop :=
  K ≤ D ∧
    a (contactIndex D K) ≠ 0 ∧
    ∀ i : Fin (D + 1), D - K < (i : ℕ) → a i = 0

/-- Reciprocity limits the contact order at infinity to half the formal degree. -/
theorem two_mul_contact_le_degree
    {D K : ℕ} {a : Fin (D + 1) → R}
    (hrec : IsReciprocal D a) (hcontact : HasContactAtInfinity D a K) :
    2 * K ≤ D := by
  rcases hcontact with ⟨hKD, hpivot, hhigh⟩
  by_contra hbound
  have hDKK : D - K < K := by omega
  let iK : Fin (D + 1) := ⟨K, by omega⟩
  have hiKzero : a iK = 0 := hhigh iK (by simpa [iK] using hDKK)
  have hreverse : reverseIndex D iK = contactIndex D K := by
    apply Fin.ext
    simp [iK]
  apply hpivot
  rw [← hreverse, ← hrec iK]
  exact hiKzero

/-- In the equality case, every coefficient except the middle coefficient vanishes. -/
theorem coeff_eq_middle_of_two_mul_contact_eq_degree
    {D K : ℕ} {a : Fin (D + 1) → R}
    (hrec : IsReciprocal D a) (hcontact : HasContactAtInfinity D a K)
    (hsharp : 2 * K = D) (i : Fin (D + 1)) :
    a i = if (i : ℕ) = K then a (contactIndex D K) else 0 := by
  rcases hcontact with ⟨hKD, hpivot, hhigh⟩
  have hmiddle : D - K = K := by omega
  by_cases hi : (i : ℕ) = K
  · have hind : i = contactIndex D K := by
      apply Fin.ext
      simpa [hmiddle] using hi
    subst i
    simp [hmiddle]
  · rw [if_neg hi]
    rcases lt_or_gt_of_ne hi with hlow | hhighIndex
    · rw [hrec i]
      apply hhigh (reverseIndex D i)
      simp only [reverseIndex_val]
      omega
    · exact hhigh i (by omega)

/-- Under reciprocity and genuine contact, equality in the half-contact bound is equivalent
to support on the single middle coefficient. -/
theorem two_mul_contact_eq_degree_iff_single_middle
    {D K : ℕ} {a : Fin (D + 1) → R}
    (hrec : IsReciprocal D a) (hcontact : HasContactAtInfinity D a K) :
    2 * K = D ↔
      ∀ i, a i = if (i : ℕ) = K then a (contactIndex D K) else 0 := by
  constructor
  · intro hsharp i
    exact coeff_eq_middle_of_two_mul_contact_eq_degree hrec hcontact hsharp i
  · intro hsingle
    rcases hcontact with ⟨hKD, hpivot, hhigh⟩
    have hindex : D - K = K := by
      by_contra hne
      have hzero := hsingle (contactIndex D K)
      rw [if_neg (by simpa using hne)] at hzero
      exact hpivot hzero
    omega

/-- Sharp contact in the half-degree inequality forces the formal degree to be even. -/
theorem even_degree_of_sharp_contact
    {D K : ℕ} {a : Fin (D + 1) → R}
    (_hrec : IsReciprocal D a) (_hcontact : HasContactAtInfinity D a K)
    (hsharp : 2 * K = D) : Even D := by
  exact ⟨K, by omega⟩

/-- For odd formal degree `D = 2 * K + 1`, floor-sharp contact has exactly the two adjacent
middle coefficients available; reciprocity makes their values equal. -/
theorem coeff_eq_two_middle_of_odd_floor_contact
    {D K : ℕ} {a : Fin (D + 1) → R}
    (hrec : IsReciprocal D a) (hcontact : HasContactAtInfinity D a K)
    (hodd : D = 2 * K + 1) (i : Fin (D + 1)) :
    a i =
      if (i : ℕ) = K ∨ (i : ℕ) = K + 1
      then a (contactIndex D K)
      else 0 := by
  rcases hcontact with ⟨hKD, hpivot, hhigh⟩
  have hpivotIndex : D - K = K + 1 := by omega
  by_cases hi : (i : ℕ) = K ∨ (i : ℕ) = K + 1
  · rw [if_pos hi]
    rcases hi with hi | hi
    · rw [hrec i]
      congr 1
      apply Fin.ext
      simp only [reverseIndex_val, contactIndex_val]
      omega
    · congr 1
      apply Fin.ext
      simp only [contactIndex_val]
      omega
  · rw [if_neg hi]
    have hiK : (i : ℕ) ≠ K := fun h ↦ hi (Or.inl h)
    have hiK1 : (i : ℕ) ≠ K + 1 := fun h ↦ hi (Or.inr h)
    by_cases hlow : (i : ℕ) < K
    · rw [hrec i]
      apply hhigh (reverseIndex D i)
      simp only [reverseIndex_val]
      omega
    · apply hhigh i
      omega

end LeanProofs.TwoBaseIntegerExponent.ReciprocalHalfContact
