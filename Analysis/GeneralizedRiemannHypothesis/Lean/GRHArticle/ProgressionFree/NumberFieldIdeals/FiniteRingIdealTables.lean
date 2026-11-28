import Mathlib.Data.Finset.Powerset
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Computing all ideal carriers in a finite ring

With an explicit enumerator and arithmetic for the finite ring, exhaustive
subset tests compute its ideal carriers, prime condition, indices, and
products. The verifier interprets the carriers as actual Lean ideals.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals.FiniteRing

open Finset

variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]

/-- The finite closure conditions for an ideal carrier. -/
def IsIdealCarrier (A : Finset R) : Prop :=
  0 ∈ A ∧ (∀ a ∈ A, ∀ b ∈ A, a+b ∈ A) ∧ (∀ r : R, ∀ a ∈ A, r*a ∈ A)

instance (A : Finset R) : Decidable (IsIdealCarrier A) :=
  inferInstanceAs (Decidable (0 ∈ A ∧ (∀ a ∈ A, ∀ b ∈ A, a+b ∈ A) ∧
    (∀ r : R, ∀ a ∈ A, r*a ∈ A)))

/-- The exhaustive list of ideal carriers. -/
def idealCarriers (R : Type*) [CommRing R] [Fintype R] [DecidableEq R] : Finset (Finset R) :=
  (univ : Finset R).powerset.filter IsIdealCarrier

@[simp] theorem mem_idealCarriers (A : Finset R) : A ∈ idealCarriers R ↔ IsIdealCarrier A := by
  simp [idealCarriers]

/-- The actual ideal interpreted from a finite carrier and its closure evidence. -/
def idealOfCarrier (A : Finset R) (hA : IsIdealCarrier A) : Ideal R where
  carrier := A
  zero_mem' := hA.1
  add_mem' := fun ha hb ↦ hA.2.1 _ ha _ hb
  smul_mem' := fun r _ ha ↦ hA.2.2 r _ ha

omit [Fintype R] [DecidableEq R] in
@[simp] theorem mem_idealOfCarrier {A : Finset R} (hA : IsIdealCarrier A) (a : R) :
    a ∈ idealOfCarrier A hA ↔ a ∈ A := Iff.rfl

/-- Proof-side inverse from an abstract ideal to its carrier. -/
noncomputable def carrierOfIdeal (I : Ideal R) : Finset R := by
  classical
  exact Finset.univ.filter (· ∈ I)

omit [DecidableEq R] in
@[simp] theorem mem_carrierOfIdeal (I : Ideal R) (a : R) : a ∈ carrierOfIdeal I ↔ a ∈ I := by
  classical
  simp [carrierOfIdeal]

omit [DecidableEq R] in
theorem isIdealCarrier_carrierOfIdeal (I : Ideal R) : IsIdealCarrier (carrierOfIdeal I) := by
  simp only [IsIdealCarrier, mem_carrierOfIdeal]
  exact ⟨I.zero_mem, fun _ ha _ hb ↦ I.add_mem ha hb, fun r _ ha ↦ I.mul_mem_left r ha⟩

omit [DecidableEq R] in
/-- The carriers enumerate exactly the actual ideals. -/
theorem idealOfCarrier_carrierOfIdeal (I : Ideal R) :
    idealOfCarrier (carrierOfIdeal I) (isIdealCarrier_carrierOfIdeal I) = I := by
  ext a
  simp

/-- The prime condition for a finite ideal carrier. -/
def IsPrimeCarrier (A : Finset R) : Prop :=
  1 ∉ A ∧ ∀ a b : R, a*b ∈ A → a ∈ A ∨ b ∈ A

instance (A : Finset R) : Decidable (IsPrimeCarrier A) :=
  inferInstanceAs (Decidable (1 ∉ A ∧ ∀ a b : R, a*b ∈ A → a ∈ A ∨ b ∈ A))

omit [Fintype R] [DecidableEq R] in
theorem isPrimeCarrier_iff {A : Finset R} (hA : IsIdealCarrier A) :
    IsPrimeCarrier A ↔ (idealOfCarrier A hA).IsPrime := by
  constructor
  · intro h
    exact ⟨fun htop ↦ h.1 ((Ideal.eq_top_iff_one _).mp htop), fun hab ↦ h.2 _ _ hab⟩
  · intro h
    exact ⟨fun h1 ↦ h.ne_top ((Ideal.eq_top_iff_one _).mpr h1), fun _ _ hab ↦ h.mem_or_mem hab⟩

/-- Index of the finite ideal in the additive underlying group. -/
def carrierIndex (A : Finset R) : ℕ := Fintype.card R / A.card

omit [DecidableEq R] in
theorem carrierIndex_eq_card_quotient {A : Finset R} (hA : IsIdealCarrier A) :
    carrierIndex A = Nat.card (R ⧸ idealOfCarrier A hA) := by
  let J := idealOfCarrier A hA
  have hcard : Nat.card J.toAddSubgroup = A.card := by
    change Nat.card (A : Set R) = A.card
    simp
  have hmul := J.toAddSubgroup.card_mul_index
  rw [hcard, Nat.card_eq_fintype_card] at hmul
  have hpos : 0 < A.card := Finset.card_pos.mpr ⟨0,hA.1⟩
  change Fintype.card R / A.card = J.toAddSubgroup.index
  rw [← hmul, Nat.mul_div_cancel_left _ hpos]

/-- The product carrier, computed as the intersection of all ideal carriers
containing every generator product. -/
def carrierProduct (A B : Finset R) : Finset R :=
  univ.filter fun x ↦ ∀ C ∈ idealCarriers R, (∀ a ∈ A, ∀ b ∈ B, a*b ∈ C) → x ∈ C

theorem mem_carrierProduct_iff {A B : Finset R} (hA : IsIdealCarrier A) (hB : IsIdealCarrier B) (x : R) :
    x ∈ carrierProduct A B ↔ x ∈ idealOfCarrier A hA * idealOfCarrier B hB := by
  simp only [carrierProduct, mem_filter, mem_univ, true_and]
  constructor
  · intro hx
    let I := idealOfCarrier A hA * idealOfCarrier B hB
    have hI : carrierOfIdeal I ∈ idealCarriers R :=
      (mem_idealCarriers _).mpr (isIdealCarrier_carrierOfIdeal I)
    apply (mem_carrierOfIdeal I x).mp (hx _ hI ?_)
    intro a ha b hb
    exact (mem_carrierOfIdeal I _).mpr (Ideal.mul_mem_mul ha hb)
  · intro hx C hC hproducts
    let hC' := (mem_idealCarriers C).mp hC
    have hle : idealOfCarrier A hA * idealOfCarrier B hB ≤ idealOfCarrier C hC' :=
      Ideal.mul_le.mpr hproducts
    exact hle hx

end GRHArticle.ProgressionFree.NumberFieldIdeals.FiniteRing
