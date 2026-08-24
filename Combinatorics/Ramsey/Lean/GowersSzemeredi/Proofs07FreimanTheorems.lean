import GowersSzemeredi.Sections06_07

/-!
# Boundary cases in the qualitative Freiman theorems

The article implicitly works with nonempty finite sets.  Without that
hypothesis, both qualitative statements in Section 7 demand a generalized
progression of positive formal size bounded by zero.  This module preserves
the legacy signatures and proves the empty-set counterexamples, so the
correction in the statement catalogue remains mechanically auditable.
-/

set_option autoImplicit false

noncomputable section

open scoped Pointwise
open Finset

namespace LeanProofs.GowersSzemeredi

/-- The original live signature of Theorem 7.1, before making nonemptiness
explicit. -/
def theorem_7_1_without_nonempty : Prop :=
  ∀ C : Real, 0 < C →
    ∃ d0 : Nat, ∃ K : Real, 0 < K ∧ ∀ A : Finset Int,
      (((((A + A).card : Real) ≤ C * A.card) →
          HasFreimanCover A d0 K) ∧
       ((((A - A).card : Real) ≤ C * A.card) →
          HasFreimanCover A d0 K))

/-- The original live signature of Theorem 7.2, before making nonemptiness
explicit. -/
def theorem_7_2_without_nonempty : Prop :=
  ∀ c0 : Real, 0 < c0 →
    ∃ c K : Real, ∃ d0 : Nat, 0 < c ∧ 0 < K ∧
      ∀ (D : Nat) (A : Finset (Fin D → Int)),
        c0 * (A.card : Real) ^ 3 ≤ Finset.addEnergy A A →
        HasBalogSzemerediProgression A c K d0

private theorem generalizedAP_size_pos {G : Type*} [AddCommMonoid G]
    (P : GeneralizedAP G) (hlength : ∀ i, 0 < P.length i) :
    0 < P.size := by
  unfold GeneralizedAP.size
  exact Finset.prod_pos fun i _ => hlength i

/-- The empty set refutes the legacy Theorem 7.1 signature. -/
theorem theorem_7_1_empty_counterexample :
    ¬ theorem_7_1_without_nonempty := by
  intro h
  obtain ⟨d0, K, _hK, hcover⟩ := h 1 (by norm_num)
  have hsmall : ((((∅ : Finset Int) + ∅).card : Real) ≤
      (1 : Real) * (∅ : Finset Int).card) := by simp
  obtain ⟨P, _hdim, hlength, hsize, _hsub⟩ :=
    (hcover (∅ : Finset Int)).1 hsmall
  have hPposNat : 0 < P.size :=
    generalizedAP_size_pos P fun i => (hlength i).2
  have hPpos : (0 : Real) < P.size := by exact_mod_cast hPposNat
  have hPzero : (P.size : Real) ≤ 0 := by simpa using hsize
  linarith

/-- The empty set also refutes the legacy Balog--Szemeredi signature. -/
theorem theorem_7_2_empty_counterexample :
    ¬ theorem_7_2_without_nonempty := by
  intro h
  obtain ⟨c, K, d0, _hc, _hK, hcover⟩ := h 1 (by norm_num)
  let A : Finset (Fin 0 → Int) := ∅
  have henergy : (1 : Real) * (A.card : Real) ^ 3 ≤
      Finset.addEnergy A A := by simp [A]
  obtain ⟨P, _hdim, hlength, hsize, _hinter⟩ :=
    hcover 0 A henergy
  have hPposNat : 0 < P.size :=
    generalizedAP_size_pos P hlength
  have hPpos : (0 : Real) < P.size := by exact_mod_cast hPposNat
  have hPzero : (P.size : Real) ≤ 0 := by simpa [A] using hsize
  linarith

end LeanProofs.GowersSzemeredi
