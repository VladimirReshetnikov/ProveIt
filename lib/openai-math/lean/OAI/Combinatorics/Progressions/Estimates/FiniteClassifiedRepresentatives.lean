/- Modified for ProveIt: adapt import paths to Mathlib v4.32.0.
Mathematical statements and proofs unchanged. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_finite_indexed_representative_enumeration
    {Γ α : Type*} [Fintype Γ] (valid : Γ → α → Prop) (rel : Γ → α → α → Prop)
    {B : ℝ}
    (hbranch : ∀ i, ∃ n : ℕ, (n : ℝ) ≤ B ∧ ∃ candidate : Fin n → α,
      (∀ j, valid i (candidate j)) ∧
      ∀ x, valid i x → ∃ j, rel i (candidate j) x) :
    ∃ n : ℕ, (n : ℝ) ≤ Fintype.card Γ * B ∧
      ∃ candidate : Fin n → Γ × α,
        (∀ j, valid (candidate j).1 (candidate j).2) ∧
        ∀ i x, valid i x → ∃ j,
          (candidate j).1 = i ∧ rel i (candidate j).2 x := by
  classical
  choose n hn candidate hvalid hcover using hbranch
  let J := Σ i : Γ, Fin (n i)
  let e := Fintype.equivFin J
  let combined : Fin (Fintype.card J) → Γ × α :=
    fun j => ((e.symm j).1, candidate (e.symm j).1 (e.symm j).2)
  refine ⟨Fintype.card J, ?_, combined, ?_, ?_⟩
  · change ((Fintype.card (Σ i : Γ, Fin (n i)) : ℕ) : ℝ) ≤ _
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin, Nat.cast_sum]
    calc
      (∑ i, (n i : ℝ)) ≤ ∑ _i : Γ, B := Finset.sum_le_sum (fun i _ => hn i)
      _ = Fintype.card Γ * B := by simp
  · intro j
    exact hvalid (e.symm j).1 (e.symm j).2
  · intro i x hx
    obtain ⟨j, hj⟩ := hcover i x hx
    have hpair : combined (e ⟨i, j⟩) = (i, candidate i j) :=
      congrArg (fun k : J => (k.1, candidate k.1 k.2)) (e.symm_apply_apply ⟨i, j⟩)
    refine ⟨e ⟨i, j⟩, congrArg Prod.fst hpair, ?_⟩
    rw [hpair]
    exact hj

theorem exists_finite_indexed_enumeration
    {Γ α : Type*} [Fintype Γ] (valid : Γ → α → Prop) {B : ℝ}
    (hbranch : ∀ i, ∃ n : ℕ, (n : ℝ) ≤ B ∧ ∃ candidate : Fin n → α,
      (∀ j, valid i (candidate j)) ∧
      ∀ x, valid i x → ∃ j, candidate j = x) :
    ∃ n : ℕ, (n : ℝ) ≤ Fintype.card Γ * B ∧
      ∃ candidate : Fin n → Γ × α,
        (∀ j, valid (candidate j).1 (candidate j).2) ∧
        ∀ i x, valid i x → ∃ j, candidate j = (i, x) := by
  obtain ⟨n, hn, candidate, hvalid, hcover⟩ :=
    exists_finite_indexed_representative_enumeration valid (fun _ => Eq) hbranch
  refine ⟨n, hn, candidate, hvalid, ?_⟩
  intro i x hx
  obtain ⟨j, hi, hj⟩ := hcover i x hx
  exact ⟨j, Prod.ext hi hj⟩

theorem exists_finite_indexed_finset_enumeration
    {Γ α : Type*} [Fintype Γ] (S : Γ → Finset α) {B : ℝ}
    (hcard : ∀ i, ((S i).card : ℝ) ≤ B) :
    ∃ n : ℕ, (n : ℝ) ≤ Fintype.card Γ * B ∧
      ∃ candidate : Fin n → Γ × α,
        (∀ j, (candidate j).2 ∈ S (candidate j).1) ∧
        ∀ i x, x ∈ S i → ∃ j, candidate j = (i, x) := by
  classical
  apply exists_finite_indexed_enumeration (fun i x => x ∈ S i)
  intro i
  let e := Fintype.equivFin (S i)
  refine ⟨Fintype.card (S i), ?_, fun j => (e.symm j).val,
    fun j => (e.symm j).property, ?_⟩
  · simpa only [Fintype.card_coe] using hcard i
  · intro x hx
    exact ⟨e ⟨x, hx⟩, congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)⟩

end Erdos3

end

section

namespace Erdos3

theorem exists_finite_classified_representatives {Λ α : Type*} {n : ℕ}
    (labels : Fin n → Λ) (valid : Λ → α → Prop) (rel : Λ → α → α → Prop)
    (hlabels : ∀ l x, valid l x → ∃ i, labels i = l) {B : ℝ}
    (hbranch : ∀ i, ∃ c : ℕ, (c : ℝ) ≤ B ∧ ∃ candidate : Fin c → α,
      (∀ j, valid (labels i) (candidate j)) ∧
      ∀ x, valid (labels i) x → ∃ j, rel (labels i) (candidate j) x) :
    ∃ c : ℕ, (c : ℝ) ≤ (n : ℝ) * B ∧ ∃ candidate : Fin c → Λ × α,
      (∀ j, valid (candidate j).1 (candidate j).2) ∧
      ∀ l x, valid l x → ∃ j, (candidate j).1 = l ∧ rel l (candidate j).2 x := by
  obtain ⟨c, hc, family, hvalid, hcover⟩ :=
    exists_finite_indexed_representative_enumeration
      (fun i => valid (labels i)) (fun i => rel (labels i)) hbranch
  let candidate := fun j : Fin c => (labels (family j).1, (family j).2)
  refine ⟨c, by simpa only [Fintype.card_fin] using hc, candidate, hvalid, ?_⟩
  intro l x hx
  obtain ⟨i, hi⟩ := hlabels l x hx
  obtain ⟨j, hj, hr⟩ := hcover i x (hi ▸ hx)
  refine ⟨j, ?_, ?_⟩
  · change labels (family j).1 = l
    rw [hj, hi]
  · exact hi ▸ hr

end Erdos3

end

end OAI
