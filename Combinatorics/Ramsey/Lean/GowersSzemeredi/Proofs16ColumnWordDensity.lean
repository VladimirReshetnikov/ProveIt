import GowersSzemeredi.Proofs16ColumnWordGluing

/-! Uniform counts for compatible representations of every nonempty anchor
list. The recurrence retains the distinct triple and word densities. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Density for a word of `k+1` triples. -/
def columnWordDensity (lambda eta : Real) : Nat → Real
  | 0 => lambda
  | k+1 => eta^2*lambda^3*(columnWordDensity lambda eta k)^3/64

theorem columnWordDensity_pos {lambda eta : Real} (hl : 0 < lambda) (he : 0 < eta) (k : Nat) :
    0 < columnWordDensity lambda eta k := by
  induction k with
  | zero => exact hl
  | succ k ih => dsimp only [columnWordDensity]; positivity

/-- Every nonempty list of popular anchors has a dense compatible family. -/
theorem column_word_representations_count {N : Nat} [NeZero N]
    (B P : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real) {lambda eta : Real}
    (hl : 0 < lambda) (he : 0 < eta)
    (hP : ∀ a ∈ P, lambda*(N : Real)^2 ≤ (columnTripleRepresentations B T L r a).card)
    (hrich : ∀ U V : Finset (ZMod N), U ⊆ B → V ⊆ B →
      ∀ beta1 beta2 : Real, 0 ≤ beta1 → 0 ≤ beta2 →
        beta1*N ≤ (U.card : Real) → beta2*N ≤ (V.card : Real) →
        (beta1*beta2*eta)^2*(N : Real)^3 ≤ ((mixedExactColumnQuadruples U V T L r).card : Real))
    (a : ZMod N) (as : List (ZMod N)) (has : ∀ x ∈ a::as, x ∈ P) :
    columnWordDensity lambda eta as.length*(N : Real)^(3*as.length+2) ≤
      (columnWordRepresentations B T L r (a::as)).card := by
  induction as generalizing a with
  | nil =>
    have hcard : (columnTripleRepresentations B T L r a).card ≤
        (columnWordRepresentations B T L r [a]).card := by
      apply Finset.card_le_card_of_injOn (fun t => (t,()))
      · intro t ht
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩
      · intro t _ u _ heq
        exact congrArg Prod.fst heq
    exact (hP a (has a (by simp))).trans (by exact_mod_cast hcard)
  | cons b as ih =>
    have hb := ih b (fun x hx => has x (by simp only [List.mem_cons] at hx ⊢; exact Or.inr hx))
    have ha := hP a (has a (by simp))
    have h := column_word_representations_step B T L r a b as hl
      (columnWordDensity_pos hl he as.length) ha hb hrich
    simpa [columnWordDensity, Nat.mul_add, Nat.add_assoc] using h

end LeanProofs.GowersSzemeredi
