import GowersSzemeredi.Proofs16ThresholdWordGluing

/-! Uniform counts for compatible representations of every nonempty anchor
list. The recurrence retains the distinct triple and word densities. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Density for a word of `k+1` triples. -/
def thresholdColumnWordDensity (lambda eta : Real) : Nat → Real
  | 0 => lambda
  | k+1 => eta^2*lambda^3*(thresholdColumnWordDensity lambda eta k)^3/128

theorem thresholdColumnWordDensity_pos {lambda eta : Real} (hl : 0 < lambda) (he : 0 < eta) (k : Nat) :
    0 < thresholdColumnWordDensity lambda eta k := by
  induction k with
  | zero => exact hl
  | succ k ih => dsimp only [thresholdColumnWordDensity]; positivity

/-- Every nonempty list of popular anchors has a dense compatible family. -/
theorem threshold_column_word_representations_count {N : Nat} [NeZero N]
    (B P : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real) {lambda eta beta : Real}
    (hl : 0 < lambda) (he : 0 < eta)
    (hP : ∀ a ∈ P, lambda*(N : Real)^2 ≤ (columnTripleRepresentations B T L r a).card)
    (hrich : ThresholdColumnRichness B T L r beta eta)
    (K : Nat) (hcut : ∀ j ≤ K, beta ≤ thresholdColumnWordDensity lambda eta j/2)
    (a : ZMod N) (as : List (ZMod N)) (has : ∀ x ∈ a::as, x ∈ P) (hsize : as.length ≤ K) :
    thresholdColumnWordDensity lambda eta as.length*(N : Real)^(3*as.length+2) ≤
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
    have hb := ih b (fun x hx => has x (by simp only [List.mem_cons] at hx ⊢; exact Or.inr hx)) (by simp only [List.length_cons] at hsize; omega)
    have ha := hP a (has a (by simp))
    have h := threshold_column_word_representations_step B T L r a b as hl
      (thresholdColumnWordDensity_pos hl he as.length) ha hb hrich (hcut 0 (Nat.zero_le _))
      (hcut as.length (by simp only [List.length_cons] at hsize; omega))
    simpa [thresholdColumnWordDensity, Nat.mul_add, Nat.add_assoc] using h

end LeanProofs.GowersSzemeredi
