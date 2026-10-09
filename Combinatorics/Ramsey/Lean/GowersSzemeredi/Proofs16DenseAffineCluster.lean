import GowersSzemeredi.Proofs16BohrRecentering

/-! Dense affine recentering on an arbitrary test set inside a common
Freiman domain. The translation point itself need not be in that domain. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- One anchor gives an affine formula for a whole family on a translated
cluster. Only the points of the two clusters need belong to the domain. -/
theorem affine_family_on_translated_cluster {N : Nat} {κ : Type*}
    (D W : Finset (ZMod N)) (L : κ → ZMod N → ZMod N) (t : ZMod N)
    (hWne : W.Nonempty) (hW : W ⊆ D) (hdom : ∀ x ∈ W, t + x ∈ D)
    (hL : ∀ j, IsFreimanLinearOn D (L j)) :
    ∃ c : κ → ZMod N, ∀ j, ∀ x ∈ W, L j (t + x) = c j + L j x := by
  obtain ⟨b, hb⟩ := hWne
  refine ⟨fun j => L j (t + b) - L j b, ?_⟩
  intro j x hx
  have h := hL j (t + x) b (t + b) x (hdom x hx) (hW hb) (hdom b hb) (hW hx) (by ring)
  linear_combination h

/-- Averaging retains the ambient density on a test set, together with
simultaneous affine formulas for the family. -/
theorem exists_dense_affine_cluster {N : Nat} [NeZero N] {κ : Type*}
    (D E C : Finset (ZMod N)) (L : κ → ZMod N → ZMod N)
    (hE : E ⊆ D) (hC : C ⊆ D) (hCne : C.Nonempty)
    (hL : ∀ j, IsFreimanLinearOn D (L j)) {alpha : Real}
    (ha : 0 < alpha) (hcard : alpha * N ≤ E.card) :
    ∃ (t : ZMod N) (W : Finset (ZMod N)) (c : κ → ZMod N),
      W.Nonempty ∧ W ⊆ C ∧ alpha * (C.card : Real) ≤ W.card ∧
      (∀ x ∈ W, t + x ∈ E) ∧
      ∀ j, ∀ x ∈ W, L j (t + x) = c j + L j x := by
  obtain ⟨t, ht⟩ := exists_dense_localTranslate E C hcard
  let W := localTranslateCoordinates E C t
  have hCpos : (0 : Real) < C.card := by exact_mod_cast hCne.card_pos
  have hWne : W.Nonempty := Finset.card_pos.mp (by exact_mod_cast (mul_pos ha hCpos).trans_le ht)
  have hWC : W ⊆ C := Finset.filter_subset _ _
  have hWE : ∀ x ∈ W, t + x ∈ E := fun x hx => (Finset.mem_filter.mp hx).2
  obtain ⟨c, hc⟩ := affine_family_on_translated_cluster D W L t hWne (hWC.trans hC)
    (fun x hx => hE (hWE x hx)) hL
  exact ⟨t, W, c, hWne, hWC, ht, hWE, hc⟩

end LeanProofs.GowersSzemeredi
