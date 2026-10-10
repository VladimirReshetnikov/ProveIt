import GowersSzemeredi.Proofs16GluedPairMaps

/-! The last two pieces of the final selection in Milićević's Proposition 9.3
(arXiv:2601.01682, printed pp. 67–68).

* `exists_index_window` (F4, linear domains). Each `a ∈ A` carries an index
  set `S_a ⊆ [m]` with `|S_a| ≤ k ≤ m`. Some `J ⊆ [m]` with `|J| = k`
  contains `S_a` for at least `|A| / C(m, k)` of the `a`'s, by pigeonholing a
  `k`-superset of each `S_a`. On those `a`, the domain
  `U_a = B(θ_i(a) : i ∈ J; η)` is linear in `a`. It lies inside the domain
  built from `S_a`, since more frequencies give a smaller Bohr set
  (`bohr_anti`), so every containment proved for `S_a` survives.
  Milićević averages over a random `J` of size `8s₀`; pigeonholing gives
  the same `C(m, k)^(−1)` loss.
* `gluedPairMap_relate` (F5, relating back). Suppose the chosen pair `p`
  for `a` is compatible with another pair `q = (z + a, z)`. Then the glued
  map equals `φ_{z+a} − φ_z` on the common quarter-radius Bohr set. This is
  Milićević's `|Z(φ_a − φ_{z+a} + φ_z)| ≥ (ρ/4)^{4d}|G₂|` in exact form. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- **A common window of indices.** -/
theorem exists_index_window {α : Type*} (A : Finset α) (S : α → Finset Nat) {m k : Nat}
    (hk : k ≤ m) (hS : ∀ a ∈ A, S a ⊆ Finset.range m ∧ (S a).card ≤ k) :
    ∃ J ⊆ Finset.range m, J.card = k ∧
      A.card ≤ m.choose k * (A.filter fun a => S a ⊆ J).card := by
  have hsup : ∀ a, ∃ J, a ∈ A → S a ⊆ J ∧ J ⊆ Finset.range m ∧ J.card = k := by
    intro a
    by_cases ha : a ∈ A
    · obtain ⟨J, h1, h2, h3⟩ := Finset.exists_subsuperset_card_eq (hS a ha).1 (hS a ha).2
        (by rw [Finset.card_range]; exact hk)
      exact ⟨J, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨∅, fun h => absurd h ha⟩
  choose Jof hJof using hsup
  set W := (Finset.range m).powersetCard k with hW
  have hmaps : ∀ a ∈ A, Jof a ∈ W := by
    intro a ha
    obtain ⟨-, h2, h3⟩ := hJof a ha
    exact Finset.mem_powersetCard.mpr ⟨h2, h3⟩
  have hWcard : W.card = m.choose k := by rw [Finset.card_powersetCard, Finset.card_range]
  have hWne : W.Nonempty := Finset.powersetCard_nonempty.mpr (by rw [Finset.card_range]; exact hk)
  obtain ⟨J, hJW, hJmax⟩ := Finset.exists_max_image W
    (fun J => (A.filter fun a => Jof a = J).card) hWne
  refine ⟨J, (Finset.mem_powersetCard.mp hJW).1, (Finset.mem_powersetCard.mp hJW).2, ?_⟩
  have hsum : A.card = ∑ J' ∈ W, (A.filter fun a => Jof a = J').card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hfib : (A.filter fun a => Jof a = J).card ≤ (A.filter fun a => S a ⊆ J).card := by
    refine Finset.card_le_card fun a ha => ?_
    obtain ⟨haA, haJ⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨haA, haJ ▸ (hJof a haA).1⟩
  calc A.card = ∑ J' ∈ W, (A.filter fun a => Jof a = J').card := hsum
    _ ≤ ∑ _J' ∈ W, (A.filter fun a => Jof a = J).card := Finset.sum_le_sum hJmax
    _ = m.choose k * (A.filter fun a => Jof a = J).card := by
        rw [Finset.sum_const, smul_eq_mul, hWcard]
    _ ≤ m.choose k * (A.filter fun a => S a ⊆ J).card := Nat.mul_le_mul_left _ hfib

/-- **Relating back**: the glued map is the difference at any compatible pair. -/
theorem gluedPairMap_relate {N : Nat} [NeZero N] (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {r : Real} (hr : 0 ≤ r)
    (hL : ∀ x, IsFreimanLinearOn (bohr (T x) r) (L x)) (hL0 : ∀ x, L x 0 = 0)
    {p q z : ZMod N × ZMod N} (hpq : ColumnPairCompatible T L r p q)
    (hpz : ColumnPairCompatible T L r p z) {w : ZMod N}
    (hw : w ∈ bohr (columnDifferenceSpectrum T p) (r / 4))
    (hwz : w ∈ bohr (columnDifferenceSpectrum T z) (r / 4)) :
    gluedPairMap T L r p q w = columnDifferenceMap L z w := by
  obtain ⟨-, -, hP, -⟩ := gluedPairMap_spec T L hr hL hL0 hpq
  rw [hP w hw]
  have h4 : r / 4 ≤ r := by linarith
  exact hpz w (bohr_mono_radius _ h4 hw) (bohr_mono_radius _ h4 hwz)

end LeanProofs.GowersSzemeredi
