/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.NativeCrossFactorization

namespace OAI

section

namespace Erdos3.NativeVectorCorrelation

theorem exists_fixed_coordinate {G I : Type*} [Fintype I]
    {degree N : ℕ} [NeZero N] {p q : ℝ}
    (H : Finset G) (hH : H.Nonempty) (f : G → I → ZMod N → ℂ)
    (hI : (Fintype.card I : ℝ) ≤ Real.exp q)
    (hcorr : ∀ h ∈ H, Nonempty (NativeVectorCorrelation degree N p (f h))) :
    ∃ i : I, ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
      Real.exp (-q) * H.card ≤ (H'.card : ℝ) ∧
      ∀ h ∈ H', Nonempty (NativeVectorCorrelation degree N p (fun _ : Unit => f h i)) := by
  classical
  let W (h : {h // h ∈ H}) := Classical.choice (hcorr h.val h.property)
  obtain ⟨h₀, hh₀⟩ := hH
  let code (h : G) := if hh : h ∈ H then (W ⟨h, hh⟩).coordinate else (W ⟨h₀, hh₀⟩).coordinate
  obtain ⟨i, _, H', hsub, hH', hfixed, hdense⟩ := exists_exponential_constant_fiber
    H ⟨h₀, hh₀⟩ code Set.univ (Set.toFinite _) (fun _ _ => Set.mem_univ _)
    (by simpa only [Set.ncard_univ, Nat.card_eq_fintype_card] using hI)
  refine ⟨i, H', hsub, hH', hdense, ?_⟩
  intro h hh
  let Wh := W ⟨h, hsub hh⟩
  have hi : Wh.coordinate = i := by
    simpa only [code, dite_eq_left (hsub hh)] using hfixed h hh
  exact ⟨{ Wh with
    coordinate := ()
    correlation := by simpa only [hi] using Wh.correlation }⟩

end Erdos3.NativeVectorCorrelation

end

end OAI
