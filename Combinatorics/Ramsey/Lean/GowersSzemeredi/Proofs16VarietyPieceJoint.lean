import GowersSzemeredi.Proofs16LineExtractor
import GowersSzemeredi.Proofs16VarietyTranslate

/-! Glue from variety pieces to the joint variety cover.

The peer's `exists_joint_freiman_variety_cover` covers a union of `n`
translated variety graphs. It requires one common mixed-phase count `r`, a
common radius floor `δ`, and each graph as `IsGraphOver` a shifted
half-radius variety. Variety pieces (`IsVarietyPiece`, from
`structure_side_of_milicevic`) give each piece its own `r ≤ B`, radius
`≥ exp(−B)`, and pointwise agreement. This module supplies the glue.

* `padPhases`: extend `L : Fin r → …` by zero maps to `Fin R`, for `r ≤ R`.
  Zero maps are Freiman-linear (`padPhases_freiman`), and their variety
  conditions `|0·x| ≤ ρN` always hold, so the variety does not change
  (`bilinearBohrVariety_padPhases`).
* `pieceGraph`: a piece's graph, on `Point N 2`.
* `IsVarietyPiece.joint`: a variety piece at density `c` gives data with
  common phase count `⌊B⌋`, radius `≥ exp(−B)`, and the piece graph
  `IsGraphOver` the shifted half-radius variety. Here `B = milicevicBound D c`.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- Pad a phase family by zero maps. -/
def padPhases {N r : Nat} (L : Fin r → ZMod N → ZMod N) (R : Nat) : Fin R → ZMod N → ZMod N :=
  fun k => if hk : k.val < r then L ⟨k.val, hk⟩ else fun _ => 0

theorem padPhases_freiman {N r : Nat} {B : Finset (ZMod N)} {L : Fin r → ZMod N → ZMod N}
    (hL : ∀ k, IsFreimanLinearOn B (L k)) (R : Nat) (k : Fin R) :
    IsFreimanLinearOn B (padPhases L R k) := by
  unfold padPhases
  by_cases hk : k.val < r
  · simp only [dif_pos hk]
    exact hL _
  · simp only [dif_neg hk]
    intro _ _ _ _ _ _ _ _ _
    simp

theorem bilinearBohrVariety_padPhases {N : Nat} [NeZero N] (Γ Ψ : Finset (ZMod N)) {r : Nat}
    (L : Fin r → ZMod N → ZMod N) {R : Nat} (hrR : r ≤ R) {ρ : Real} (hρ : 0 ≤ ρ) :
    bilinearBohrVariety Γ Ψ (padPhases L R) ρ = bilinearBohrVariety Γ Ψ L ρ := by
  ext p
  rw [mem_bilinearBohrVariety_iff, mem_bilinearBohrVariety_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h k => ?_, fun h k => ?_⟩)
  · have := h ⟨k.val, lt_of_lt_of_le k.isLt hrR⟩
    simpa [padPhases, k.isLt] using this
  · unfold padPhases
    by_cases hk : k.val < r
    · simp only [dif_pos hk]
      exact h _
    · simp only [dif_neg hk, zero_mul]
      simp [centeredAbs]
      positivity

/-- A piece's graph, on `Point N 2`. -/
def pieceGraph {N : Nat} [NeZero N] (G : Finset (ZMod N × ZMod N))
    (f : ZMod N × ZMod N → ZMod N) : Finset (Point N 2 × ZMod N) :=
  partialGraph (G.image pairPoint) (fun x => f (x 0, x 1))

/-- **Variety pieces in joint-cover form.** -/
theorem IsVarietyPiece.joint {N : Nat} [NeZero N] {D : Nat} {c : Real}
    {φ : ZMod N × ZMod N → ZMod N} {G : Finset (ZMod N × ZMod N)}
    (h : IsVarietyPiece D c φ G) :
    ∃ (Γ Ψ : Finset (ZMod N)) (L : Fin ⌊milicevicBound D c⌋₊ → ZMod N → ZMod N) (ρ : Real)
      (s t : ZMod N) (Φ : ZMod N × ZMod N → ZMod N),
      (Γ.card : Real) ≤ milicevicBound D c ∧ (Ψ.card : Real) ≤ milicevicBound D c ∧
      Real.exp (-milicevicBound D c) ≤ ρ ∧
      (∀ k, IsFreimanLinearOn (bohr Ψ ρ) (L k)) ∧
      IsEBihomomorphism (bilinearBohrVariety Γ Ψ L ρ) Φ {0} ∧
      IsGraphOver (pieceGraph G φ)
        (shiftPairs (bilinearBohrVariety Γ Ψ L (ρ / 2)) s t)
        (fun q => Φ (q.1 - s, q.2 - t)) := by
  obtain ⟨Γ, Ψ, r, L, ρ, s, t, Φ, hΓ, hΨ, hr, hρ, hL, hΦ, hG⟩ := h
  have hρpos : 0 < ρ := (Real.exp_pos _).trans_le hρ
  have hrR : r ≤ ⌊milicevicBound D c⌋₊ := Nat.le_floor hr
  refine ⟨Γ, Ψ, padPhases L _, ρ, s, t, Φ, hΓ, hΨ, hρ, padPhases_freiman hL _, ?_, ?_⟩
  · rw [bilinearBohrVariety_padPhases Γ Ψ L hrR hρpos.le]
    exact hΦ
  · rw [bilinearBohrVariety_padPhases Γ Ψ L hrR (by positivity)]
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hqV, hqφ⟩ := hG q hq
    have h0 : (pairPoint q) 0 = q.1 := rfl
    have h1 : (pairPoint q) 1 = q.2 := rfl
    simp only [h0, h1]
    refine ⟨(mem_shiftPairs _ s t _).mpr hqV, ?_⟩
    exact hqφ

end LeanProofs.GowersSzemeredi
