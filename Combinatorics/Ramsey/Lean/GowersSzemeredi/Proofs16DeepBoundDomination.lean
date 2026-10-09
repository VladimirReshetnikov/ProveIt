import GowersSzemeredi.Proofs16DeepEventuallyPrime

/-! Any bound is dominated by Milićević's bound at a fixed density.

The chain after the structure side is stated with `IsVarietyPiece D c` and
`milicevicBound D c = (2 + 2 log c⁻¹)^D`, but each step uses only one
density `c ∈ (0, 1]`. At such a density `milicevicBound D c ≥ 2^D` is
unbounded in `D`. So a piece with any finite bound `Bnd c` is an
`IsVarietyPiece D c` for a suitable `D` depending on `c`:
* `exists_milicevicBound_ge`: some `D` has `B ≤ milicevicBound D c`;
* `IsVarietyPieceB.mono`, `IsVarietyPieceB.toD` and `DeepStructureAt.mono`:
  bounds may be increased, and Milićević's bound gives `IsVarietyPiece`.

`Proofs16DeepBoundSlices` applies this to the padded slice-class cover. It
imports the OAI port, so it is checked on the full-verification host. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- **Milićević's bound dominates any value at a fixed density.** -/
theorem exists_milicevicBound_ge {c : Real} (hc : 0 < c) (hc1 : c ≤ 1) (B : Real) :
    ∃ D : Nat, B ≤ milicevicBound D c := by
  obtain ⟨D, hD⟩ := pow_unbounded_of_one_lt B (by norm_num : (1 : Real) < 2)
  refine ⟨D, hD.le.trans ?_⟩
  unfold milicevicBound
  exact pow_le_pow_left₀ (by norm_num) (two_le_milicevic_base hc hc1) D

/-- A variety piece with a smaller bound is one with a larger bound. -/
theorem IsVarietyPieceB.mono {N : Nat} [NeZero N] {Bnd Bnd' : Real → Real} {c : Real}
    (hle : Bnd c ≤ Bnd' c) {φ : ZMod N × ZMod N → ZMod N} {G : Finset (ZMod N × ZMod N)}
    (h : IsVarietyPieceB Bnd c φ G) : IsVarietyPieceB Bnd' c φ G := by
  obtain ⟨Γ, Ψ, r, L, ρ, s, t, Φ, hΓ, hΨ, hr, hρ, hL, hΦ, hG⟩ := h
  refine ⟨Γ, Ψ, r, L, ρ, s, t, Φ, hΓ.trans hle, hΨ.trans hle, hr.trans hle, ?_, hL, hΦ, hG⟩
  exact (Real.exp_le_exp.mpr (neg_le_neg hle)).trans hρ

/-- `IsVarietyPieceB` at Milićević's bound is `IsVarietyPiece`. -/
theorem IsVarietyPieceB.toD {N : Nat} [NeZero N] {Bnd : Real → Real} {D : Nat} {c : Real}
    (hle : Bnd c ≤ milicevicBound D c) {φ : ZMod N × ZMod N → ZMod N}
    {G : Finset (ZMod N × ZMod N)} (h : IsVarietyPieceB Bnd c φ G) : IsVarietyPiece D c φ G :=
  IsVarietyPieceB.mono (Bnd' := milicevicBound D) hle h

/-- The deep structure conclusion with a larger bound. -/
theorem DeepStructureAt.mono {Bnd Bnd' : Real → Real} {N : Nat} [NeZero N] {c : Real}
    (hle : Bnd c ≤ Bnd' c) (h : DeepStructureAt Bnd N c) : DeepStructureAt Bnd' N c := by
  intro A φ hA hφ
  obtain ⟨Γ, Ψ, r, L, ρ, s, t, Φ, hΓ, hΨ, hr, hρ, hL, hΦ, hagree⟩ := h A φ hA hφ
  have hexp : Real.exp (-Bnd' c) ≤ Real.exp (-Bnd c) := Real.exp_le_exp.mpr (neg_le_neg hle)
  refine ⟨Γ, Ψ, r, L, ρ, s, t, Φ, hΓ.trans hle, hΨ.trans hle, hr.trans hle, hexp.trans hρ, hL, hΦ,
    ?_⟩
  exact (mul_le_mul_of_nonneg_right hexp (by positivity)).trans hagree

end LeanProofs.GowersSzemeredi
