import GowersSzemeredi.Proofs16VarietyUnions

/-! Bohr–Bohr sets are Bohr; consequences for variety sections.

Milićević (arXiv:2601.01682), Proposition 2.37: for a Freiman-linear
`φ : B(Γ;ρ) → 𝕋^d` with `r = |Γ|`, the set `{x ∈ B : ‖φ(x)‖ ≤ σ}` contains a
Bohr set of codimension at most `d + (2r log(σ⁻¹ρ⁻¹))^{O(1)}` and radius at
least `σ (2r log(σ⁻¹ρ⁻¹))^{−O(1)}`.

`BohrBohrIsBohr D` states the `d = 1`, `G = ZMod N` case with one exponent
`D` for the `O(1)`. It is a hypothesis (not asserted). Consequence: for
fixed `x`, the y-section of a bilinear Bohr variety,
`{y ∈ B(Ψ;ρ) : |L(y)·x| ≤ ρN}`, contains a genuine Bohr set. This is the
section-by-section packing route of research notes J.2. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- The quasi-polynomial loss `(2 r log(1/(σρ)))` of Proposition 2.37, made
at least `2` so its powers are monotone. -/
def bohrBohrLoss (r : Nat) (σ ρ : Real) : Real :=
  max 2 (2 * r * Real.log ((σ * ρ)⁻¹))

/-- **Proposition 2.37 (d = 1) as a hypothesis.** -/
def BohrBohrIsBohr (D : Nat) : Prop :=
  ∀ (N : Nat) [NeZero N] (Γ : Finset (ZMod N)) (ρ σ : Real) (φ : ZMod N → ZMod N),
    0 < ρ → 0 < σ → IsFreimanLinearOn (bohr Γ ρ) φ →
    ∃ (Γ' : Finset (ZMod N)) (ρ' : Real),
      (Γ'.card : Real) ≤ 1 + bohrBohrLoss Γ.card σ ρ ^ D ∧
      σ * (bohrBohrLoss Γ.card σ ρ ^ D)⁻¹ ≤ ρ' ∧
      bohr Γ' ρ' ⊆ (bohr Γ ρ).filter fun x => (centeredAbs (φ x) : Real) ≤ σ * N

/-- Multiplying a Freiman-linear map by a constant keeps it Freiman-linear. -/
theorem IsFreimanLinearOn.mul_right {N : Nat} {B : Finset (ZMod N)} {L : ZMod N → ZMod N}
    (h : IsFreimanLinearOn B L) (x : ZMod N) : IsFreimanLinearOn B (fun y => L y * x) := by
  intro y₁ y₂ y₃ y₄ h1 h2 h3 h4 hsum
  have := h y₁ y₂ y₃ y₄ h1 h2 h3 h4 hsum
  show L y₁ * x + L y₂ * x = L y₃ * x + L y₄ * x
  rw [← add_mul, ← add_mul, this]

/-- **Variety sections contain Bohr sets.** Under `BohrBohrIsBohr D`, for
each fixed `x` and each `k`, the `y`-section `{y ∈ B(Ψ;ρ) : |L_k(y)·x| ≤ ρN}`
contains a Bohr set of codimension `≤ 1 + loss^D` and radius `≥ ρ/loss^D`. -/
theorem variety_section_contains_bohr {D : Nat} (hBB : BohrBohrIsBohr D)
    {N : Nat} [NeZero N] {Ψ : Finset (ZMod N)} {r : Nat} {L : Fin r → ZMod N → ZMod N}
    {ρ : Real} (hρ : 0 < ρ) (hL : ∀ k, IsFreimanLinearOn (bohr Ψ ρ) (L k)) (x : ZMod N) (k : Fin r) :
    ∃ (Ψ' : Finset (ZMod N)) (ρ' : Real),
      (Ψ'.card : Real) ≤ 1 + bohrBohrLoss Ψ.card ρ ρ ^ D ∧
      ρ * (bohrBohrLoss Ψ.card ρ ρ ^ D)⁻¹ ≤ ρ' ∧
      ∀ y ∈ bohr Ψ' ρ', y ∈ bohr Ψ ρ ∧ (centeredAbs (L k y * x) : Real) ≤ ρ * N := by
  obtain ⟨Ψ', ρ', hcard, hrad, hsub⟩ :=
    hBB N Ψ ρ ρ (fun y => L k y * x) hρ hρ ((hL k).mul_right x)
  refine ⟨Ψ', ρ', hcard, hrad, fun y hy => ?_⟩
  obtain ⟨hyB, hsmall⟩ := Finset.mem_filter.mp (hsub hy)
  exact ⟨hyB, hsmall⟩

end LeanProofs.GowersSzemeredi
