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

/-- Bohr sets shrink as the radius shrinks. -/
theorem bohr_mono_radius {N : Nat} [NeZero N] (K : Finset (ZMod N)) {ρ ρ' : Real} (h : ρ' ≤ ρ) :
    bohr K ρ' ⊆ bohr K ρ := by
  intro x hx
  unfold bohr at hx ⊢
  obtain ⟨_, hx⟩ := Finset.mem_filter.mp hx
  have hN : (0 : Real) ≤ N := Nat.cast_nonneg N
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r hr =>
    (hx r hr).trans (mul_le_mul_of_nonneg_right h hN)⟩

/-- **Whole variety sections contain Bohr sets.** Under `BohrBohrIsBohr D`,
for each `x ∈ B(Γ;ρ)` there is a Bohr set `B(Ψ'';ρ'')` with
`|Ψ''| ≤ r (1 + loss^D)` (plus `|Ψ|` if `r = 0`) and `ρ'' ≥ ρ / loss^D`
such that `{x} × B(Ψ'';ρ'') ⊆ V`. -/
theorem variety_full_section_contains_bohr {D : Nat} (hBB : BohrBohrIsBohr D)
    {N : Nat} [NeZero N] {Γ Ψ : Finset (ZMod N)} {r : Nat} {L : Fin r → ZMod N → ZMod N}
    {ρ : Real} (hρ : 0 < ρ) (hL : ∀ k, IsFreimanLinearOn (bohr Ψ ρ) (L k))
    (x : ZMod N) (hx : x ∈ bohr Γ ρ) :
    ∃ (Ψ'' : Finset (ZMod N)) (ρ'' : Real),
      (Ψ''.card : Real) ≤ Ψ.card + r * (1 + bohrBohrLoss Ψ.card ρ ρ ^ D) ∧
      ρ * (bohrBohrLoss Ψ.card ρ ρ ^ D)⁻¹ ≤ ρ'' ∧ ρ'' ≤ ρ ∧
      ∀ y ∈ bohr Ψ'' ρ'', (x, y) ∈ bilinearBohrVariety Γ Ψ L ρ := by
  classical
  have hsec := fun k => variety_section_contains_bohr hBB hρ hL x k
  choose Ψk ρk hcard hrad hsub using hsec
  set rad₀ := ρ * (bohrBohrLoss Ψ.card ρ ρ ^ D)⁻¹ with hrad₀def
  have hloss : (1 : Real) ≤ bohrBohrLoss Ψ.card ρ ρ ^ D :=
    one_le_pow₀ ((by norm_num : (1 : Real) ≤ 2).trans (le_max_left _ _))
  have hrad₀ρ : rad₀ ≤ ρ := by
    rw [hrad₀def]
    exact mul_le_of_le_one_right hρ.le (inv_le_one_of_one_le₀ hloss)
  refine ⟨Ψ ∪ Finset.univ.biUnion Ψk, rad₀, ?_, le_rfl, hrad₀ρ, ?_⟩
  · have h1 := Finset.card_union_le Ψ (Finset.univ.biUnion Ψk)
    have h2 : (Finset.univ.biUnion Ψk).card ≤ ∑ k, (Ψk k).card := Finset.card_biUnion_le
    have h3 : ((∑ k, (Ψk k).card : Nat) : Real) ≤ ∑ _k : Fin r, (1 + bohrBohrLoss Ψ.card ρ ρ ^ D) := by
      push_cast
      exact Finset.sum_le_sum fun k _ => hcard k
    have h4 : (∑ _k : Fin r, (1 + bohrBohrLoss Ψ.card ρ ρ ^ D)) = r * (1 + bohrBohrLoss Ψ.card ρ ρ ^ D) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h12 : ((Ψ ∪ Finset.univ.biUnion Ψk).card : Real) ≤ Ψ.card + ∑ k, (Ψk k).card := by
      exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)
    push_cast at h12 h3
    linarith
  · intro y hy
    -- `y` lies in `B(Ψ;ρ)` and in every section
    have hyΨ : y ∈ bohr Ψ ρ :=
      bohr_mono_radius Ψ hrad₀ρ (bohr_anti Finset.subset_union_left rad₀ hy)
    have hyk : ∀ k, y ∈ bohr (Ψk k) (ρk k) := by
      intro k
      apply bohr_mono_radius (Ψk k) (hrad k)
      apply bohr_anti _ rad₀ hy
      exact Finset.subset_union_right.trans' (Finset.subset_biUnion_of_mem Ψk (Finset.mem_univ k))
    apply product_mem_bilinearBohrVariety hx hyΨ
    intro k
    exact ((hsub k) y (hyk k)).2

end LeanProofs.GowersSzemeredi
