import GowersSzemeredi.Definitions

/-! Part J, input (S): Milićević's structure theorem for Freiman
bihomomorphisms, stated over `ZMod N`.

L. Milićević, *General inverse theory for the U⁴ norm* (arXiv:2601.01682,
2026), Theorem 1.4, for finite abelian groups `G₁, G₂, H`, reads as follows.
Let `φ : A → H` be a Freiman bihomomorphism on `A ⊆ G₁ × G₂` with
`|A| ≥ c|G₁||G₂|`. Then there are:

* a set `E ⊆ H` of rank `(2 log c⁻¹)^{O(1)}`;
* Bohr sets `B₁, B₂` of codimension `(2 log c⁻¹)^{O(1)}` and radius
  `exp(−(2 log c⁻¹)^{O(1)})`;
* shifts `s, t`, and an `E`-bihomomorphism `Φ : B₁ × B₂ → H` with
  `Φ(x,y) = φ(x+s, y+t)` for at least `exp(−(2 log c⁻¹)^{O(1)})|G₁||G₂|`
  points.

The paper does not make the `O(1)` explicit. `MilicevicBihomStructure D`
states the theorem for `G₁ = G₂ = H = ZMod N` with every bound replaced by
`milicevicBound D c = (2 + 2 log c⁻¹)^D`. Since the base is at least two,
multiplicative constants and different exponents are absorbed by enlarging
`D`. So the printed theorem implies `∃ D, MilicevicBihomStructure D`. That
existence is NOT asserted here; the Prop is a hypothesis for the
conditional dimension-three route of research notes Part J.

Bohr sets use the project's `bohr K ρ`, i.e. `|r d| ≤ ρN` for `r ∈ K`.
That is the condition `‖r d / N‖_𝕋 ≤ ρ`, with codimension `|K|`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- `Φ` respects every directional additive quadruple inside `A`, in each
coordinate, up to an error in `E`. With `E = {0}` this is a Freiman
bihomomorphism. -/
def IsEBihomomorphism {N : Nat} (A : Finset (ZMod N × ZMod N))
    (Φ : ZMod N × ZMod N → ZMod N) (E : Set (ZMod N)) : Prop :=
  (∀ x₁ x₂ x₃ x₄ y : ZMod N, x₁ + x₂ = x₃ + x₄ →
      (x₁, y) ∈ A → (x₂, y) ∈ A → (x₃, y) ∈ A → (x₄, y) ∈ A →
      Φ (x₁, y) + Φ (x₂, y) - Φ (x₃, y) - Φ (x₄, y) ∈ E) ∧
  (∀ x y₁ y₂ y₃ y₄ : ZMod N, y₁ + y₂ = y₃ + y₄ →
      (x, y₁) ∈ A → (x, y₂) ∈ A → (x, y₃) ∈ A → (x, y₄) ∈ A →
      Φ (x, y₁) + Φ (x, y₂) - Φ (x, y₃) - Φ (x, y₄) ∈ E)

/-- `E` has rank at most `r`: every element is a `0/1`-combination of `r`
fixed elements. -/
def SetRankLE {N : Nat} (E : Set (ZMod N)) (r : Nat) : Prop :=
  ∃ a : Fin r → ZMod N, ∀ e ∈ E, ∃ ε : Fin r → Bool,
    e = ∑ i, if ε i then a i else 0

/-- The common bound `(2 + 2 log c⁻¹)^D`. -/
def milicevicBound (D : Nat) (c : Real) : Real :=
  (2 + 2 * Real.log c⁻¹) ^ D

/-- Milićević's Theorem 1.4 over `ZMod N`, with explicit exponent `D`
(see the module docstring). -/
def MilicevicBihomStructure (D : Nat) : Prop :=
  ∀ (N : Nat) [NeZero N] (A : Finset (ZMod N × ZMod N))
    (φ : ZMod N × ZMod N → ZMod N) (c : Real),
    0 < c → c * (N : Real) ^ 2 ≤ A.card → IsEBihomomorphism A φ {0} →
    ∃ (E : Set (ZMod N)) (r : Nat) (K₁ K₂ : Finset (ZMod N)) (ρ₁ ρ₂ : Real)
      (s t : ZMod N) (Φ : ZMod N × ZMod N → ZMod N),
      SetRankLE E r ∧ (r : Real) ≤ milicevicBound D c ∧
      (K₁.card : Real) ≤ milicevicBound D c ∧ (K₂.card : Real) ≤ milicevicBound D c ∧
      Real.exp (-milicevicBound D c) ≤ ρ₁ ∧ Real.exp (-milicevicBound D c) ≤ ρ₂ ∧
      IsEBihomomorphism (bohr K₁ ρ₁ ×ˢ bohr K₂ ρ₂) Φ E ∧
      Real.exp (-milicevicBound D c) * (N : Real) ^ 2 ≤
        (((bohr K₁ ρ₁ ×ˢ bohr K₂ ρ₂).filter fun p =>
          (p.1 + s, p.2 + t) ∈ A ∧ Φ p = φ (p.1 + s, p.2 + t)).card : Real)

theorem two_le_milicevic_base {c : Real} (hc : 0 < c) (hc1 : c ≤ 1) :
    2 ≤ 2 + 2 * Real.log c⁻¹ := by
  have h : 0 ≤ Real.log c⁻¹ := Real.log_nonneg ((one_le_inv₀ hc).mpr hc1)
  linarith

theorem milicevicBound_mono {D D' : Nat} (hD : D ≤ D') {c : Real} (hc : 0 < c) (hc1 : c ≤ 1) :
    milicevicBound D c ≤ milicevicBound D' c :=
  pow_le_pow_right₀ (by linarith [two_le_milicevic_base hc hc1]) hD

/-- A density-`c` subset of `ZMod N × ZMod N` forces `c ≤ 1`. -/
theorem density_le_one_of_card {N : Nat} [NeZero N] {A : Finset (ZMod N × ZMod N)} {c : Real}
    (h : c * (N : Real) ^ 2 ≤ A.card) : c ≤ 1 := by
  have hN : (0 : Real) < (N : Real) ^ 2 := by
    have : (0 : Real) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    positivity
  have hA : (A.card : Real) ≤ (N : Real) ^ 2 := by
    have h1 : A.card ≤ Fintype.card (ZMod N × ZMod N) := Finset.card_le_univ A
    rw [Fintype.card_prod, ZMod.card] at h1
    exact_mod_cast (show A.card ≤ N ^ 2 by simpa [sq] using h1)
  by_contra hc
  push_neg at hc
  nlinarith

/-- The hypothesis weakens as `D` grows, so only its existence matters. -/
theorem MilicevicBihomStructure.mono {D D' : Nat} (hD : D ≤ D')
    (h : MilicevicBihomStructure D) : MilicevicBihomStructure D' := by
  intro N _ A φ c hc hA hφ
  have hc1 := density_le_one_of_card hA
  have hle := milicevicBound_mono hD hc hc1
  obtain ⟨E, r, K₁, K₂, ρ₁, ρ₂, s, t, Φ, hE, hr, hK₁, hK₂, hρ₁, hρ₂, hΦ, hagree⟩ :=
    h N A φ c hc hA hφ
  have hexp : Real.exp (-milicevicBound D' c) ≤ Real.exp (-milicevicBound D c) :=
    Real.exp_le_exp.mpr (neg_le_neg hle)
  have hN : (0 : Real) ≤ (N : Real) ^ 2 := by positivity
  exact ⟨E, r, K₁, K₂, ρ₁, ρ₂, s, t, Φ, hE, hr.trans hle, hK₁.trans hle, hK₂.trans hle,
    hexp.trans hρ₁, hexp.trans hρ₂, hΦ,
    (mul_le_mul_of_nonneg_right hexp hN).trans hagree⟩

end LeanProofs.GowersSzemeredi
