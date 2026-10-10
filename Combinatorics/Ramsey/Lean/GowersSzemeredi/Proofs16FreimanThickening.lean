import GowersSzemeredi.Proofs16SandersLinearPart
import GowersSzemeredi.Proofs16BohrFourTerm

/-! Freiman homomorphisms extend affinely to Bohr thickenings (J.5c Further
question 1, a structural step towards domain coherence).

Let `f` be a Freiman 8-homomorphism on `A`. Let `ψ = quadSumExt A f` be its
extension to four-term sums. Suppose `bohr Γ ρ ⊆ 2A − 2A`, as
`sanders_linear_part` arranges at Sanders-strength rank. Then
`f̂(b + k) = ψ(k) + f(b)`, for `b ∈ A` and `k ∈ B(Γ; ρ/4)`, is well defined.
It extends `f`, and it is Freiman-affine on the thickening
`A + B(Γ; ρ/4)`.
* `thickeningExt_spec`: `f̂(b + k) = ψ(k) + f(b)` for every such
  representation.
* `freiman_bohr_thickening`: `f̂ = f` on `A`, and `f̂` is Freiman-linear on
  `A + B(Γ; ρ/4)`.

So each frequency map `θ_i` of Proposition 9.3 is Freiman on a structured,
Bohr-thickened domain, not only on a bare dense set. Whether `X` can be
placed inside all `J` thickenings at once is still open. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The Bohr thickening `A + B(Γ; ρ/4)`. -/
def bohrThickening {N : Nat} [NeZero N] (A Γ : Finset (ZMod N)) (ρ : Real) : Finset (ZMod N) :=
  (A ×ˢ bohr Γ (ρ / 4)).image fun p => p.1 + p.2

/-- The affine extension to the thickening. -/
def thickeningExt {N : Nat} [NeZero N] (A Γ : Finset (ZMod N)) (ρ : Real)
    (f : ZMod N → ZMod N) (a : ZMod N) : ZMod N :=
  if h : ∃ p ∈ A ×ˢ bohr Γ (ρ / 4), p.1 + p.2 = a then
    quadSumExt A f h.choose.2 + f h.choose.1 else 0

/-- `ψ` is Freiman-linear on all four-term sums. -/
theorem quadSumExt_freimanLinear_univ {N : Nat} {A : Finset (ZMod N)} {f : ZMod N → ZMod N}
    (hf : FreimanHom 8 A f) :
    ∀ y₁ y₂ y₃ y₄, y₁ ∈ quadSumSet A → y₂ ∈ quadSumSet A → y₃ ∈ quadSumSet A →
      y₄ ∈ quadSumSet A → y₁ + y₂ = y₃ + y₄ →
      quadSumExt A f y₁ + quadSumExt A f y₂ = quadSumExt A f y₃ + quadSumExt A f y₄ := by
  intro y₁ y₂ y₃ y₄ h₁ h₂ h₃ h₄ he
  have hS : ∀ x ∈ ({y₁, y₂, y₃, y₄} : Finset (ZMod N)), x ∈ quadSumSet A := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  exact quadSumExt_freimanLinear hf _ hS y₁ y₂ y₃ y₄ (by simp) (by simp) (by simp) (by simp) he

theorem thickeningExt_spec {N : Nat} [NeZero N] {A Γ : Finset (ZMod N)} {ρ : Real}
    (hρ : 0 ≤ ρ) {f : ZMod N → ZMod N} (hf : FreimanHom 8 A f)
    (hQS : ∀ x ∈ bohr Γ ρ, x ∈ quadSumSet A) {b k : ZMod N} (hb : b ∈ A)
    (hk : k ∈ bohr Γ (ρ / 4)) :
    thickeningExt A Γ ρ f (b + k) = quadSumExt A f k + f b := by
  have hf4 : FreimanHom 4 A f := IsAddFreimanHom.mono (by decide : 4 ≤ 8) hf
  have hlin := quadSumExt_freimanLinear_univ hf
  have hex : ∃ p ∈ A ×ˢ bohr Γ (ρ / 4), p.1 + p.2 = b + k :=
    ⟨(b, k), Finset.mem_product.mpr ⟨hb, hk⟩, rfl⟩
  rw [thickeningExt, dif_pos hex]
  obtain ⟨hmem, heq⟩ := hex.choose_spec
  obtain ⟨hb', hk'⟩ := Finset.mem_product.mp hmem
  set b' := hex.choose.1
  set k' := hex.choose.2
  have hmono : ∀ {x : ZMod N} {σ : Real}, σ ≤ ρ → x ∈ bohr Γ σ → x ∈ quadSumSet A :=
    fun hσ hx => hQS _ (bohr_mono_radius Γ hσ hx)
  have h4 : ρ / 4 ≤ ρ := by linarith
  have h2 : ρ / 4 + ρ / 4 ≤ ρ := by linarith
  have hkk : k - k' ∈ bohr Γ (ρ / 4 + ρ / 4) := bohr_sub_radius Γ hk hk'
  have h0 : (0 : ZMod N) ∈ quadSumSet A := by
    obtain ⟨a, ha⟩ : A.Nonempty := ⟨b, hb⟩
    exact ⟨a, ha, a, ha, a, ha, a, ha, by ring⟩
  -- `ψ k − ψ k′ = ψ(k − k′) = f b′ − f b`
  have e1 := hlin k 0 k' (k - k') (hmono h4 hk) h0 (hmono h4 hk') (hmono h2 hkk) (by ring)
  have e2 := quadSumExt_sub hf4 hb' hb
  have e3 : b' - b = k - k' := by linear_combination heq
  rw [quadSumExt_zero hf4 ⟨b, hb⟩] at e1
  rw [e3] at e2
  linear_combination -e1 - e2

/-- **Freiman maps extend to Bohr thickenings.** -/
theorem freiman_bohr_thickening {N : Nat} [NeZero N] {A Γ : Finset (ZMod N)} {ρ : Real}
    (hρ : 0 ≤ ρ) {f : ZMod N → ZMod N} (hf : FreimanHom 8 A f)
    (hQS : ∀ x ∈ bohr Γ ρ, x ∈ quadSumSet A) :
    (∀ a ∈ A, thickeningExt A Γ ρ f a = f a) ∧
      IsFreimanLinearOn (bohrThickening A Γ ρ) (thickeningExt A Γ ρ f) := by
  have hf4 : FreimanHom 4 A f := IsAddFreimanHom.mono (by decide : 4 ≤ 8) hf
  have hlin := quadSumExt_freimanLinear_univ hf
  have h4 : ρ / 4 ≤ ρ := by linarith
  have hmono : ∀ {x : ZMod N} {σ : Real}, σ ≤ ρ → x ∈ bohr Γ σ → x ∈ quadSumSet A :=
    fun hσ hx => hQS _ (bohr_mono_radius Γ hσ hx)
  have h0mem : (0 : ZMod N) ∈ bohr Γ (ρ / 4) := zero_mem_bohr Γ (by positivity)
  refine ⟨fun a ha => ?_, ?_⟩
  · have := thickeningExt_spec hρ hf hQS ha h0mem
    rw [add_zero] at this
    rw [this, quadSumExt_zero hf4 ⟨a, ha⟩, zero_add]
  · intro y₁ y₂ y₃ y₄ hy₁ hy₂ hy₃ hy₄ he
    obtain ⟨⟨b₁, k₁⟩, hp₁, rfl⟩ := Finset.mem_image.mp hy₁
    obtain ⟨⟨b₂, k₂⟩, hp₂, rfl⟩ := Finset.mem_image.mp hy₂
    obtain ⟨⟨b₃, k₃⟩, hp₃, rfl⟩ := Finset.mem_image.mp hy₃
    obtain ⟨⟨b₄, k₄⟩, hp₄, rfl⟩ := Finset.mem_image.mp hy₄
    obtain ⟨g₁, l₁⟩ := Finset.mem_product.mp hp₁
    obtain ⟨g₂, l₂⟩ := Finset.mem_product.mp hp₂
    obtain ⟨g₃, l₃⟩ := Finset.mem_product.mp hp₃
    obtain ⟨g₄, l₄⟩ := Finset.mem_product.mp hp₄
    simp only at he ⊢
    rw [thickeningExt_spec hρ hf hQS g₁ l₁, thickeningExt_spec hρ hf hQS g₂ l₂,
      thickeningExt_spec hρ hf hQS g₃ l₃, thickeningExt_spec hρ hf hQS g₄ l₄]
    have h0 : (0 : ZMod N) ∈ quadSumSet A := ⟨b₁, g₁, b₁, g₁, b₁, g₁, b₁, g₁, by ring⟩
    have hψ0 := quadSumExt_zero hf4 ⟨b₁, g₁⟩
    have hk12 : k₁ + k₂ ∈ bohr Γ (ρ / 4 + ρ / 4) := bohr_add_radius Γ l₁ l₂
    have hk34 : k₃ + k₄ ∈ bohr Γ (ρ / 4 + ρ / 4) := bohr_add_radius Γ l₃ l₄
    have hβ : k₃ + k₄ - (k₁ + k₂) ∈ bohr Γ (ρ / 4 + ρ / 4 + (ρ / 4 + ρ / 4)) :=
      bohr_sub_radius Γ hk34 hk12
    have h2 : ρ / 4 + ρ / 4 ≤ ρ := by linarith
    have h22 : ρ / 4 + ρ / 4 + (ρ / 4 + ρ / 4) ≤ ρ := by linarith
    -- ψ k₁ + ψ k₂ = ψ(k₁ + k₂), and the same for k₃, k₄
    have e12 := hlin k₁ k₂ (k₁ + k₂) 0 (hmono h4 l₁) (hmono h4 l₂) (hmono h2 hk12) h0 (by ring)
    have e34 := hlin k₃ k₄ (k₃ + k₄) 0 (hmono h4 l₃) (hmono h4 l₄) (hmono h2 hk34) h0 (by ring)
    -- the base points: f b₁ + f b₂ − f b₃ − f b₄ = ψ(b₁ + b₂ − b₃ − b₄)
    have eb := quadSumExt_spec hf4 g₁ g₂ g₃ g₄
    have hbk : b₁ + b₂ - b₃ - b₄ = k₃ + k₄ - (k₁ + k₂) := by linear_combination he
    rw [hbk] at eb
    -- ψ(k₁ + k₂) + ψ(β) = ψ(k₃ + k₄)
    have e := hlin (k₁ + k₂) (k₃ + k₄ - (k₁ + k₂)) (k₃ + k₄) 0 (hmono h2 hk12)
      (hmono h22 hβ) (hmono h2 hk34) h0 (by ring)
    rw [hψ0] at e12 e34 e
    linear_combination e12 - e34 + e - eb

end LeanProofs.GowersSzemeredi
