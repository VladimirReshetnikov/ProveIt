import GowersSzemeredi.Proofs16BohrBohrSections
import GowersSzemeredi.Proofs16BohrDenseDifference
import GowersSzemeredi.Proofs16BohrSpectrum
import GowersSzemeredi.Proofs07BohrHom

/-! Two simplifications of [49]'s algebraic regularity iteration in prime
`ℤ/N`.

**Lemma 8 by Bogolyubov.** In the proof of [49] Theorem 33, a combination
`z ↦ Σ λⱼ Lⱼ(z)` of Freiman-linear maps vanishes on a dense subset `F` of
the current domain. Lemma 8 then finds a sub-coset-progression inside the
Freiman subgroup `F`. With Bohr domains in `ℤ/N`, Bogolyubov does this
directly. Let `f` be Freiman-linear on `B(Ψ;σ)` and constant on
`F ⊆ B(Ψ;σ/4)`, where `|F| = αN`. Then `f(x) = f(0)` for every
`x ∈ 2F − 2F`, and `2F − 2F` contains `B(Spec_α F; 1/(8π))`
(`bogolyubov_classical`), with `|Spec| ≤ 16α⁻²`
(`freiman_const_on_bohr_of_dense`). The new domain is a Bohr set whose
rank grows by `16α⁻²`.

**Lemma 30 by linear algebra.** [49] bounds the length of the chain of
relation lattices `Λ₀ ⊊ Λ₁ ⊊ ⋯ ⊆ ℤʳ` by `O(r²(log r + log K))`, using
lattice determinants. In prime `ℤ/N` the coefficients can be taken in
the field. The relations satisfied by maps `L : κ → (ℤ/N → ℤ/N)` on a
domain `D` form a subspace (`relationSubmodule`). Shrinking the domain can
only enlarge it (`relationSubmodule_anti`), and a strictly increasing
chain of subspaces of `(ℤ/N)^κ` has at most `|κ|` steps
(`strict_chain_length_le`). So the iteration in Theorem 33 stops after at
most `r` steps. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- Linear combinations of Freiman-linear maps are Freiman-linear. -/
theorem IsFreimanLinearOn.linear_combination {N : Nat} {κ : Type*} [Fintype κ]
    {B : Finset (ZMod N)} {L : κ → ZMod N → ZMod N} (hL : ∀ j, IsFreimanLinearOn B (L j))
    (w : κ → ZMod N) : IsFreimanLinearOn B (fun y => ∑ j, w j * L j y) := by
  intro y₁ y₂ y₃ y₄ h₁ h₂ h₃ h₄ h
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_add, ← mul_add, hL j y₁ y₂ y₃ y₄ h₁ h₂ h₃ h₄ h]

/-- **A Freiman-linear map constant on a dense set is constant on a Bohr
set** (the `ℤ/N` replacement for [49] Lemma 8). -/
theorem freiman_const_on_bohr_of_dense {N : Nat} [NeZero N] (Ψ : Finset (ZMod N))
    {σ : Real} (hσ : 0 ≤ σ) {f : ZMod N → ZMod N} (hf : IsFreimanLinearOn (bohr Ψ σ) f)
    (F : Finset (ZMod N)) (hF : F ⊆ bohr Ψ (σ / 4)) {v : ZMod N} (hconst : ∀ z ∈ F, f z = v)
    {α : Real} (hα : 0 < α) (hcard : (F.card : Real) = α * N) :
    ((section7Spectrum F α).card : Real) ≤ 16 * α ^ (-(2 : Real)) ∧
      ∀ x ∈ bohr (section7Spectrum F α) (1 / (8 * Real.pi)),
        x ∈ bohr Ψ σ ∧ f x = f 0 := by
  obtain ⟨hspec, hrep⟩ := bogolyubov_classical F α hα hcard
  refine ⟨hspec, fun x hx => ?_⟩
  obtain ⟨a, ha, e, he, b, hb, c, hc, hxeq⟩ := hrep x hx
  have hquarter : σ / 4 = (σ / 2) / 2 := by ring
  have hhalf : ∀ {p q : ZMod N}, p ∈ F → q ∈ F → p - q ∈ bohr Ψ (σ / 2) := by
    intro p q hp hq
    have hp' := hF hp
    have hq' := neg_mem_bohr (hF hq)
    rw [hquarter] at hp' hq'
    simpa [sub_eq_add_neg] using bohr_add_half hp' hq'
  have hsub : ∀ {ρ : Real}, ρ ≤ σ → bohr Ψ ρ ⊆ bohr Ψ σ := fun h => bohr_mono_radius Ψ h
  have hσ2 : σ / 2 ≤ σ := by linarith
  have hσ4 : σ / 4 ≤ σ := by linarith
  have h0 : (0 : ZMod N) ∈ bohr Ψ σ := zero_mem_bohr Ψ hσ
  set d₁ := a - b
  set d₂ := e - c
  have hd₁ : d₁ ∈ bohr Ψ (σ / 2) := hhalf ha hb
  have hd₂ : d₂ ∈ bohr Ψ (σ / 2) := hhalf he hc
  have hxsum : x = d₁ + d₂ := by rw [hxeq]; simp only [d₁, d₂]; ring
  have hxB : x ∈ bohr Ψ σ := by rw [hxsum]; exact bohr_add_half hd₁ hd₂
  refine ⟨hxB, ?_⟩
  -- `b + d₁ = a + 0` and `c + d₂ = e + 0`
  have hf₁ := hf b d₁ a 0 (hsub hσ4 (hF hb)) (hsub hσ2 hd₁) (hsub hσ4 (hF ha)) h0
    (by simp only [d₁]; ring)
  have hf₂ := hf c d₂ e 0 (hsub hσ4 (hF hc)) (hsub hσ2 hd₂) (hsub hσ4 (hF he)) h0
    (by simp only [d₂]; ring)
  -- `d₁ + d₂ = x + 0`
  have hf₃ := hf d₁ d₂ x 0 (hsub hσ2 hd₁) (hsub hσ2 hd₂) hxB h0 (by rw [hxsum, add_zero])
  rw [hconst b hb, hconst a ha] at hf₁
  rw [hconst c hc, hconst e he] at hf₂
  linear_combination hf₁ + hf₂ - hf₃

/-- The coefficient vectors annihilating the maps on a domain, relative to
their values at `0`. -/
def relationSubmodule {N : Nat} [Fact N.Prime] {κ : Type*} [Fintype κ]
    (D : Finset (ZMod N)) (L : κ → ZMod N → ZMod N) : Submodule (ZMod N) (κ → ZMod N) where
  carrier := {w | ∀ y ∈ D, ∑ j, w j * (L j y - L j 0) = 0}
  add_mem' := by
    intro p q hp hq y hy
    simp only [Set.mem_setOf_eq] at hp hq ⊢
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, hp y hy, hq y hy, add_zero]
  zero_mem' := by
    intro y _
    simp
  smul_mem' := by
    intro t p hp y hy
    simp only [Set.mem_setOf_eq] at hp ⊢
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hp y hy, mul_zero]

theorem mem_relationSubmodule {N : Nat} [Fact N.Prime] {κ : Type*} [Fintype κ]
    {D : Finset (ZMod N)} {L : κ → ZMod N → ZMod N} {w : κ → ZMod N} :
    w ∈ relationSubmodule D L ↔ ∀ y ∈ D, ∑ j, w j * (L j y - L j 0) = 0 := Iff.rfl

/-- Shrinking the domain enlarges the relation subspace. -/
theorem relationSubmodule_anti {N : Nat} [Fact N.Prime] {κ : Type*} [Fintype κ]
    {D D' : Finset (ZMod N)} (h : D' ⊆ D) (L : κ → ZMod N → ZMod N) :
    relationSubmodule D L ≤ relationSubmodule D' L :=
  fun _ hw y hy => hw y (h hy)

/-- **A strictly increasing chain of subspaces of `(ℤ/N)^κ` has at most
`|κ|` steps** (the `ℤ/N` replacement for [49] Lemma 30). -/
theorem strict_chain_length_le {N : Nat} [Fact N.Prime] {κ : Type*} [Fintype κ]
    (Λ : Nat → Submodule (ZMod N) (κ → ZMod N)) (n : Nat)
    (hchain : ∀ s < n, Λ s < Λ (s + 1)) : n ≤ Fintype.card κ := by
  have hrank : ∀ s ≤ n, s ≤ Module.finrank (ZMod N) (Λ s) := by
    intro s
    induction s with
    | zero => intro _; exact Nat.zero_le _
    | succ s ih =>
      intro hs
      have h1 := ih (by omega)
      have h2 := Submodule.finrank_lt_finrank_of_lt (hchain s (by omega))
      omega
  have hle := Submodule.finrank_le (Λ n)
  rw [Module.finrank_fintype_fun_eq_card] at hle
  exact (hrank n le_rfl).trans hle

end LeanProofs.GowersSzemeredi
