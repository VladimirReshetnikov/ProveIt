import GowersSzemeredi.Proofs16ClaimNineFourSelection
import GowersSzemeredi.Proofs16Lemma92Pair

/-! The core of Milićević's Claim 9.4 (arXiv:2601.01682, printed p. 66): from
many escaping decompositions to a new Freiman homomorphism.

Prescribe, for `εN³` triples `(x, y, a)`, a decomposition
`ξ₀ − ξ₁ = ξ₂ − ξ₃` of a frequency, with `ξ₀ ∈ ⟨Γ_{x+a}⟩_R`,
`ξ₁ ∈ ⟨Γ_x⟩_R`, `ξ₂ ∈ ⟨Γ_{y+a}⟩_R` and `ξ₃ ∈ ⟨Γ_y⟩_R`.
1. `claim_9_4_selection` gives four maps `ψ_i` realizing it on a
   `(2R+1)^(−4d)` fraction.
2. On those triples `ψ₀(x+a) − ψ₁(x) = ψ₂(y+a) − ψ₃(y)` depends only on
   `(a, y)`. So `ψ₀` and `ψ₁` are separated with `ω = y`, and
   `milicevic_lemma_9_2_pair` applies with `c = ε/(2R+1)^(4d)`.
3. This yields a Freiman homomorphism `θ` on a Bohr set, the linear part
   of `ψ₀` on a dense set of values, with `ψ₁ x − ψ₁ x′ = θ(x − x′)` on
   the event fibers.

`claim_9_4_core` states this. The escaping frequency is
`ξ₀ − ξ₁ = ψ₀(x+a) − ψ₁(x)` on the event triples. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- **The core of Claim 9.4.** -/
theorem claim_9_4_core {N : Nat} [NeZero N] [Fact N.Prime] (Γ : ZMod N → Finset (ZMod N))
    {d R : Nat} (hΓ : ∀ z, (Γ z).card ≤ d) (Tr : Finset (ZMod N × ZMod N × ZMod N))
    (ξ : ZMod N × ZMod N × ZMod N → Fin 4 → ZMod N)
    (hξ : ∀ t ∈ Tr, ξ t 0 ∈ spanBall (Γ (t.1 + t.2.2)) R ∧ ξ t 1 ∈ spanBall (Γ t.1) R ∧
      ξ t 2 ∈ spanBall (Γ (t.2.1 + t.2.2)) R ∧ ξ t 3 ∈ spanBall (Γ t.2.1) R)
    (hdec : ∀ t ∈ Tr, ξ t 0 - ξ t 1 = ξ t 2 - ξ t 3)
    {ε : Real} (hε : 0 < ε) (hTr : ε * (N : Real) ^ 3 ≤ Tr.card) :
    ∃ ψ : Fin 4 → ZMod N → ZMod N, (∀ i z, ψ i z ∈ spanBall (Γ z) R) ∧
      ∃ (E : Finset (ZMod N × ZMod N × ZMod N)) (B : Finset (ZMod N)) (θ : ZMod N → ZMod N),
        E ⊆ Tr ∧ ε / ((2 * R + 1) ^ d : Nat) ^ 4 * (N : Real) ^ 3 ≤ E.card ∧
        (∀ t ∈ E, ψ 0 (t.1 + t.2.2) - ψ 1 t.1 = ξ t 0 - ξ t 1) ∧
        FreimanHom 8 B (ψ 0) ∧
        FreimanHom 2 (bohr (section7Spectrum B ((B.card : Real) / N))
          (((B.card : Real) / N) / (32 * Real.pi))) θ ∧
        ∀ t ∈ E, ∀ t' ∈ E, t.2.1 = t'.2.1 → t.2.2 = t'.2.2 →
          t.1 + t.2.2 ∈ B → t'.1 + t'.2.2 ∈ B →
          t.1 - t'.1 ∈ bohr (section7Spectrum B ((B.card : Real) / N))
            (((B.card : Real) / N) / (32 * Real.pi)) →
          ψ 1 t.1 - ψ 1 t'.1 = θ (t.1 - t'.1) := by
  obtain ⟨ψ, hψ, hcount⟩ := claim_9_4_selection Γ hΓ Tr ξ hξ
  set K := (2 * R + 1) ^ d with hKdef
  have hKpos : 0 < K := Nat.pos_of_ne_zero (by positivity)
  let E := Tr.filter fun t => ψ 0 (t.1 + t.2.2) = ξ t 0 ∧ ψ 1 t.1 = ξ t 1 ∧
    ψ 2 (t.2.1 + t.2.2) = ξ t 2 ∧ ψ 3 t.2.1 = ξ t 3
  have hEcard : ε / (K : Real) ^ 4 * (N : Real) ^ 3 ≤ E.card := by
    have hK4 : (0 : Real) < (K : Real) ^ 4 := by positivity
    have h : (Tr.card : Real) ≤ (K : Real) ^ 4 * E.card := by exact_mod_cast hcount
    rw [div_mul_eq_mul_div, div_le_iff₀ hK4]
    nlinarith
  -- the separated family `(x, a, y)`
  let Q := E.image fun t => (t.1, t.2.2, t.2.1)
  have hQcard : Q.card = E.card := by
    apply Finset.card_image_of_injOn
    intro t _ t' _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Prod.ext h.2.2 h.2.1)
  have hsep : ∀ x x' a y, (x, a, y) ∈ Q → (x', a, y) ∈ Q →
      ψ 0 (x + a) - ψ 1 x = ψ 0 (x' + a) - ψ 1 x' := by
    have key : ∀ x a y, (x, a, y) ∈ Q → ψ 0 (x + a) - ψ 1 x = ψ 2 (y + a) - ψ 3 y := by
      intro x a y h
      obtain ⟨t, ht, he⟩ := Finset.mem_image.mp h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      obtain ⟨htT, e0, e1, e2, e3⟩ := Finset.mem_filter.mp ht
      rw [e0, e1, e2, e3]
      exact hdec t htT
    intro x x' a y h h'
    rw [key x a y h, key x' a y h']
  have hQ : ε / (K : Real) ^ 4 * (N : Real) ^ 2 * Fintype.card (ZMod N) ≤ Q.card := by
    rw [ZMod.card, hQcard]
    calc ε / (K : Real) ^ 4 * (N : Real) ^ 2 * (N : Real) = ε / (K : Real) ^ 4 * (N : Real) ^ 3 := by
          ring
      _ ≤ (E.card : Real) := hEcard
  obtain ⟨B, -, θ, -, hF, -, hθ, -, hshare⟩ :=
    milicevic_lemma_9_2_pair (ψ 0) (ψ 1) Q hsep (by positivity) hQ
  refine ⟨ψ, hψ, E, B, θ, Finset.filter_subset _ _, by exact_mod_cast hEcard, ?_, hF, hθ, ?_⟩
  · intro t ht
    obtain ⟨-, e0, e1, -, -⟩ := Finset.mem_filter.mp ht
    rw [e0, e1]
  · intro t ht t' ht' hy ha hB hB' hd
    have hq : (t.1, t.2.2, t.2.1) ∈ Q := Finset.mem_image_of_mem _ ht
    have hq' : (t'.1, t.2.2, t.2.1) ∈ Q := by
      rw [ha, hy]; exact Finset.mem_image_of_mem _ ht'
    exact hshare t.1 t'.1 t.2.2 t.2.1 hq hq' hB (by rw [ha]; exact hB') hd

end LeanProofs.GowersSzemeredi
