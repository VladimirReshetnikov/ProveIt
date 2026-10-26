import DiophantineConsistency.NativeFieldCycles2011

/-!
Focused arithmetic checks. In particular511 is a real permitted cycle;
the theorem deliberately does not claim that all cycles have value zero.
-/

namespace DiophantineConsistency.NativeFieldCycles2011Checks

open NativeFieldCycles2011

set_option Elab.async false

/-- All hypotheses of the offset19 theorem hold on the nonzero511 self-loop. -/
example : ∃ (S epsilon : Fin 1 → ℕ) (sstar : ℕ),
    (∀ i, S i < 512) ∧ (∀ i, epsilon i ≤ 1) ∧
    (∀ i, S ((Equiv.refl (Fin 1)) i) = (2*S i + epsilon i)%512) ∧
    (∀ i, epsilon i = 1 → S i = sstar) ∧
    S 0 = 511 ∧ S 0 ≠ 0 := by
  refine ⟨fun _ => 511, fun _ => 1, 511, ?_⟩
  decide

/-- The all-zero cycle also satisfies the same hypotheses, with no
requirement that the exceptional branch is ever taken. -/
example : ∃ (S epsilon : Fin 1 → ℕ),
    (∀ i, S i < 512) ∧ (∀ i, epsilon i ≤ 1) ∧
    (∀ i, S ((Equiv.refl (Fin 1)) i) = (2*S i + epsilon i)%512) ∧
    (∀ i, epsilon i = 1 → S i = 37) ∧ S 0 = 0 := by
  refine ⟨fun _ => 0, fun _ => 0, ?_⟩
  decide

example {A : Type*} [Finite A] (sigma : A ≃ A)
    (S epsilon : A → ℕ) (sstar : ℕ)
    (hS : ∀ i, S i < 512) (he : ∀ i, epsilon i ≤ 1)
    (hstep : ∀ i, S (sigma i) = (2*S i + epsilon i)%512)
    (hgate : ∀ i, epsilon i = 1 → S i = sstar)
    (i : A) (hstart : S i = 510) : False :=
  offset19_excludes_510 sigma S epsilon sstar hS he hstep hgate i hstart

/-- The offset20 theorem specializes to an infinite index type and an
arbitrary, not necessarily invertible source map. -/
example (theta : ℕ → ℕ) (S e : ℕ → ℕ)
    (he : ∀ i, e i ≤ 2)
    (hstep : ∀ i, S i = (4*S (theta i))%512 + e i) : S 0 ≠ 510 :=
  offset20_excludes_510 theta S e he hstep 0

/-- The actual mutually exclusive two-selector prefix discharges the
generic bound without any terminal-color hypothesis. -/
example {A : Type*} (theta : A → A) (S d₀ d₁ : A → ℕ)
    (hone : ∀ i, d₀ i + d₁ i ≤ 1)
    (hstep : ∀ i, S i = (4*S (theta i))%512 + d₀ (theta i) + 2*d₁ (theta i)) :
    ∀ i, S i ≠ 510 := by
  apply offset20_excludes_510 theta S (fun i => d₀ (theta i) + 2*d₁ (theta i))
  · intro i
    have hh := hone (theta i)
    omega
  · intro i
    have hh := hstep i
    omega

#print axioms offset19_excludes_510
#print axioms offset20_excludes_510

end DiophantineConsistency.NativeFieldCycles2011Checks
