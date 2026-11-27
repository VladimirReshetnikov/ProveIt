import IPRADerivations.Foundations.BoundedDecision

/-!
# Case analysis over the values of bounded terms

A reusable piece of the embedding framework, extending `Foundations/BoundedDecision`: if terms
`σ 0, …, σ (m − 1)` are provably `≤ B`, any formula `φ` may be derived by deriving it separately
for every valuation `ρ` of the terms by numerals `≤ B`, in a context where `σ i = num (ρ i)` holds.
The valuation is known in the metatheory, so each case may use arguments that depend on it
(which vertex of a simplex carries which colour, say).

* `bounded_cases`: the case split, by recursion on the number of terms in the metatheory, through
  `BoundedDecision.cases_num`; the derivation has `(B + 1)^m` cases.
-/

namespace LeanProofs.IPRA.Foundations.BoundedCases

open_ipra exports

set_option autoImplicit false

variable {n : ℕ}

/-- A context that derives everything the context `Γ` derives. -/
def Extends (Γ Δ : List (Fm PTm n)) : Prop := ∀ ψ : Fm PTm n, (Γ ⊢[PRAAx] ψ) → (Δ ⊢[PRAAx] ψ)

theorem Extends.refl (Γ : List (Fm PTm n)) : Extends Γ Γ := fun _ h => h

theorem Extends.cons {Γ Δ : List (Fm PTm n)} (h : Extends Γ Δ) (χ : Fm PTm n) : Extends Γ (χ :: Δ) :=
  fun ψ hψ => (h ψ hψ).wk

/-- The induction behind `bounded_cases`: the terms with index `≥ j` are already fixed. -/
theorem cases_aux {m : ℕ} (B : ℕ) (σ : Fin m → PTm n) {Γ : List (Fm PTm n)} (φ : Fm PTm n)
    (k : ∀ ρ : Fin m → ℕ, (∀ i, ρ i ≤ B) → ∀ Δ : List (Fm PTm n), Extends Γ Δ →
      (∀ i, Δ ⊢[PRAAx] σ i ≐ num (ρ i)) → (Δ ⊢[PRAAx] φ)) :
    ∀ (j : ℕ), j ≤ m → ∀ (Δ : List (Fm PTm n)), Extends Γ Δ → ∀ (ρ : Fin m → ℕ), (∀ i, ρ i ≤ B) →
      (∀ i : Fin m, j ≤ i.val → (Δ ⊢[PRAAx] σ i ≐ num (ρ i))) →
      (∀ i, Δ ⊢[PRAAx] le (σ i) (num B)) → (Δ ⊢[PRAAx] φ)
  | 0, _, Δ, hΔ, ρ, hρ, hdet, _ => k ρ hρ Δ hΔ (fun i => hdet i (Nat.zero_le _))
  | j + 1, hj, Δ, hΔ, ρ, hρ, hdet, hle => by
    refine BoundedDecision.cases_num B (hle ⟨j, by omega⟩) (fun v hv => .impI ?_)
    refine cases_aux B σ φ k j (by omega) _ (hΔ.cons _) (fun i => if i.val = j then v else ρ i) ?_ ?_
      (fun i => (hle i).wk)
    · intro i
      by_cases hi : i.val = j
      · simp [hi, hv]
      · simp [hi, hρ i]
    · intro i hi
      by_cases hij : i.val = j
      · have e : i = ⟨j, by omega⟩ := Fin.ext hij
        rw [if_pos hij, e]
        exact Prf.hyp0
      · have hi' : j + 1 ≤ i.val := by omega
        simpa [hij] using (hdet i hi').wk

/-- Case analysis over the numeral values of terms `≤ B`. -/
theorem bounded_cases {m : ℕ} (B : ℕ) (σ : Fin m → PTm n) {Γ : List (Fm PTm n)} (φ : Fm PTm n)
    (hle : ∀ i, Γ ⊢[PRAAx] le (σ i) (num B))
    (k : ∀ ρ : Fin m → ℕ, (∀ i, ρ i ≤ B) → ∀ Δ : List (Fm PTm n), Extends Γ Δ →
      (∀ i, Δ ⊢[PRAAx] σ i ≐ num (ρ i)) → (Δ ⊢[PRAAx] φ)) : Γ ⊢[PRAAx] φ :=
  cases_aux B σ φ k m le_rfl Γ (Extends.refl Γ) (fun _ => 0) (fun _ => Nat.zero_le _)
    (fun i hi => absurd i.isLt (by omega)) hle

end LeanProofs.IPRA.Foundations.BoundedCases
