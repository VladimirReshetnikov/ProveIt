import IPRADerivations.Core.Basic
import IPRADerivations.Core.Header

/-!
# The open contract calculus

Packet: `foundations/ipra_kifcs_framework_2026-11-16`, `paper/sections/04_open_contracts.tex`
(`def:contract` and the statements built on it); the same calculus is used by
`foundations/ipra_kifcr_framework_2026-11-16` ("Closure by supplied producers") and
`foundations/darc_ipra_framework_2026-11-16` ("Contract/sequent equivalence").

An open contract from a list `A` of formulas to a formula `φ` is the property that every context deriving
all members of `A` derives `φ`:

`Contract A φ := ∀ Δ, (∀ ψ ∈ A, Δ ⊢ ψ) → Δ ⊢ φ`.

* `contract_iff_sequent` (`thm:contract-sequent`): `Contract A φ ↔ A ⊢ φ`;
* `identity`: `φ ∈ A` gives `Contract A φ`;
* `pairing`: contracts to `φ` and to `ψ` give a contract to `φ ∧ ψ`;
* `bind` ("Unary bind"): `Contract A φ` and `Contract (φ :: A) χ` give `Contract A χ`;
* `weaken_interface` (`lem:contract-weakening`): `A ⊆ B` and `Contract A φ` give `Contract B φ`;
* `closed` ("Closed contracts"): `Contract [] φ ↔ [] ⊢ φ`;
* `singleton` ("Singleton implication"): `Contract [ψ] φ` is equivalent to `[ψ] ⊢ φ` and to `⊢ ψ → φ`;
* `normalization` (`prop:contract-normalization`): lists with the same members give equivalent contracts;
* `substitution` (`thm:contract-subst`): `Contract A φ` gives `Contract A[σ] φ[σ]`;
* `residual_discharge` (`thm:residual-discharge`): a contract from `R ++ Γ` and a context deriving every
  member of `R` and of `Γ` give the conclusion in that context;
* `compose` ("Composition of local rules", "Closure by producer contracts"): contracts `A_i ⇒ φ_i` and a
  contract from `φ_0, …, φ_{m−1}, B` to `χ` give a contract from `A_0 ++ ⋯ ++ A_{m−1} ++ B` to `χ`.

Two discharge statements of `foundations/darc_ipra_framework_2026-11-16`:

* `full_discharge` ("Full discharge"): if every residual is a theorem, `⊢ B_i`, the compiled conclusion is a
  theorem, `⊢ Φ`;
* `discharge_some` (`cor:incremental-discharge`, "Incremental producer discharge"): from `R, Γ ⊢ Φ`, if every
  residual of `R` is either kept in `R'` or derivable from `Γ`, then `R', Γ ⊢ Φ`.

The statements are about derivability in iPRA and are proved in the metatheory from simultaneous cut,
weakening and substitution of the deduction kernel.
-/

namespace LeanProofs.IPRA.Foundations.OpenContracts

open_ipra

variable {n : ℕ}

/-- An open contract: every context deriving all members of `A` derives `φ`. -/
def Contract (A : List (Fm PTm n)) (φ : Fm PTm n) : Prop :=
  ∀ Δ : List (Fm PTm n), (∀ ψ ∈ A, Δ ⊢[PRAAx] ψ) → (Δ ⊢[PRAAx] φ)

variable {A B : List (Fm PTm n)} {φ ψ χ : Fm PTm n}

/-- `thm:contract-sequent`. -/
theorem contract_iff_sequent : Contract A φ ↔ (A ⊢[PRAAx] φ) :=
  ⟨fun c => c A fun _ h => .hyp h, fun h _ k => h.trans k⟩

theorem identity (h : φ ∈ A) : Contract A φ := fun _ k => k φ h

theorem pairing (c₁ : Contract A φ) (c₂ : Contract A ψ) : Contract A (φ ⋏ ψ) :=
  fun Δ k => .andI (c₁ Δ k) (c₂ Δ k)

/-- "Unary bind". -/
theorem bind (c₁ : Contract A φ) (c₂ : Contract (φ :: A) χ) : Contract A χ :=
  fun Δ k => c₂ Δ fun θ h => by
    rcases List.mem_cons.mp h with rfl | h'
    · exact c₁ Δ k
    · exact k θ h'

/-- `lem:contract-weakening`. -/
theorem weaken_interface (s : A ⊆ B) (c : Contract A φ) : Contract B φ :=
  fun Δ k => c Δ fun θ h => k θ (s h)

/-- "Closed contracts". -/
theorem closed : Contract ([] : List (Fm PTm n)) φ ↔ (([] : List (Fm PTm n)) ⊢[PRAAx] φ) :=
  contract_iff_sequent

/-- "Singleton implication". -/
theorem singleton :
    (Contract [ψ] φ ↔ ([ψ] ⊢[PRAAx] φ)) ∧ (Contract [ψ] φ ↔ (([] : List (Fm PTm n)) ⊢[PRAAx] ψ ⟶ φ)) :=
  ⟨contract_iff_sequent,
    contract_iff_sequent.trans ⟨fun h => .impI h, fun h => .impE h.wk Prf.hyp0⟩⟩

/-- `prop:contract-normalization`: permutation and duplicate invariance. -/
theorem normalization (h₁ : A ⊆ B) (h₂ : B ⊆ A) : Contract A φ ↔ Contract B φ :=
  ⟨weaken_interface h₁, weaken_interface h₂⟩

/-- `thm:contract-subst`. -/
theorem substitution {m : ℕ} (c : Contract A φ) (σ : Fin n → PTm m) :
    Contract (A.map fun θ => θ.subst σ) (φ.subst σ) :=
  contract_iff_sequent.mpr ((contract_iff_sequent.mp c).subst σ)

/-- `thm:residual-discharge`. -/
theorem residual_discharge {R Γ Δ : List (Fm PTm n)} (c : Contract (R ++ Γ) φ)
    (hR : ∀ θ ∈ R, Δ ⊢[PRAAx] θ) (hΓ : ∀ θ ∈ Γ, Δ ⊢[PRAAx] θ) : Δ ⊢[PRAAx] φ :=
  c Δ fun θ h => (List.mem_append.mp h).elim (hR θ) (hΓ θ)

/-- "Composition of local rules": producer contracts `A_i ⇒ φ_i` compose with a contract from the `φ_i` and
`B`. -/
theorem compose (rs : List (List (Fm PTm n) × Fm PTm n)) (hrs : ∀ r ∈ rs, Contract r.1 r.2)
    (t : Contract (rs.map Prod.snd ++ B) χ) : Contract (rs.flatMap Prod.fst ++ B) χ :=
  fun Δ k => t Δ fun θ h => by
    rcases List.mem_append.mp h with h₁ | h₂
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h₁
      exact hrs r hr Δ fun ξ hξ => k ξ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨r, hr, hξ⟩))
    · exact k θ (List.mem_append_right _ h₂)

/-! ## Discharging residuals -/

/-- "Full discharge": a contract whose premises are all theorems has a theorem as conclusion. -/
theorem full_discharge (c : Contract A φ) (h : ∀ θ ∈ A, ([] : List (Fm PTm n)) ⊢[PRAAx] θ) :
    ([] : List (Fm PTm n)) ⊢[PRAAx] φ :=
  c [] h

/-- `cor:incremental-discharge`: residuals that are derivable from `Γ` may be dropped; the others stay. -/
theorem discharge_some {R R' Γ : List (Fm PTm n)} (h : (R ++ Γ) ⊢[PRAAx] φ)
    (hR : ∀ θ ∈ R, θ ∈ R' ∨ (Γ ⊢[PRAAx] θ)) : (R' ++ Γ) ⊢[PRAAx] φ :=
  h.trans fun θ hθ => by
    rcases List.mem_append.mp hθ with h₁ | h₂
    · rcases hR θ h₁ with hk | hd
      · exact .hyp (List.mem_append_left _ hk)
      · exact hd.weaken (List.subset_append_right _ _)
    · exact .hyp (List.mem_append_right _ h₂)

end LeanProofs.IPRA.Foundations.OpenContracts
