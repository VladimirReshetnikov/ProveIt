import IPRADerivations.Core.Basic
import IPRADerivations.Core.Header

/-!
# The structural rules of the certificate calculi

The framework packets build their contract and certificate calculi on a small set of admissible rules for
derivability in iPRA. Each of them is a property of the object derivations `Γ ⊢[PRAAx] φ` themselves, proved
here in the metatheory from the deduction kernel:

* `simultaneous_cut`: if `Γ ⊢ φ` and `Δ ⊢ ψ` for every `ψ ∈ Γ`, then `Δ ⊢ φ`
  (`ipra_kifc_framework_2026-11-15`, `ipra_kifc_framework_2026-11-16`, `ipra_kifcr_framework_2026-11-16`,
  `ipra_kifcs_framework_2026-11-16`: `lem:cut`; `darc_ipra_framework_2026-11-16`: "Simultaneous cut";
  `STRIVE-iPRA-framework-2026-11-16`: Theorem "Boundary composition");
* `residual_cut`: if `R, Γ ⊢ A` and `Γ ⊢ B` for every `B ∈ R`, then `Γ ⊢ A`
  (`scope_ipra_framework_2026-11-16`: "Simultaneous residual cut");
* `residual_discharge`: `Γ ⊢ B` and `B, Γ ⊢ A` give `Γ ⊢ A` (the same packet: "Residual discharge");
* `boundary_intro`: `B, Γ ⊢ A` gives `Γ ⊢ B → A` (the same packet: "Boundary introduction");
* `weakening`: `Γ ⊢ φ` and `Γ ⊆ Δ` give `Δ ⊢ φ` (`darc_ipra_framework_2026-11-16`: "Weakening");
* `specialization`: `Γ ⊢ φ` gives `Γ[σ] ⊢ φ[σ]` for every substitution `σ` of terms for the free variables
  (the KIFC editions and DARC: "Substitution"; SCOPE: "Specialization");
* `existential_sealing`: `Γ ⊢ ∃c V(c)` and `V(c), Γ⁺ ⊢ Φ⁺` give `Γ ⊢ Φ`
  (`darc_ipra_framework_2026-11-16`: `lem:exseal`; `scope_ipra_framework_2026-11-16`: Theorem "Private
  sealing"; `STRIVE-iPRA-framework-2026-11-16`: Theorem "Local certificate sealing");
* `qf_induction`: for a quantifier-free `I(z, x)`, from `⊢ I(0, x)` and `I(z, x) ⊢ I(Sz, x)`, every term
  instance `I(t, u)` is derivable in every context (the KIFC editions and DARC: `lem:qfind`).

These are the rules the packets assume of the object theory; the contract calculi built on them are not
formalized here.
-/

namespace LeanProofs.IPRA.Foundations.StructuralRules

open_ipra

variable {n : ℕ} {Γ Δ : List (Fm PTm n)}

/-- Simultaneous cut. -/
theorem simultaneous_cut {φ : Fm PTm n} (h : Γ ⊢[PRAAx] φ) (k : ∀ ψ ∈ Γ, Δ ⊢[PRAAx] ψ) : Δ ⊢[PRAAx] φ :=
  h.trans k

/-- Simultaneous cut of a list of residual hypotheses. -/
theorem residual_cut {R : List (Fm PTm n)} {A : Fm PTm n} (h : (R ++ Γ) ⊢[PRAAx] A)
    (k : ∀ B ∈ R, Γ ⊢[PRAAx] B) : Γ ⊢[PRAAx] A :=
  h.trans fun ψ hψ => by
    rcases List.mem_append.mp hψ with hR | hΓ
    · exact k ψ hR
    · exact .hyp hΓ

/-- Discharge of one residual hypothesis. -/
theorem residual_discharge {A B : Fm PTm n} (h₁ : Γ ⊢[PRAAx] B) (h₂ : (B :: Γ) ⊢[PRAAx] A) :
    Γ ⊢[PRAAx] A :=
  .impE (.impI h₂) h₁

/-- A boundary hypothesis becomes an implication. -/
theorem boundary_intro {A B : Fm PTm n} (h : (B :: Γ) ⊢[PRAAx] A) : Γ ⊢[PRAAx] B ⟶ A :=
  .impI h

/-- Weakening of the context. -/
theorem weakening {φ : Fm PTm n} (h : Γ ⊢[PRAAx] φ) (s : Γ ⊆ Δ) : Δ ⊢[PRAAx] φ :=
  h.weaken s

/-- Substitution of terms for the free variables. -/
theorem specialization {φ : Fm PTm n} (h : Γ ⊢[PRAAx] φ) {m : ℕ} (σ : Fin n → PTm m) :
    Γ.map (fun ψ => ψ.subst σ) ⊢[PRAAx] φ.subst σ :=
  h.subst σ

/-- Sealing of a proof-local certificate: an existential producer and a certificate-parametric consumer. -/
theorem existential_sealing {V : Fm PTm (n + 1)} {Φ : Fm PTm n} (h₁ : Γ ⊢[PRAAx] Fm.ex V)
    (h₂ : (V :: Γ.map Fm.shift) ⊢[PRAAx] Φ.shift) : Γ ⊢[PRAAx] Φ :=
  .exE h₁ h₂

/-- The quantifier-free induction interface: every term instance of the invariant is derivable. -/
theorem qf_induction {k : ℕ} (I : Fm PTm (k + 1)) (hI : I.QF)
    (h0 : ([] : List (Fm PTm k)) ⊢[PRAAx] I.subst (Syn.inst zero))
    (hS : [I] ⊢[PRAAx] I.subst (Syn.repl (succ (var 0)))) (σ : Fin (k + 1) → PTm n) :
    Γ ⊢[PRAAx] I.subst σ :=
  inst (ind I hI h0 hS) σ

end LeanProofs.IPRA.Foundations.StructuralRules
