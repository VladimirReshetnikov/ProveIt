import IPRADerivations.Foundations.StructuralRules
import IPRADerivations.Core.Header

/-!
# Variants of certificate sealing

Packets: `tapir_ipra_framework_2026-11-16` (Theorem `thm:seal`, "Certificate sealing"),
`scope_ipra_framework_2026-11-16_2` (`thm:scoped-realization`, `cor:conditional` "Conditional boundary",
`thm:dependent-sealing` "Dependent sealing") and `scope_ipra_framework_2026-11-16` (Theorem "Existential
output"). All are admissible rules of the object derivations, proved here in the metatheory from the
existential elimination of the deduction kernel (`StructuralRules.existential_sealing`):

* `certificate_sealing` (`thm:seal`, `thm:scoped-realization`): `Γ ⊢ ∃c V(c)` and `V(c), Γ⁺ ⊢ G⁺` give `Γ ⊢ G`;
* `conditional_boundary` (`cor:conditional`): from the extractor `V(c), Γ⁺ ⊢ G⁺` alone, `Γ ⊢ (∃c V(c)) → G`;
* `dependent_sealing` (`thm:dependent-sealing`): `Γ ⊢ ∃x A(x)`, `A(x), Γ⁺ ⊢ ∃y B(x, y)` and
  `B(x, y), (A(x), Γ⁺)⁺ ⊢ G⁺⁺` give `Γ ⊢ G` (two nested scopes, closed in reverse order);
* `existential_output` ("Existential output"): `Γ ⊢ ∃c V(c)` and, inside the certificate scope, a derivation
  of `∃z P(z)` (by existential introduction with a witness `t(c)`) give `Γ ⊢ ∃z P(z)` without a global
  function `c ↦ t(c)`.
-/

namespace LeanProofs.IPRA.Foundations.SealingVariants

open_ipra
open LeanProofs.IPRA.Foundations.StructuralRules (existential_sealing)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `thm:seal`, `thm:scoped-realization`. -/
theorem certificate_sealing {V : Fm PTm (n + 1)} {G : Fm PTm n} (h₁ : Γ ⊢[PRAAx] Fm.ex V)
    (h₂ : (V :: Γ.map Fm.shift) ⊢[PRAAx] G.shift) : Γ ⊢[PRAAx] G :=
  existential_sealing h₁ h₂

/-- `cor:conditional`: the extractor alone gives the conditional boundary `(∃c V(c)) → G`. -/
theorem conditional_boundary {V : Fm PTm (n + 1)} {G : Fm PTm n}
    (h : (V :: Γ.map Fm.shift) ⊢[PRAAx] G.shift) : Γ ⊢[PRAAx] Fm.ex V ⟶ G := by
  refine .impI (existential_sealing Prf.hyp0 (h.weaken ?_))
  intro ψ hψ
  rcases List.mem_cons.mp hψ with e | hψ
  · exact List.mem_cons.mpr (Or.inl e)
  · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr hψ)))

/-- `thm:dependent-sealing`: two nested certificate scopes. -/
theorem dependent_sealing {A : Fm PTm (n + 1)} {B : Fm PTm (n + 2)} {G : Fm PTm n}
    (h₁ : Γ ⊢[PRAAx] Fm.ex A) (h₂ : (A :: Γ.map Fm.shift) ⊢[PRAAx] Fm.ex B)
    (h₃ : (B :: (A :: Γ.map Fm.shift).map Fm.shift) ⊢[PRAAx] G.shift.shift) : Γ ⊢[PRAAx] G :=
  existential_sealing h₁ (existential_sealing h₂ h₃)

/-- "Existential output": an existential conclusion derived inside the certificate scope escapes it. -/
theorem existential_output {V : Fm PTm (n + 1)} {P : Fm PTm (n + 1)} (h₁ : Γ ⊢[PRAAx] Fm.ex V)
    (h₂ : (V :: Γ.map Fm.shift) ⊢[PRAAx] (Fm.ex P).shift) : Γ ⊢[PRAAx] Fm.ex P :=
  existential_sealing h₁ h₂

end LeanProofs.IPRA.Foundations.SealingVariants
