import IPRADerivations.Foundations.IterationFusion
import IPRADerivations.Core.Header

/-!
# Proof-producing composition of local operations

Packet: `foundations/ipra_resources_and_elimination_2026-11-15`, `paper/sections/02_framework.tex`, the local
contract `eq:local-operation`, `V_A(a, D(a, k), z) → V_B(a, k, T(a, k, z))`, and Proposition
`prop:composition` ("Proof-producing composition"): two such operations compose; the composite demand is
obtained by substituting the second demand into the first, the composite output is ordinary PR composition,
and substitution and implication elimination compose the two supplied internal proofs.

An operation is given by a demand `D(k)` (a unary term), an output `T(k, z)` (a binary term) and its
contract between validity formulas `V(d, z)` and `W(k, y)` (variables `0`, `1`), as a rule at arbitrary
contexts and terms (`Contract`): it acts on given proofs and does not use the truth of an input certificate.

* `cdem`, `cout`: the composite demand `D₁(D₂(k))` and output `T₂(k, T₁(D₂(k), z))`, with `app1_cdem`,
  `inst2_cout` (substitution commutes with the composite syntax);
* `compose` (`prop:composition`): `Contract V_A V_B D₁ T₁` and `Contract V_B V_C D₂ T₂` give
  `Contract V_A V_C (D₁ ∘ D₂) (T₂ ∘ T₁)`: the first contract at the intermediate demand `r = D₂(k)`
  concludes exactly the premise of the second.

The finite maximum of several demands is `ModulusNormalization.modulus_le` (it dominates each listed
index); it may replace the demands only together with a restriction proof, which is a separate hypothesis.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.OperationComposition

open_ipra
open LeanProofs.IPRA.Foundations.IterationFusion (app1)

/-- `V(d, z)` at given terms. -/
def at2 {m : ℕ} (V : Fm PTm 2) (a b : PTm m) : Fm PTm m := V.subst ![a, b]

/-- The local contract `V(D(k), z) → W(k, T(k, z))`, as a rule on proofs. -/
def Contract (V W : Fm PTm 2) (D : PTm 1) (T : PTm 2) : Prop :=
  ∀ {m : ℕ} {Δ : List (Fm PTm m)} (k z : PTm m),
    (Δ ⊢[PRAAx] at2 V (app1 D k) z) → (Δ ⊢[PRAAx] at2 W k (inst2 T k z))

/-- The composite demand `D₁(D₂(k))`. -/
def cdem (D₁ D₂ : PTm 1) : PTm 1 := Syn.subst ![D₂] D₁

/-- The composite output `T₂(k, T₁(D₂(k), z))`. -/
def cout (D₂ : PTm 1) (T₁ T₂ : PTm 2) : PTm 2 :=
  Syn.subst ![Syn.var 0, Syn.subst ![app1 D₂ (Syn.var 0), Syn.var 1] T₁] T₂

theorem app1_cdem {m : ℕ} (D₁ D₂ : PTm 1) (k : PTm m) : app1 (cdem D₁ D₂) k = app1 D₁ (app1 D₂ k) := by
  simp only [app1, cdem, Syn.subst_subst]
  congr 1; funext i; fin_cases i; rfl

theorem inst2_cout {m : ℕ} (D₂ : PTm 1) (T₁ T₂ : PTm 2) (k z : PTm m) :
    inst2 (cout D₂ T₁ T₂) k z = inst2 T₂ k (inst2 T₁ (app1 D₂ k) z) := by
  have e₀ : Syn.subst ![k, z] (app1 D₂ (Syn.var 0 : PTm 2)) = app1 D₂ k := by
    simp only [app1, Syn.subst_subst]
    congr 1; funext i; fin_cases i; simp
  have e₁ : Syn.subst ![k, z] (Syn.subst ![app1 D₂ (Syn.var 0), Syn.var 1] T₁) = inst2 T₁ (app1 D₂ k) z := by
    rw [Syn.subst_subst]
    simp only [inst2]
    congr 1; funext j; fin_cases j
    · exact e₀
    · simp
  simp only [inst2, cout, Syn.subst_subst]
  congr 1; funext i; fin_cases i
  · simp
  · simpa [inst2] using e₁

/-- `prop:composition`: the composite of two operations is an operation. -/
theorem compose {VA VB VC : Fm PTm 2} {D₁ D₂ : PTm 1} {T₁ T₂ : PTm 2}
    (h₁ : Contract VA VB D₁ T₁) (h₂ : Contract VB VC D₂ T₂) :
    Contract VA VC (cdem D₁ D₂) (cout D₂ T₁ T₂) := by
  intro m Δ k z h
  rw [app1_cdem] at h
  rw [inst2_cout]
  exact h₂ k _ (h₁ (app1 D₂ k) z h)

end LeanProofs.IPRA.Foundations.OperationComposition
