import IPRADerivations.Core.Basic

/-!
# Congruence of a term in all its arguments

`Prf.eqCongr t h` derives `t[σ] ≐ t[σ']` from derivations `h i : Γ ⊢ σ i ≐ σ' i`. In use, the two substitutions
are written out, the derivations are matched to the variables by a case split, and the substitutions are pushed
back through the term. `ipra_congr` does this from the template and the list of derivations alone:

    theorem f_congr (ha : Γ ⊢ a ≐ a') (hb : Γ ⊢ b ≐ b') : Γ ⊢ f a b ≐ f a' b' := by
      ipra_congr (f (var 0) (var 1) : PTm 2) with [ha, hb]

* `EqPair Γ` packs a derived equation with its two sides, so that a vector of derivations determines both
  substitutions;
* `eqCongrPairs t v` is `Prf.eqCongr` for such a vector;
* `ipra_congr t with [h₀, …, h_{k−1}]` closes a goal `Γ ⊢ s ≐ s'` whose sides are `t` at the left and right sides
  of the `hᵢ`, up to `simp` (the lemmas `subst_f` that push substitutions through defined terms are simp
  lemmas); `ipra_congr t with [h₀, …] using [l₁, …]` adds simp lemmas, for definitions to be unfolded.
-/

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- A derived equation with its sides. -/
structure EqPair (Γ : List (Fm PTm n)) where
  /-- The left side. -/
  lhs : PTm n
  /-- The right side. -/
  rhs : PTm n
  /-- The derivation. -/
  eq : Γ ⊢[PRAAx] lhs ≐ rhs

/-- Congruence of a term in all its variables, for a vector of derived equations. -/
theorem eqCongrPairs {k : ℕ} (t : PTm k) (v : Fin k → EqPair Γ) :
    Γ ⊢[PRAAx] Syn.subst (fun i => (v i).lhs) t ≐ Syn.subst (fun i => (v i).rhs) t :=
  Prf.eqCongr t fun i => (v i).eq

end LeanProofs.IPRA

/-- `ipra_congr t with [h₀, …, h_{k−1}]` derives `t[a₀, …] ≐ t[b₀, …]` from `hᵢ : Γ ⊢ aᵢ ≐ bᵢ`, for a template
`t : PTm k` written with `var 0, …, var (k − 1)`. -/
syntax "ipra_congr " term " with " "[" term,* "]" (" using " "[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| ipra_congr $t with [$hs,*]) => do
      let ps ← hs.getElems.mapM fun h => `((⟨_, _, $h⟩ : LeanProofs.IPRA.EqPair _))
      `(tactic| simpa using LeanProofs.IPRA.eqCongrPairs $t ![$ps,*])
  | `(tactic| ipra_congr $t with [$hs,*] using [$ls,*]) => do
      let ps ← hs.getElems.mapM fun h => `((⟨_, _, $h⟩ : LeanProofs.IPRA.EqPair _))
      `(tactic| simpa [$ls,*] using LeanProofs.IPRA.eqCongrPairs $t ![$ps,*])
